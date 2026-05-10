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
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_ListB(GibCursor end_r_910, GibCursor end_r_912,
                         GibCursor loc_908, GibCursor arg_191_249_424);
GibCursorGibCursorProd _traverse_ListA(GibCursor end_r_915,
                                       GibCursor arg_98_264_439);
GibCursorGibCursorProd _print_List(GibCursor end_r_918,
                                   GibCursor arg_153_268_443);
GibCursorGibCursorGibCursorProd mkListB(GibCursor end_r_921, GibCursor loc_919,
                                        GibInt len_34_291_466);
GibCursorGibCursorProd _traverse_List(GibCursor end_r_924,
                                      GibCursor arg_140_293_470);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_ListA(GibCursor end_r_928, GibCursor end_r_930,
                         GibCursor loc_926, GibCursor arg_93_302_479);
GibCursorGibCursorGibIntProd reduceB(GibCursor *end_r_933,
                                     GibCursor *lst_36_307_484);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_ListA(GibCursor end_r_937, GibCursor end_r_939, GibCursor loc_935,
            GibCursor arg_88_315_493);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_ListB(GibCursor end_r_943, GibCursor end_r_945, GibCursor loc_941,
            GibCursor arg_176_330_498);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_List(GibCursor end_r_949, GibCursor end_r_951, GibCursor loc_947,
           GibCursor arg_114_345_513);
GibCursorGibCursorProd _traverse_ListB(GibCursor end_r_954,
                                       GibCursor arg_206_358_526);
GibCursorGibCursorProd _print_ListA(GibCursor end_r_957,
                                    GibCursor arg_103_369_535);
GibCursorGibCursorProd _print_ListB(GibCursor end_r_960,
                                    GibCursor arg_221_380_546);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_List(GibCursor end_r_964, GibCursor end_r_966,
                        GibCursor loc_962, GibCursor arg_127_406_572);
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
    gib_add_symbol(2176, ")");
    gib_add_symbol(2177, "(NilB");
    gib_add_symbol(2178, "(NilA");
    gib_add_symbol(2179, "(Nil");
    gib_add_symbol(2180, "(ConsB");
    gib_add_symbol(2181, "(ConsA");
    gib_add_symbol(2182, "(Cons");
    gib_add_symbol(2183, " ->r ");
    gib_add_symbol(2184, " ->i ");
    gib_add_symbol(2185, " ");
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_ListB(GibCursor end_r_910,
                                                                           GibCursor end_r_912,
                                                                           GibCursor loc_908,
                                                                           GibCursor arg_191_249_424)
{
    GibPackedTag tmpval_2197 = *(GibPackedTag *) arg_191_249_424;
    GibCursor tmpcur_2198 = arg_191_249_424 + 1;
    
    
  switch_2256:
    ;
    switch (tmpval_2197) {
        
      case 0:
        {
            GibInt tmpval_2199 = *(GibInt *) tmpcur_2198;
            GibCursor tmpcur_2200 = tmpcur_2198 + sizeof(GibInt);
            GibInt tmpval_2201 = *(GibInt *) tmpcur_2200;
            GibCursor tmpcur_2202 = tmpcur_2200 + sizeof(GibInt);
            GibInt tmpval_2203 = *(GibInt *) tmpcur_2202;
            GibCursor tmpcur_2204 = tmpcur_2202 + sizeof(GibInt);
            GibInt tmpval_2205 = *(GibInt *) tmpcur_2204;
            GibCursor tmpcur_2206 = tmpcur_2204 + sizeof(GibInt);
            GibInt tmpval_2207 = *(GibInt *) tmpcur_2206;
            GibCursor tmpcur_2208 = tmpcur_2206 + sizeof(GibInt);
            GibInt tmpval_2209 = *(GibInt *) tmpcur_2208;
            GibCursor tmpcur_2210 = tmpcur_2208 + sizeof(GibInt);
            GibCursor jump_1240 = tmpcur_2208 + 8;
            GibCursor jump_1239 = tmpcur_2206 + 8;
            GibCursor jump_1238 = tmpcur_2204 + 8;
            GibCursor jump_1237 = tmpcur_2202 + 8;
            GibCursor jump_1236 = tmpcur_2200 + 8;
            GibCursor jump_1235 = tmpcur_2198 + 8;
            GibCursor loc_985 = loc_908 + 1;
            GibCursor loc_986 = loc_985 + 8;
            GibCursor loc_987 = loc_986 + 8;
            GibCursor loc_988 = loc_987 + 8;
            GibCursor loc_989 = loc_988 + 8;
            GibCursor loc_990 = loc_989 + 8;
            GibCursor loc_991 = loc_990 + 8;
            
            *(GibPackedTag *) loc_908 = 0;
            
            GibCursor writetag_1586 = loc_908 + 1;
            GibCursor after_tag_1587 = loc_908 + 1;
            
            *(GibInt *) after_tag_1587 = tmpval_2199;
            
            GibCursor writecur_1591 = after_tag_1587 + sizeof(GibInt);
            
            *(GibInt *) writecur_1591 = tmpval_2201;
            
            GibCursor writecur_1592 = writecur_1591 + sizeof(GibInt);
            
            *(GibInt *) writecur_1592 = tmpval_2203;
            
            GibCursor writecur_1593 = writecur_1592 + sizeof(GibInt);
            
            *(GibInt *) writecur_1593 = tmpval_2205;
            
            GibCursor writecur_1594 = writecur_1593 + sizeof(GibInt);
            
            *(GibInt *) writecur_1594 = tmpval_2207;
            
            GibCursor writecur_1595 = writecur_1594 + sizeof(GibInt);
            
            *(GibInt *) writecur_1595 = tmpval_2209;
            
            GibCursor writecur_1596 = writecur_1595 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_0 =
                                                               _copy_without_ptrs_ListB(end_r_910, end_r_912, loc_991, tmpcur_2210);
            GibCursor pvrtmp_2211 = tmp_struct_0.field0;
            GibCursor pvrtmp_2212 = tmp_struct_0.field1;
            GibCursor pvrtmp_2213 = tmp_struct_0.field2;
            GibCursor pvrtmp_2214 = tmp_struct_0.field3;
            GibCursor pvrtmp_2215 = tmp_struct_0.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_1;
            
            return_1.field0 = pvrtmp_2211;
            return_1.field1 = pvrtmp_2212;
            return_1.field2 = pvrtmp_2213;
            return_1.field3 = loc_908;
            return_1.field4 = pvrtmp_2215;
            return return_1;
            break;
        }
        
      case 1:
        {
            GibCursor jump_loc_1243 = arg_191_249_424 + 1;
            
            *(GibPackedTag *) loc_908 = 1;
            
            GibCursor writetag_1601 = loc_908 + 1;
            GibCursor after_tag_1602 = loc_908 + 1;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_2;
            
            return_2.field0 = end_r_910;
            return_2.field1 = end_r_912;
            return_2.field2 = jump_loc_1243;
            return_2.field3 = loc_908;
            return_2.field4 = after_tag_1602;
            return return_2;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_5 = *(uintptr_t *) tmpcur_2198;
            GibCursor tmpcur_2228 = GIB_UNTAG(tagged_tmpcur_5);
            GibCursor tmpaftercur_2229 = tmpcur_2198 + 8;
            uint16_t tmptag_2230 = GIB_GET_TAG(tagged_tmpcur_5);
            GibCursor end_from_tagged_indr_1352 = tmpcur_2228 + tmptag_2230;
            GibCursor jump_loc_1354 = tmpcur_2198 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_3 =
                                                               _copy_without_ptrs_ListB(tmpcur_2228, end_r_912, loc_908, tmpcur_2228);
            GibCursor pvrtmp_2231 = tmp_struct_3.field0;
            GibCursor pvrtmp_2232 = tmp_struct_3.field1;
            GibCursor pvrtmp_2233 = tmp_struct_3.field2;
            GibCursor pvrtmp_2234 = tmp_struct_3.field3;
            GibCursor pvrtmp_2235 = tmp_struct_3.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_4;
            
            return_4.field0 = end_r_910;
            return_4.field1 = pvrtmp_2232;
            return_4.field2 = jump_loc_1354;
            return_4.field3 = pvrtmp_2234;
            return_4.field4 = pvrtmp_2235;
            return return_4;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_8 = *(uintptr_t *) tmpcur_2198;
            GibCursor tmpcur_2242 = GIB_UNTAG(tagged_tmpcur_8);
            GibCursor tmpaftercur_2243 = tmpcur_2198 + 8;
            uint16_t tmptag_2244 = GIB_GET_TAG(tagged_tmpcur_8);
            GibCursor end_from_tagged_indr_1352 = tmpcur_2242 + tmptag_2244;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_6 =
                                                               _copy_without_ptrs_ListB(tmpcur_2242, end_r_912, loc_908, tmpcur_2242);
            GibCursor pvrtmp_2245 = tmp_struct_6.field0;
            GibCursor pvrtmp_2246 = tmp_struct_6.field1;
            GibCursor pvrtmp_2247 = tmp_struct_6.field2;
            GibCursor pvrtmp_2248 = tmp_struct_6.field3;
            GibCursor pvrtmp_2249 = tmp_struct_6.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_7;
            
            return_7.field0 = pvrtmp_2245;
            return_7.field1 = pvrtmp_2246;
            return_7.field2 = pvrtmp_2247;
            return_7.field3 = pvrtmp_2248;
            return_7.field4 = pvrtmp_2249;
            return return_7;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2197");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_ListA(GibCursor end_r_915,
                                       GibCursor arg_98_264_439)
{
    GibPackedTag tmpval_2257 = *(GibPackedTag *) arg_98_264_439;
    GibCursor tmpcur_2258 = arg_98_264_439 + 1;
    
    
  switch_2273:
    ;
    switch (tmpval_2257) {
        
      case 0:
        {
            GibInt tmpval_2259 = *(GibInt *) tmpcur_2258;
            GibCursor tmpcur_2260 = tmpcur_2258 + sizeof(GibInt);
            GibCursor jump_1245 = tmpcur_2258 + 8;
            GibCursorGibCursorProd tmp_struct_9 =
                                    _traverse_ListA(end_r_915, tmpcur_2260);
            GibCursor pvrtmp_2261 = tmp_struct_9.field0;
            GibCursor pvrtmp_2262 = tmp_struct_9.field1;
            GibCursorGibCursorProd return_10;
            
            return_10.field0 = pvrtmp_2261;
            return_10.field1 = pvrtmp_2262;
            return return_10;
            break;
        }
        
      case 1:
        {
            GibCursor jump_loc_1248 = arg_98_264_439 + 1;
            GibCursorGibCursorProd return_11;
            
            return_11.field0 = end_r_915;
            return_11.field1 = jump_loc_1248;
            return return_11;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_14 = *(uintptr_t *) tmpcur_2258;
            GibCursor tmpcur_2263 = GIB_UNTAG(tagged_tmpcur_14);
            GibCursor tmpaftercur_2264 = tmpcur_2258 + 8;
            uint16_t tmptag_2265 = GIB_GET_TAG(tagged_tmpcur_14);
            GibCursor end_from_tagged_indr_1358 = tmpcur_2263 + tmptag_2265;
            GibCursor jump_loc_1360 = tmpcur_2258 + 8;
            GibCursorGibCursorProd tmp_struct_12 =
                                    _traverse_ListA(tmpcur_2263, tmpcur_2263);
            GibCursor pvrtmp_2266 = tmp_struct_12.field0;
            GibCursor pvrtmp_2267 = tmp_struct_12.field1;
            GibCursorGibCursorProd return_13;
            
            return_13.field0 = end_r_915;
            return_13.field1 = jump_loc_1360;
            return return_13;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_17 = *(uintptr_t *) tmpcur_2258;
            GibCursor tmpcur_2268 = GIB_UNTAG(tagged_tmpcur_17);
            GibCursor tmpaftercur_2269 = tmpcur_2258 + 8;
            uint16_t tmptag_2270 = GIB_GET_TAG(tagged_tmpcur_17);
            GibCursor end_from_tagged_indr_1358 = tmpcur_2268 + tmptag_2270;
            GibCursorGibCursorProd tmp_struct_15 =
                                    _traverse_ListA(tmpcur_2268, tmpcur_2268);
            GibCursor pvrtmp_2271 = tmp_struct_15.field0;
            GibCursor pvrtmp_2272 = tmp_struct_15.field1;
            GibCursorGibCursorProd return_16;
            
            return_16.field0 = pvrtmp_2271;
            return_16.field1 = pvrtmp_2272;
            return return_16;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2257");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_List(GibCursor end_r_918,
                                   GibCursor arg_153_268_443)
{
    GibPackedTag tmpval_2274 = *(GibPackedTag *) arg_153_268_443;
    GibCursor tmpcur_2275 = arg_153_268_443 + 1;
    
    
  switch_2298:
    ;
    switch (tmpval_2274) {
        
      case 0:
        {
            GibInt tmpval_2276 = *(GibInt *) tmpcur_2275;
            GibCursor tmpcur_2277 = tmpcur_2275 + sizeof(GibInt);
            GibInt tmpval_2278 = *(GibInt *) tmpcur_2277;
            GibCursor tmpcur_2279 = tmpcur_2277 + sizeof(GibInt);
            GibInt tmpval_2280 = *(GibInt *) tmpcur_2279;
            GibCursor tmpcur_2281 = tmpcur_2279 + sizeof(GibInt);
            GibInt tmpval_2282 = *(GibInt *) tmpcur_2281;
            GibCursor tmpcur_2283 = tmpcur_2281 + sizeof(GibInt);
            GibCursor jump_1253 = tmpcur_2281 + 8;
            GibCursor jump_1252 = tmpcur_2279 + 8;
            GibCursor jump_1251 = tmpcur_2277 + 8;
            GibCursor jump_1250 = tmpcur_2275 + 8;
            unsigned char wildcard_166_275_450 = gib_print_symbol(2182);
            unsigned char wildcard_173_276_451 = gib_print_symbol(2185);
            unsigned char y_160_277_452 = printf("%ld", tmpval_2276);
            unsigned char wildcard_172_278_453 = gib_print_symbol(2185);
            unsigned char y_161_279_454 = printf("%ld", tmpval_2278);
            unsigned char wildcard_171_280_455 = gib_print_symbol(2185);
            unsigned char y_162_281_456 = printf("%ld", tmpval_2280);
            unsigned char wildcard_170_282_457 = gib_print_symbol(2185);
            unsigned char y_163_283_458 = printf("%ld", tmpval_2282);
            unsigned char wildcard_169_284_459 = gib_print_symbol(2185);
            GibCursorGibCursorProd tmp_struct_18 =
                                    _print_ListA(end_r_918, tmpcur_2283);
            GibCursor pvrtmp_2284 = tmp_struct_18.field0;
            GibCursor pvrtmp_2285 = tmp_struct_18.field1;
            unsigned char wildcard_168_286_461 = gib_print_symbol(2185);
            GibCursorGibCursorProd tmp_struct_19 =
                                    _print_List(pvrtmp_2284, pvrtmp_2285);
            GibCursor pvrtmp_2286 = tmp_struct_19.field0;
            GibCursor pvrtmp_2287 = tmp_struct_19.field1;
            unsigned char wildcard_167_288_463 = gib_print_symbol(2176);
            GibCursorGibCursorProd return_20;
            
            return_20.field0 = pvrtmp_2286;
            return_20.field1 = pvrtmp_2287;
            return return_20;
            break;
        }
        
      case 1:
        {
            GibCursor jump_loc_1257 = arg_153_268_443 + 1;
            unsigned char wildcard_174_289_464 = gib_print_symbol(2179);
            unsigned char wildcard_175_290_465 = gib_print_symbol(2176);
            GibCursorGibCursorProd return_21;
            
            return_21.field0 = end_r_918;
            return_21.field1 = jump_loc_1257;
            return return_21;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_24 = *(uintptr_t *) tmpcur_2275;
            GibCursor tmpcur_2288 = GIB_UNTAG(tagged_tmpcur_24);
            GibCursor tmpaftercur_2289 = tmpcur_2275 + 8;
            uint16_t tmptag_2290 = GIB_GET_TAG(tagged_tmpcur_24);
            GibCursor end_from_tagged_indr_1364 = tmpcur_2288 + tmptag_2290;
            GibCursor jump_loc_1366 = tmpcur_2275 + 8;
            unsigned char wildcard_1369 = gib_print_symbol(2184);
            GibCursorGibCursorProd tmp_struct_22 =
                                    _print_List(tmpcur_2288, tmpcur_2288);
            GibCursor pvrtmp_2291 = tmp_struct_22.field0;
            GibCursor pvrtmp_2292 = tmp_struct_22.field1;
            GibCursorGibCursorProd return_23;
            
            return_23.field0 = end_r_918;
            return_23.field1 = jump_loc_1366;
            return return_23;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_27 = *(uintptr_t *) tmpcur_2275;
            GibCursor tmpcur_2293 = GIB_UNTAG(tagged_tmpcur_27);
            GibCursor tmpaftercur_2294 = tmpcur_2275 + 8;
            uint16_t tmptag_2295 = GIB_GET_TAG(tagged_tmpcur_27);
            GibCursor end_from_tagged_indr_1364 = tmpcur_2293 + tmptag_2295;
            unsigned char wildcard_1369 = gib_print_symbol(2183);
            GibCursorGibCursorProd tmp_struct_25 =
                                    _print_List(tmpcur_2293, tmpcur_2293);
            GibCursor pvrtmp_2296 = tmp_struct_25.field0;
            GibCursor pvrtmp_2297 = tmp_struct_25.field1;
            GibCursorGibCursorProd return_26;
            
            return_26.field0 = pvrtmp_2296;
            return_26.field1 = pvrtmp_2297;
            return return_26;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2274");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorProd mkListB(GibCursor end_r_921, GibCursor loc_919,
                                        GibInt len_34_291_466)
{
    if (loc_919 + 58 > end_r_921) {
        gib_grow_region(&loc_919, &end_r_921);
    }
    
    GibBool fltIf_419_467 = len_34_291_466 <= 0;
    
    if (fltIf_419_467) {
        *(GibPackedTag *) loc_919 = 1;
        
        GibCursor writetag_1651 = loc_919 + 1;
        GibCursor after_tag_1652 = loc_919 + 1;
        GibCursorGibCursorGibCursorProd return_28;
        
        return_28.field0 = end_r_921;
        return_28.field1 = loc_919;
        return_28.field2 = after_tag_1652;
        return return_28;
    } else {
        GibInt fltAppE_420_468 = len_34_291_466 - 1;
        GibCursor loc_1026 = loc_919 + 1;
        GibCursor loc_1027 = loc_1026 + 8;
        GibCursor loc_1028 = loc_1027 + 8;
        GibCursor loc_1029 = loc_1028 + 8;
        GibCursor loc_1030 = loc_1029 + 8;
        GibCursor loc_1031 = loc_1030 + 8;
        GibCursor loc_1032 = loc_1031 + 8;
        
        *(GibPackedTag *) loc_919 = 0;
        
        GibCursor writetag_1660 = loc_919 + 1;
        GibCursor after_tag_1661 = loc_919 + 1;
        
        *(GibInt *) after_tag_1661 = len_34_291_466;
        
        GibCursor writecur_1665 = after_tag_1661 + sizeof(GibInt);
        
        *(GibInt *) writecur_1665 = len_34_291_466;
        
        GibCursor writecur_1666 = writecur_1665 + sizeof(GibInt);
        
        *(GibInt *) writecur_1666 = len_34_291_466;
        
        GibCursor writecur_1667 = writecur_1666 + sizeof(GibInt);
        
        *(GibInt *) writecur_1667 = len_34_291_466;
        
        GibCursor writecur_1668 = writecur_1667 + sizeof(GibInt);
        
        *(GibInt *) writecur_1668 = len_34_291_466;
        
        GibCursor writecur_1669 = writecur_1668 + sizeof(GibInt);
        
        *(GibInt *) writecur_1669 = len_34_291_466;
        
        GibCursor writecur_1670 = writecur_1669 + sizeof(GibInt);
        GibCursorGibCursorGibCursorProd tmp_struct_29 =
                                         mkListB(end_r_921, loc_1032, fltAppE_420_468);
        GibCursor pvrtmp_2303 = tmp_struct_29.field0;
        GibCursor pvrtmp_2304 = tmp_struct_29.field1;
        GibCursor pvrtmp_2305 = tmp_struct_29.field2;
        GibCursorGibCursorGibCursorProd return_30;
        
        return_30.field0 = pvrtmp_2303;
        return_30.field1 = loc_919;
        return_30.field2 = pvrtmp_2305;
        return return_30;
    }
}
GibCursorGibCursorProd _traverse_List(GibCursor end_r_924,
                                      GibCursor arg_140_293_470)
{
    GibPackedTag tmpval_2314 = *(GibPackedTag *) arg_140_293_470;
    GibCursor tmpcur_2315 = arg_140_293_470 + 1;
    
    
  switch_2338:
    ;
    switch (tmpval_2314) {
        
      case 0:
        {
            GibInt tmpval_2316 = *(GibInt *) tmpcur_2315;
            GibCursor tmpcur_2317 = tmpcur_2315 + sizeof(GibInt);
            GibInt tmpval_2318 = *(GibInt *) tmpcur_2317;
            GibCursor tmpcur_2319 = tmpcur_2317 + sizeof(GibInt);
            GibInt tmpval_2320 = *(GibInt *) tmpcur_2319;
            GibCursor tmpcur_2321 = tmpcur_2319 + sizeof(GibInt);
            GibInt tmpval_2322 = *(GibInt *) tmpcur_2321;
            GibCursor tmpcur_2323 = tmpcur_2321 + sizeof(GibInt);
            GibCursor jump_1264 = tmpcur_2321 + 8;
            GibCursor jump_1263 = tmpcur_2319 + 8;
            GibCursor jump_1262 = tmpcur_2317 + 8;
            GibCursor jump_1261 = tmpcur_2315 + 8;
            GibCursorGibCursorProd tmp_struct_34 =
                                    _traverse_ListA(end_r_924, tmpcur_2323);
            GibCursor pvrtmp_2324 = tmp_struct_34.field0;
            GibCursor pvrtmp_2325 = tmp_struct_34.field1;
            GibCursorGibCursorProd tmp_struct_35 =
                                    _traverse_List(pvrtmp_2324, pvrtmp_2325);
            GibCursor pvrtmp_2326 = tmp_struct_35.field0;
            GibCursor pvrtmp_2327 = tmp_struct_35.field1;
            GibCursorGibCursorProd return_36;
            
            return_36.field0 = pvrtmp_2326;
            return_36.field1 = pvrtmp_2327;
            return return_36;
            break;
        }
        
      case 1:
        {
            GibCursor jump_loc_1268 = arg_140_293_470 + 1;
            GibCursorGibCursorProd return_37;
            
            return_37.field0 = end_r_924;
            return_37.field1 = jump_loc_1268;
            return return_37;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_40 = *(uintptr_t *) tmpcur_2315;
            GibCursor tmpcur_2328 = GIB_UNTAG(tagged_tmpcur_40);
            GibCursor tmpaftercur_2329 = tmpcur_2315 + 8;
            uint16_t tmptag_2330 = GIB_GET_TAG(tagged_tmpcur_40);
            GibCursor end_from_tagged_indr_1370 = tmpcur_2328 + tmptag_2330;
            GibCursor jump_loc_1372 = tmpcur_2315 + 8;
            GibCursorGibCursorProd tmp_struct_38 =
                                    _traverse_List(tmpcur_2328, tmpcur_2328);
            GibCursor pvrtmp_2331 = tmp_struct_38.field0;
            GibCursor pvrtmp_2332 = tmp_struct_38.field1;
            GibCursorGibCursorProd return_39;
            
            return_39.field0 = end_r_924;
            return_39.field1 = jump_loc_1372;
            return return_39;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_43 = *(uintptr_t *) tmpcur_2315;
            GibCursor tmpcur_2333 = GIB_UNTAG(tagged_tmpcur_43);
            GibCursor tmpaftercur_2334 = tmpcur_2315 + 8;
            uint16_t tmptag_2335 = GIB_GET_TAG(tagged_tmpcur_43);
            GibCursor end_from_tagged_indr_1370 = tmpcur_2333 + tmptag_2335;
            GibCursorGibCursorProd tmp_struct_41 =
                                    _traverse_List(tmpcur_2333, tmpcur_2333);
            GibCursor pvrtmp_2336 = tmp_struct_41.field0;
            GibCursor pvrtmp_2337 = tmp_struct_41.field1;
            GibCursorGibCursorProd return_42;
            
            return_42.field0 = pvrtmp_2336;
            return_42.field1 = pvrtmp_2337;
            return return_42;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2314");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_ListA(GibCursor end_r_928,
                                                                           GibCursor end_r_930,
                                                                           GibCursor loc_926,
                                                                           GibCursor arg_93_302_479)
{
    GibPackedTag tmpval_2339 = *(GibPackedTag *) arg_93_302_479;
    GibCursor tmpcur_2340 = arg_93_302_479 + 1;
    
    
  switch_2388:
    ;
    switch (tmpval_2339) {
        
      case 0:
        {
            GibInt tmpval_2341 = *(GibInt *) tmpcur_2340;
            GibCursor tmpcur_2342 = tmpcur_2340 + sizeof(GibInt);
            GibCursor jump_1270 = tmpcur_2340 + 8;
            GibCursor loc_1065 = loc_926 + 1;
            GibCursor loc_1066 = loc_1065 + 8;
            
            *(GibPackedTag *) loc_926 = 0;
            
            GibCursor writetag_1699 = loc_926 + 1;
            GibCursor after_tag_1700 = loc_926 + 1;
            
            *(GibInt *) after_tag_1700 = tmpval_2341;
            
            GibCursor writecur_1704 = after_tag_1700 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_44 =
                                                               _copy_without_ptrs_ListA(end_r_928, end_r_930, loc_1066, tmpcur_2342);
            GibCursor pvrtmp_2343 = tmp_struct_44.field0;
            GibCursor pvrtmp_2344 = tmp_struct_44.field1;
            GibCursor pvrtmp_2345 = tmp_struct_44.field2;
            GibCursor pvrtmp_2346 = tmp_struct_44.field3;
            GibCursor pvrtmp_2347 = tmp_struct_44.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_45;
            
            return_45.field0 = pvrtmp_2343;
            return_45.field1 = pvrtmp_2344;
            return_45.field2 = pvrtmp_2345;
            return_45.field3 = loc_926;
            return_45.field4 = pvrtmp_2347;
            return return_45;
            break;
        }
        
      case 1:
        {
            GibCursor jump_loc_1273 = arg_93_302_479 + 1;
            
            *(GibPackedTag *) loc_926 = 1;
            
            GibCursor writetag_1709 = loc_926 + 1;
            GibCursor after_tag_1710 = loc_926 + 1;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_46;
            
            return_46.field0 = end_r_928;
            return_46.field1 = end_r_930;
            return_46.field2 = jump_loc_1273;
            return_46.field3 = loc_926;
            return_46.field4 = after_tag_1710;
            return return_46;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_49 = *(uintptr_t *) tmpcur_2340;
            GibCursor tmpcur_2360 = GIB_UNTAG(tagged_tmpcur_49);
            GibCursor tmpaftercur_2361 = tmpcur_2340 + 8;
            uint16_t tmptag_2362 = GIB_GET_TAG(tagged_tmpcur_49);
            GibCursor end_from_tagged_indr_1376 = tmpcur_2360 + tmptag_2362;
            GibCursor jump_loc_1378 = tmpcur_2340 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_47 =
                                                               _copy_without_ptrs_ListA(tmpcur_2360, end_r_930, loc_926, tmpcur_2360);
            GibCursor pvrtmp_2363 = tmp_struct_47.field0;
            GibCursor pvrtmp_2364 = tmp_struct_47.field1;
            GibCursor pvrtmp_2365 = tmp_struct_47.field2;
            GibCursor pvrtmp_2366 = tmp_struct_47.field3;
            GibCursor pvrtmp_2367 = tmp_struct_47.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_48;
            
            return_48.field0 = end_r_928;
            return_48.field1 = pvrtmp_2364;
            return_48.field2 = jump_loc_1378;
            return_48.field3 = pvrtmp_2366;
            return_48.field4 = pvrtmp_2367;
            return return_48;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_52 = *(uintptr_t *) tmpcur_2340;
            GibCursor tmpcur_2374 = GIB_UNTAG(tagged_tmpcur_52);
            GibCursor tmpaftercur_2375 = tmpcur_2340 + 8;
            uint16_t tmptag_2376 = GIB_GET_TAG(tagged_tmpcur_52);
            GibCursor end_from_tagged_indr_1376 = tmpcur_2374 + tmptag_2376;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_50 =
                                                               _copy_without_ptrs_ListA(tmpcur_2374, end_r_930, loc_926, tmpcur_2374);
            GibCursor pvrtmp_2377 = tmp_struct_50.field0;
            GibCursor pvrtmp_2378 = tmp_struct_50.field1;
            GibCursor pvrtmp_2379 = tmp_struct_50.field2;
            GibCursor pvrtmp_2380 = tmp_struct_50.field3;
            GibCursor pvrtmp_2381 = tmp_struct_50.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_51;
            
            return_51.field0 = pvrtmp_2377;
            return_51.field1 = pvrtmp_2378;
            return_51.field2 = pvrtmp_2379;
            return_51.field3 = pvrtmp_2380;
            return_51.field4 = pvrtmp_2381;
            return return_51;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2339");
            exit(1);
        }
    }
}

GibCursorGibCursorGibIntProd reduceB(GibCursor *end_r_933,
             GibCursor *lst_36_307_484)
{
    GibPackedTag tmpval_2389 = *(GibPackedTag *) (*lst_36_307_484);
    //GibCursor tmpcur_2390 = lst_36_307_484 + 1;
    *lst_36_307_484 += 1;
    
    
  switch_2418:
    ;
    switch (tmpval_2389) {
        
      case 1:
        {
            //GibCursor jump_loc_1276 = lst_36_307_484 + 1;
            GibCursorGibCursorGibIntProd return_53;
            
            //return_53.field0 = end_r_933;
            //return_53.field1 = jump_loc_1276;
            return_53.field2 = 0;
            //*res += 0;
            return return_53;
            break;
        }
        
      case 0:
        {
            GibInt tmpval_2391 = *(GibInt *) (*lst_36_307_484);

            // GibCursor tmpcur_2392 = tmpcur_2390 + sizeof(GibInt);
            //
            // GibInt tmpval_2393 = *(GibInt *) tmpcur_2392;
            // GibCursor tmpcur_2394 = tmpcur_2392 + sizeof(GibInt);
            // GibInt tmpval_2395 = *(GibInt *) tmpcur_2394;
            // GibCursor tmpcur_2396 = tmpcur_2394 + sizeof(GibInt);
            // GibInt tmpval_2397 = *(GibInt *) tmpcur_2396;
            // GibCursor tmpcur_2398 = tmpcur_2396 + sizeof(GibInt);
            // GibInt tmpval_2399 = *(GibInt *) tmpcur_2398;
            // GibCursor tmpcur_2400 = tmpcur_2398 + sizeof(GibInt);
            // GibInt tmpval_2401 = *(GibInt *) tmpcur_2400;
            // GibCursor tmpcur_2402 = tmpcur_2400 + sizeof(GibInt);

            //*lst_36_307_484 += ((sizeof(GibInt)) * 6);

            *lst_36_307_484 += sizeof(GibInt);
            *lst_36_307_484 += sizeof(GibInt);
            *lst_36_307_484 += sizeof(GibInt);
            *lst_36_307_484 += sizeof(GibInt);
            *lst_36_307_484 += sizeof(GibInt);
            *lst_36_307_484 += sizeof(GibInt);

            // GibCursor jump_1282 = tmpcur_2400 + 8;
            // GibCursor jump_1281 = tmpcur_2398 + 8;
            // GibCursor jump_1280 = tmpcur_2396 + 8;
            // GibCursor jump_1279 = tmpcur_2394 + 8;
            // GibCursor jump_1278 = tmpcur_2392 + 8;
            // GibCursor jump_1277 = tmpcur_2390 + 8;

            //*res = *res + tmpval_2391;
             GibCursorGibCursorGibIntProd tmp_struct_54 = reduceB(end_r_933, lst_36_307_484);

            //GibCursor pvrtmp_2403 = tmp_struct_54.field0;
            //GibCursor pvrtmp_2404 = tmp_struct_54.field1;
            GibInt pvrtmp_2405 = tmp_struct_54.field2;
            GibInt tailprim_1284 = tmpval_2391 + pvrtmp_2405;
            GibCursorGibCursorGibIntProd return_55;
            
            //return_55.field0 = pvrtmp_2403;
            //return_55.field1 = pvrtmp_2404;
            return_55.field2 = tailprim_1284;
            return return_55;
            break;
        }
        
//       case GIB_INDIRECTION_TAG:
//         {
//             uintptr_t tagged_tmpcur_58 = *(uintptr_t *) tmpcur_2390;
//             GibCursor tmpcur_2406 = GIB_UNTAG(tagged_tmpcur_58);
//             GibCursor tmpaftercur_2407 = tmpcur_2390 + 8;
//             uint16_t tmptag_2408 = GIB_GET_TAG(tagged_tmpcur_58);
//             GibCursor end_from_tagged_indr_1382 = tmpcur_2406 + tmptag_2408;
//             GibCursor jump_loc_1384 = tmpcur_2390 + 8;
//             GibCursorGibCursorGibIntProd tmp_struct_56 =
//                                           reduceB(tmpcur_2406, tmpcur_2406);
//             GibCursor pvrtmp_2409 = tmp_struct_56.field0;
//             GibCursor pvrtmp_2410 = tmp_struct_56.field1;
//             GibInt pvrtmp_2411 = tmp_struct_56.field2;
//             GibCursorGibCursorGibIntProd return_57;
//
//             return_57.field0 = end_r_933;
//             return_57.field1 = jump_loc_1384;
//             return_57.field2 = pvrtmp_2411;
//             return return_57;
//             break;
//         }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_61 = *(uintptr_t *) (*lst_36_307_484);
            GibCursor tmpcur_2412 = GIB_UNTAG(tagged_tmpcur_61);
            //GibCursor tmpaftercur_2413 = tmpcur_2390 + 8;
            *lst_36_307_484 = tmpcur_2412;

            // uint16_t tmptag_2414 = GIB_GET_TAG(tagged_tmpcur_61);
            // GibCursor end_from_tagged_indr_1382 = tmpcur_2412 + tmptag_2414;

            GibCursorGibCursorGibIntProd tmp_struct_59 = reduceB(lst_36_307_484, lst_36_307_484);
            return tmp_struct_59;

//             GibCursor pvrtmp_2415 = tmp_struct_59.field0;
//             GibCursor pvrtmp_2416 = tmp_struct_59.field1;
//             GibInt pvrtmp_2417 = tmp_struct_59.field2;
//             GibCursorGibCursorGibIntProd return_60;
//
//             return_60.field0 = pvrtmp_2415;
//             return_60.field1 = pvrtmp_2416;
//             return_60.field2 = pvrtmp_2417;
//             return return_60;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2389");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_ListA(GibCursor end_r_937,
                                                              GibCursor end_r_939,
                                                              GibCursor loc_935,
                                                              GibCursor arg_88_315_493)
{
    if (loc_935 + 18 > end_r_939) {
        gib_grow_region(&loc_935, &end_r_939);
    }
    
    GibPackedTag tmpval_2419 = *(GibPackedTag *) arg_88_315_493;
    GibCursor tmpcur_2420 = arg_88_315_493 + 1;
    
    
  switch_2468:
    ;
    switch (tmpval_2419) {
        
      case 0:
        {
            GibInt tmpval_2421 = *(GibInt *) tmpcur_2420;
            GibCursor tmpcur_2422 = tmpcur_2420 + sizeof(GibInt);
            GibCursor jump_1285 = tmpcur_2420 + 8;
            GibCursor loc_1089 = loc_935 + 1;
            GibCursor loc_1090 = loc_1089 + 8;
            
            *(GibPackedTag *) loc_935 = 0;
            
            GibCursor writetag_1751 = loc_935 + 1;
            GibCursor after_tag_1752 = loc_935 + 1;
            
            *(GibInt *) after_tag_1752 = tmpval_2421;
            
            GibCursor writecur_1756 = after_tag_1752 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_62 =
                                                               _copy_ListA(end_r_937, end_r_939, loc_1090, tmpcur_2422);
            GibCursor pvrtmp_2423 = tmp_struct_62.field0;
            GibCursor pvrtmp_2424 = tmp_struct_62.field1;
            GibCursor pvrtmp_2425 = tmp_struct_62.field2;
            GibCursor pvrtmp_2426 = tmp_struct_62.field3;
            GibCursor pvrtmp_2427 = tmp_struct_62.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_63;
            
            return_63.field0 = pvrtmp_2423;
            return_63.field1 = pvrtmp_2424;
            return_63.field2 = pvrtmp_2425;
            return_63.field3 = loc_935;
            return_63.field4 = pvrtmp_2427;
            return return_63;
            break;
        }
        
      case 1:
        {
            GibCursor jump_loc_1288 = arg_88_315_493 + 1;
            
            *(GibPackedTag *) loc_935 = 1;
            
            GibCursor writetag_1761 = loc_935 + 1;
            GibCursor after_tag_1762 = loc_935 + 1;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_64;
            
            return_64.field0 = end_r_937;
            return_64.field1 = end_r_939;
            return_64.field2 = jump_loc_1288;
            return_64.field3 = loc_935;
            return_64.field4 = after_tag_1762;
            return return_64;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_67 = *(uintptr_t *) tmpcur_2420;
            GibCursor tmpcur_2440 = GIB_UNTAG(tagged_tmpcur_67);
            GibCursor tmpaftercur_2441 = tmpcur_2420 + 8;
            uint16_t tmptag_2442 = GIB_GET_TAG(tagged_tmpcur_67);
            GibCursor end_from_tagged_indr_1388 = tmpcur_2440 + tmptag_2442;
            GibCursor jump_loc_1390 = tmpcur_2420 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_65 =
                                                               _copy_ListA(tmpcur_2440, end_r_939, loc_935, tmpcur_2440);
            GibCursor pvrtmp_2443 = tmp_struct_65.field0;
            GibCursor pvrtmp_2444 = tmp_struct_65.field1;
            GibCursor pvrtmp_2445 = tmp_struct_65.field2;
            GibCursor pvrtmp_2446 = tmp_struct_65.field3;
            GibCursor pvrtmp_2447 = tmp_struct_65.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_66;
            
            return_66.field0 = end_r_937;
            return_66.field1 = pvrtmp_2444;
            return_66.field2 = jump_loc_1390;
            return_66.field3 = pvrtmp_2446;
            return_66.field4 = pvrtmp_2447;
            return return_66;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_70 = *(uintptr_t *) tmpcur_2420;
            GibCursor tmpcur_2454 = GIB_UNTAG(tagged_tmpcur_70);
            GibCursor tmpaftercur_2455 = tmpcur_2420 + 8;
            uint16_t tmptag_2456 = GIB_GET_TAG(tagged_tmpcur_70);
            GibCursor end_from_tagged_indr_1388 = tmpcur_2454 + tmptag_2456;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_68 =
                                                               _copy_ListA(tmpcur_2454, end_r_939, loc_935, tmpcur_2454);
            GibCursor pvrtmp_2457 = tmp_struct_68.field0;
            GibCursor pvrtmp_2458 = tmp_struct_68.field1;
            GibCursor pvrtmp_2459 = tmp_struct_68.field2;
            GibCursor pvrtmp_2460 = tmp_struct_68.field3;
            GibCursor pvrtmp_2461 = tmp_struct_68.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_69;
            
            return_69.field0 = pvrtmp_2457;
            return_69.field1 = pvrtmp_2458;
            return_69.field2 = pvrtmp_2459;
            return_69.field3 = pvrtmp_2460;
            return_69.field4 = pvrtmp_2461;
            return return_69;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2419");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_ListB(GibCursor end_r_943,
                                                              GibCursor end_r_945,
                                                              GibCursor loc_941,
                                                              GibCursor arg_176_330_498)
{
    if (loc_941 + 58 > end_r_945) {
        gib_grow_region(&loc_941, &end_r_945);
    }
    
    GibPackedTag tmpval_2469 = *(GibPackedTag *) arg_176_330_498;
    GibCursor tmpcur_2470 = arg_176_330_498 + 1;
    
    
  switch_2528:
    ;
    switch (tmpval_2469) {
        
      case 0:
        {
            GibInt tmpval_2471 = *(GibInt *) tmpcur_2470;
            GibCursor tmpcur_2472 = tmpcur_2470 + sizeof(GibInt);
            GibInt tmpval_2473 = *(GibInt *) tmpcur_2472;
            GibCursor tmpcur_2474 = tmpcur_2472 + sizeof(GibInt);
            GibInt tmpval_2475 = *(GibInt *) tmpcur_2474;
            GibCursor tmpcur_2476 = tmpcur_2474 + sizeof(GibInt);
            GibInt tmpval_2477 = *(GibInt *) tmpcur_2476;
            GibCursor tmpcur_2478 = tmpcur_2476 + sizeof(GibInt);
            GibInt tmpval_2479 = *(GibInt *) tmpcur_2478;
            GibCursor tmpcur_2480 = tmpcur_2478 + sizeof(GibInt);
            GibInt tmpval_2481 = *(GibInt *) tmpcur_2480;
            GibCursor tmpcur_2482 = tmpcur_2480 + sizeof(GibInt);
            GibCursor jump_1295 = tmpcur_2480 + 8;
            GibCursor jump_1294 = tmpcur_2478 + 8;
            GibCursor jump_1293 = tmpcur_2476 + 8;
            GibCursor jump_1292 = tmpcur_2474 + 8;
            GibCursor jump_1291 = tmpcur_2472 + 8;
            GibCursor jump_1290 = tmpcur_2470 + 8;
            GibCursor loc_1107 = loc_941 + 1;
            GibCursor loc_1108 = loc_1107 + 8;
            GibCursor loc_1109 = loc_1108 + 8;
            GibCursor loc_1110 = loc_1109 + 8;
            GibCursor loc_1111 = loc_1110 + 8;
            GibCursor loc_1112 = loc_1111 + 8;
            GibCursor loc_1113 = loc_1112 + 8;
            
            *(GibPackedTag *) loc_941 = 0;
            
            GibCursor writetag_1789 = loc_941 + 1;
            GibCursor after_tag_1790 = loc_941 + 1;
            
            *(GibInt *) after_tag_1790 = tmpval_2471;
            
            GibCursor writecur_1794 = after_tag_1790 + sizeof(GibInt);
            
            *(GibInt *) writecur_1794 = tmpval_2473;
            
            GibCursor writecur_1795 = writecur_1794 + sizeof(GibInt);
            
            *(GibInt *) writecur_1795 = tmpval_2475;
            
            GibCursor writecur_1796 = writecur_1795 + sizeof(GibInt);
            
            *(GibInt *) writecur_1796 = tmpval_2477;
            
            GibCursor writecur_1797 = writecur_1796 + sizeof(GibInt);
            
            *(GibInt *) writecur_1797 = tmpval_2479;
            
            GibCursor writecur_1798 = writecur_1797 + sizeof(GibInt);
            
            *(GibInt *) writecur_1798 = tmpval_2481;
            
            GibCursor writecur_1799 = writecur_1798 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_74 =
                                                               _copy_ListB(end_r_943, end_r_945, loc_1113, tmpcur_2482);
            GibCursor pvrtmp_2483 = tmp_struct_74.field0;
            GibCursor pvrtmp_2484 = tmp_struct_74.field1;
            GibCursor pvrtmp_2485 = tmp_struct_74.field2;
            GibCursor pvrtmp_2486 = tmp_struct_74.field3;
            GibCursor pvrtmp_2487 = tmp_struct_74.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_75;
            
            return_75.field0 = pvrtmp_2483;
            return_75.field1 = pvrtmp_2484;
            return_75.field2 = pvrtmp_2485;
            return_75.field3 = loc_941;
            return_75.field4 = pvrtmp_2487;
            return return_75;
            break;
        }
        
      case 1:
        {
            GibCursor jump_loc_1298 = arg_176_330_498 + 1;
            
            *(GibPackedTag *) loc_941 = 1;
            
            GibCursor writetag_1804 = loc_941 + 1;
            GibCursor after_tag_1805 = loc_941 + 1;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_76;
            
            return_76.field0 = end_r_943;
            return_76.field1 = end_r_945;
            return_76.field2 = jump_loc_1298;
            return_76.field3 = loc_941;
            return_76.field4 = after_tag_1805;
            return return_76;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_79 = *(uintptr_t *) tmpcur_2470;
            GibCursor tmpcur_2500 = GIB_UNTAG(tagged_tmpcur_79);
            GibCursor tmpaftercur_2501 = tmpcur_2470 + 8;
            uint16_t tmptag_2502 = GIB_GET_TAG(tagged_tmpcur_79);
            GibCursor end_from_tagged_indr_1394 = tmpcur_2500 + tmptag_2502;
            GibCursor jump_loc_1396 = tmpcur_2470 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_77 =
                                                               _copy_ListB(tmpcur_2500, end_r_945, loc_941, tmpcur_2500);
            GibCursor pvrtmp_2503 = tmp_struct_77.field0;
            GibCursor pvrtmp_2504 = tmp_struct_77.field1;
            GibCursor pvrtmp_2505 = tmp_struct_77.field2;
            GibCursor pvrtmp_2506 = tmp_struct_77.field3;
            GibCursor pvrtmp_2507 = tmp_struct_77.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_78;
            
            return_78.field0 = end_r_943;
            return_78.field1 = pvrtmp_2504;
            return_78.field2 = jump_loc_1396;
            return_78.field3 = pvrtmp_2506;
            return_78.field4 = pvrtmp_2507;
            return return_78;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_82 = *(uintptr_t *) tmpcur_2470;
            GibCursor tmpcur_2514 = GIB_UNTAG(tagged_tmpcur_82);
            GibCursor tmpaftercur_2515 = tmpcur_2470 + 8;
            uint16_t tmptag_2516 = GIB_GET_TAG(tagged_tmpcur_82);
            GibCursor end_from_tagged_indr_1394 = tmpcur_2514 + tmptag_2516;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_80 =
                                                               _copy_ListB(tmpcur_2514, end_r_945, loc_941, tmpcur_2514);
            GibCursor pvrtmp_2517 = tmp_struct_80.field0;
            GibCursor pvrtmp_2518 = tmp_struct_80.field1;
            GibCursor pvrtmp_2519 = tmp_struct_80.field2;
            GibCursor pvrtmp_2520 = tmp_struct_80.field3;
            GibCursor pvrtmp_2521 = tmp_struct_80.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_81;
            
            return_81.field0 = pvrtmp_2517;
            return_81.field1 = pvrtmp_2518;
            return_81.field2 = pvrtmp_2519;
            return_81.field3 = pvrtmp_2520;
            return_81.field4 = pvrtmp_2521;
            return return_81;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2469");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_List(GibCursor end_r_949,
                                                             GibCursor end_r_951,
                                                             GibCursor loc_947,
                                                             GibCursor arg_114_345_513)
{
    if (loc_947 + 42 > end_r_951) {
        gib_grow_region(&loc_947, &end_r_951);
    }
    
    GibPackedTag tmpval_2529 = *(GibPackedTag *) arg_114_345_513;
    GibCursor tmpcur_2530 = arg_114_345_513 + 1;
    
    
  switch_2593:
    ;
    switch (tmpval_2529) {
        
      case 0:
        {
            GibInt tmpval_2531 = *(GibInt *) tmpcur_2530;
            GibCursor tmpcur_2532 = tmpcur_2530 + sizeof(GibInt);
            GibInt tmpval_2533 = *(GibInt *) tmpcur_2532;
            GibCursor tmpcur_2534 = tmpcur_2532 + sizeof(GibInt);
            GibInt tmpval_2535 = *(GibInt *) tmpcur_2534;
            GibCursor tmpcur_2536 = tmpcur_2534 + sizeof(GibInt);
            GibInt tmpval_2537 = *(GibInt *) tmpcur_2536;
            GibCursor tmpcur_2538 = tmpcur_2536 + sizeof(GibInt);
            GibCursor jump_1303 = tmpcur_2536 + 8;
            GibCursor jump_1302 = tmpcur_2534 + 8;
            GibCursor jump_1301 = tmpcur_2532 + 8;
            GibCursor jump_1300 = tmpcur_2530 + 8;
            GibCursor loc_1142 = loc_947 + 1;
            GibCursor loc_1143 = loc_1142 + 8;
            GibCursor loc_1144 = loc_1143 + 8;
            GibCursor loc_1145 = loc_1144 + 8;
            GibCursor loc_1146 = loc_1145 + 8;
            
            *(GibPackedTag *) loc_947 = 0;
            
            GibCursor writetag_1833 = loc_947 + 1;
            GibCursor after_tag_1834 = loc_947 + 1;
            
            *(GibInt *) after_tag_1834 = tmpval_2531;
            
            GibCursor writecur_1838 = after_tag_1834 + sizeof(GibInt);
            
            *(GibInt *) writecur_1838 = tmpval_2533;
            
            GibCursor writecur_1839 = writecur_1838 + sizeof(GibInt);
            
            *(GibInt *) writecur_1839 = tmpval_2535;
            
            GibCursor writecur_1840 = writecur_1839 + sizeof(GibInt);
            
            *(GibInt *) writecur_1840 = tmpval_2537;
            
            GibCursor writecur_1841 = writecur_1840 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_86 =
                                                               _copy_ListA(end_r_949, end_r_951, loc_1146, tmpcur_2538);
            GibCursor pvrtmp_2539 = tmp_struct_86.field0;
            GibCursor pvrtmp_2540 = tmp_struct_86.field1;
            GibCursor pvrtmp_2541 = tmp_struct_86.field2;
            GibCursor pvrtmp_2542 = tmp_struct_86.field3;
            GibCursor pvrtmp_2543 = tmp_struct_86.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_87 =
                                                               _copy_List(pvrtmp_2539, pvrtmp_2540, pvrtmp_2543, pvrtmp_2541);
            GibCursor pvrtmp_2548 = tmp_struct_87.field0;
            GibCursor pvrtmp_2549 = tmp_struct_87.field1;
            GibCursor pvrtmp_2550 = tmp_struct_87.field2;
            GibCursor pvrtmp_2551 = tmp_struct_87.field3;
            GibCursor pvrtmp_2552 = tmp_struct_87.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_88;
            
            return_88.field0 = pvrtmp_2548;
            return_88.field1 = pvrtmp_2549;
            return_88.field2 = pvrtmp_2550;
            return_88.field3 = loc_947;
            return_88.field4 = pvrtmp_2552;
            return return_88;
            break;
        }
        
      case 1:
        {
            GibCursor jump_loc_1307 = arg_114_345_513 + 1;
            
            *(GibPackedTag *) loc_947 = 1;
            
            GibCursor writetag_1848 = loc_947 + 1;
            GibCursor after_tag_1849 = loc_947 + 1;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_89;
            
            return_89.field0 = end_r_949;
            return_89.field1 = end_r_951;
            return_89.field2 = jump_loc_1307;
            return_89.field3 = loc_947;
            return_89.field4 = after_tag_1849;
            return return_89;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_92 = *(uintptr_t *) tmpcur_2530;
            GibCursor tmpcur_2565 = GIB_UNTAG(tagged_tmpcur_92);
            GibCursor tmpaftercur_2566 = tmpcur_2530 + 8;
            uint16_t tmptag_2567 = GIB_GET_TAG(tagged_tmpcur_92);
            GibCursor end_from_tagged_indr_1400 = tmpcur_2565 + tmptag_2567;
            GibCursor jump_loc_1402 = tmpcur_2530 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_90 =
                                                               _copy_List(tmpcur_2565, end_r_951, loc_947, tmpcur_2565);
            GibCursor pvrtmp_2568 = tmp_struct_90.field0;
            GibCursor pvrtmp_2569 = tmp_struct_90.field1;
            GibCursor pvrtmp_2570 = tmp_struct_90.field2;
            GibCursor pvrtmp_2571 = tmp_struct_90.field3;
            GibCursor pvrtmp_2572 = tmp_struct_90.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_91;
            
            return_91.field0 = end_r_949;
            return_91.field1 = pvrtmp_2569;
            return_91.field2 = jump_loc_1402;
            return_91.field3 = pvrtmp_2571;
            return_91.field4 = pvrtmp_2572;
            return return_91;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_95 = *(uintptr_t *) tmpcur_2530;
            GibCursor tmpcur_2579 = GIB_UNTAG(tagged_tmpcur_95);
            GibCursor tmpaftercur_2580 = tmpcur_2530 + 8;
            uint16_t tmptag_2581 = GIB_GET_TAG(tagged_tmpcur_95);
            GibCursor end_from_tagged_indr_1400 = tmpcur_2579 + tmptag_2581;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_93 =
                                                               _copy_List(tmpcur_2579, end_r_951, loc_947, tmpcur_2579);
            GibCursor pvrtmp_2582 = tmp_struct_93.field0;
            GibCursor pvrtmp_2583 = tmp_struct_93.field1;
            GibCursor pvrtmp_2584 = tmp_struct_93.field2;
            GibCursor pvrtmp_2585 = tmp_struct_93.field3;
            GibCursor pvrtmp_2586 = tmp_struct_93.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_94;
            
            return_94.field0 = pvrtmp_2582;
            return_94.field1 = pvrtmp_2583;
            return_94.field2 = pvrtmp_2584;
            return_94.field3 = pvrtmp_2585;
            return_94.field4 = pvrtmp_2586;
            return return_94;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2529");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_ListB(GibCursor end_r_954,
                                       GibCursor arg_206_358_526)
{
    GibPackedTag tmpval_2594 = *(GibPackedTag *) arg_206_358_526;
    GibCursor tmpcur_2595 = arg_206_358_526 + 1;
    
    
  switch_2620:
    ;
    switch (tmpval_2594) {
        
      case 0:
        {
            GibInt tmpval_2596 = *(GibInt *) tmpcur_2595;
            GibCursor tmpcur_2597 = tmpcur_2595 + sizeof(GibInt);
            GibInt tmpval_2598 = *(GibInt *) tmpcur_2597;
            GibCursor tmpcur_2599 = tmpcur_2597 + sizeof(GibInt);
            GibInt tmpval_2600 = *(GibInt *) tmpcur_2599;
            GibCursor tmpcur_2601 = tmpcur_2599 + sizeof(GibInt);
            GibInt tmpval_2602 = *(GibInt *) tmpcur_2601;
            GibCursor tmpcur_2603 = tmpcur_2601 + sizeof(GibInt);
            GibInt tmpval_2604 = *(GibInt *) tmpcur_2603;
            GibCursor tmpcur_2605 = tmpcur_2603 + sizeof(GibInt);
            GibInt tmpval_2606 = *(GibInt *) tmpcur_2605;
            GibCursor tmpcur_2607 = tmpcur_2605 + sizeof(GibInt);
            GibCursor jump_1314 = tmpcur_2605 + 8;
            GibCursor jump_1313 = tmpcur_2603 + 8;
            GibCursor jump_1312 = tmpcur_2601 + 8;
            GibCursor jump_1311 = tmpcur_2599 + 8;
            GibCursor jump_1310 = tmpcur_2597 + 8;
            GibCursor jump_1309 = tmpcur_2595 + 8;
            GibCursorGibCursorProd tmp_struct_99 =
                                    _traverse_ListB(end_r_954, tmpcur_2607);
            GibCursor pvrtmp_2608 = tmp_struct_99.field0;
            GibCursor pvrtmp_2609 = tmp_struct_99.field1;
            GibCursorGibCursorProd return_100;
            
            return_100.field0 = pvrtmp_2608;
            return_100.field1 = pvrtmp_2609;
            return return_100;
            break;
        }
        
      case 1:
        {
            GibCursor jump_loc_1317 = arg_206_358_526 + 1;
            GibCursorGibCursorProd return_101;
            
            return_101.field0 = end_r_954;
            return_101.field1 = jump_loc_1317;
            return return_101;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_104 = *(uintptr_t *) tmpcur_2595;
            GibCursor tmpcur_2610 = GIB_UNTAG(tagged_tmpcur_104);
            GibCursor tmpaftercur_2611 = tmpcur_2595 + 8;
            uint16_t tmptag_2612 = GIB_GET_TAG(tagged_tmpcur_104);
            GibCursor end_from_tagged_indr_1406 = tmpcur_2610 + tmptag_2612;
            GibCursor jump_loc_1408 = tmpcur_2595 + 8;
            GibCursorGibCursorProd tmp_struct_102 =
                                    _traverse_ListB(tmpcur_2610, tmpcur_2610);
            GibCursor pvrtmp_2613 = tmp_struct_102.field0;
            GibCursor pvrtmp_2614 = tmp_struct_102.field1;
            GibCursorGibCursorProd return_103;
            
            return_103.field0 = end_r_954;
            return_103.field1 = jump_loc_1408;
            return return_103;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_107 = *(uintptr_t *) tmpcur_2595;
            GibCursor tmpcur_2615 = GIB_UNTAG(tagged_tmpcur_107);
            GibCursor tmpaftercur_2616 = tmpcur_2595 + 8;
            uint16_t tmptag_2617 = GIB_GET_TAG(tagged_tmpcur_107);
            GibCursor end_from_tagged_indr_1406 = tmpcur_2615 + tmptag_2617;
            GibCursorGibCursorProd tmp_struct_105 =
                                    _traverse_ListB(tmpcur_2615, tmpcur_2615);
            GibCursor pvrtmp_2618 = tmp_struct_105.field0;
            GibCursor pvrtmp_2619 = tmp_struct_105.field1;
            GibCursorGibCursorProd return_106;
            
            return_106.field0 = pvrtmp_2618;
            return_106.field1 = pvrtmp_2619;
            return return_106;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2594");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_ListA(GibCursor end_r_957,
                                    GibCursor arg_103_369_535)
{
    GibPackedTag tmpval_2621 = *(GibPackedTag *) arg_103_369_535;
    GibCursor tmpcur_2622 = arg_103_369_535 + 1;
    
    
  switch_2637:
    ;
    switch (tmpval_2621) {
        
      case 0:
        {
            GibInt tmpval_2623 = *(GibInt *) tmpcur_2622;
            GibCursor tmpcur_2624 = tmpcur_2622 + sizeof(GibInt);
            GibCursor jump_1319 = tmpcur_2622 + 8;
            unsigned char wildcard_108_372_538 = gib_print_symbol(2181);
            unsigned char wildcard_111_373_539 = gib_print_symbol(2185);
            unsigned char y_106_374_540 = printf("%ld", tmpval_2623);
            unsigned char wildcard_110_375_541 = gib_print_symbol(2185);
            GibCursorGibCursorProd tmp_struct_108 =
                                    _print_ListA(end_r_957, tmpcur_2624);
            GibCursor pvrtmp_2625 = tmp_struct_108.field0;
            GibCursor pvrtmp_2626 = tmp_struct_108.field1;
            unsigned char wildcard_109_377_543 = gib_print_symbol(2176);
            GibCursorGibCursorProd return_109;
            
            return_109.field0 = pvrtmp_2625;
            return_109.field1 = pvrtmp_2626;
            return return_109;
            break;
        }
        
      case 1:
        {
            GibCursor jump_loc_1322 = arg_103_369_535 + 1;
            unsigned char wildcard_112_378_544 = gib_print_symbol(2178);
            unsigned char wildcard_113_379_545 = gib_print_symbol(2176);
            GibCursorGibCursorProd return_110;
            
            return_110.field0 = end_r_957;
            return_110.field1 = jump_loc_1322;
            return return_110;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_113 = *(uintptr_t *) tmpcur_2622;
            GibCursor tmpcur_2627 = GIB_UNTAG(tagged_tmpcur_113);
            GibCursor tmpaftercur_2628 = tmpcur_2622 + 8;
            uint16_t tmptag_2629 = GIB_GET_TAG(tagged_tmpcur_113);
            GibCursor end_from_tagged_indr_1412 = tmpcur_2627 + tmptag_2629;
            GibCursor jump_loc_1414 = tmpcur_2622 + 8;
            unsigned char wildcard_1417 = gib_print_symbol(2184);
            GibCursorGibCursorProd tmp_struct_111 =
                                    _print_ListA(tmpcur_2627, tmpcur_2627);
            GibCursor pvrtmp_2630 = tmp_struct_111.field0;
            GibCursor pvrtmp_2631 = tmp_struct_111.field1;
            GibCursorGibCursorProd return_112;
            
            return_112.field0 = end_r_957;
            return_112.field1 = jump_loc_1414;
            return return_112;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_116 = *(uintptr_t *) tmpcur_2622;
            GibCursor tmpcur_2632 = GIB_UNTAG(tagged_tmpcur_116);
            GibCursor tmpaftercur_2633 = tmpcur_2622 + 8;
            uint16_t tmptag_2634 = GIB_GET_TAG(tagged_tmpcur_116);
            GibCursor end_from_tagged_indr_1412 = tmpcur_2632 + tmptag_2634;
            unsigned char wildcard_1417 = gib_print_symbol(2183);
            GibCursorGibCursorProd tmp_struct_114 =
                                    _print_ListA(tmpcur_2632, tmpcur_2632);
            GibCursor pvrtmp_2635 = tmp_struct_114.field0;
            GibCursor pvrtmp_2636 = tmp_struct_114.field1;
            GibCursorGibCursorProd return_115;
            
            return_115.field0 = pvrtmp_2635;
            return_115.field1 = pvrtmp_2636;
            return return_115;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2621");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_ListB(GibCursor end_r_960,
                                    GibCursor arg_221_380_546)
{
    GibPackedTag tmpval_2638 = *(GibPackedTag *) arg_221_380_546;
    GibCursor tmpcur_2639 = arg_221_380_546 + 1;
    
    
  switch_2664:
    ;
    switch (tmpval_2638) {
        
      case 0:
        {
            GibInt tmpval_2640 = *(GibInt *) tmpcur_2639;
            GibCursor tmpcur_2641 = tmpcur_2639 + sizeof(GibInt);
            GibInt tmpval_2642 = *(GibInt *) tmpcur_2641;
            GibCursor tmpcur_2643 = tmpcur_2641 + sizeof(GibInt);
            GibInt tmpval_2644 = *(GibInt *) tmpcur_2643;
            GibCursor tmpcur_2645 = tmpcur_2643 + sizeof(GibInt);
            GibInt tmpval_2646 = *(GibInt *) tmpcur_2645;
            GibCursor tmpcur_2647 = tmpcur_2645 + sizeof(GibInt);
            GibInt tmpval_2648 = *(GibInt *) tmpcur_2647;
            GibCursor tmpcur_2649 = tmpcur_2647 + sizeof(GibInt);
            GibInt tmpval_2650 = *(GibInt *) tmpcur_2649;
            GibCursor tmpcur_2651 = tmpcur_2649 + sizeof(GibInt);
            GibCursor jump_1329 = tmpcur_2649 + 8;
            GibCursor jump_1328 = tmpcur_2647 + 8;
            GibCursor jump_1327 = tmpcur_2645 + 8;
            GibCursor jump_1326 = tmpcur_2643 + 8;
            GibCursor jump_1325 = tmpcur_2641 + 8;
            GibCursor jump_1324 = tmpcur_2639 + 8;
            unsigned char wildcard_236_388_554 = gib_print_symbol(2180);
            unsigned char wildcard_244_389_555 = gib_print_symbol(2185);
            unsigned char y_229_390_556 = printf("%ld", tmpval_2640);
            unsigned char wildcard_243_391_557 = gib_print_symbol(2185);
            unsigned char y_230_392_558 = printf("%ld", tmpval_2642);
            unsigned char wildcard_242_393_559 = gib_print_symbol(2185);
            unsigned char y_231_394_560 = printf("%ld", tmpval_2644);
            unsigned char wildcard_241_395_561 = gib_print_symbol(2185);
            unsigned char y_232_396_562 = printf("%ld", tmpval_2646);
            unsigned char wildcard_240_397_563 = gib_print_symbol(2185);
            unsigned char y_233_398_564 = printf("%ld", tmpval_2648);
            unsigned char wildcard_239_399_565 = gib_print_symbol(2185);
            unsigned char y_234_400_566 = printf("%ld", tmpval_2650);
            unsigned char wildcard_238_401_567 = gib_print_symbol(2185);
            GibCursorGibCursorProd tmp_struct_117 =
                                    _print_ListB(end_r_960, tmpcur_2651);
            GibCursor pvrtmp_2652 = tmp_struct_117.field0;
            GibCursor pvrtmp_2653 = tmp_struct_117.field1;
            unsigned char wildcard_237_403_569 = gib_print_symbol(2176);
            GibCursorGibCursorProd return_118;
            
            return_118.field0 = pvrtmp_2652;
            return_118.field1 = pvrtmp_2653;
            return return_118;
            break;
        }
        
      case 1:
        {
            GibCursor jump_loc_1332 = arg_221_380_546 + 1;
            unsigned char wildcard_245_404_570 = gib_print_symbol(2177);
            unsigned char wildcard_246_405_571 = gib_print_symbol(2176);
            GibCursorGibCursorProd return_119;
            
            return_119.field0 = end_r_960;
            return_119.field1 = jump_loc_1332;
            return return_119;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_122 = *(uintptr_t *) tmpcur_2639;
            GibCursor tmpcur_2654 = GIB_UNTAG(tagged_tmpcur_122);
            GibCursor tmpaftercur_2655 = tmpcur_2639 + 8;
            uint16_t tmptag_2656 = GIB_GET_TAG(tagged_tmpcur_122);
            GibCursor end_from_tagged_indr_1418 = tmpcur_2654 + tmptag_2656;
            GibCursor jump_loc_1420 = tmpcur_2639 + 8;
            unsigned char wildcard_1423 = gib_print_symbol(2184);
            GibCursorGibCursorProd tmp_struct_120 =
                                    _print_ListB(tmpcur_2654, tmpcur_2654);
            GibCursor pvrtmp_2657 = tmp_struct_120.field0;
            GibCursor pvrtmp_2658 = tmp_struct_120.field1;
            GibCursorGibCursorProd return_121;
            
            return_121.field0 = end_r_960;
            return_121.field1 = jump_loc_1420;
            return return_121;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_125 = *(uintptr_t *) tmpcur_2639;
            GibCursor tmpcur_2659 = GIB_UNTAG(tagged_tmpcur_125);
            GibCursor tmpaftercur_2660 = tmpcur_2639 + 8;
            uint16_t tmptag_2661 = GIB_GET_TAG(tagged_tmpcur_125);
            GibCursor end_from_tagged_indr_1418 = tmpcur_2659 + tmptag_2661;
            unsigned char wildcard_1423 = gib_print_symbol(2183);
            GibCursorGibCursorProd tmp_struct_123 =
                                    _print_ListB(tmpcur_2659, tmpcur_2659);
            GibCursor pvrtmp_2662 = tmp_struct_123.field0;
            GibCursor pvrtmp_2663 = tmp_struct_123.field1;
            GibCursorGibCursorProd return_124;
            
            return_124.field0 = pvrtmp_2662;
            return_124.field1 = pvrtmp_2663;
            return return_124;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2638");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_List(GibCursor end_r_964,
                                                                          GibCursor end_r_966,
                                                                          GibCursor loc_962,
                                                                          GibCursor arg_127_406_572)
{
    GibPackedTag tmpval_2665 = *(GibPackedTag *) arg_127_406_572;
    GibCursor tmpcur_2666 = arg_127_406_572 + 1;
    
    
  switch_2729:
    ;
    switch (tmpval_2665) {
        
      case 0:
        {
            GibInt tmpval_2667 = *(GibInt *) tmpcur_2666;
            GibCursor tmpcur_2668 = tmpcur_2666 + sizeof(GibInt);
            GibInt tmpval_2669 = *(GibInt *) tmpcur_2668;
            GibCursor tmpcur_2670 = tmpcur_2668 + sizeof(GibInt);
            GibInt tmpval_2671 = *(GibInt *) tmpcur_2670;
            GibCursor tmpcur_2672 = tmpcur_2670 + sizeof(GibInt);
            GibInt tmpval_2673 = *(GibInt *) tmpcur_2672;
            GibCursor tmpcur_2674 = tmpcur_2672 + sizeof(GibInt);
            GibCursor jump_1337 = tmpcur_2672 + 8;
            GibCursor jump_1336 = tmpcur_2670 + 8;
            GibCursor jump_1335 = tmpcur_2668 + 8;
            GibCursor jump_1334 = tmpcur_2666 + 8;
            GibCursor loc_1201 = loc_962 + 1;
            GibCursor loc_1202 = loc_1201 + 8;
            GibCursor loc_1203 = loc_1202 + 8;
            GibCursor loc_1204 = loc_1203 + 8;
            GibCursor loc_1205 = loc_1204 + 8;
            
            *(GibPackedTag *) loc_962 = 0;
            
            GibCursor writetag_1929 = loc_962 + 1;
            GibCursor after_tag_1930 = loc_962 + 1;
            
            *(GibInt *) after_tag_1930 = tmpval_2667;
            
            GibCursor writecur_1934 = after_tag_1930 + sizeof(GibInt);
            
            *(GibInt *) writecur_1934 = tmpval_2669;
            
            GibCursor writecur_1935 = writecur_1934 + sizeof(GibInt);
            
            *(GibInt *) writecur_1935 = tmpval_2671;
            
            GibCursor writecur_1936 = writecur_1935 + sizeof(GibInt);
            
            *(GibInt *) writecur_1936 = tmpval_2673;
            
            GibCursor writecur_1937 = writecur_1936 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_126 =
                                                               _copy_without_ptrs_ListA(end_r_964, end_r_966, loc_1205, tmpcur_2674);
            GibCursor pvrtmp_2675 = tmp_struct_126.field0;
            GibCursor pvrtmp_2676 = tmp_struct_126.field1;
            GibCursor pvrtmp_2677 = tmp_struct_126.field2;
            GibCursor pvrtmp_2678 = tmp_struct_126.field3;
            GibCursor pvrtmp_2679 = tmp_struct_126.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_127 =
                                                               _copy_without_ptrs_List(pvrtmp_2675, pvrtmp_2676, pvrtmp_2679, pvrtmp_2677);
            GibCursor pvrtmp_2684 = tmp_struct_127.field0;
            GibCursor pvrtmp_2685 = tmp_struct_127.field1;
            GibCursor pvrtmp_2686 = tmp_struct_127.field2;
            GibCursor pvrtmp_2687 = tmp_struct_127.field3;
            GibCursor pvrtmp_2688 = tmp_struct_127.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_128;
            
            return_128.field0 = pvrtmp_2684;
            return_128.field1 = pvrtmp_2685;
            return_128.field2 = pvrtmp_2686;
            return_128.field3 = loc_962;
            return_128.field4 = pvrtmp_2688;
            return return_128;
            break;
        }
        
      case 1:
        {
            GibCursor jump_loc_1341 = arg_127_406_572 + 1;
            
            *(GibPackedTag *) loc_962 = 1;
            
            GibCursor writetag_1944 = loc_962 + 1;
            GibCursor after_tag_1945 = loc_962 + 1;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_129;
            
            return_129.field0 = end_r_964;
            return_129.field1 = end_r_966;
            return_129.field2 = jump_loc_1341;
            return_129.field3 = loc_962;
            return_129.field4 = after_tag_1945;
            return return_129;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_132 = *(uintptr_t *) tmpcur_2666;
            GibCursor tmpcur_2701 = GIB_UNTAG(tagged_tmpcur_132);
            GibCursor tmpaftercur_2702 = tmpcur_2666 + 8;
            uint16_t tmptag_2703 = GIB_GET_TAG(tagged_tmpcur_132);
            GibCursor end_from_tagged_indr_1424 = tmpcur_2701 + tmptag_2703;
            GibCursor jump_loc_1426 = tmpcur_2666 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_130 =
                                                               _copy_without_ptrs_List(tmpcur_2701, end_r_966, loc_962, tmpcur_2701);
            GibCursor pvrtmp_2704 = tmp_struct_130.field0;
            GibCursor pvrtmp_2705 = tmp_struct_130.field1;
            GibCursor pvrtmp_2706 = tmp_struct_130.field2;
            GibCursor pvrtmp_2707 = tmp_struct_130.field3;
            GibCursor pvrtmp_2708 = tmp_struct_130.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_131;
            
            return_131.field0 = end_r_964;
            return_131.field1 = pvrtmp_2705;
            return_131.field2 = jump_loc_1426;
            return_131.field3 = pvrtmp_2707;
            return_131.field4 = pvrtmp_2708;
            return return_131;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_135 = *(uintptr_t *) tmpcur_2666;
            GibCursor tmpcur_2715 = GIB_UNTAG(tagged_tmpcur_135);
            GibCursor tmpaftercur_2716 = tmpcur_2666 + 8;
            uint16_t tmptag_2717 = GIB_GET_TAG(tagged_tmpcur_135);
            GibCursor end_from_tagged_indr_1424 = tmpcur_2715 + tmptag_2717;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_133 =
                                                               _copy_without_ptrs_List(tmpcur_2715, end_r_966, loc_962, tmpcur_2715);
            GibCursor pvrtmp_2718 = tmp_struct_133.field0;
            GibCursor pvrtmp_2719 = tmp_struct_133.field1;
            GibCursor pvrtmp_2720 = tmp_struct_133.field2;
            GibCursor pvrtmp_2721 = tmp_struct_133.field3;
            GibCursor pvrtmp_2722 = tmp_struct_133.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_134;
            
            return_134.field0 = pvrtmp_2718;
            return_134.field1 = pvrtmp_2719;
            return_134.field2 = pvrtmp_2720;
            return_134.field3 = pvrtmp_2721;
            return_134.field4 = pvrtmp_2722;
            return return_134;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2665");
            exit(1);
        }
    }
}
int main(int argc, char **argv)
{
    int init_143 = gib_init(argc, argv);
    
    info_table_initialize();
    symbol_table_initialize();
    
    GibChunk region_2186 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_972 = region_2186.start;
    GibCursor end_r_972 = region_2186.end;
    GibCursorGibCursorGibCursorProd tmp_struct_136 =
                                     mkListB(end_r_972, r_972, 2500000);
    GibCursor pvrtmp_2187 = tmp_struct_136.field0;
    GibCursor pvrtmp_2188 = tmp_struct_136.field1;
    GibCursor pvrtmp_2189 = tmp_struct_136.field2;
    GibInt timed_2035;
    GibVector *times_141 = gib_vector_alloc(gib_get_iters_param(),
                                            sizeof(double));
    struct timespec begin_timed_2035;
    struct timespec end_timed_2035;
    
    for (long long iters_timed_2035 = 0; iters_timed_2035 <
         gib_get_iters_param(); iters_timed_2035++) {
        if (iters_timed_2035 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_save_state();
            gib_ptr_bumpalloc_save_state();
        }
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed_2035);
        
        GibCursorGibCursorGibIntProd tmp_struct_137 = reduceB(&pvrtmp_2187, &pvrtmp_2188);
        // GibCursor pvrtmp_2194 = tmp_struct_137.field0;
        // GibCursor pvrtmp_2195 = tmp_struct_137.field1;
        GibInt pvrtmp_2196 = tmp_struct_137.field2;
        
        timed_2035 = pvrtmp_2196;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed_2035);
        if (iters_timed_2035 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_restore_state();
            gib_ptr_bumpalloc_restore_state();
        }

        pvrtmp_2187 = tmp_struct_136.field0;
        pvrtmp_2188 = tmp_struct_136.field1;
        
        double itertime_138 = gib_difftimespecs(&begin_timed_2035,
                                                &end_timed_2035);
        
        printf("itertime: %lf\n", itertime_138);
        gib_vector_inplace_update(times_141, iters_timed_2035, &itertime_138);
    }
    gib_vector_inplace_sort(times_141, gib_compare_doubles);
    
    double *tmp_142 = (double *) gib_vector_nth(times_141,
                                                gib_get_iters_param() / 2);
    double selftimed_140 = *tmp_142;
    double batchtime_139 = gib_sum_timing_array(times_141);
    
    gib_print_timing_array(times_141);
    gib_vector_free(times_141);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_139);
    printf("SELFTIMED: %e\n", selftimed_140);
    printf("%ld", timed_2035);
    printf("\n");
    
    int exit_144 = gib_exit();
    
    return exit_144;
}
