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

void add1Tree(GibCursor *end_r_440,
              GibCursor *end_r_442,
              GibCursor *loc_438,
              GibCursor *t_31_136_213,
              GibCursorGibCursorGibCursorGibCursorGibCursorProd *Ret
              );


GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_Tree(GibCursor end_r_446, GibCursor end_r_448, GibCursor loc_444,
           GibCursor arg_89_141_222);
void sumTree(GibCursor *end_r_451,
             GibCursor *tr_36_150_231,
             GibCursorGibCursorGibIntProd *Ret);
GibCursorGibCursorGibCursorProd mkTree(GibCursor end_r_454, GibCursor loc_452,
                                       GibInt d_41_155_239,
                                       GibInt acc_42_156_240);
GibCursorGibCursorProd _traverse_Tree(GibCursor end_r_457,
                                      GibCursor arg_107_163_248);
GibCursorGibCursorProd _print_Tree(GibCursor end_r_460,
                                   GibCursor arg_116_170_255);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_Tree(GibCursor end_r_464, GibCursor end_r_466,
                        GibCursor loc_462, GibCursor arg_98_187_272);
typedef enum {
            GibInt_T,
            GibFloat_T,
            GibSym_T,
            GibBool_T,
            GibVector_T,
            GibList_T,
            GibCursor_T,
            Tree_T,
        } GibDatatype;
void info_table_initialize(void)
{
    int error = gib_info_table_initialize(8);
    
    if (error < 0) {
        fprintf(stderr, "Couldn't initialize info table, errorno=%d", error);
        exit(1);
    }
    
    GibDatatype field_tys[3];
    
    error = gib_info_table_insert_packed_dcon(Tree_T, 0, 8, 0, 1, 0, field_tys,
                                              0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, Tree_T, 0);
        exit(1);
    }
    field_tys[0] = Tree_T;
    field_tys[1] = Tree_T;
    error = gib_info_table_insert_packed_dcon(Tree_T, 1, 8, 0, 1, 2, field_tys,
                                              2);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, Tree_T, 1);
        exit(1);
    }
    gib_info_table_finalize();
}
void symbol_table_initialize(void)
{
    gib_add_symbol(1130, ")");
    gib_add_symbol(1131, "(Node");
    gib_add_symbol(1132, "(Leaf");
    gib_add_symbol(1133, " ->r ");
    gib_add_symbol(1134, " ->i ");
    gib_add_symbol(1135, " ");
}
//GibCursorGibCursorGibCursorGibCursorGibCursorProd
void add1Tree(GibCursor *end_r_440,
              GibCursor *end_r_442,
              GibCursor *loc_438,
              GibCursor *t_31_136_213,
              GibCursorGibCursorGibCursorGibCursorGibCursorProd *Ret
        )
{
    if (*loc_438 + 18 > *end_r_442) {
        gib_grow_region(loc_438, end_r_442);
    }
    
    GibPackedTag tmpval_1169 = *(GibPackedTag *) (*t_31_136_213);
    //GibCursor tmpcur_1170 = t_31_136_213 + 1;
    *t_31_136_213 += 1;
    
    
  switch_1229:
    ;
    switch (tmpval_1169) {
        
      case 0:
        {
            GibInt tmpval_1171 = *(GibInt *) (*t_31_136_213);

            //not used
            //GibCursor tmpcur_1172 = tmpcur_1170 + sizeof(GibInt);

            //GibCursor jump_597 = tmpcur_1170 + 8;
            *t_31_136_213 += 8;

            GibInt fltPkd_196_215 = tmpval_1171 + 1;
            
            *(GibPackedTag *) (*loc_438) = 0;
            
            //GibCursor writetag_782 = loc_438 + 1;
            //GibCursor after_tag_783 = loc_438 + 1;
            *loc_438 += 1;
            
            *(GibInt *) (*loc_438) = fltPkd_196_215;
            
            //GibCursor writecur_787 = after_tag_783 + sizeof(GibInt);
            *(loc_438) += sizeof(GibInt);

            //GibCursorGibCursorGibCursorGibCursorGibCursorProd return_0;
            
            Ret->field0 = *end_r_440;
            Ret->field1 = *end_r_442;
            Ret->field2 = *t_31_136_213;
            Ret->field4 = *loc_438;
            // return return_0;
            break;
        }
        
      case 1:
        {
            GibInt tmpval_1177 = *(GibInt *) (*t_31_136_213);

            //GibCursor tmpcur_1178 = tmpcur_1170 + sizeof(GibInt);
            *t_31_136_213 += sizeof(GibInt);


            //GibCursor jump_599 = tmpcur_1170 + 8;
            GibInt fltPkd_197_219 = tmpval_1177 + 1;

            //GibCursor loc_495 = loc_438 + 1;
            //GibCursor loc_496 = loc_495 + 8;

            
            *(GibPackedTag *) (*loc_438) = 1;
            *loc_438 += 1;
            
            //GibCursor writetag_798 = loc_438 + 1;
            //GibCursor after_tag_799 = loc_438 + 1;
            
            *(GibInt *) (*loc_438) = fltPkd_197_219;
            *loc_438 += 8;
            
            //GibCursor writecur_803 = after_tag_799 + sizeof(GibInt);
            add1Tree(end_r_440, end_r_442, loc_438, t_31_136_213, Ret);


            // GibCursor pvrtmp_1179 = tmp_struct_1.field0;
            // GibCursor pvrtmp_1180 = tmp_struct_1.field1;
            // GibCursor pvrtmp_1181 = tmp_struct_1.field2;
            // GibCursor pvrtmp_1182 = tmp_struct_1.field3;
            // GibCursor pvrtmp_1183 = tmp_struct_1.field4;

            add1Tree(end_r_440, end_r_442, loc_438, t_31_136_213, Ret);


            // GibCursor pvrtmp_1188 = tmp_struct_2.field0;
            // GibCursor pvrtmp_1189 = tmp_struct_2.field1;
            // GibCursor pvrtmp_1190 = tmp_struct_2.field2;
            // GibCursor pvrtmp_1191 = tmp_struct_2.field3;
            // GibCursor pvrtmp_1192 = tmp_struct_2.field4;
            /*GibCursorGibCursorGibCursorGibCursorGibCursorProd return_3;
            
            return_3.field0 = pvrtmp_1188;
            return_3.field1 = pvrtmp_1189;
            return_3.field2 = pvrtmp_1190;
            return_3.field3 = loc_438;
            return_3.field4 = pvrtmp_1192;
            return return_3*/;
            break;
        }
        
//       case GIB_INDIRECTION_TAG:
//         {
//             uintptr_t tagged_tmpcur_6 = *(uintptr_t *) tmpcur_1170;
//             GibCursor tmpcur_1201 = GIB_UNTAG(tagged_tmpcur_6);
//             GibCursor tmpaftercur_1202 = tmpcur_1170 + 8;
//             uint16_t tmptag_1203 = GIB_GET_TAG(tagged_tmpcur_6);
//             GibCursor end_from_tagged_indr_645 = tmpcur_1201 + tmptag_1203;
//             GibCursor jump_loc_647 = tmpcur_1170 + 8;
//             GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_4 =
//                                                                add1Tree(tmpcur_1201, end_r_442, loc_438, tmpcur_1201);
//             GibCursor pvrtmp_1204 = tmp_struct_4.field0;
//             GibCursor pvrtmp_1205 = tmp_struct_4.field1;
//             GibCursor pvrtmp_1206 = tmp_struct_4.field2;
//             GibCursor pvrtmp_1207 = tmp_struct_4.field3;
//             GibCursor pvrtmp_1208 = tmp_struct_4.field4;
//             GibCursorGibCursorGibCursorGibCursorGibCursorProd return_5;
//
//             return_5.field0 = end_r_440;
//             return_5.field1 = pvrtmp_1205;
//             return_5.field2 = jump_loc_647;
//             return_5.field3 = pvrtmp_1207;
//             return_5.field4 = pvrtmp_1208;
//             return return_5;
//             break;
//         }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_9 = *(uintptr_t *) (*t_31_136_213);
            GibCursor tmpcur_1215 = GIB_UNTAG(tagged_tmpcur_9);
            //GibCursor tmpaftercur_1216 = tmpcur_1170 + 8;
            //uint16_t tmptag_1217 = GIB_GET_TAG(tagged_tmpcur_9);
            //GibCursor end_from_tagged_indr_645 = tmpcur_1215 + tmptag_1217;
            *t_31_136_213 = tmpcur_1215;

            add1Tree(t_31_136_213, end_r_442, loc_438, t_31_136_213, Ret);

//             GibCursor pvrtmp_1218 = tmp_struct_7.field0;
//             GibCursor pvrtmp_1219 = tmp_struct_7.field1;
//             GibCursor pvrtmp_1220 = tmp_struct_7.field2;
//             GibCursor pvrtmp_1221 = tmp_struct_7.field3;
//             GibCursor pvrtmp_1222 = tmp_struct_7.field4;
//             GibCursorGibCursorGibCursorGibCursorGibCursorProd return_8;
//
//             return_8.field0 = pvrtmp_1218;
//             return_8.field1 = pvrtmp_1219;
//             return_8.field2 = pvrtmp_1220;
//             return_8.field3 = pvrtmp_1221;
//             return_8.field4 = pvrtmp_1222;
//             return return_8;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1169");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_Tree(GibCursor end_r_446,
                                                             GibCursor end_r_448,
                                                             GibCursor loc_444,
                                                             GibCursor arg_89_141_222)
{
    if (loc_444 + 18 > end_r_448) {
        gib_grow_region(&loc_444, &end_r_448);
    }
    
    GibPackedTag tmpval_1230 = *(GibPackedTag *) arg_89_141_222;
    GibCursor tmpcur_1231 = arg_89_141_222 + 1;
    
    
  switch_1290:
    ;
    switch (tmpval_1230) {
        
      case 0:
        {
            GibInt tmpval_1232 = *(GibInt *) tmpcur_1231;
            GibCursor tmpcur_1233 = tmpcur_1231 + sizeof(GibInt);
            GibCursor jump_603 = tmpcur_1231 + 8;
            
            *(GibPackedTag *) loc_444 = 0;
            
            GibCursor writetag_822 = loc_444 + 1;
            GibCursor after_tag_823 = loc_444 + 1;
            
            *(GibInt *) after_tag_823 = tmpval_1232;
            
            GibCursor writecur_827 = after_tag_823 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_13;
            
            return_13.field0 = end_r_446;
            return_13.field1 = end_r_448;
            return_13.field2 = jump_603;
            return_13.field3 = loc_444;
            return_13.field4 = writecur_827;
            return return_13;
            break;
        }
        
      case 1:
        {
            GibInt tmpval_1238 = *(GibInt *) tmpcur_1231;
            GibCursor tmpcur_1239 = tmpcur_1231 + sizeof(GibInt);
            GibCursor jump_605 = tmpcur_1231 + 8;
            GibCursor loc_517 = loc_444 + 1;
            GibCursor loc_518 = loc_517 + 8;
            
            *(GibPackedTag *) loc_444 = 1;
            
            GibCursor writetag_838 = loc_444 + 1;
            GibCursor after_tag_839 = loc_444 + 1;
            
            *(GibInt *) after_tag_839 = tmpval_1238;
            
            GibCursor writecur_843 = after_tag_839 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_14 =
                                                               _copy_Tree(end_r_446, end_r_448, loc_518, tmpcur_1239);
            GibCursor pvrtmp_1240 = tmp_struct_14.field0;
            GibCursor pvrtmp_1241 = tmp_struct_14.field1;
            GibCursor pvrtmp_1242 = tmp_struct_14.field2;
            GibCursor pvrtmp_1243 = tmp_struct_14.field3;
            GibCursor pvrtmp_1244 = tmp_struct_14.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_15 =
                                                               _copy_Tree(pvrtmp_1240, pvrtmp_1241, pvrtmp_1244, pvrtmp_1242);
            GibCursor pvrtmp_1249 = tmp_struct_15.field0;
            GibCursor pvrtmp_1250 = tmp_struct_15.field1;
            GibCursor pvrtmp_1251 = tmp_struct_15.field2;
            GibCursor pvrtmp_1252 = tmp_struct_15.field3;
            GibCursor pvrtmp_1253 = tmp_struct_15.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_16;
            
            return_16.field0 = pvrtmp_1249;
            return_16.field1 = pvrtmp_1250;
            return_16.field2 = pvrtmp_1251;
            return_16.field3 = loc_444;
            return_16.field4 = pvrtmp_1253;
            return return_16;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_19 = *(uintptr_t *) tmpcur_1231;
            GibCursor tmpcur_1262 = GIB_UNTAG(tagged_tmpcur_19);
            GibCursor tmpaftercur_1263 = tmpcur_1231 + 8;
            uint16_t tmptag_1264 = GIB_GET_TAG(tagged_tmpcur_19);
            GibCursor end_from_tagged_indr_651 = tmpcur_1262 + tmptag_1264;
            GibCursor jump_loc_653 = tmpcur_1231 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_17 =
                                                               _copy_Tree(tmpcur_1262, end_r_448, loc_444, tmpcur_1262);
            GibCursor pvrtmp_1265 = tmp_struct_17.field0;
            GibCursor pvrtmp_1266 = tmp_struct_17.field1;
            GibCursor pvrtmp_1267 = tmp_struct_17.field2;
            GibCursor pvrtmp_1268 = tmp_struct_17.field3;
            GibCursor pvrtmp_1269 = tmp_struct_17.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_18;
            
            return_18.field0 = end_r_446;
            return_18.field1 = pvrtmp_1266;
            return_18.field2 = jump_loc_653;
            return_18.field3 = pvrtmp_1268;
            return_18.field4 = pvrtmp_1269;
            return return_18;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_22 = *(uintptr_t *) tmpcur_1231;
            GibCursor tmpcur_1276 = GIB_UNTAG(tagged_tmpcur_22);
            GibCursor tmpaftercur_1277 = tmpcur_1231 + 8;
            uint16_t tmptag_1278 = GIB_GET_TAG(tagged_tmpcur_22);
            GibCursor end_from_tagged_indr_651 = tmpcur_1276 + tmptag_1278;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_20 =
                                                               _copy_Tree(tmpcur_1276, end_r_448, loc_444, tmpcur_1276);
            GibCursor pvrtmp_1279 = tmp_struct_20.field0;
            GibCursor pvrtmp_1280 = tmp_struct_20.field1;
            GibCursor pvrtmp_1281 = tmp_struct_20.field2;
            GibCursor pvrtmp_1282 = tmp_struct_20.field3;
            GibCursor pvrtmp_1283 = tmp_struct_20.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_21;
            
            return_21.field0 = pvrtmp_1279;
            return_21.field1 = pvrtmp_1280;
            return_21.field2 = pvrtmp_1281;
            return_21.field3 = pvrtmp_1282;
            return_21.field4 = pvrtmp_1283;
            return return_21;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1230");
            exit(1);
        }
    }
}

void sumTree(GibCursor *end_r_451,
             GibCursor *tr_36_150_231,
             GibCursorGibCursorGibIntProd *Res)
{
    GibPackedTag tmpval_1291 = *(GibPackedTag *) (*tr_36_150_231);
    //GibCursor tmpcur_1292 = tr_36_150_231 + 1;
    (*tr_36_150_231) += 1;
    
    
  switch_1315:
    ;
    switch (tmpval_1291) {
        
      case 0:
        {
            GibInt tmpval_1293 = *(GibInt *) (*tr_36_150_231);
            //GibCursor tmpcur_1294 = tmpcur_1292 + sizeof(GibInt);
            //GibCursor jump_609 = tmpcur_1292 + 8;

            *(tr_36_150_231) += 8;

            // GibCursorGibCursorGibIntProd return_26;
            // return_26.field0 = end_r_451;
            // return_26.field1 = jump_609;
            // return_26.field2 = tmpval_1293;
            // return return_26;
            Res->field0 = *end_r_451;
            Res->field1 =  *tr_36_150_231;
            Res->field2 += tmpval_1293;
            break;
        }
        
      case 1:
        {
            GibInt tmpval_1295 = *(GibInt *) (*tr_36_150_231);

            //GibCursor tmpcur_1296 = tmpcur_1292 + sizeof(GibInt);
            *tr_36_150_231 += sizeof(GibInt);
            //GibCursor jump_610 = tmpcur_1292 + 8;

            sumTree(end_r_451, tr_36_150_231, Res);

            // GibCursor pvrtmp_1297 = tmp_struct_27.field0;
            // GibCursor pvrtmp_1298 = tmp_struct_27.field1;
            // GibInt pvrtmp_1299 = tmp_struct_27.field2;
            // GibInt fltPrm_200_237 = tmpval_1295 + pvrtmp_1299;


            sumTree(end_r_451, tr_36_150_231, Res);


            // GibCursor pvrtmp_1300 = tmp_struct_28.field0;
            // GibCursor pvrtmp_1301 = tmp_struct_28.field1;
            // GibInt pvrtmp_1302 = tmp_struct_28.field2;
            // GibInt tailprim_613 = fltPrm_200_237 + pvrtmp_1302;
            // GibCursorGibCursorGibIntProd return_29;
            
            // return_29.field0 = pvrtmp_1300;
            // return_29.field1 = pvrtmp_1301;
            // return_29.field2 = tailprim_613;
            // return return_29;

            break;
        }
        
//       case GIB_INDIRECTION_TAG:
//         {
//             uintptr_t tagged_tmpcur_32 = *(uintptr_t *) tmpcur_1292;
//             GibCursor tmpcur_1303 = GIB_UNTAG(tagged_tmpcur_32);
//             GibCursor tmpaftercur_1304 = tmpcur_1292 + 8;
//             uint16_t tmptag_1305 = GIB_GET_TAG(tagged_tmpcur_32);
//             GibCursor end_from_tagged_indr_657 = tmpcur_1303 + tmptag_1305;
//             GibCursor jump_loc_659 = tmpcur_1292 + 8;
//             GibCursorGibCursorGibIntProd tmp_struct_30 =
//                                           sumTree(tmpcur_1303, tmpcur_1303);
//             GibCursor pvrtmp_1306 = tmp_struct_30.field0;
//             GibCursor pvrtmp_1307 = tmp_struct_30.field1;
//             GibInt pvrtmp_1308 = tmp_struct_30.field2;
//             GibCursorGibCursorGibIntProd return_31;
//
//             return_31.field0 = end_r_451;
//             return_31.field1 = jump_loc_659;
//             return_31.field2 = pvrtmp_1308;
//             return return_31;
//             break;
//         }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_35 = *(uintptr_t *) (*tr_36_150_231);
            GibCursor tmpcur_1309 = GIB_UNTAG(tagged_tmpcur_35);

            //GibCursor tmpaftercur_1310 = tmpcur_1292 + 8;
            //uint16_t tmptag_1311 = GIB_GET_TAG(tagged_tmpcur_35);
            //GibCursor end_from_tagged_indr_657 = tmpcur_1309 + tmptag_1311;
            *tr_36_150_231 = tmpcur_1309;

            sumTree(tr_36_150_231, tr_36_150_231, Res);

            // GibCursor pvrtmp_1312 = tmp_struct_33.field0;
            // GibCursor pvrtmp_1313 = tmp_struct_33.field1;
            // GibInt pvrtmp_1314 = tmp_struct_33.field2;
            // GibCursorGibCursorGibIntProd return_34;
            
            // return_34.field0 = pvrtmp_1312;
            // return_34.field1 = pvrtmp_1313;
            // return_34.field2 = pvrtmp_1314;
            // return return_34;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1291");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorProd mkTree(GibCursor end_r_454, GibCursor loc_452,
                                       GibInt d_41_155_239,
                                       GibInt acc_42_156_240)
{
    if (loc_452 + 18 > end_r_454) {
        gib_grow_region(&loc_452, &end_r_454);
    }
    
    GibBool fltIf_203_241 = d_41_155_239 == 0;
    
    if (fltIf_203_241) {
        *(GibPackedTag *) loc_452 = 0;
        
        GibCursor writetag_876 = loc_452 + 1;
        GibCursor after_tag_877 = loc_452 + 1;
        
        *(GibInt *) after_tag_877 = acc_42_156_240;
        
        GibCursor writecur_881 = after_tag_877 + sizeof(GibInt);
        GibCursorGibCursorGibCursorProd return_36;
        
        return_36.field0 = end_r_454;
        return_36.field1 = loc_452;
        return_36.field2 = writecur_881;
        return return_36;
    } else {
        GibInt fltAppE_205_242 = d_41_155_239 - 1;
        GibInt fltAppE_206_243 = d_41_155_239 + acc_42_156_240;
        GibCursor loc_539 = loc_452 + 1;
        GibCursor loc_540 = loc_539 + 8;
        
        *(GibPackedTag *) loc_452 = 1;
        
        GibCursor writetag_888 = loc_452 + 1;
        GibCursor after_tag_889 = loc_452 + 1;
        
        *(GibInt *) after_tag_889 = d_41_155_239;
        
        GibCursor writecur_893 = after_tag_889 + sizeof(GibInt);
        GibCursorGibCursorGibCursorProd tmp_struct_37 =
                                         mkTree(end_r_454, loc_540, fltAppE_205_242, fltAppE_206_243);
        GibCursor pvrtmp_1320 = tmp_struct_37.field0;
        GibCursor pvrtmp_1321 = tmp_struct_37.field1;
        GibCursor pvrtmp_1322 = tmp_struct_37.field2;
        GibInt fltAppE_208_245 = d_41_155_239 - 1;
        GibInt fltAppE_209_246 = d_41_155_239 + acc_42_156_240;
        GibCursorGibCursorGibCursorProd tmp_struct_38 =
                                         mkTree(pvrtmp_1320, pvrtmp_1322, fltAppE_208_245, fltAppE_209_246);
        GibCursor pvrtmp_1327 = tmp_struct_38.field0;
        GibCursor pvrtmp_1328 = tmp_struct_38.field1;
        GibCursor pvrtmp_1329 = tmp_struct_38.field2;
        GibCursorGibCursorGibCursorProd return_39;
        
        return_39.field0 = pvrtmp_1327;
        return_39.field1 = loc_452;
        return_39.field2 = pvrtmp_1329;
        return return_39;
    }
}
GibCursorGibCursorProd _traverse_Tree(GibCursor end_r_457,
                                      GibCursor arg_107_163_248)
{
    GibPackedTag tmpval_1338 = *(GibPackedTag *) arg_107_163_248;
    GibCursor tmpcur_1339 = arg_107_163_248 + 1;
    
    
  switch_1358:
    ;
    switch (tmpval_1338) {
        
      case 0:
        {
            GibInt tmpval_1340 = *(GibInt *) tmpcur_1339;
            GibCursor tmpcur_1341 = tmpcur_1339 + sizeof(GibInt);
            GibCursor jump_616 = tmpcur_1339 + 8;
            GibCursorGibCursorProd return_43;
            
            return_43.field0 = end_r_457;
            return_43.field1 = jump_616;
            return return_43;
            break;
        }
        
      case 1:
        {
            GibInt tmpval_1342 = *(GibInt *) tmpcur_1339;
            GibCursor tmpcur_1343 = tmpcur_1339 + sizeof(GibInt);
            GibCursor jump_618 = tmpcur_1339 + 8;
            GibCursorGibCursorProd tmp_struct_44 =
                                    _traverse_Tree(end_r_457, tmpcur_1343);
            GibCursor pvrtmp_1344 = tmp_struct_44.field0;
            GibCursor pvrtmp_1345 = tmp_struct_44.field1;
            GibCursorGibCursorProd tmp_struct_45 =
                                    _traverse_Tree(pvrtmp_1344, pvrtmp_1345);
            GibCursor pvrtmp_1346 = tmp_struct_45.field0;
            GibCursor pvrtmp_1347 = tmp_struct_45.field1;
            GibCursorGibCursorProd return_46;
            
            return_46.field0 = pvrtmp_1346;
            return_46.field1 = pvrtmp_1347;
            return return_46;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_49 = *(uintptr_t *) tmpcur_1339;
            GibCursor tmpcur_1348 = GIB_UNTAG(tagged_tmpcur_49);
            GibCursor tmpaftercur_1349 = tmpcur_1339 + 8;
            uint16_t tmptag_1350 = GIB_GET_TAG(tagged_tmpcur_49);
            GibCursor end_from_tagged_indr_663 = tmpcur_1348 + tmptag_1350;
            GibCursor jump_loc_665 = tmpcur_1339 + 8;
            GibCursorGibCursorProd tmp_struct_47 =
                                    _traverse_Tree(tmpcur_1348, tmpcur_1348);
            GibCursor pvrtmp_1351 = tmp_struct_47.field0;
            GibCursor pvrtmp_1352 = tmp_struct_47.field1;
            GibCursorGibCursorProd return_48;
            
            return_48.field0 = end_r_457;
            return_48.field1 = jump_loc_665;
            return return_48;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_52 = *(uintptr_t *) tmpcur_1339;
            GibCursor tmpcur_1353 = GIB_UNTAG(tagged_tmpcur_52);
            GibCursor tmpaftercur_1354 = tmpcur_1339 + 8;
            uint16_t tmptag_1355 = GIB_GET_TAG(tagged_tmpcur_52);
            GibCursor end_from_tagged_indr_663 = tmpcur_1353 + tmptag_1355;
            GibCursorGibCursorProd tmp_struct_50 =
                                    _traverse_Tree(tmpcur_1353, tmpcur_1353);
            GibCursor pvrtmp_1356 = tmp_struct_50.field0;
            GibCursor pvrtmp_1357 = tmp_struct_50.field1;
            GibCursorGibCursorProd return_51;
            
            return_51.field0 = pvrtmp_1356;
            return_51.field1 = pvrtmp_1357;
            return return_51;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1338");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_Tree(GibCursor end_r_460,
                                   GibCursor arg_116_170_255)
{
    GibPackedTag tmpval_1359 = *(GibPackedTag *) arg_116_170_255;
    GibCursor tmpcur_1360 = arg_116_170_255 + 1;
    
    
  switch_1379:
    ;
    switch (tmpval_1359) {
        
      case 0:
        {
            GibInt tmpval_1361 = *(GibInt *) tmpcur_1360;
            GibCursor tmpcur_1362 = tmpcur_1360 + sizeof(GibInt);
            GibCursor jump_622 = tmpcur_1360 + 8;
            unsigned char wildcard_119_172_257 = gib_print_symbol(1132);
            unsigned char wildcard_121_173_258 = gib_print_symbol(1135);
            unsigned char y_118_174_259 = printf("%ld", tmpval_1361);
            unsigned char wildcard_120_175_260 = gib_print_symbol(1130);
            GibCursorGibCursorProd return_53;
            
            return_53.field0 = end_r_460;
            return_53.field1 = jump_622;
            return return_53;
            break;
        }
        
      case 1:
        {
            GibInt tmpval_1363 = *(GibInt *) tmpcur_1360;
            GibCursor tmpcur_1364 = tmpcur_1360 + sizeof(GibInt);
            GibCursor jump_624 = tmpcur_1360 + 8;
            unsigned char wildcard_128_179_264 = gib_print_symbol(1131);
            unsigned char wildcard_132_180_265 = gib_print_symbol(1135);
            unsigned char y_125_181_266 = printf("%ld", tmpval_1363);
            unsigned char wildcard_131_182_267 = gib_print_symbol(1135);
            GibCursorGibCursorProd tmp_struct_54 =
                                    _print_Tree(end_r_460, tmpcur_1364);
            GibCursor pvrtmp_1365 = tmp_struct_54.field0;
            GibCursor pvrtmp_1366 = tmp_struct_54.field1;
            unsigned char wildcard_130_184_269 = gib_print_symbol(1135);
            GibCursorGibCursorProd tmp_struct_55 =
                                    _print_Tree(pvrtmp_1365, pvrtmp_1366);
            GibCursor pvrtmp_1367 = tmp_struct_55.field0;
            GibCursor pvrtmp_1368 = tmp_struct_55.field1;
            unsigned char wildcard_129_186_271 = gib_print_symbol(1130);
            GibCursorGibCursorProd return_56;
            
            return_56.field0 = pvrtmp_1367;
            return_56.field1 = pvrtmp_1368;
            return return_56;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_59 = *(uintptr_t *) tmpcur_1360;
            GibCursor tmpcur_1369 = GIB_UNTAG(tagged_tmpcur_59);
            GibCursor tmpaftercur_1370 = tmpcur_1360 + 8;
            uint16_t tmptag_1371 = GIB_GET_TAG(tagged_tmpcur_59);
            GibCursor end_from_tagged_indr_669 = tmpcur_1369 + tmptag_1371;
            GibCursor jump_loc_671 = tmpcur_1360 + 8;
            unsigned char wildcard_674 = gib_print_symbol(1134);
            GibCursorGibCursorProd tmp_struct_57 =
                                    _print_Tree(tmpcur_1369, tmpcur_1369);
            GibCursor pvrtmp_1372 = tmp_struct_57.field0;
            GibCursor pvrtmp_1373 = tmp_struct_57.field1;
            GibCursorGibCursorProd return_58;
            
            return_58.field0 = end_r_460;
            return_58.field1 = jump_loc_671;
            return return_58;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_62 = *(uintptr_t *) tmpcur_1360;
            GibCursor tmpcur_1374 = GIB_UNTAG(tagged_tmpcur_62);
            GibCursor tmpaftercur_1375 = tmpcur_1360 + 8;
            uint16_t tmptag_1376 = GIB_GET_TAG(tagged_tmpcur_62);
            GibCursor end_from_tagged_indr_669 = tmpcur_1374 + tmptag_1376;
            unsigned char wildcard_674 = gib_print_symbol(1133);
            GibCursorGibCursorProd tmp_struct_60 =
                                    _print_Tree(tmpcur_1374, tmpcur_1374);
            GibCursor pvrtmp_1377 = tmp_struct_60.field0;
            GibCursor pvrtmp_1378 = tmp_struct_60.field1;
            GibCursorGibCursorProd return_61;
            
            return_61.field0 = pvrtmp_1377;
            return_61.field1 = pvrtmp_1378;
            return return_61;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1359");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_Tree(GibCursor end_r_464,
                                                                          GibCursor end_r_466,
                                                                          GibCursor loc_462,
                                                                          GibCursor arg_98_187_272)
{
    GibPackedTag tmpval_1380 = *(GibPackedTag *) arg_98_187_272;
    GibCursor tmpcur_1381 = arg_98_187_272 + 1;
    
    
  switch_1440:
    ;
    switch (tmpval_1380) {
        
      case 0:
        {
            GibInt tmpval_1382 = *(GibInt *) tmpcur_1381;
            GibCursor tmpcur_1383 = tmpcur_1381 + sizeof(GibInt);
            GibCursor jump_628 = tmpcur_1381 + 8;
            
            *(GibPackedTag *) loc_462 = 0;
            
            GibCursor writetag_936 = loc_462 + 1;
            GibCursor after_tag_937 = loc_462 + 1;
            
            *(GibInt *) after_tag_937 = tmpval_1382;
            
            GibCursor writecur_941 = after_tag_937 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_63;
            
            return_63.field0 = end_r_464;
            return_63.field1 = end_r_466;
            return_63.field2 = jump_628;
            return_63.field3 = loc_462;
            return_63.field4 = writecur_941;
            return return_63;
            break;
        }
        
      case 1:
        {
            GibInt tmpval_1388 = *(GibInt *) tmpcur_1381;
            GibCursor tmpcur_1389 = tmpcur_1381 + sizeof(GibInt);
            GibCursor jump_630 = tmpcur_1381 + 8;
            GibCursor loc_581 = loc_462 + 1;
            GibCursor loc_582 = loc_581 + 8;
            
            *(GibPackedTag *) loc_462 = 1;
            
            GibCursor writetag_952 = loc_462 + 1;
            GibCursor after_tag_953 = loc_462 + 1;
            
            *(GibInt *) after_tag_953 = tmpval_1388;
            
            GibCursor writecur_957 = after_tag_953 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_64 =
                                                               _copy_without_ptrs_Tree(end_r_464, end_r_466, loc_582, tmpcur_1389);
            GibCursor pvrtmp_1390 = tmp_struct_64.field0;
            GibCursor pvrtmp_1391 = tmp_struct_64.field1;
            GibCursor pvrtmp_1392 = tmp_struct_64.field2;
            GibCursor pvrtmp_1393 = tmp_struct_64.field3;
            GibCursor pvrtmp_1394 = tmp_struct_64.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_65 =
                                                               _copy_without_ptrs_Tree(pvrtmp_1390, pvrtmp_1391, pvrtmp_1394, pvrtmp_1392);
            GibCursor pvrtmp_1399 = tmp_struct_65.field0;
            GibCursor pvrtmp_1400 = tmp_struct_65.field1;
            GibCursor pvrtmp_1401 = tmp_struct_65.field2;
            GibCursor pvrtmp_1402 = tmp_struct_65.field3;
            GibCursor pvrtmp_1403 = tmp_struct_65.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_66;
            
            return_66.field0 = pvrtmp_1399;
            return_66.field1 = pvrtmp_1400;
            return_66.field2 = pvrtmp_1401;
            return_66.field3 = loc_462;
            return_66.field4 = pvrtmp_1403;
            return return_66;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_69 = *(uintptr_t *) tmpcur_1381;
            GibCursor tmpcur_1412 = GIB_UNTAG(tagged_tmpcur_69);
            GibCursor tmpaftercur_1413 = tmpcur_1381 + 8;
            uint16_t tmptag_1414 = GIB_GET_TAG(tagged_tmpcur_69);
            GibCursor end_from_tagged_indr_675 = tmpcur_1412 + tmptag_1414;
            GibCursor jump_loc_677 = tmpcur_1381 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_67 =
                                                               _copy_without_ptrs_Tree(tmpcur_1412, end_r_466, loc_462, tmpcur_1412);
            GibCursor pvrtmp_1415 = tmp_struct_67.field0;
            GibCursor pvrtmp_1416 = tmp_struct_67.field1;
            GibCursor pvrtmp_1417 = tmp_struct_67.field2;
            GibCursor pvrtmp_1418 = tmp_struct_67.field3;
            GibCursor pvrtmp_1419 = tmp_struct_67.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_68;
            
            return_68.field0 = end_r_464;
            return_68.field1 = pvrtmp_1416;
            return_68.field2 = jump_loc_677;
            return_68.field3 = pvrtmp_1418;
            return_68.field4 = pvrtmp_1419;
            return return_68;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_72 = *(uintptr_t *) tmpcur_1381;
            GibCursor tmpcur_1426 = GIB_UNTAG(tagged_tmpcur_72);
            GibCursor tmpaftercur_1427 = tmpcur_1381 + 8;
            uint16_t tmptag_1428 = GIB_GET_TAG(tagged_tmpcur_72);
            GibCursor end_from_tagged_indr_675 = tmpcur_1426 + tmptag_1428;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_70 =
                                                               _copy_without_ptrs_Tree(tmpcur_1426, end_r_466, loc_462, tmpcur_1426);
            GibCursor pvrtmp_1429 = tmp_struct_70.field0;
            GibCursor pvrtmp_1430 = tmp_struct_70.field1;
            GibCursor pvrtmp_1431 = tmp_struct_70.field2;
            GibCursor pvrtmp_1432 = tmp_struct_70.field3;
            GibCursor pvrtmp_1433 = tmp_struct_70.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_71;
            
            return_71.field0 = pvrtmp_1429;
            return_71.field1 = pvrtmp_1430;
            return_71.field2 = pvrtmp_1431;
            return_71.field3 = pvrtmp_1432;
            return_71.field4 = pvrtmp_1433;
            return return_71;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1380");
            exit(1);
        }
    }
}
int main(int argc, char **argv)
{
    int init_86 = gib_init(argc, argv);
    
    info_table_initialize();
    symbol_table_initialize();
    
    GibChunk region_1136 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_479 = region_1136.start;
    GibCursor end_r_479 = region_1136.end;
    GibCursorGibCursorGibCursorProd tmp_struct_73 =
                                     mkTree(end_r_479, r_479, 23, 0);
    GibCursor pvrtmp_1137 = tmp_struct_73.field0;
    GibCursor pvrtmp_1138 = tmp_struct_73.field1;
    GibCursor pvrtmp_1139 = tmp_struct_73.field2;
    GibChunk region_1144 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_478 = region_1144.start;
    GibCursor end_r_478 = region_1144.end;
    GibCursor pvrtmp_1156;
    GibCursor pvrtmp_1157;
    GibCursor pvrtmp_1158;
    GibVector *times_78 = gib_vector_alloc(gib_get_iters_param(),
                                           sizeof(double));
    struct timespec begin_pvrtmp_1156;
    struct timespec end_pvrtmp_1156;
    
    for (long long iters_pvrtmp_1156 = 0; iters_pvrtmp_1156 <
         gib_get_iters_param(); iters_pvrtmp_1156++) {
        if (iters_pvrtmp_1156 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_save_state();
            gib_ptr_bumpalloc_save_state();
        }
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_1156);

        GibCursorGibCursorGibCursorGibCursorGibCursorProd Res;
        Res.field3 = r_478;
        add1Tree(&pvrtmp_1137, &end_r_478, &r_478, &pvrtmp_1138, &Res);

        GibCursor pvrtmp_1145 = Res.field0;
        GibCursor pvrtmp_1146 = Res.field1;
        GibCursor pvrtmp_1147 = Res.field2;
        GibCursor pvrtmp_1148 = Res.field3;
        GibCursor pvrtmp_1149 = Res.field4;
        
        pvrtmp_1156 = pvrtmp_1146;
        pvrtmp_1157 = pvrtmp_1148;
        pvrtmp_1158 = pvrtmp_1149;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_1156);
        if (iters_pvrtmp_1156 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_restore_state();
            gib_ptr_bumpalloc_restore_state();
        }

        pvrtmp_1137 = tmp_struct_73.field0;
        end_r_478 = region_1144.end;
        r_478 = region_1144.start;
        pvrtmp_1138 = tmp_struct_73.field1;

        double itertime_75 = gib_difftimespecs(&begin_pvrtmp_1156,
                                               &end_pvrtmp_1156);
        
        printf("itertime: %lf\n", itertime_75);
        gib_vector_inplace_update(times_78, iters_pvrtmp_1156, &itertime_75);
    }
    gib_vector_inplace_sort(times_78, gib_compare_doubles);
    
    double *tmp_79 = (double *) gib_vector_nth(times_78, gib_get_iters_param() /
                                               2);
    double selftimed_77 = *tmp_79;
    double batchtime_76 = gib_sum_timing_array(times_78);
    
    gib_print_timing_array(times_78);
    gib_vector_free(times_78);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_76);
    printf("SELFTIMED: %e\n", selftimed_77);
    
    GibInt timed_1031;
    GibVector *times_84 = gib_vector_alloc(gib_get_iters_param(),
                                           sizeof(double));
    struct timespec begin_timed_1031;
    struct timespec end_timed_1031;

    for (long long iters_timed_1031 = 0; iters_timed_1031 <
         gib_get_iters_param(); iters_timed_1031++) {
        if (iters_timed_1031 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_save_state();
            gib_ptr_bumpalloc_save_state();
        }
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed_1031);

        GibCursorGibCursorGibIntProd Res;
        sumTree(&end_r_478, &pvrtmp_1157, &Res);

        GibCursor pvrtmp_1166 = Res.field0;
        GibCursor pvrtmp_1167 = Res.field1;
        GibInt pvrtmp_1168 = Res.field2;
        
        timed_1031 = pvrtmp_1168;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed_1031);
        if (iters_timed_1031 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_restore_state();
            gib_ptr_bumpalloc_restore_state();
        }

        //Save the state of mutable cursors.
        end_r_478 = region_1144.end;
        pvrtmp_1157 = region_1144.start;
        Res.field2 = 0;
        
        double itertime_81 = gib_difftimespecs(&begin_timed_1031,
                                               &end_timed_1031);
        
        printf("itertime: %lf\n", itertime_81);
        gib_vector_inplace_update(times_84, iters_timed_1031, &itertime_81);
    }
    gib_vector_inplace_sort(times_84, gib_compare_doubles);
    
    double *tmp_85 = (double *) gib_vector_nth(times_84, gib_get_iters_param() /
                                               2);
    double selftimed_83 = *tmp_85;
    double batchtime_82 = gib_sum_timing_array(times_84);
    
    gib_print_timing_array(times_84);
    gib_vector_free(times_84);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_82);
    printf("SELFTIMED: %e\n", selftimed_83);
    printf("%ld", timed_1031);
    printf("\n");
    
    int exit_87 = gib_exit();
    
    return exit_87;
}

// gcc -std=gnu11  -O3  -flto  -D_GIBBON_GENGC=0  -D_GIBBON_SIMPLE_WRITE_BARRIER=0  -D_GIBBON_EAGER_PROMOTION=1  -o /home/vidushs/Applications/src/gibbon/microbench/manual_soa_examples/MonoTree.aos.exe -I/home/vidushs/Applications/src/gibbon/gibbon-rts/build -L/home/vidushs/Applications/src/gibbon/gibbon-rts/build -Wl,-rpath=/home/vidushs/Applications/src/gibbon/gibbon-rts/build /home/vidushs/Applications/src/gibbon/microbench/manual_soa_examples/MonoTree.aos.c /home/vidushs/Applications/src/gibbon/gibbon-rts/build/gibbon_rts.o -lm  -lgibbon_rts_ng

// gcc -std=gnu11  -g  -flto  -D_GIBBON_GENGC=0  -D_GIBBON_SIMPLE_WRITE_BARRIER=0  -D_GIBBON_EAGER_PROMOTION=1  -o /home/vidushs/Applications/src/gibbon/microbench/manual_soa_examples/MonoTree.aos.exe -I/home/vidushs/Applications/src/gibbon/gibbon-rts/build -L/home/vidushs/Applications/src/gibbon/gibbon-rts/build -Wl,-rpath=/home/vidushs/Applications/src/gibbon/gibbon-rts/build /home/vidushs/Applications/src/gibbon/microbench/manual_soa_examples/MonoTree.aos.c /home/vidushs/Applications/src/gibbon/gibbon-rts/build/gibbon_rts.o -lm  -lgibbon_rts_ng

