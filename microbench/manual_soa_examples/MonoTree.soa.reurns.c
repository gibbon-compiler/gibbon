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
typedef struct GibCursorPtr3Prod_struct {
            GibCursor field0[3];
        } GibCursorPtr3Prod;
typedef struct GibCursorPtr3GibCursorPtr3Prod_struct {
            GibCursor field0[3];
            GibCursor field1[3];
        } GibCursorPtr3GibCursorPtr3Prod;
typedef struct GibCursorPtr3GibCursorPtr3GibIntProd_struct {
            GibCursor field0[3];
            GibCursor field1[3];
            GibInt field2;
        } GibCursorPtr3GibCursorPtr3GibIntProd;
typedef struct GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod_struct {
            GibCursor field0[3];
            GibCursor field1[3];
            GibCursor field2[3];
        } GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod;
typedef struct GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod_struct {
            GibCursor field0[3];
            GibCursor field1[3];
            GibCursor field2[3];
            GibCursor field3[3];
            GibCursor field4[3];
        } GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod;


void add1Tree(GibCursor cursor_ptr_1322[3], GibCursor cursor_ptr_1321[3],
              GibCursor cursor_ptr_1323[3], GibCursor t_31_136_213[3],
              GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod *Ret
             );

GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod
_copy_Tree(GibCursor cursor_ptr_1436[3], GibCursor cursor_ptr_1435[3],
           GibCursor cursor_ptr_1437[3], GibCursor arg_89_141_222[3]);
GibCursorPtr3GibCursorPtr3GibIntProd sumTree(GibCursor cursor_ptr_1549[3],
                                             GibCursor tr_36_150_231[3]);
GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod mkTree(GibCursor cursor_ptr_1622[3],
                                                   GibCursor cursor_ptr_1623[3],
                                                   GibInt d_41_155_239,
                                                   GibInt acc_42_156_240);
GibCursorPtr3GibCursorPtr3Prod _traverse_Tree(GibCursor cursor_ptr_1658[3],
                                              GibCursor arg_107_163_248[3]);
GibCursorPtr3GibCursorPtr3Prod _print_Tree(GibCursor cursor_ptr_1732[3],
                                           GibCursor arg_116_170_255[3]);
GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod
_copy_without_ptrs_Tree(GibCursor cursor_ptr_1807[3],
                        GibCursor cursor_ptr_1806[3],
                        GibCursor cursor_ptr_1808[3],
                        GibCursor arg_98_187_272[3]);
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
    gib_add_symbol(2091, ")");
    gib_add_symbol(2092, "(Node");
    gib_add_symbol(2093, "(Leaf");
    gib_add_symbol(2094, " ->r ");
    gib_add_symbol(2095, " ->i ");
    gib_add_symbol(2096, " ");
}
void add1Tree(GibCursor cursor_ptr_1322[3],
              GibCursor cursor_ptr_1321[3],
              GibCursor cursor_ptr_1323[3],
              GibCursor t_31_136_213[3],
              GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod *Ret
             )
{
    GibCursor *end_r_625 = &cursor_ptr_1321[1];
    GibCursor *end_r_626 = &cursor_ptr_1321[2];
    GibCursor *end_r_624 = &cursor_ptr_1321[0];

    GibCursor *loc_IntTy_619 = &cursor_ptr_1323[1];
    GibCursor *loc_IntTy_620 = &cursor_ptr_1323[2];
    GibCursor *loc_618 = &cursor_ptr_1323[0];
    
    if (*loc_IntTy_620 + 17 > *end_r_626 ||
         (*loc_IntTy_619 + 17 > *end_r_625 ||
           *loc_618 + 34 > *end_r_624)) {
        gib_grow_region(loc_IntTy_620, end_r_626);
        gib_grow_region(loc_IntTy_619, end_r_625);
        gib_grow_region(loc_618, end_r_624);
    }
    
    // GibCursor end_r_621 = cursor_ptr_1322[0];
    // GibCursor end_r_622 = cursor_ptr_1322[1];
    // GibCursor end_r_623 = cursor_ptr_1322[2];

    //GibCursor overwrite_reg_1324[3] = {end_r_624, end_r_625, end_r_626};
    GibCursor *dcon_1328 = &t_31_136_213[0];
    GibPackedTag tmpval_2134 = *(GibPackedTag *) (*dcon_1328);
    //GibCursor tmpcur_2135 = dcon_1328 + 1;
    *dcon_1328 += 1;
    
    
  switch_2206:
    ;
    switch (tmpval_2134) {
        
      case 0:
        {
            GibCursor *soa_field_0_1330 = &t_31_136_213[1];
            //GibCursor *soa_field_1_1331 = &t_31_136_213[2];

            GibInt tmpval_2136 = *(GibInt *) *soa_field_0_1330;

            //GibCursor tmpcur_2137 = soa_field_0_1330 + sizeof(GibInt);

            //GibCursor *loc_615 = &t_31_136_213[0];

            //GibCursor jumpf_dloc_945 = loc_615 + 1;
            //*loc_615 += 1;

            // GibCursor *loc_IntTy_616 = &t_31_136_213[1];
            GibCursor *loc_IntTy_617 = &t_31_136_213[2];

            //GibCursor jumpf_floc_loc_946 = soa_field_0_1330 + 8;
            *soa_field_0_1330 += 8;

            //GibCursor jumpf_floc_loc_947 = loc_IntTy_617 + 0;

            // GibCursor cursor_ptr_1334[3] = {jumpf_dloc_945, jumpf_floc_loc_946,
            //                                 jumpf_floc_loc_947};

            GibInt fltPkd_196_215 = tmpval_2136 + 1;
            //GibCursor new_dloc_740 = loc_618 + 1;
            //GibCursor new_floc_loc_742 = loc_IntTy_620 + 8;
            
            *(GibPackedTag *) *loc_618 = 0;
            
            //GibCursor writetag_1335 = loc_618 + 1;
            //GibCursor after_tag_1336 = loc_618 + 1;
            *loc_618 += 1;
            
            *(GibInt *) *loc_IntTy_619 = fltPkd_196_215;
            
            //GibCursor writecur_1340 = loc_IntTy_619 + sizeof(GibInt);
            *loc_IntTy_619 += sizeof(GibInt);

            // GibCursor aft_soa_loc_1342[3] = {after_tag_1336, writecur_1340,
            //                                  loc_IntTy_620};

            // GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod
            // return_0;
            
            memcpy(Ret->field0, cursor_ptr_1322, sizeof(GibCursor [3]));
            memcpy(Ret->field1, cursor_ptr_1321, sizeof(GibCursor [3]));
            memcpy(Ret->field2, t_31_136_213, sizeof(GibCursor [3]));
            //memcpy(Ret->field3, cursor_ptr_1323, sizeof(GibCursor [3]));
            memcpy(Ret->field4, cursor_ptr_1323, sizeof(GibCursor [3]));
            //return return_0;
            break;
        }
        
      case 1:
        {
            //GibCursor *soa_field_0_1346 = &t_31_136_213[1];
            GibCursor *soa_field_1_1347 = &t_31_136_213[2];

            GibInt tmpval_2142 = *(GibInt *) *soa_field_1_1347;

            //GibCursor tmpcur_2143 = soa_field_1_1347 + sizeof(GibInt);
            *soa_field_1_1347 += sizeof(GibInt);


            // GibCursor cursor_ptr_1327[3] = {tmpcur_2135, soa_field_0_1346,
            //                                 tmpcur_2143};

            //GibCursor *loc_615 = &t_31_136_213[0];

            //GibCursor jumpf_dloc_949 = loc_615 + 1;
            //*loc_615 += 1;

            // GibCursor *loc_IntTy_616 = &t_31_136_213[1];
            // GibCursor *loc_IntTy_617 = &t_31_136_213[2];

            //GibCursor jumpf_floc_loc_951 = soa_field_1_1347 + 8;
            //*soa_field_1_1347 += 8;

            //GibCursor jumpf_floc_loc_950 = loc_IntTy_616 + 0;

            // GibCursor loc_717 = jumpf_dloc_949 + 0;
            // GibCursor loc_716 = jumpf_floc_loc_951 + 0;
            // GibCursor loc_715 = jumpf_floc_loc_950 + 0;
            // GibCursor cursor_ptr_1351[3] = {jumpf_dloc_949, jumpf_floc_loc_950,
            //                                 jumpf_floc_loc_951};
            GibInt fltPkd_197_219 = tmpval_2142 + 1;

            //GibCursor new_dloc_740 = loc_618 + 1;

            //GibCursor new_floc_loc_742 = loc_IntTy_620 + 8;
            // GibCursor cursor_ptr_1352[3] = {new_dloc_740, loc_IntTy_619,
            //                                 new_floc_loc_742};
            
            *(GibPackedTag *) *loc_618 = 1;
            *loc_618 += 1;
            
            // GibCursor writetag_1371 = loc_618 + 1;
            // GibCursor after_tag_1372 = loc_618 + 1;
            
            *(GibInt *) *loc_IntTy_620 = fltPkd_197_219;

            *loc_IntTy_620 += 8;

            add1Tree(cursor_ptr_1322, cursor_ptr_1321, cursor_ptr_1323, t_31_136_213, Ret);

            // GibCursor pvrtmp_2144[3];
            
//             memcpy(pvrtmp_2144, tmp_struct_1.field0, sizeof(GibCursor [3]));
//
//             GibCursor pvrtmp_2145[3];
//
//             memcpy(pvrtmp_2145, tmp_struct_1.field1, sizeof(GibCursor [3]));
//
//             GibCursor pvrtmp_2146[3];
//
//             memcpy(pvrtmp_2146, tmp_struct_1.field2, sizeof(GibCursor [3]));
//
//             GibCursor pvrtmp_2147[3];
//
//             memcpy(pvrtmp_2147, tmp_struct_1.field3, sizeof(GibCursor [3]));
//
//             GibCursor pvrtmp_2148[3];
//
//             memcpy(pvrtmp_2148, tmp_struct_1.field4, sizeof(GibCursor [3]));
            
            add1Tree(cursor_ptr_1322, cursor_ptr_1321, cursor_ptr_1323, t_31_136_213, Ret);

//             GibCursor pvrtmp_2153[3];
//
//             memcpy(pvrtmp_2153, tmp_struct_2.field0, sizeof(GibCursor [3]));
//
//             GibCursor pvrtmp_2154[3];
//
//             memcpy(pvrtmp_2154, tmp_struct_2.field1, sizeof(GibCursor [3]));
//
//             GibCursor pvrtmp_2155[3];
//
//             memcpy(pvrtmp_2155, tmp_struct_2.field2, sizeof(GibCursor [3]));
//
//             GibCursor pvrtmp_2156[3];
//
//             memcpy(pvrtmp_2156, tmp_struct_2.field3, sizeof(GibCursor [3]));
//
//             GibCursor pvrtmp_2157[3];
//
//             memcpy(pvrtmp_2157, tmp_struct_2.field4, sizeof(GibCursor [3]));
//
//             GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod
//             return_3;
            
            // memcpy(return_3.field0, pvrtmp_2153, sizeof(GibCursor [3]));
            // memcpy(return_3.field1, pvrtmp_2154, sizeof(GibCursor [3]));
            // memcpy(return_3.field2, pvrtmp_2155, sizeof(GibCursor [3]));
            // memcpy(return_3.field3, cursor_ptr_1323, sizeof(GibCursor [3]));
            // memcpy(return_3.field4, pvrtmp_2157, sizeof(GibCursor [3]));
            // return return_3;
            break;
        }
        
//       case GIB_INDIRECTION_TAG:
//         {
//             GibCursor soa_field_0_1384 = t_31_136_213[1];
//             GibCursor soa_field_1_1385 = t_31_136_213[2];
//             uintptr_t tagged_tmpcur_8 = *(uintptr_t *) tmpcur_2135;
//             GibCursor tmpcur_2166 = GIB_UNTAG(tagged_tmpcur_8);
//             GibCursor tmpaftercur_2167 = tmpcur_2135 + 8;
//             uint16_t tmptag_2168 = GIB_GET_TAG(tagged_tmpcur_8);
//             GibCursor end_from_tagged_dcon_redir_1398 = tmpcur_2166 +
//                       tmptag_2168;
//             GibCursor field_nxt_1395 = soa_field_0_1384 + 1;
//             uintptr_t tagged_tmpcur_7 = *(uintptr_t *) field_nxt_1395;
//             GibCursor tmpcur_2169 = GIB_UNTAG(tagged_tmpcur_7);
//             GibCursor tmpaftercur_2170 = field_nxt_1395 + 8;
//             uint16_t tmptag_2171 = GIB_GET_TAG(tagged_tmpcur_7);
//             GibCursor end_from_tagged_fld_redir_1399 = tmpcur_2169 +
//                       tmptag_2171;
//             GibCursor field_nxt_1396 = soa_field_1_1385 + 1;
//             uintptr_t tagged_tmpcur_6 = *(uintptr_t *) field_nxt_1396;
//             GibCursor tmpcur_2172 = GIB_UNTAG(tagged_tmpcur_6);
//             GibCursor tmpaftercur_2173 = field_nxt_1396 + 8;
//             uint16_t tmptag_2174 = GIB_GET_TAG(tagged_tmpcur_6);
//             GibCursor end_from_tagged_fld_redir_1400 = tmpcur_2172 +
//                       tmptag_2174;
//             GibCursor indr_1045[3] = {tmpcur_2166, tmpcur_2169, tmpcur_2172};
//             GibCursor loc_615 = t_31_136_213[0];
//             GibCursor jump_dloc_1049 = loc_615 + 9;
//             GibCursor loc_IntTy_617 = t_31_136_213[2];
//             GibCursor loc_IntTy_616 = t_31_136_213[1];
//             GibCursor aft_indir_loc_1057 = loc_IntTy_616 + 9;
//             GibCursor aft_indir_loc_1058 = loc_IntTy_617 + 9;
//             GibCursor cursor_ptr_1401[3] = {jump_dloc_1049, aft_indir_loc_1057,
//                                             aft_indir_loc_1058};
//             GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod
//             tmp_struct_4 =
//              add1Tree(indr_1045, overwrite_reg_1324, cursor_ptr_1323, indr_1045);
//             GibCursor pvrtmp_2175[3];
//
//             memcpy(pvrtmp_2175, tmp_struct_4.field0, sizeof(GibCursor [3]));
//
//             GibCursor pvrtmp_2176[3];
//
//             memcpy(pvrtmp_2176, tmp_struct_4.field1, sizeof(GibCursor [3]));
//
//             GibCursor pvrtmp_2177[3];
//
//             memcpy(pvrtmp_2177, tmp_struct_4.field2, sizeof(GibCursor [3]));
//
//             GibCursor pvrtmp_2178[3];
//
//             memcpy(pvrtmp_2178, tmp_struct_4.field3, sizeof(GibCursor [3]));
//
//             GibCursor pvrtmp_2179[3];
//
//             memcpy(pvrtmp_2179, tmp_struct_4.field4, sizeof(GibCursor [3]));
//
//             GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod
//             return_5;
//
//             memcpy(return_5.field0, cursor_ptr_1322, sizeof(GibCursor [3]));
//             memcpy(return_5.field1, pvrtmp_2176, sizeof(GibCursor [3]));
//             memcpy(return_5.field2, cursor_ptr_1401, sizeof(GibCursor [3]));
//             memcpy(return_5.field3, pvrtmp_2178, sizeof(GibCursor [3]));
//             memcpy(return_5.field4, pvrtmp_2179, sizeof(GibCursor [3]));
//             return return_5;
//             break;
//         }
        
      case GIB_REDIRECTION_TAG:
        {
            GibCursor *soa_field_0_1412 = &t_31_136_213[1];
            GibCursor *soa_field_1_1413 = &t_31_136_213[2];

            uintptr_t tagged_tmpcur_13 = *(uintptr_t *) (*dcon_1328);
            GibCursor tmpcur_2186 = GIB_UNTAG(tagged_tmpcur_13);
            *dcon_1328 = tmpcur_2186;

            // GibCursor tmpaftercur_2187 = tmpcur_2135 + 8;
            // uint16_t tmptag_2188 = GIB_GET_TAG(tagged_tmpcur_13);
            // GibCursor end_from_tagged_dcon_redir_1421 = tmpcur_2186 +
            //           tmptag_2188;

            GibCursor field_nxt_1419 = *soa_field_0_1412 + 1;
            uintptr_t tagged_tmpcur_12 = *(uintptr_t *) field_nxt_1419;
            GibCursor tmpcur_2189 = GIB_UNTAG(tagged_tmpcur_12);
            *soa_field_0_1412 = tmpcur_2189;

            // GibCursor tmpaftercur_2190 = field_nxt_1419 + 8;
            // uint16_t tmptag_2191 = GIB_GET_TAG(tagged_tmpcur_12);
            // GibCursor end_from_tagged_fld_redir_1422 = tmpcur_2189 +
            //           tmptag_2191;

            GibCursor field_nxt_1420 = *soa_field_1_1413 + 1;
            uintptr_t tagged_tmpcur_11 = *(uintptr_t *) field_nxt_1420;
            GibCursor tmpcur_2192 = GIB_UNTAG(tagged_tmpcur_11);
            *soa_field_1_1413 = tmpcur_2192;


            // GibCursor tmpaftercur_2193 = field_nxt_1420 + 8;
            // uint16_t tmptag_2194 = GIB_GET_TAG(tagged_tmpcur_11);
            // GibCursor end_from_tagged_fld_redir_1423 = tmpcur_2192 +
            //           tmptag_2194;

            // GibCursor indr_1045[3] = {tmpcur_2186, tmpcur_2189, tmpcur_2192};

            // GibCursor copy_dloc_1059 = loc_618 + 0;
            // GibCursor copy_floc_loc_1061 = loc_IntTy_620 + 0;
            // GibCursor copy_floc_loc_1060 = loc_IntTy_619 + 0;
            // GibCursor cursor_ptr_1424[3] = {copy_dloc_1059, copy_floc_loc_1060,
            //                                 copy_floc_loc_1061};

            add1Tree(t_31_136_213, cursor_ptr_1321, cursor_ptr_1323, t_31_136_213, Ret);


//             GibCursor pvrtmp_2195[3];
//
//             memcpy(pvrtmp_2195, tmp_struct_9.field0, sizeof(GibCursor [3]));
//
//             GibCursor pvrtmp_2196[3];
//
//             memcpy(pvrtmp_2196, tmp_struct_9.field1, sizeof(GibCursor [3]));
//
//             GibCursor pvrtmp_2197[3];
//
//             memcpy(pvrtmp_2197, tmp_struct_9.field2, sizeof(GibCursor [3]));
//
//             GibCursor pvrtmp_2198[3];
//
//             memcpy(pvrtmp_2198, tmp_struct_9.field3, sizeof(GibCursor [3]));
//
//             GibCursor pvrtmp_2199[3];
//
//             memcpy(pvrtmp_2199, tmp_struct_9.field4, sizeof(GibCursor [3]));
//
//             GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod
//             return_10;
//
//             memcpy(return_10.field0, pvrtmp_2195, sizeof(GibCursor [3]));
//             memcpy(return_10.field1, pvrtmp_2196, sizeof(GibCursor [3]));
//             memcpy(return_10.field2, pvrtmp_2197, sizeof(GibCursor [3]));
//             memcpy(return_10.field3, pvrtmp_2198, sizeof(GibCursor [3]));
//             memcpy(return_10.field4, pvrtmp_2199, sizeof(GibCursor [3]));
//             return return_10;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2134");
            exit(1);
        }
    }
}

GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod _copy_Tree(GibCursor cursor_ptr_1436[3],
                                                                                 GibCursor cursor_ptr_1435[3],
                                                                                 GibCursor cursor_ptr_1437[3],
                                                                                 GibCursor arg_89_141_222[3])
{
    GibCursor end_r_636 = cursor_ptr_1435[0];
    GibCursor end_r_637 = cursor_ptr_1435[1];
    GibCursor end_r_638 = cursor_ptr_1435[2];
    GibCursor loc_IntTy_631 = cursor_ptr_1437[1];
    GibCursor loc_IntTy_632 = cursor_ptr_1437[2];
    GibCursor loc_630 = cursor_ptr_1437[0];
    
    if (loc_IntTy_632 + 17 > end_r_638 || (loc_IntTy_631 + 17 > end_r_637 ||
                                           loc_630 + 34 > end_r_636)) {
        gib_grow_region(&loc_IntTy_632, &end_r_638);
        gib_grow_region(&loc_IntTy_631, &end_r_637);
        gib_grow_region(&loc_630, &end_r_636);
    }
    
    GibCursor end_r_633 = cursor_ptr_1436[0];
    GibCursor end_r_634 = cursor_ptr_1436[1];
    GibCursor end_r_635 = cursor_ptr_1436[2];
    GibCursor overwrite_reg_1438[3] = {end_r_636, end_r_637, end_r_638};
    GibCursor dcon_1442 = arg_89_141_222[0];
    GibPackedTag tmpval_2207 = *(GibPackedTag *) dcon_1442;
    GibCursor tmpcur_2208 = dcon_1442 + 1;
    
    
  switch_2279:
    ;
    switch (tmpval_2207) {
        
      case 0:
        {
            GibCursor soa_field_0_1444 = arg_89_141_222[1];
            GibCursor soa_field_1_1445 = arg_89_141_222[2];
            GibInt tmpval_2209 = *(GibInt *) soa_field_0_1444;
            GibCursor tmpcur_2210 = soa_field_0_1444 + sizeof(GibInt);
            GibCursor loc_627 = arg_89_141_222[0];
            GibCursor jumpf_dloc_959 = loc_627 + 1;
            GibCursor loc_IntTy_628 = arg_89_141_222[1];
            GibCursor loc_IntTy_629 = arg_89_141_222[2];
            GibCursor jumpf_floc_loc_960 = soa_field_0_1444 + 8;
            GibCursor jumpf_floc_loc_961 = loc_IntTy_629 + 0;
            GibCursor cursor_ptr_1448[3] = {jumpf_dloc_959, jumpf_floc_loc_960,
                                            jumpf_floc_loc_961};
            GibCursor new_floc_loc_788 = loc_IntTy_632 + 8;
            GibCursor new_dloc_786 = loc_630 + 1;
            
            *(GibPackedTag *) loc_630 = 0;
            
            GibCursor writetag_1449 = loc_630 + 1;
            GibCursor after_tag_1450 = loc_630 + 1;
            
            *(GibInt *) loc_IntTy_631 = tmpval_2209;
            
            GibCursor writecur_1454 = loc_IntTy_631 + sizeof(GibInt);
            GibCursor aft_soa_loc_1456[3] = {after_tag_1450, writecur_1454,
                                             loc_IntTy_632};
            GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod
            return_14;
            
            memcpy(return_14.field0, cursor_ptr_1436, sizeof(GibCursor [3]));
            memcpy(return_14.field1, overwrite_reg_1438, sizeof(GibCursor [3]));
            memcpy(return_14.field2, cursor_ptr_1448, sizeof(GibCursor [3]));
            memcpy(return_14.field3, cursor_ptr_1437, sizeof(GibCursor [3]));
            memcpy(return_14.field4, aft_soa_loc_1456, sizeof(GibCursor [3]));
            return return_14;
            break;
        }
        
      case 1:
        {
            GibCursor soa_field_0_1460 = arg_89_141_222[1];
            GibCursor soa_field_1_1461 = arg_89_141_222[2];
            GibInt tmpval_2215 = *(GibInt *) soa_field_1_1461;
            GibCursor tmpcur_2216 = soa_field_1_1461 + sizeof(GibInt);
            GibCursor cursor_ptr_1441[3] = {tmpcur_2208, soa_field_0_1460,
                                            tmpcur_2216};
            GibCursor loc_627 = arg_89_141_222[0];
            GibCursor jumpf_dloc_963 = loc_627 + 1;
            GibCursor loc_IntTy_628 = arg_89_141_222[1];
            GibCursor loc_IntTy_629 = arg_89_141_222[2];
            GibCursor jumpf_floc_loc_965 = soa_field_1_1461 + 8;
            GibCursor jumpf_floc_loc_964 = loc_IntTy_628 + 0;
            GibCursor loc_763 = jumpf_dloc_963 + 0;
            GibCursor loc_762 = jumpf_floc_loc_965 + 0;
            GibCursor loc_761 = jumpf_floc_loc_964 + 0;
            GibCursor cursor_ptr_1465[3] = {jumpf_dloc_963, jumpf_floc_loc_964,
                                            jumpf_floc_loc_965};
            GibCursor new_floc_loc_788 = loc_IntTy_632 + 8;
            GibCursor new_dloc_786 = loc_630 + 1;
            GibCursor cursor_ptr_1466[3] = {new_dloc_786, loc_IntTy_631,
                                            new_floc_loc_788};
            
            *(GibPackedTag *) loc_630 = 1;
            
            GibCursor writetag_1485 = loc_630 + 1;
            GibCursor after_tag_1486 = loc_630 + 1;
            
            *(GibInt *) loc_IntTy_632 = tmpval_2215;
            
            GibCursor writecur_1490 = loc_IntTy_632 + sizeof(GibInt);
            GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod
            tmp_struct_15 =
             _copy_Tree(cursor_ptr_1436, overwrite_reg_1438, cursor_ptr_1466, cursor_ptr_1441);
            GibCursor pvrtmp_2217[3];
            
            memcpy(pvrtmp_2217, tmp_struct_15.field0, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2218[3];
            
            memcpy(pvrtmp_2218, tmp_struct_15.field1, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2219[3];
            
            memcpy(pvrtmp_2219, tmp_struct_15.field2, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2220[3];
            
            memcpy(pvrtmp_2220, tmp_struct_15.field3, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2221[3];
            
            memcpy(pvrtmp_2221, tmp_struct_15.field4, sizeof(GibCursor [3]));
            
            GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod
            tmp_struct_16 =
             _copy_Tree(pvrtmp_2217, pvrtmp_2218, pvrtmp_2221, pvrtmp_2219);
            GibCursor pvrtmp_2226[3];
            
            memcpy(pvrtmp_2226, tmp_struct_16.field0, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2227[3];
            
            memcpy(pvrtmp_2227, tmp_struct_16.field1, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2228[3];
            
            memcpy(pvrtmp_2228, tmp_struct_16.field2, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2229[3];
            
            memcpy(pvrtmp_2229, tmp_struct_16.field3, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2230[3];
            
            memcpy(pvrtmp_2230, tmp_struct_16.field4, sizeof(GibCursor [3]));
            
            GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod
            return_17;
            
            memcpy(return_17.field0, pvrtmp_2226, sizeof(GibCursor [3]));
            memcpy(return_17.field1, pvrtmp_2227, sizeof(GibCursor [3]));
            memcpy(return_17.field2, pvrtmp_2228, sizeof(GibCursor [3]));
            memcpy(return_17.field3, cursor_ptr_1437, sizeof(GibCursor [3]));
            memcpy(return_17.field4, pvrtmp_2230, sizeof(GibCursor [3]));
            return return_17;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            GibCursor soa_field_0_1498 = arg_89_141_222[1];
            GibCursor soa_field_1_1499 = arg_89_141_222[2];
            uintptr_t tagged_tmpcur_22 = *(uintptr_t *) tmpcur_2208;
            GibCursor tmpcur_2239 = GIB_UNTAG(tagged_tmpcur_22);
            GibCursor tmpaftercur_2240 = tmpcur_2208 + 8;
            uint16_t tmptag_2241 = GIB_GET_TAG(tagged_tmpcur_22);
            GibCursor end_from_tagged_dcon_redir_1512 = tmpcur_2239 +
                      tmptag_2241;
            GibCursor field_nxt_1509 = soa_field_0_1498 + 1;
            uintptr_t tagged_tmpcur_21 = *(uintptr_t *) field_nxt_1509;
            GibCursor tmpcur_2242 = GIB_UNTAG(tagged_tmpcur_21);
            GibCursor tmpaftercur_2243 = field_nxt_1509 + 8;
            uint16_t tmptag_2244 = GIB_GET_TAG(tagged_tmpcur_21);
            GibCursor end_from_tagged_fld_redir_1513 = tmpcur_2242 +
                      tmptag_2244;
            GibCursor field_nxt_1510 = soa_field_1_1499 + 1;
            uintptr_t tagged_tmpcur_20 = *(uintptr_t *) field_nxt_1510;
            GibCursor tmpcur_2245 = GIB_UNTAG(tagged_tmpcur_20);
            GibCursor tmpaftercur_2246 = field_nxt_1510 + 8;
            uint16_t tmptag_2247 = GIB_GET_TAG(tagged_tmpcur_20);
            GibCursor end_from_tagged_fld_redir_1514 = tmpcur_2245 +
                      tmptag_2247;
            GibCursor indr_1062[3] = {tmpcur_2239, tmpcur_2242, tmpcur_2245};
            GibCursor loc_627 = arg_89_141_222[0];
            GibCursor jump_dloc_1066 = loc_627 + 9;
            GibCursor loc_IntTy_629 = arg_89_141_222[2];
            GibCursor loc_IntTy_628 = arg_89_141_222[1];
            GibCursor aft_indir_loc_1074 = loc_IntTy_628 + 9;
            GibCursor aft_indir_loc_1075 = loc_IntTy_629 + 9;
            GibCursor cursor_ptr_1515[3] = {jump_dloc_1066, aft_indir_loc_1074,
                                            aft_indir_loc_1075};
            GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod
            tmp_struct_18 =
             _copy_Tree(indr_1062, overwrite_reg_1438, cursor_ptr_1437, indr_1062);
            GibCursor pvrtmp_2248[3];
            
            memcpy(pvrtmp_2248, tmp_struct_18.field0, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2249[3];
            
            memcpy(pvrtmp_2249, tmp_struct_18.field1, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2250[3];
            
            memcpy(pvrtmp_2250, tmp_struct_18.field2, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2251[3];
            
            memcpy(pvrtmp_2251, tmp_struct_18.field3, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2252[3];
            
            memcpy(pvrtmp_2252, tmp_struct_18.field4, sizeof(GibCursor [3]));
            
            GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod
            return_19;
            
            memcpy(return_19.field0, cursor_ptr_1436, sizeof(GibCursor [3]));
            memcpy(return_19.field1, pvrtmp_2249, sizeof(GibCursor [3]));
            memcpy(return_19.field2, cursor_ptr_1515, sizeof(GibCursor [3]));
            memcpy(return_19.field3, pvrtmp_2251, sizeof(GibCursor [3]));
            memcpy(return_19.field4, pvrtmp_2252, sizeof(GibCursor [3]));
            return return_19;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            GibCursor soa_field_0_1526 = arg_89_141_222[1];
            GibCursor soa_field_1_1527 = arg_89_141_222[2];
            uintptr_t tagged_tmpcur_27 = *(uintptr_t *) tmpcur_2208;
            GibCursor tmpcur_2259 = GIB_UNTAG(tagged_tmpcur_27);
            GibCursor tmpaftercur_2260 = tmpcur_2208 + 8;
            uint16_t tmptag_2261 = GIB_GET_TAG(tagged_tmpcur_27);
            GibCursor end_from_tagged_dcon_redir_1535 = tmpcur_2259 +
                      tmptag_2261;
            GibCursor field_nxt_1533 = soa_field_0_1526 + 1;
            uintptr_t tagged_tmpcur_26 = *(uintptr_t *) field_nxt_1533;
            GibCursor tmpcur_2262 = GIB_UNTAG(tagged_tmpcur_26);
            GibCursor tmpaftercur_2263 = field_nxt_1533 + 8;
            uint16_t tmptag_2264 = GIB_GET_TAG(tagged_tmpcur_26);
            GibCursor end_from_tagged_fld_redir_1536 = tmpcur_2262 +
                      tmptag_2264;
            GibCursor field_nxt_1534 = soa_field_1_1527 + 1;
            uintptr_t tagged_tmpcur_25 = *(uintptr_t *) field_nxt_1534;
            GibCursor tmpcur_2265 = GIB_UNTAG(tagged_tmpcur_25);
            GibCursor tmpaftercur_2266 = field_nxt_1534 + 8;
            uint16_t tmptag_2267 = GIB_GET_TAG(tagged_tmpcur_25);
            GibCursor end_from_tagged_fld_redir_1537 = tmpcur_2265 +
                      tmptag_2267;
            GibCursor indr_1062[3] = {tmpcur_2259, tmpcur_2262, tmpcur_2265};
            GibCursor copy_dloc_1076 = loc_630 + 0;
            GibCursor copy_floc_loc_1078 = loc_IntTy_632 + 0;
            GibCursor copy_floc_loc_1077 = loc_IntTy_631 + 0;
            GibCursor cursor_ptr_1538[3] = {copy_dloc_1076, copy_floc_loc_1077,
                                            copy_floc_loc_1078};
            GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod
            tmp_struct_23 =
             _copy_Tree(indr_1062, overwrite_reg_1438, cursor_ptr_1538, indr_1062);
            GibCursor pvrtmp_2268[3];
            
            memcpy(pvrtmp_2268, tmp_struct_23.field0, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2269[3];
            
            memcpy(pvrtmp_2269, tmp_struct_23.field1, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2270[3];
            
            memcpy(pvrtmp_2270, tmp_struct_23.field2, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2271[3];
            
            memcpy(pvrtmp_2271, tmp_struct_23.field3, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2272[3];
            
            memcpy(pvrtmp_2272, tmp_struct_23.field4, sizeof(GibCursor [3]));
            
            GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod
            return_24;
            
            memcpy(return_24.field0, pvrtmp_2268, sizeof(GibCursor [3]));
            memcpy(return_24.field1, pvrtmp_2269, sizeof(GibCursor [3]));
            memcpy(return_24.field2, pvrtmp_2270, sizeof(GibCursor [3]));
            memcpy(return_24.field3, pvrtmp_2271, sizeof(GibCursor [3]));
            memcpy(return_24.field4, pvrtmp_2272, sizeof(GibCursor [3]));
            return return_24;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2207");
            exit(1);
        }
    }
}
GibCursorPtr3GibCursorPtr3GibIntProd sumTree(GibCursor cursor_ptr_1549[3],
                                             GibCursor tr_36_150_231[3])
{
    GibCursor end_r_642 = cursor_ptr_1549[0];
    GibCursor end_r_643 = cursor_ptr_1549[1];
    GibCursor end_r_644 = cursor_ptr_1549[2];
    GibCursor dcon_1553 = tr_36_150_231[0];
    GibPackedTag tmpval_2280 = *(GibPackedTag *) dcon_1553;
    GibCursor tmpcur_2281 = dcon_1553 + 1;
    
    
  switch_2316:
    ;
    switch (tmpval_2280) {
        
      case 0:
        {
            GibCursor soa_field_0_1555 = tr_36_150_231[1];
            GibCursor soa_field_1_1556 = tr_36_150_231[2];
            GibInt tmpval_2282 = *(GibInt *) soa_field_0_1555;
            GibCursor tmpcur_2283 = soa_field_0_1555 + sizeof(GibInt);
            GibCursor loc_639 = tr_36_150_231[0];
            GibCursor jumpf_dloc_973 = loc_639 + 1;
            GibCursor loc_IntTy_640 = tr_36_150_231[1];
            GibCursor loc_IntTy_641 = tr_36_150_231[2];
            GibCursor jumpf_floc_loc_974 = soa_field_0_1555 + 8;
            GibCursor jumpf_floc_loc_975 = loc_IntTy_641 + 0;
            GibCursor cursor_ptr_1559[3] = {jumpf_dloc_973, jumpf_floc_loc_974,
                                            jumpf_floc_loc_975};
            GibCursorPtr3GibCursorPtr3GibIntProd return_28;
            
            memcpy(return_28.field0, cursor_ptr_1549, sizeof(GibCursor [3]));
            memcpy(return_28.field1, cursor_ptr_1559, sizeof(GibCursor [3]));
            return_28.field2 = tmpval_2282;
            return return_28;
            break;
        }
        
      case 1:
        {
            GibCursor soa_field_0_1561 = tr_36_150_231[1];
            GibCursor soa_field_1_1562 = tr_36_150_231[2];
            GibInt tmpval_2284 = *(GibInt *) soa_field_1_1562;
            GibCursor tmpcur_2285 = soa_field_1_1562 + sizeof(GibInt);
            GibCursor cursor_ptr_1552[3] = {tmpcur_2281, soa_field_0_1561,
                                            tmpcur_2285};
            GibCursor loc_639 = tr_36_150_231[0];
            GibCursor jumpf_dloc_976 = loc_639 + 1;
            GibCursor loc_IntTy_640 = tr_36_150_231[1];
            GibCursor loc_IntTy_641 = tr_36_150_231[2];
            GibCursor jumpf_floc_loc_978 = soa_field_1_1562 + 8;
            GibCursor jumpf_floc_loc_977 = loc_IntTy_640 + 0;
            GibCursor loc_806 = jumpf_dloc_976 + 0;
            GibCursor loc_805 = jumpf_floc_loc_978 + 0;
            GibCursor loc_804 = jumpf_floc_loc_977 + 0;
            GibCursor cursor_ptr_1566[3] = {jumpf_dloc_976, jumpf_floc_loc_977,
                                            jumpf_floc_loc_978};
            GibCursorPtr3GibCursorPtr3GibIntProd tmp_struct_29 =
                                                  sumTree(cursor_ptr_1549, cursor_ptr_1552);
            GibCursor pvrtmp_2286[3];
            
            memcpy(pvrtmp_2286, tmp_struct_29.field0, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2287[3];
            
            memcpy(pvrtmp_2287, tmp_struct_29.field1, sizeof(GibCursor [3]));
            
            GibInt pvrtmp_2288 = tmp_struct_29.field2;
            GibInt fltPrm_200_237 = tmpval_2284 + pvrtmp_2288;
            GibCursorPtr3GibCursorPtr3GibIntProd tmp_struct_30 =
                                                  sumTree(pvrtmp_2286, pvrtmp_2287);
            GibCursor pvrtmp_2289[3];
            
            memcpy(pvrtmp_2289, tmp_struct_30.field0, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2290[3];
            
            memcpy(pvrtmp_2290, tmp_struct_30.field1, sizeof(GibCursor [3]));
            
            GibInt pvrtmp_2291 = tmp_struct_30.field2;
            GibInt tailprim_985 = fltPrm_200_237 + pvrtmp_2291;
            GibCursorPtr3GibCursorPtr3GibIntProd return_31;
            
            memcpy(return_31.field0, pvrtmp_2289, sizeof(GibCursor [3]));
            memcpy(return_31.field1, pvrtmp_2290, sizeof(GibCursor [3]));
            return_31.field2 = tailprim_985;
            return return_31;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            GibCursor soa_field_0_1579 = tr_36_150_231[1];
            GibCursor soa_field_1_1580 = tr_36_150_231[2];
            uintptr_t tagged_tmpcur_36 = *(uintptr_t *) tmpcur_2281;
            GibCursor tmpcur_2292 = GIB_UNTAG(tagged_tmpcur_36);
            GibCursor tmpaftercur_2293 = tmpcur_2281 + 8;
            uint16_t tmptag_2294 = GIB_GET_TAG(tagged_tmpcur_36);
            GibCursor end_from_tagged_dcon_redir_1593 = tmpcur_2292 +
                      tmptag_2294;
            GibCursor field_nxt_1590 = soa_field_0_1579 + 1;
            uintptr_t tagged_tmpcur_35 = *(uintptr_t *) field_nxt_1590;
            GibCursor tmpcur_2295 = GIB_UNTAG(tagged_tmpcur_35);
            GibCursor tmpaftercur_2296 = field_nxt_1590 + 8;
            uint16_t tmptag_2297 = GIB_GET_TAG(tagged_tmpcur_35);
            GibCursor end_from_tagged_fld_redir_1594 = tmpcur_2295 +
                      tmptag_2297;
            GibCursor field_nxt_1591 = soa_field_1_1580 + 1;
            uintptr_t tagged_tmpcur_34 = *(uintptr_t *) field_nxt_1591;
            GibCursor tmpcur_2298 = GIB_UNTAG(tagged_tmpcur_34);
            GibCursor tmpaftercur_2299 = field_nxt_1591 + 8;
            uint16_t tmptag_2300 = GIB_GET_TAG(tagged_tmpcur_34);
            GibCursor end_from_tagged_fld_redir_1595 = tmpcur_2298 +
                      tmptag_2300;
            GibCursor indr_1079[3] = {tmpcur_2292, tmpcur_2295, tmpcur_2298};
            GibCursor loc_639 = tr_36_150_231[0];
            GibCursor jump_dloc_1083 = loc_639 + 9;
            GibCursor loc_IntTy_641 = tr_36_150_231[2];
            GibCursor loc_IntTy_640 = tr_36_150_231[1];
            GibCursor aft_indir_loc_1091 = loc_IntTy_640 + 9;
            GibCursor aft_indir_loc_1092 = loc_IntTy_641 + 9;
            GibCursor cursor_ptr_1596[3] = {jump_dloc_1083, aft_indir_loc_1091,
                                            aft_indir_loc_1092};
            GibCursorPtr3GibCursorPtr3GibIntProd tmp_struct_32 =
                                                  sumTree(indr_1079, indr_1079);
            GibCursor pvrtmp_2301[3];
            
            memcpy(pvrtmp_2301, tmp_struct_32.field0, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2302[3];
            
            memcpy(pvrtmp_2302, tmp_struct_32.field1, sizeof(GibCursor [3]));
            
            GibInt pvrtmp_2303 = tmp_struct_32.field2;
            GibCursorPtr3GibCursorPtr3GibIntProd return_33;
            
            memcpy(return_33.field0, cursor_ptr_1549, sizeof(GibCursor [3]));
            memcpy(return_33.field1, cursor_ptr_1596, sizeof(GibCursor [3]));
            return_33.field2 = pvrtmp_2303;
            return return_33;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            GibCursor soa_field_0_1604 = tr_36_150_231[1];
            GibCursor soa_field_1_1605 = tr_36_150_231[2];
            uintptr_t tagged_tmpcur_41 = *(uintptr_t *) tmpcur_2281;
            GibCursor tmpcur_2304 = GIB_UNTAG(tagged_tmpcur_41);
            GibCursor tmpaftercur_2305 = tmpcur_2281 + 8;
            uint16_t tmptag_2306 = GIB_GET_TAG(tagged_tmpcur_41);
            GibCursor end_from_tagged_dcon_redir_1613 = tmpcur_2304 +
                      tmptag_2306;
            GibCursor field_nxt_1611 = soa_field_0_1604 + 1;
            uintptr_t tagged_tmpcur_40 = *(uintptr_t *) field_nxt_1611;
            GibCursor tmpcur_2307 = GIB_UNTAG(tagged_tmpcur_40);
            GibCursor tmpaftercur_2308 = field_nxt_1611 + 8;
            uint16_t tmptag_2309 = GIB_GET_TAG(tagged_tmpcur_40);
            GibCursor end_from_tagged_fld_redir_1614 = tmpcur_2307 +
                      tmptag_2309;
            GibCursor field_nxt_1612 = soa_field_1_1605 + 1;
            uintptr_t tagged_tmpcur_39 = *(uintptr_t *) field_nxt_1612;
            GibCursor tmpcur_2310 = GIB_UNTAG(tagged_tmpcur_39);
            GibCursor tmpaftercur_2311 = field_nxt_1612 + 8;
            uint16_t tmptag_2312 = GIB_GET_TAG(tagged_tmpcur_39);
            GibCursor end_from_tagged_fld_redir_1615 = tmpcur_2310 +
                      tmptag_2312;
            GibCursor indr_1079[3] = {tmpcur_2304, tmpcur_2307, tmpcur_2310};
            GibCursorPtr3GibCursorPtr3GibIntProd tmp_struct_37 =
                                                  sumTree(indr_1079, indr_1079);
            GibCursor pvrtmp_2313[3];
            
            memcpy(pvrtmp_2313, tmp_struct_37.field0, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2314[3];
            
            memcpy(pvrtmp_2314, tmp_struct_37.field1, sizeof(GibCursor [3]));
            
            GibInt pvrtmp_2315 = tmp_struct_37.field2;
            GibCursorPtr3GibCursorPtr3GibIntProd return_38;
            
            memcpy(return_38.field0, pvrtmp_2313, sizeof(GibCursor [3]));
            memcpy(return_38.field1, pvrtmp_2314, sizeof(GibCursor [3]));
            return_38.field2 = pvrtmp_2315;
            return return_38;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2280");
            exit(1);
        }
    }
}
GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod mkTree(GibCursor cursor_ptr_1622[3],
                                                   GibCursor cursor_ptr_1623[3],
                                                   GibInt d_41_155_239,
                                                   GibInt acc_42_156_240)
{
    GibCursor end_r_649 = cursor_ptr_1622[1];
    GibCursor end_r_648 = cursor_ptr_1622[0];
    GibCursor end_r_650 = cursor_ptr_1622[2];
    GibCursor loc_645 = cursor_ptr_1623[0];
    GibCursor loc_IntTy_646 = cursor_ptr_1623[1];
    GibCursor loc_IntTy_647 = cursor_ptr_1623[2];
    
    if (loc_IntTy_647 + 17 > end_r_650 || (loc_IntTy_646 + 17 > end_r_649 ||
                                           loc_645 + 34 > end_r_648)) {
        gib_grow_region(&loc_IntTy_647, &end_r_650);
        gib_grow_region(&loc_IntTy_646, &end_r_649);
        gib_grow_region(&loc_645, &end_r_648);
    }
    
    GibCursor overwrite_reg_1624[3] = {end_r_648, end_r_649, end_r_650};
    GibBool fltIf_203_241 = d_41_155_239 == 0;
    
    if (fltIf_203_241) {
        GibCursor new_floc_loc_834 = loc_IntTy_647 + 8;
        GibCursor new_dloc_832 = loc_645 + 1;
        
        *(GibPackedTag *) loc_645 = 0;
        
        GibCursor writetag_1625 = loc_645 + 1;
        GibCursor after_tag_1626 = loc_645 + 1;
        
        *(GibInt *) loc_IntTy_646 = acc_42_156_240;
        
        GibCursor writecur_1630 = loc_IntTy_646 + sizeof(GibInt);
        GibCursor aft_soa_loc_1632[3] = {after_tag_1626, writecur_1630,
                                         loc_IntTy_647};
        GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod return_42;
        
        memcpy(return_42.field0, overwrite_reg_1624, sizeof(GibCursor [3]));
        memcpy(return_42.field1, cursor_ptr_1623, sizeof(GibCursor [3]));
        memcpy(return_42.field2, aft_soa_loc_1632, sizeof(GibCursor [3]));
        return return_42;
    } else {
        GibInt fltAppE_205_242 = d_41_155_239 - 1;
        GibInt fltAppE_206_243 = d_41_155_239 + acc_42_156_240;
        GibCursor new_floc_loc_834 = loc_IntTy_647 + 8;
        GibCursor new_dloc_832 = loc_645 + 1;
        GibCursor cursor_ptr_1635[3] = {new_dloc_832, loc_IntTy_646,
                                        new_floc_loc_834};
        
        *(GibPackedTag *) loc_645 = 1;
        
        GibCursor writetag_1645 = loc_645 + 1;
        GibCursor after_tag_1646 = loc_645 + 1;
        
        *(GibInt *) loc_IntTy_647 = d_41_155_239;
        
        GibCursor writecur_1650 = loc_IntTy_647 + sizeof(GibInt);
        GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod tmp_struct_43 =
                                                     mkTree(overwrite_reg_1624, cursor_ptr_1635, fltAppE_205_242, fltAppE_206_243);
        GibCursor pvrtmp_2321[3];
        
        memcpy(pvrtmp_2321, tmp_struct_43.field0, sizeof(GibCursor [3]));
        
        GibCursor pvrtmp_2322[3];
        
        memcpy(pvrtmp_2322, tmp_struct_43.field1, sizeof(GibCursor [3]));
        
        GibCursor pvrtmp_2323[3];
        
        memcpy(pvrtmp_2323, tmp_struct_43.field2, sizeof(GibCursor [3]));
        
        GibInt fltAppE_208_245 = d_41_155_239 - 1;
        GibInt fltAppE_209_246 = d_41_155_239 + acc_42_156_240;
        GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod tmp_struct_44 =
                                                     mkTree(pvrtmp_2321, pvrtmp_2323, fltAppE_208_245, fltAppE_209_246);
        GibCursor pvrtmp_2328[3];
        
        memcpy(pvrtmp_2328, tmp_struct_44.field0, sizeof(GibCursor [3]));
        
        GibCursor pvrtmp_2329[3];
        
        memcpy(pvrtmp_2329, tmp_struct_44.field1, sizeof(GibCursor [3]));
        
        GibCursor pvrtmp_2330[3];
        
        memcpy(pvrtmp_2330, tmp_struct_44.field2, sizeof(GibCursor [3]));
        
        GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod return_45;
        
        memcpy(return_45.field0, pvrtmp_2328, sizeof(GibCursor [3]));
        memcpy(return_45.field1, cursor_ptr_1623, sizeof(GibCursor [3]));
        memcpy(return_45.field2, pvrtmp_2330, sizeof(GibCursor [3]));
        return return_45;
    }
}
GibCursorPtr3GibCursorPtr3Prod _traverse_Tree(GibCursor cursor_ptr_1658[3],
                                              GibCursor arg_107_163_248[3])
{
    GibCursor end_r_654 = cursor_ptr_1658[0];
    GibCursor end_r_655 = cursor_ptr_1658[1];
    GibCursor end_r_656 = cursor_ptr_1658[2];
    GibCursor dcon_1662 = arg_107_163_248[0];
    GibPackedTag tmpval_2339 = *(GibPackedTag *) dcon_1662;
    GibCursor tmpcur_2340 = dcon_1662 + 1;
    
    
  switch_2371:
    ;
    switch (tmpval_2339) {
        
      case 0:
        {
            GibCursor soa_field_0_1664 = arg_107_163_248[1];
            GibCursor soa_field_1_1665 = arg_107_163_248[2];
            GibInt tmpval_2341 = *(GibInt *) soa_field_0_1664;
            GibCursor tmpcur_2342 = soa_field_0_1664 + sizeof(GibInt);
            GibCursor loc_651 = arg_107_163_248[0];
            GibCursor jumpf_dloc_988 = loc_651 + 1;
            GibCursor loc_IntTy_652 = arg_107_163_248[1];
            GibCursor loc_IntTy_653 = arg_107_163_248[2];
            GibCursor jumpf_floc_loc_989 = soa_field_0_1664 + 8;
            GibCursor jumpf_floc_loc_990 = loc_IntTy_653 + 0;
            GibCursor cursor_ptr_1668[3] = {jumpf_dloc_988, jumpf_floc_loc_989,
                                            jumpf_floc_loc_990};
            GibCursorPtr3GibCursorPtr3Prod return_46;
            
            memcpy(return_46.field0, cursor_ptr_1658, sizeof(GibCursor [3]));
            memcpy(return_46.field1, cursor_ptr_1668, sizeof(GibCursor [3]));
            return return_46;
            break;
        }
        
      case 1:
        {
            GibCursor soa_field_0_1670 = arg_107_163_248[1];
            GibCursor soa_field_1_1671 = arg_107_163_248[2];
            GibInt tmpval_2343 = *(GibInt *) soa_field_1_1671;
            GibCursor tmpcur_2344 = soa_field_1_1671 + sizeof(GibInt);
            GibCursor cursor_ptr_1661[3] = {tmpcur_2340, soa_field_0_1670,
                                            tmpcur_2344};
            GibCursor loc_651 = arg_107_163_248[0];
            GibCursor jumpf_dloc_992 = loc_651 + 1;
            GibCursor loc_IntTy_652 = arg_107_163_248[1];
            GibCursor loc_IntTy_653 = arg_107_163_248[2];
            GibCursor jumpf_floc_loc_994 = soa_field_1_1671 + 8;
            GibCursor jumpf_floc_loc_993 = loc_IntTy_652 + 0;
            GibCursor loc_852 = jumpf_dloc_992 + 0;
            GibCursor loc_851 = jumpf_floc_loc_994 + 0;
            GibCursor loc_850 = jumpf_floc_loc_993 + 0;
            GibCursor cursor_ptr_1675[3] = {jumpf_dloc_992, jumpf_floc_loc_993,
                                            jumpf_floc_loc_994};
            GibCursorPtr3GibCursorPtr3Prod tmp_struct_47 =
                                            _traverse_Tree(cursor_ptr_1658, cursor_ptr_1661);
            GibCursor pvrtmp_2345[3];
            
            memcpy(pvrtmp_2345, tmp_struct_47.field0, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2346[3];
            
            memcpy(pvrtmp_2346, tmp_struct_47.field1, sizeof(GibCursor [3]));
            
            GibCursorPtr3GibCursorPtr3Prod tmp_struct_48 =
                                            _traverse_Tree(pvrtmp_2345, pvrtmp_2346);
            GibCursor pvrtmp_2347[3];
            
            memcpy(pvrtmp_2347, tmp_struct_48.field0, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2348[3];
            
            memcpy(pvrtmp_2348, tmp_struct_48.field1, sizeof(GibCursor [3]));
            
            GibCursorPtr3GibCursorPtr3Prod return_49;
            
            memcpy(return_49.field0, pvrtmp_2347, sizeof(GibCursor [3]));
            memcpy(return_49.field1, pvrtmp_2348, sizeof(GibCursor [3]));
            return return_49;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            GibCursor soa_field_0_1688 = arg_107_163_248[1];
            GibCursor soa_field_1_1689 = arg_107_163_248[2];
            uintptr_t tagged_tmpcur_54 = *(uintptr_t *) tmpcur_2340;
            GibCursor tmpcur_2349 = GIB_UNTAG(tagged_tmpcur_54);
            GibCursor tmpaftercur_2350 = tmpcur_2340 + 8;
            uint16_t tmptag_2351 = GIB_GET_TAG(tagged_tmpcur_54);
            GibCursor end_from_tagged_dcon_redir_1702 = tmpcur_2349 +
                      tmptag_2351;
            GibCursor field_nxt_1699 = soa_field_0_1688 + 1;
            uintptr_t tagged_tmpcur_53 = *(uintptr_t *) field_nxt_1699;
            GibCursor tmpcur_2352 = GIB_UNTAG(tagged_tmpcur_53);
            GibCursor tmpaftercur_2353 = field_nxt_1699 + 8;
            uint16_t tmptag_2354 = GIB_GET_TAG(tagged_tmpcur_53);
            GibCursor end_from_tagged_fld_redir_1703 = tmpcur_2352 +
                      tmptag_2354;
            GibCursor field_nxt_1700 = soa_field_1_1689 + 1;
            uintptr_t tagged_tmpcur_52 = *(uintptr_t *) field_nxt_1700;
            GibCursor tmpcur_2355 = GIB_UNTAG(tagged_tmpcur_52);
            GibCursor tmpaftercur_2356 = field_nxt_1700 + 8;
            uint16_t tmptag_2357 = GIB_GET_TAG(tagged_tmpcur_52);
            GibCursor end_from_tagged_fld_redir_1704 = tmpcur_2355 +
                      tmptag_2357;
            GibCursor indr_1093[3] = {tmpcur_2349, tmpcur_2352, tmpcur_2355};
            GibCursor loc_651 = arg_107_163_248[0];
            GibCursor jump_dloc_1097 = loc_651 + 9;
            GibCursor loc_IntTy_653 = arg_107_163_248[2];
            GibCursor loc_IntTy_652 = arg_107_163_248[1];
            GibCursor aft_indir_loc_1105 = loc_IntTy_652 + 9;
            GibCursor aft_indir_loc_1106 = loc_IntTy_653 + 9;
            GibCursor cursor_ptr_1705[3] = {jump_dloc_1097, aft_indir_loc_1105,
                                            aft_indir_loc_1106};
            GibCursorPtr3GibCursorPtr3Prod tmp_struct_50 =
                                            _traverse_Tree(indr_1093, indr_1093);
            GibCursor pvrtmp_2358[3];
            
            memcpy(pvrtmp_2358, tmp_struct_50.field0, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2359[3];
            
            memcpy(pvrtmp_2359, tmp_struct_50.field1, sizeof(GibCursor [3]));
            
            GibCursorPtr3GibCursorPtr3Prod return_51;
            
            memcpy(return_51.field0, cursor_ptr_1658, sizeof(GibCursor [3]));
            memcpy(return_51.field1, cursor_ptr_1705, sizeof(GibCursor [3]));
            return return_51;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            GibCursor soa_field_0_1713 = arg_107_163_248[1];
            GibCursor soa_field_1_1714 = arg_107_163_248[2];
            uintptr_t tagged_tmpcur_59 = *(uintptr_t *) tmpcur_2340;
            GibCursor tmpcur_2360 = GIB_UNTAG(tagged_tmpcur_59);
            GibCursor tmpaftercur_2361 = tmpcur_2340 + 8;
            uint16_t tmptag_2362 = GIB_GET_TAG(tagged_tmpcur_59);
            GibCursor end_from_tagged_dcon_redir_1722 = tmpcur_2360 +
                      tmptag_2362;
            GibCursor field_nxt_1720 = soa_field_0_1713 + 1;
            uintptr_t tagged_tmpcur_58 = *(uintptr_t *) field_nxt_1720;
            GibCursor tmpcur_2363 = GIB_UNTAG(tagged_tmpcur_58);
            GibCursor tmpaftercur_2364 = field_nxt_1720 + 8;
            uint16_t tmptag_2365 = GIB_GET_TAG(tagged_tmpcur_58);
            GibCursor end_from_tagged_fld_redir_1723 = tmpcur_2363 +
                      tmptag_2365;
            GibCursor field_nxt_1721 = soa_field_1_1714 + 1;
            uintptr_t tagged_tmpcur_57 = *(uintptr_t *) field_nxt_1721;
            GibCursor tmpcur_2366 = GIB_UNTAG(tagged_tmpcur_57);
            GibCursor tmpaftercur_2367 = field_nxt_1721 + 8;
            uint16_t tmptag_2368 = GIB_GET_TAG(tagged_tmpcur_57);
            GibCursor end_from_tagged_fld_redir_1724 = tmpcur_2366 +
                      tmptag_2368;
            GibCursor indr_1093[3] = {tmpcur_2360, tmpcur_2363, tmpcur_2366};
            GibCursorPtr3GibCursorPtr3Prod tmp_struct_55 =
                                            _traverse_Tree(indr_1093, indr_1093);
            GibCursor pvrtmp_2369[3];
            
            memcpy(pvrtmp_2369, tmp_struct_55.field0, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2370[3];
            
            memcpy(pvrtmp_2370, tmp_struct_55.field1, sizeof(GibCursor [3]));
            
            GibCursorPtr3GibCursorPtr3Prod return_56;
            
            memcpy(return_56.field0, pvrtmp_2369, sizeof(GibCursor [3]));
            memcpy(return_56.field1, pvrtmp_2370, sizeof(GibCursor [3]));
            return return_56;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2339");
            exit(1);
        }
    }
}
GibCursorPtr3GibCursorPtr3Prod _print_Tree(GibCursor cursor_ptr_1732[3],
                                           GibCursor arg_116_170_255[3])
{
    GibCursor end_r_660 = cursor_ptr_1732[0];
    GibCursor end_r_661 = cursor_ptr_1732[1];
    GibCursor end_r_662 = cursor_ptr_1732[2];
    GibCursor dcon_1736 = arg_116_170_255[0];
    GibPackedTag tmpval_2372 = *(GibPackedTag *) dcon_1736;
    GibCursor tmpcur_2373 = dcon_1736 + 1;
    
    
  switch_2404:
    ;
    switch (tmpval_2372) {
        
      case 0:
        {
            GibCursor soa_field_0_1738 = arg_116_170_255[1];
            GibCursor soa_field_1_1739 = arg_116_170_255[2];
            GibInt tmpval_2374 = *(GibInt *) soa_field_0_1738;
            GibCursor tmpcur_2375 = soa_field_0_1738 + sizeof(GibInt);
            GibCursor loc_657 = arg_116_170_255[0];
            GibCursor jumpf_dloc_1002 = loc_657 + 1;
            GibCursor loc_IntTy_658 = arg_116_170_255[1];
            GibCursor loc_IntTy_659 = arg_116_170_255[2];
            GibCursor jumpf_floc_loc_1003 = soa_field_0_1738 + 8;
            GibCursor jumpf_floc_loc_1004 = loc_IntTy_659 + 0;
            GibCursor cursor_ptr_1742[3] = {jumpf_dloc_1002,
                                            jumpf_floc_loc_1003,
                                            jumpf_floc_loc_1004};
            unsigned char wildcard_119_172_257 = gib_print_symbol(2093);
            unsigned char wildcard_121_173_258 = gib_print_symbol(2096);
            unsigned char y_118_174_259 = printf("%ld", tmpval_2374);
            unsigned char wildcard_120_175_260 = gib_print_symbol(2091);
            GibCursorPtr3GibCursorPtr3Prod return_60;
            
            memcpy(return_60.field0, cursor_ptr_1732, sizeof(GibCursor [3]));
            memcpy(return_60.field1, cursor_ptr_1742, sizeof(GibCursor [3]));
            return return_60;
            break;
        }
        
      case 1:
        {
            GibCursor soa_field_0_1744 = arg_116_170_255[1];
            GibCursor soa_field_1_1745 = arg_116_170_255[2];
            GibInt tmpval_2376 = *(GibInt *) soa_field_1_1745;
            GibCursor tmpcur_2377 = soa_field_1_1745 + sizeof(GibInt);
            GibCursor cursor_ptr_1735[3] = {tmpcur_2373, soa_field_0_1744,
                                            tmpcur_2377};
            GibCursor loc_657 = arg_116_170_255[0];
            GibCursor jumpf_dloc_1006 = loc_657 + 1;
            GibCursor loc_IntTy_658 = arg_116_170_255[1];
            GibCursor loc_IntTy_659 = arg_116_170_255[2];
            GibCursor jumpf_floc_loc_1008 = soa_field_1_1745 + 8;
            GibCursor jumpf_floc_loc_1007 = loc_IntTy_658 + 0;
            GibCursor loc_874 = jumpf_dloc_1006 + 0;
            GibCursor loc_873 = jumpf_floc_loc_1008 + 0;
            GibCursor loc_872 = jumpf_floc_loc_1007 + 0;
            GibCursor cursor_ptr_1749[3] = {jumpf_dloc_1006,
                                            jumpf_floc_loc_1007,
                                            jumpf_floc_loc_1008};
            unsigned char wildcard_128_179_264 = gib_print_symbol(2092);
            unsigned char wildcard_132_180_265 = gib_print_symbol(2096);
            unsigned char y_125_181_266 = printf("%ld", tmpval_2376);
            unsigned char wildcard_131_182_267 = gib_print_symbol(2096);
            GibCursorPtr3GibCursorPtr3Prod tmp_struct_61 =
                                            _print_Tree(cursor_ptr_1732, cursor_ptr_1735);
            GibCursor pvrtmp_2378[3];
            
            memcpy(pvrtmp_2378, tmp_struct_61.field0, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2379[3];
            
            memcpy(pvrtmp_2379, tmp_struct_61.field1, sizeof(GibCursor [3]));
            
            unsigned char wildcard_130_184_269 = gib_print_symbol(2096);
            GibCursorPtr3GibCursorPtr3Prod tmp_struct_62 =
                                            _print_Tree(pvrtmp_2378, pvrtmp_2379);
            GibCursor pvrtmp_2380[3];
            
            memcpy(pvrtmp_2380, tmp_struct_62.field0, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2381[3];
            
            memcpy(pvrtmp_2381, tmp_struct_62.field1, sizeof(GibCursor [3]));
            
            unsigned char wildcard_129_186_271 = gib_print_symbol(2091);
            GibCursorPtr3GibCursorPtr3Prod return_63;
            
            memcpy(return_63.field0, pvrtmp_2380, sizeof(GibCursor [3]));
            memcpy(return_63.field1, pvrtmp_2381, sizeof(GibCursor [3]));
            return return_63;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            GibCursor soa_field_0_1762 = arg_116_170_255[1];
            GibCursor soa_field_1_1763 = arg_116_170_255[2];
            uintptr_t tagged_tmpcur_68 = *(uintptr_t *) tmpcur_2373;
            GibCursor tmpcur_2382 = GIB_UNTAG(tagged_tmpcur_68);
            GibCursor tmpaftercur_2383 = tmpcur_2373 + 8;
            uint16_t tmptag_2384 = GIB_GET_TAG(tagged_tmpcur_68);
            GibCursor end_from_tagged_dcon_redir_1776 = tmpcur_2382 +
                      tmptag_2384;
            GibCursor field_nxt_1773 = soa_field_0_1762 + 1;
            uintptr_t tagged_tmpcur_67 = *(uintptr_t *) field_nxt_1773;
            GibCursor tmpcur_2385 = GIB_UNTAG(tagged_tmpcur_67);
            GibCursor tmpaftercur_2386 = field_nxt_1773 + 8;
            uint16_t tmptag_2387 = GIB_GET_TAG(tagged_tmpcur_67);
            GibCursor end_from_tagged_fld_redir_1777 = tmpcur_2385 +
                      tmptag_2387;
            GibCursor field_nxt_1774 = soa_field_1_1763 + 1;
            uintptr_t tagged_tmpcur_66 = *(uintptr_t *) field_nxt_1774;
            GibCursor tmpcur_2388 = GIB_UNTAG(tagged_tmpcur_66);
            GibCursor tmpaftercur_2389 = field_nxt_1774 + 8;
            uint16_t tmptag_2390 = GIB_GET_TAG(tagged_tmpcur_66);
            GibCursor end_from_tagged_fld_redir_1778 = tmpcur_2388 +
                      tmptag_2390;
            GibCursor indr_1107[3] = {tmpcur_2382, tmpcur_2385, tmpcur_2388};
            GibCursor loc_657 = arg_116_170_255[0];
            GibCursor jump_dloc_1111 = loc_657 + 9;
            GibCursor loc_IntTy_659 = arg_116_170_255[2];
            GibCursor loc_IntTy_658 = arg_116_170_255[1];
            GibCursor aft_indir_loc_1119 = loc_IntTy_658 + 9;
            GibCursor aft_indir_loc_1120 = loc_IntTy_659 + 9;
            GibCursor cursor_ptr_1779[3] = {jump_dloc_1111, aft_indir_loc_1119,
                                            aft_indir_loc_1120};
            unsigned char wildcard_1118 = gib_print_symbol(2095);
            GibCursorPtr3GibCursorPtr3Prod tmp_struct_64 =
                                            _print_Tree(indr_1107, indr_1107);
            GibCursor pvrtmp_2391[3];
            
            memcpy(pvrtmp_2391, tmp_struct_64.field0, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2392[3];
            
            memcpy(pvrtmp_2392, tmp_struct_64.field1, sizeof(GibCursor [3]));
            
            GibCursorPtr3GibCursorPtr3Prod return_65;
            
            memcpy(return_65.field0, cursor_ptr_1732, sizeof(GibCursor [3]));
            memcpy(return_65.field1, cursor_ptr_1779, sizeof(GibCursor [3]));
            return return_65;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            GibCursor soa_field_0_1787 = arg_116_170_255[1];
            GibCursor soa_field_1_1788 = arg_116_170_255[2];
            uintptr_t tagged_tmpcur_73 = *(uintptr_t *) tmpcur_2373;
            GibCursor tmpcur_2393 = GIB_UNTAG(tagged_tmpcur_73);
            GibCursor tmpaftercur_2394 = tmpcur_2373 + 8;
            uint16_t tmptag_2395 = GIB_GET_TAG(tagged_tmpcur_73);
            GibCursor end_from_tagged_dcon_redir_1796 = tmpcur_2393 +
                      tmptag_2395;
            GibCursor field_nxt_1794 = soa_field_0_1787 + 1;
            uintptr_t tagged_tmpcur_72 = *(uintptr_t *) field_nxt_1794;
            GibCursor tmpcur_2396 = GIB_UNTAG(tagged_tmpcur_72);
            GibCursor tmpaftercur_2397 = field_nxt_1794 + 8;
            uint16_t tmptag_2398 = GIB_GET_TAG(tagged_tmpcur_72);
            GibCursor end_from_tagged_fld_redir_1797 = tmpcur_2396 +
                      tmptag_2398;
            GibCursor field_nxt_1795 = soa_field_1_1788 + 1;
            uintptr_t tagged_tmpcur_71 = *(uintptr_t *) field_nxt_1795;
            GibCursor tmpcur_2399 = GIB_UNTAG(tagged_tmpcur_71);
            GibCursor tmpaftercur_2400 = field_nxt_1795 + 8;
            uint16_t tmptag_2401 = GIB_GET_TAG(tagged_tmpcur_71);
            GibCursor end_from_tagged_fld_redir_1798 = tmpcur_2399 +
                      tmptag_2401;
            GibCursor indr_1107[3] = {tmpcur_2393, tmpcur_2396, tmpcur_2399};
            unsigned char wildcard_1118 = gib_print_symbol(2094);
            GibCursorPtr3GibCursorPtr3Prod tmp_struct_69 =
                                            _print_Tree(indr_1107, indr_1107);
            GibCursor pvrtmp_2402[3];
            
            memcpy(pvrtmp_2402, tmp_struct_69.field0, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2403[3];
            
            memcpy(pvrtmp_2403, tmp_struct_69.field1, sizeof(GibCursor [3]));
            
            GibCursorPtr3GibCursorPtr3Prod return_70;
            
            memcpy(return_70.field0, pvrtmp_2402, sizeof(GibCursor [3]));
            memcpy(return_70.field1, pvrtmp_2403, sizeof(GibCursor [3]));
            return return_70;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2372");
            exit(1);
        }
    }
}
GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod _copy_without_ptrs_Tree(GibCursor cursor_ptr_1807[3],
                                                                                              GibCursor cursor_ptr_1806[3],
                                                                                              GibCursor cursor_ptr_1808[3],
                                                                                              GibCursor arg_98_187_272[3])
{
    GibCursor end_r_669 = cursor_ptr_1807[0];
    GibCursor end_r_670 = cursor_ptr_1807[1];
    GibCursor end_r_671 = cursor_ptr_1807[2];
    GibCursor end_r_672 = cursor_ptr_1806[0];
    GibCursor end_r_673 = cursor_ptr_1806[1];
    GibCursor end_r_674 = cursor_ptr_1806[2];
    GibCursor dcon_1812 = arg_98_187_272[0];
    GibPackedTag tmpval_2405 = *(GibPackedTag *) dcon_1812;
    GibCursor tmpcur_2406 = dcon_1812 + 1;
    
    
  switch_2477:
    ;
    switch (tmpval_2405) {
        
      case 0:
        {
            GibCursor soa_field_0_1814 = arg_98_187_272[1];
            GibCursor soa_field_1_1815 = arg_98_187_272[2];
            GibInt tmpval_2407 = *(GibInt *) soa_field_0_1814;
            GibCursor tmpcur_2408 = soa_field_0_1814 + sizeof(GibInt);
            GibCursor loc_663 = arg_98_187_272[0];
            GibCursor jumpf_dloc_1016 = loc_663 + 1;
            GibCursor loc_IntTy_664 = arg_98_187_272[1];
            GibCursor loc_IntTy_665 = arg_98_187_272[2];
            GibCursor jumpf_floc_loc_1017 = soa_field_0_1814 + 8;
            GibCursor jumpf_floc_loc_1018 = loc_IntTy_665 + 0;
            GibCursor cursor_ptr_1818[3] = {jumpf_dloc_1016,
                                            jumpf_floc_loc_1017,
                                            jumpf_floc_loc_1018};
            GibCursor loc_IntTy_668 = cursor_ptr_1808[2];
            GibCursor new_floc_loc_924 = loc_IntTy_668 + 8;
            GibCursor loc_666 = cursor_ptr_1808[0];
            GibCursor new_dloc_922 = loc_666 + 1;
            GibCursor loc_IntTy_667 = cursor_ptr_1808[1];
            
            *(GibPackedTag *) loc_666 = 0;
            
            GibCursor writetag_1819 = loc_666 + 1;
            GibCursor after_tag_1820 = loc_666 + 1;
            
            *(GibInt *) loc_IntTy_667 = tmpval_2407;
            
            GibCursor writecur_1824 = loc_IntTy_667 + sizeof(GibInt);
            GibCursor aft_soa_loc_1826[3] = {after_tag_1820, writecur_1824,
                                             loc_IntTy_668};
            GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod
            return_74;
            
            memcpy(return_74.field0, cursor_ptr_1807, sizeof(GibCursor [3]));
            memcpy(return_74.field1, cursor_ptr_1806, sizeof(GibCursor [3]));
            memcpy(return_74.field2, cursor_ptr_1818, sizeof(GibCursor [3]));
            memcpy(return_74.field3, cursor_ptr_1808, sizeof(GibCursor [3]));
            memcpy(return_74.field4, aft_soa_loc_1826, sizeof(GibCursor [3]));
            return return_74;
            break;
        }
        
      case 1:
        {
            GibCursor soa_field_0_1830 = arg_98_187_272[1];
            GibCursor soa_field_1_1831 = arg_98_187_272[2];
            GibInt tmpval_2413 = *(GibInt *) soa_field_1_1831;
            GibCursor tmpcur_2414 = soa_field_1_1831 + sizeof(GibInt);
            GibCursor cursor_ptr_1811[3] = {tmpcur_2406, soa_field_0_1830,
                                            tmpcur_2414};
            GibCursor loc_663 = arg_98_187_272[0];
            GibCursor jumpf_dloc_1020 = loc_663 + 1;
            GibCursor loc_IntTy_664 = arg_98_187_272[1];
            GibCursor loc_IntTy_665 = arg_98_187_272[2];
            GibCursor jumpf_floc_loc_1022 = soa_field_1_1831 + 8;
            GibCursor jumpf_floc_loc_1021 = loc_IntTy_664 + 0;
            GibCursor loc_899 = jumpf_dloc_1020 + 0;
            GibCursor loc_898 = jumpf_floc_loc_1022 + 0;
            GibCursor loc_897 = jumpf_floc_loc_1021 + 0;
            GibCursor cursor_ptr_1835[3] = {jumpf_dloc_1020,
                                            jumpf_floc_loc_1021,
                                            jumpf_floc_loc_1022};
            GibCursor loc_IntTy_668 = cursor_ptr_1808[2];
            GibCursor new_floc_loc_924 = loc_IntTy_668 + 8;
            GibCursor loc_666 = cursor_ptr_1808[0];
            GibCursor new_dloc_922 = loc_666 + 1;
            GibCursor loc_IntTy_667 = cursor_ptr_1808[1];
            GibCursor cursor_ptr_1836[3] = {new_dloc_922, loc_IntTy_667,
                                            new_floc_loc_924};
            
            *(GibPackedTag *) loc_666 = 1;
            
            GibCursor writetag_1855 = loc_666 + 1;
            GibCursor after_tag_1856 = loc_666 + 1;
            
            *(GibInt *) loc_IntTy_668 = tmpval_2413;
            
            GibCursor writecur_1860 = loc_IntTy_668 + sizeof(GibInt);
            GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod
            tmp_struct_75 =
             _copy_without_ptrs_Tree(cursor_ptr_1807, cursor_ptr_1806, cursor_ptr_1836, cursor_ptr_1811);
            GibCursor pvrtmp_2415[3];
            
            memcpy(pvrtmp_2415, tmp_struct_75.field0, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2416[3];
            
            memcpy(pvrtmp_2416, tmp_struct_75.field1, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2417[3];
            
            memcpy(pvrtmp_2417, tmp_struct_75.field2, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2418[3];
            
            memcpy(pvrtmp_2418, tmp_struct_75.field3, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2419[3];
            
            memcpy(pvrtmp_2419, tmp_struct_75.field4, sizeof(GibCursor [3]));
            
            GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod
            tmp_struct_76 =
             _copy_without_ptrs_Tree(pvrtmp_2415, pvrtmp_2416, pvrtmp_2419, pvrtmp_2417);
            GibCursor pvrtmp_2424[3];
            
            memcpy(pvrtmp_2424, tmp_struct_76.field0, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2425[3];
            
            memcpy(pvrtmp_2425, tmp_struct_76.field1, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2426[3];
            
            memcpy(pvrtmp_2426, tmp_struct_76.field2, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2427[3];
            
            memcpy(pvrtmp_2427, tmp_struct_76.field3, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2428[3];
            
            memcpy(pvrtmp_2428, tmp_struct_76.field4, sizeof(GibCursor [3]));
            
            GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod
            return_77;
            
            memcpy(return_77.field0, pvrtmp_2424, sizeof(GibCursor [3]));
            memcpy(return_77.field1, pvrtmp_2425, sizeof(GibCursor [3]));
            memcpy(return_77.field2, pvrtmp_2426, sizeof(GibCursor [3]));
            memcpy(return_77.field3, cursor_ptr_1808, sizeof(GibCursor [3]));
            memcpy(return_77.field4, pvrtmp_2428, sizeof(GibCursor [3]));
            return return_77;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            GibCursor soa_field_0_1868 = arg_98_187_272[1];
            GibCursor soa_field_1_1869 = arg_98_187_272[2];
            uintptr_t tagged_tmpcur_82 = *(uintptr_t *) tmpcur_2406;
            GibCursor tmpcur_2437 = GIB_UNTAG(tagged_tmpcur_82);
            GibCursor tmpaftercur_2438 = tmpcur_2406 + 8;
            uint16_t tmptag_2439 = GIB_GET_TAG(tagged_tmpcur_82);
            GibCursor end_from_tagged_dcon_redir_1882 = tmpcur_2437 +
                      tmptag_2439;
            GibCursor field_nxt_1879 = soa_field_0_1868 + 1;
            uintptr_t tagged_tmpcur_81 = *(uintptr_t *) field_nxt_1879;
            GibCursor tmpcur_2440 = GIB_UNTAG(tagged_tmpcur_81);
            GibCursor tmpaftercur_2441 = field_nxt_1879 + 8;
            uint16_t tmptag_2442 = GIB_GET_TAG(tagged_tmpcur_81);
            GibCursor end_from_tagged_fld_redir_1883 = tmpcur_2440 +
                      tmptag_2442;
            GibCursor field_nxt_1880 = soa_field_1_1869 + 1;
            uintptr_t tagged_tmpcur_80 = *(uintptr_t *) field_nxt_1880;
            GibCursor tmpcur_2443 = GIB_UNTAG(tagged_tmpcur_80);
            GibCursor tmpaftercur_2444 = field_nxt_1880 + 8;
            uint16_t tmptag_2445 = GIB_GET_TAG(tagged_tmpcur_80);
            GibCursor end_from_tagged_fld_redir_1884 = tmpcur_2443 +
                      tmptag_2445;
            GibCursor indr_1121[3] = {tmpcur_2437, tmpcur_2440, tmpcur_2443};
            GibCursor loc_663 = arg_98_187_272[0];
            GibCursor jump_dloc_1125 = loc_663 + 9;
            GibCursor loc_IntTy_665 = arg_98_187_272[2];
            GibCursor loc_IntTy_664 = arg_98_187_272[1];
            GibCursor aft_indir_loc_1133 = loc_IntTy_664 + 9;
            GibCursor aft_indir_loc_1134 = loc_IntTy_665 + 9;
            GibCursor cursor_ptr_1885[3] = {jump_dloc_1125, aft_indir_loc_1133,
                                            aft_indir_loc_1134};
            GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod
            tmp_struct_78 =
             _copy_without_ptrs_Tree(indr_1121, cursor_ptr_1806, cursor_ptr_1808, indr_1121);
            GibCursor pvrtmp_2446[3];
            
            memcpy(pvrtmp_2446, tmp_struct_78.field0, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2447[3];
            
            memcpy(pvrtmp_2447, tmp_struct_78.field1, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2448[3];
            
            memcpy(pvrtmp_2448, tmp_struct_78.field2, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2449[3];
            
            memcpy(pvrtmp_2449, tmp_struct_78.field3, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2450[3];
            
            memcpy(pvrtmp_2450, tmp_struct_78.field4, sizeof(GibCursor [3]));
            
            GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod
            return_79;
            
            memcpy(return_79.field0, cursor_ptr_1807, sizeof(GibCursor [3]));
            memcpy(return_79.field1, pvrtmp_2447, sizeof(GibCursor [3]));
            memcpy(return_79.field2, cursor_ptr_1885, sizeof(GibCursor [3]));
            memcpy(return_79.field3, pvrtmp_2449, sizeof(GibCursor [3]));
            memcpy(return_79.field4, pvrtmp_2450, sizeof(GibCursor [3]));
            return return_79;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            GibCursor soa_field_0_1896 = arg_98_187_272[1];
            GibCursor soa_field_1_1897 = arg_98_187_272[2];
            uintptr_t tagged_tmpcur_87 = *(uintptr_t *) tmpcur_2406;
            GibCursor tmpcur_2457 = GIB_UNTAG(tagged_tmpcur_87);
            GibCursor tmpaftercur_2458 = tmpcur_2406 + 8;
            uint16_t tmptag_2459 = GIB_GET_TAG(tagged_tmpcur_87);
            GibCursor end_from_tagged_dcon_redir_1905 = tmpcur_2457 +
                      tmptag_2459;
            GibCursor field_nxt_1903 = soa_field_0_1896 + 1;
            uintptr_t tagged_tmpcur_86 = *(uintptr_t *) field_nxt_1903;
            GibCursor tmpcur_2460 = GIB_UNTAG(tagged_tmpcur_86);
            GibCursor tmpaftercur_2461 = field_nxt_1903 + 8;
            uint16_t tmptag_2462 = GIB_GET_TAG(tagged_tmpcur_86);
            GibCursor end_from_tagged_fld_redir_1906 = tmpcur_2460 +
                      tmptag_2462;
            GibCursor field_nxt_1904 = soa_field_1_1897 + 1;
            uintptr_t tagged_tmpcur_85 = *(uintptr_t *) field_nxt_1904;
            GibCursor tmpcur_2463 = GIB_UNTAG(tagged_tmpcur_85);
            GibCursor tmpaftercur_2464 = field_nxt_1904 + 8;
            uint16_t tmptag_2465 = GIB_GET_TAG(tagged_tmpcur_85);
            GibCursor end_from_tagged_fld_redir_1907 = tmpcur_2463 +
                      tmptag_2465;
            GibCursor indr_1121[3] = {tmpcur_2457, tmpcur_2460, tmpcur_2463};
            GibCursor loc_666 = cursor_ptr_1808[0];
            GibCursor loc_IntTy_667 = cursor_ptr_1808[1];
            GibCursor loc_IntTy_668 = cursor_ptr_1808[2];
            GibCursor copy_dloc_1135 = loc_666 + 0;
            GibCursor copy_floc_loc_1137 = loc_IntTy_668 + 0;
            GibCursor copy_floc_loc_1136 = loc_IntTy_667 + 0;
            GibCursor cursor_ptr_1908[3] = {copy_dloc_1135, copy_floc_loc_1136,
                                            copy_floc_loc_1137};
            GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod
            tmp_struct_83 =
             _copy_without_ptrs_Tree(indr_1121, cursor_ptr_1806, cursor_ptr_1908, indr_1121);
            GibCursor pvrtmp_2466[3];
            
            memcpy(pvrtmp_2466, tmp_struct_83.field0, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2467[3];
            
            memcpy(pvrtmp_2467, tmp_struct_83.field1, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2468[3];
            
            memcpy(pvrtmp_2468, tmp_struct_83.field2, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2469[3];
            
            memcpy(pvrtmp_2469, tmp_struct_83.field3, sizeof(GibCursor [3]));
            
            GibCursor pvrtmp_2470[3];
            
            memcpy(pvrtmp_2470, tmp_struct_83.field4, sizeof(GibCursor [3]));
            
            GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod
            return_84;
            
            memcpy(return_84.field0, pvrtmp_2466, sizeof(GibCursor [3]));
            memcpy(return_84.field1, pvrtmp_2467, sizeof(GibCursor [3]));
            memcpy(return_84.field2, pvrtmp_2468, sizeof(GibCursor [3]));
            memcpy(return_84.field3, pvrtmp_2469, sizeof(GibCursor [3]));
            memcpy(return_84.field4, pvrtmp_2470, sizeof(GibCursor [3]));
            return return_84;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2405");
            exit(1);
        }
    }
}
int main(int argc, char **argv)
{
    int init_101 = gib_init(argc, argv);
    
    info_table_initialize();
    symbol_table_initialize();
    
    GibChunk region_2097 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_705 = region_2097.start;
    GibCursor end_r_705 = region_2097.end;
    GibChunk region_2098 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_706 = region_2098.start;
    GibCursor end_r_706 = region_2098.end;
    GibChunk region_2099 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_707 = region_2099.start;
    GibCursor end_r_707 = region_2099.end;
    GibCursor reg_ptr_1918[3] = {r_705, r_706, r_707};
    GibCursor reg_cursor_ptr_1919[3] = {end_r_705, end_r_706, end_r_707};
    GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod tmp_struct_88 =
                                                 mkTree(reg_cursor_ptr_1919, reg_ptr_1918, 23, 0);
    GibCursor pvrtmp_2100[3];
    
    memcpy(pvrtmp_2100, tmp_struct_88.field0, sizeof(GibCursor [3]));

    GibCursor pvrtmp_2101[3];

    memcpy(pvrtmp_2101, tmp_struct_88.field1, sizeof(GibCursor [3]));
    
    GibCursor pvrtmp_2102[3];
    
    memcpy(pvrtmp_2102, tmp_struct_88.field2, sizeof(GibCursor [3]));
    
    GibChunk region_2107 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_702 = region_2107.start;
    GibCursor end_r_702 = region_2107.end;
    GibChunk region_2108 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_703 = region_2108.start;
    GibCursor end_r_703 = region_2108.end;
    GibChunk region_2109 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_704 = region_2109.start;
    GibCursor end_r_704 = region_2109.end;
    GibCursor reg_ptr_1925[3] = {r_702, r_703, r_704};
    GibCursor reg_cursor_ptr_1926[3] = {end_r_702, end_r_703, end_r_704};
    GibCursor pvrtmp_2121[3];
    GibCursor pvrtmp_2122[3];
    GibCursor pvrtmp_2123[3];
    GibVector *times_93 = gib_vector_alloc(gib_get_iters_param(),
                                           sizeof(double));
    struct timespec begin_pvrtmp_2121;
    struct timespec end_pvrtmp_2121;
    
    for (long long iters_pvrtmp_2121 = 0; iters_pvrtmp_2121 <
         gib_get_iters_param(); iters_pvrtmp_2121++) {
        if (iters_pvrtmp_2121 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_save_state();
            gib_ptr_bumpalloc_save_state();
        }
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_2121);
        
        GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3GibCursorPtr3Prod
        tmp_struct_89;

        add1Tree(pvrtmp_2100, reg_cursor_ptr_1926, reg_ptr_1925, pvrtmp_2101, &tmp_struct_89);

        GibCursor pvrtmp_2110[3];
        
        memcpy(pvrtmp_2110, tmp_struct_89.field0, sizeof(GibCursor [3]));
        
        GibCursor pvrtmp_2111[3];
        
        memcpy(pvrtmp_2111, tmp_struct_89.field1, sizeof(GibCursor [3]));
        
        GibCursor pvrtmp_2112[3];
        
        memcpy(pvrtmp_2112, tmp_struct_89.field2, sizeof(GibCursor [3]));
        
        GibCursor pvrtmp_2113[3];
        
        memcpy(pvrtmp_2113, tmp_struct_89.field3, sizeof(GibCursor [3]));
        
        GibCursor pvrtmp_2114[3];
        
        memcpy(pvrtmp_2114, tmp_struct_89.field4, sizeof(GibCursor [3]));
        memcpy(pvrtmp_2121, pvrtmp_2111, sizeof(GibCursor [3]));
        memcpy(pvrtmp_2122, pvrtmp_2113, sizeof(GibCursor [3]));
        memcpy(pvrtmp_2123, pvrtmp_2114, sizeof(GibCursor [3]));
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_2121);
        if (iters_pvrtmp_2121 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_restore_state();
            gib_ptr_bumpalloc_restore_state();
        }


        memcpy(pvrtmp_2100, tmp_struct_88.field0, sizeof(GibCursor [3]));

        memcpy(pvrtmp_2101, tmp_struct_88.field1, sizeof(GibCursor [3]));


        reg_cursor_ptr_1926[0] = end_r_702;
        reg_cursor_ptr_1926[1] = end_r_703;
        reg_cursor_ptr_1926[2] = end_r_704;

        reg_ptr_1925[0] = r_702;
        reg_ptr_1925[1] = r_703;
        reg_ptr_1925[2] = r_704;


        double itertime_90 = gib_difftimespecs(&begin_pvrtmp_2121,
                                               &end_pvrtmp_2121);
        
        printf("itertime: %lf\n", itertime_90);
        gib_vector_inplace_update(times_93, iters_pvrtmp_2121, &itertime_90);
    }
    gib_vector_inplace_sort(times_93, gib_compare_doubles);
    
    double *tmp_94 = (double *) gib_vector_nth(times_93, gib_get_iters_param() /
                                               2);
    double selftimed_92 = *tmp_94;
    double batchtime_91 = gib_sum_timing_array(times_93);
    
    gib_print_timing_array(times_93);
    gib_vector_free(times_93);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_91);
    printf("SELFTIMED: %e\n", selftimed_92);
    
    GibInt timed_1992;
    GibVector *times_99 = gib_vector_alloc(gib_get_iters_param(),
                                           sizeof(double));
    struct timespec begin_timed_1992;
    struct timespec end_timed_1992;
    
    for (long long iters_timed_1992 = 0; iters_timed_1992 <
         gib_get_iters_param(); iters_timed_1992++) {
        if (iters_timed_1992 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_save_state();
            gib_ptr_bumpalloc_save_state();
        }
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed_1992);
        
        GibCursorPtr3GibCursorPtr3GibIntProd tmp_struct_95 =
                                              sumTree(reg_cursor_ptr_1926, pvrtmp_2122);
        GibCursor pvrtmp_2131[3];
        
        memcpy(pvrtmp_2131, tmp_struct_95.field0, sizeof(GibCursor [3]));
        
        GibCursor pvrtmp_2132[3];
        
        memcpy(pvrtmp_2132, tmp_struct_95.field1, sizeof(GibCursor [3]));
        
        GibInt pvrtmp_2133 = tmp_struct_95.field2;
        
        timed_1992 = pvrtmp_2133;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed_1992);
        if (iters_timed_1992 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_restore_state();
            gib_ptr_bumpalloc_restore_state();
        }
        
        double itertime_96 = gib_difftimespecs(&begin_timed_1992,
                                               &end_timed_1992);
        
        printf("itertime: %lf\n", itertime_96);
        gib_vector_inplace_update(times_99, iters_timed_1992, &itertime_96);
    }
    gib_vector_inplace_sort(times_99, gib_compare_doubles);
    
    double *tmp_100 = (double *) gib_vector_nth(times_99,
                                                gib_get_iters_param() / 2);
    double selftimed_98 = *tmp_100;
    double batchtime_97 = gib_sum_timing_array(times_99);
    
    gib_print_timing_array(times_99);
    gib_vector_free(times_99);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_97);
    printf("SELFTIMED: %e\n", selftimed_98);
    printf("%ld", timed_1992);
    printf("\n");
    
    int exit_102 = gib_exit();
    
    return exit_102;
}


// gcc -std=gnu11  -O3  -flto  -D_GIBBON_GENGC=0  -D_GIBBON_SIMPLE_WRITE_BARRIER=0  -D_GIBBON_EAGER_PROMOTION=1  -o /home/vidushs/Applications/src/gibbon/microbench/manual_soa_examples/MonoTree.soa.exe -I/home/vidushs/Applications/src/gibbon/gibbon-rts/build -L/home/vidushs/Applications/src/gibbon/gibbon-rts/build -Wl,-rpath=/home/vidushs/Applications/src/gibbon/gibbon-rts/build /home/vidushs/Applications/src/gibbon/microbench/manual_soa_examples/MonoTree.soa.c /home/vidushs/Applications/src/gibbon/gibbon-rts/build/gibbon_rts.o -lm  -lgibbon_rts_ng

// gcc -std=gnu11  -g  -flto  -D_GIBBON_GENGC=0  -D_GIBBON_SIMPLE_WRITE_BARRIER=0  -D_GIBBON_EAGER_PROMOTION=1  -o /home/vidushs/Applications/src/gibbon/microbench/manual_soa_examples/MonoTree.soa.exe -I/home/vidushs/Applications/src/gibbon/gibbon-rts/build -L/home/vidushs/Applications/src/gibbon/gibbon-rts/build -Wl,-rpath=/home/vidushs/Applications/src/gibbon/gibbon-rts/build /home/vidushs/Applications/src/gibbon/microbench/manual_soa_examples/MonoTree.soa.c /home/vidushs/Applications/src/gibbon/gibbon-rts/build/gibbon_rts.o -lm  -lgibbon_rts_ng

