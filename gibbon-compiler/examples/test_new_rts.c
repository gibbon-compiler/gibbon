/* Gibbon program. */

#include "gibbon.h"

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
            GibBoxedTag field0;
            GibCursor field1;
        } GibPackedTagGibCursorProd;
typedef struct GibCursorProd_struct {
            GibCursor field0;
        } GibCursorProd;
typedef struct GibCursorGibIntProd_struct {
            GibCursor field0;
            GibInt field1;
        } GibCursorGibIntProd;
typedef struct GibCursorGibCursorProd_struct {
            GibCursor field0;
            GibCursor field1;
        } GibCursorGibCursorProd;
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
GibCursorGibCursorGibCursorGibCursorProd add1(GibCursor end_r_595, // input region
                                              GibCursor end_r_596, // output region
                                              GibCursor loc_594, // output location
                                              GibCursor tr_25_159_253 // input location
                                             );
GibCursorGibIntProd sumtree(GibCursor end_r_598, GibCursor tr_29_163_260);
GibCursorGibCursorGibCursorProd buildtree(GibCursor end_r_600,
                                          GibCursor loc_599,
                                          GibInt n_35_169_266);
GibCursorGibCursorGibCursorGibCursorProd reverse(GibCursor end_r_604, // input region (xs)
                                                 GibCursor end_r_605, // input region (ys)
                                                 GibCursor end_r_606, // output region
                                                 GibCursor loc_603, // output location
                                                 GibCursor xs_36_170_272, // input location
                                                 GibCursor ys_37_171_273 // output location
                                                );
GibInt do_reverse();
GibInt do_tree();
GibCursorGibIntProd sum_list(GibCursor end_r_608, GibCursor xs_40_178_285);
GibCursorGibCursorGibCursorGibCursorProd _copy_Tree(GibCursor end_r_611, // input region
                                                    GibCursor end_r_612, // output region
                                                    GibCursor loc_610, // output location
                                                    GibCursor arg_103_181_289 // input location
                                                   );
GibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_Tree(GibCursor end_r_615, GibCursor end_r_616,
                        GibCursor loc_614, GibCursor arg_110_188_296);
GibCursorProd _traverse_Tree(GibCursor end_r_618, GibCursor arg_117_195_303);
GibCursorProd _print_Tree(GibCursor end_r_620, GibCursor arg_124_201_309);
GibCursorGibCursorGibCursorGibCursorProd _copy_List(GibCursor end_r_623,
                                                    GibCursor end_r_624,
                                                    GibCursor loc_622,
                                                    GibCursor arg_135_212_320);
GibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_List(GibCursor end_r_627, GibCursor end_r_628,
                        GibCursor loc_626, GibCursor arg_140_217_325);
GibCursorProd _traverse_List(GibCursor end_r_630, GibCursor arg_145_222_330);
GibCursorProd _print_List(GibCursor end_r_632, GibCursor arg_150_226_334);
GibCursorGibCursorGibCursorGibCursorProd
_add_size_and_rel_offsets_Tree(GibCursor end_r_635, GibCursor end_r_636,
                               GibCursor loc_634, GibCursor arg_578);
GibCursorGibCursorGibCursorGibCursorProd
_add_size_and_rel_offsets_List(GibCursor end_r_639, GibCursor end_r_640,
                               GibCursor loc_638, GibCursor arg_585);
typedef enum {
            GibInt_T,
            GibFloat_T,
            GibSym_T,
            GibBool_T,
            GibCursor_T,
            GibPackedTag_T,
            GibBoxedTag_T,
            GibPtr_T,
            GibSymDict_T,
            GibVector_T,
            GibList_T,
            GibSymSet_T,
            GibSymHash_T,
            GibIntHash_T,
            List_T,
            Tree_T,
        } GibDatatype;
void init_info_table(void)
{
    int error = gib_init_info_table();

    if (error < 0) {
        fprintf(stderr, "Couldn't initialize info table, errorno=%d", error);
        exit(1);
    }

    GibDatatype field_tys[2];

    field_tys[0] = GibInt_T;
    field_tys[1] = List_T;
    error = gib_insert_dcon_into_info_table(List_T, 1, 1, 1, field_tys, 2);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, List_T, 1);
        exit(1);
    }
    error = gib_insert_dcon_into_info_table(List_T, 0, 0, 0, field_tys, 0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, List_T, 0);
        exit(1);
    }
    field_tys[0] = GibInt_T;
    error = gib_insert_dcon_into_info_table(Tree_T, 0, 1, 0, field_tys, 1);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, Tree_T, 0);
        exit(1);
    }
    field_tys[0] = Tree_T;
    field_tys[1] = Tree_T;
    error = gib_insert_dcon_into_info_table(Tree_T, 1, 0, 2, field_tys, 2);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, Tree_T, 1);
        exit(1);
    }
}
void init_symbol_table(void)
{
    gib_add_symbol(1263, ")");
    gib_add_symbol(1264, "(Node ");
    gib_add_symbol(1265, "(Nil ");
    gib_add_symbol(1266, "(Leaf ");
    gib_add_symbol(1267, "(Cons ");
}
GibCursorGibCursorGibCursorGibCursorProd add1(GibCursor end_r_595, // input region
                                              GibCursor end_r_596, // output region
                                              GibCursor loc_594, // output location
                                              GibCursor tr_25_159_253 // input location
                                             )
{
    GibCursor loc_593 = (GibCursor) tr_25_159_253;

    if (loc_594 + 32 > end_r_596) {
        GibChunk new_chunk_2 = gib_alloc_chunk(end_r_596);
        GibCursor chunk_start_3 = new_chunk_2.chunk_start;
        GibCursor chunk_end_4 = new_chunk_2.chunk_end;

        end_r_596 = chunk_end_4;
        *(GibBoxedTag *) loc_594 = 255;

        GibCursor redir = loc_594 + 1;

        *(GibCursor *) redir = chunk_start_3;
        loc_594 = chunk_start_3;
    }

    GibBoxedTag tmpval_1270 = *(GibBoxedTag *) tr_25_159_253;
    GibCursor tmpcur_1271 = tr_25_159_253 + 1;


  switch_1298:
    ;
    switch (tmpval_1270) {

      case 0:
        {
            GibCursor field_cur_958 = (GibCursor) tmpcur_1271;
            GibCursor case_643 = (GibCursor) field_cur_958;
            GibInt tmpval_1272 = *(GibInt *) case_643;
            GibCursor tmpcur_1273 = case_643 + sizeof(GibInt);
            GibInt n_26_160_254 = (GibInt) tmpval_1272;
            GibCursor end_n_26_160_254 = (GibCursor) tmpcur_1273;
            GibCursor jump_864 = case_643 + 8;
            GibInt fltPkd_237_255 = n_26_160_254 + 1;

            *(GibBoxedTag *) loc_594 = 0;

            GibCursor writetag_960 = loc_594 + 1;

            *(GibInt *) writetag_960 = fltPkd_237_255;

            GibCursor writecur_961 = writetag_960 + sizeof(GibInt);
            GibCursor pvrtmp_1275 = (GibCursor) writecur_961;
            GibCursor pvrtmp_1274 = (GibCursor) loc_594;
            GibCursor taildc_865 = (GibCursor) pvrtmp_1274;
            GibCursor end_taildc_865 = (GibCursor) pvrtmp_1275;
            GibCursor pvrtmp_1277 = (GibCursor) end_taildc_865;
            GibCursor pvrtmp_1276 = (GibCursor) taildc_865;
            GibCursor fltPrd_1159 = (GibCursor) pvrtmp_1276;
            GibCursor fltPrd_1160 = (GibCursor) pvrtmp_1277;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_596,
                                                               jump_864,
                                                               fltPrd_1159,
                                                               fltPrd_1160};
            break;
        }

      case 1:
        {
            GibCursor field_cur_963 = (GibCursor) tmpcur_1271;
            GibCursor case_647 = (GibCursor) field_cur_963;
            GibCursor x_27_161_256 = (GibCursor) case_647;
            GibCursor loc_655 = loc_594 + 1;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_0 =
                                                      add1(end_r_595, end_r_596, loc_655, x_27_161_256);
            GibCursor pvrtmp_1278 = tmp_struct_0.field0;
            GibCursor pvrtmp_1279 = tmp_struct_0.field1;
            GibCursor pvrtmp_1280 = tmp_struct_0.field2;
            GibCursor pvrtmp_1281 = tmp_struct_0.field3;
            GibCursor fltPrd_1161 = (GibCursor) pvrtmp_1280;
            GibCursor fltPrd_1162 = (GibCursor) pvrtmp_1281;
            GibCursor pvrtmp_1283 = (GibCursor) fltPrd_1162;
            GibCursor pvrtmp_1282 = (GibCursor) fltPrd_1161;
            GibCursor fltPkd_238_258 = (GibCursor) pvrtmp_1282;
            GibCursor fltPrd_1163 = (GibCursor) pvrtmp_1280;
            GibCursor fltPrd_1164 = (GibCursor) pvrtmp_1281;
            GibCursor pvrtmp_1285 = (GibCursor) fltPrd_1164;
            GibCursor pvrtmp_1284 = (GibCursor) fltPrd_1163;
            GibCursor end_fltPkd_238_258 = (GibCursor) pvrtmp_1285;
            GibCursor end_r_596__941 = (GibCursor) pvrtmp_1278;
            GibCursor endof_866 = (GibCursor) pvrtmp_1279;
            GibCursor case_648 = (GibCursor) endof_866;
            GibCursor y_28_162_257 = (GibCursor) case_648;
            GibCursor loc_656 = (GibCursor) end_fltPkd_238_258;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_1 =
                                                      add1(end_r_595, end_r_596__941, loc_656, y_28_162_257);
            GibCursor pvrtmp_1286 = tmp_struct_1.field0;
            GibCursor pvrtmp_1287 = tmp_struct_1.field1;
            GibCursor pvrtmp_1288 = tmp_struct_1.field2;
            GibCursor pvrtmp_1289 = tmp_struct_1.field3;
            GibCursor fltPrd_1165 = (GibCursor) pvrtmp_1288;
            GibCursor fltPrd_1166 = (GibCursor) pvrtmp_1289;
            GibCursor pvrtmp_1291 = (GibCursor) fltPrd_1166;
            GibCursor pvrtmp_1290 = (GibCursor) fltPrd_1165;
            GibCursor fltPkd_239_259 = (GibCursor) pvrtmp_1290;
            GibCursor fltPrd_1167 = (GibCursor) pvrtmp_1288;
            GibCursor fltPrd_1168 = (GibCursor) pvrtmp_1289;
            GibCursor pvrtmp_1293 = (GibCursor) fltPrd_1168;
            GibCursor pvrtmp_1292 = (GibCursor) fltPrd_1167;
            GibCursor end_fltPkd_239_259 = (GibCursor) pvrtmp_1293;
            GibCursor end_r_596__941__942 = (GibCursor) pvrtmp_1286;
            GibCursor endof_867 = (GibCursor) pvrtmp_1287;

            *(GibBoxedTag *) loc_594 = 1;

            GibCursor writetag_966 = loc_594 + 1;
            GibCursor writecur_967 = (GibCursor) end_fltPkd_238_258;
            GibCursor writecur_968 = (GibCursor) end_fltPkd_239_259;
            GibCursor pvrtmp_1295 = (GibCursor) writecur_968;
            GibCursor pvrtmp_1294 = (GibCursor) loc_594;
            GibCursor taildc_868 = (GibCursor) pvrtmp_1294;
            GibCursor end_taildc_868 = (GibCursor) pvrtmp_1295;
            GibCursor pvrtmp_1297 = (GibCursor) end_taildc_868;
            GibCursor pvrtmp_1296 = (GibCursor) taildc_868;
            GibCursor fltPrd_1169 = (GibCursor) pvrtmp_1296;
            GibCursor fltPrd_1170 = (GibCursor) pvrtmp_1297;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_596__941__942,
                                                               endof_867,
                                                               fltPrd_1169,
                                                               fltPrd_1170};
            break;
        }

      case 255:
        {
            GibCursor tmpcur_1585 = *(GibCursor *) tmpcur_1271;
            GibCursor tmpaftercur_1586 = tmpcur_1271 + 8;
            GibBoxedTag tagtmp_1587 = *(GibBoxedTag *) tmpcur_1585;
            GibCursor tailtmp_1588 = tmpcur_1585 + 1;

            tmpval_1270 = tagtmp_1587;
            tmpcur_1271 = tailtmp_1588;
            goto switch_1298;
            break;
        }

      case 254:
        {
            GibCursor tmpcur_1585 = *(GibCursor *) tmpcur_1271;
            GibCursor tmpaftercur_1586 = tmpcur_1271 + 8;
            GibBoxedTag tagtmp_1587 = *(GibBoxedTag *) tmpcur_1585;
            GibCursor tailtmp_1588 = tmpcur_1585 + 1;

            tmpval_1270 = tagtmp_1587;
            tmpcur_1271 = tailtmp_1588;
            goto switch_1298;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1270");
            exit(1);
        }
    }
}
GibCursorGibIntProd sumtree(GibCursor end_r_598, GibCursor tr_29_163_260)
{
    GibCursor loc_597 = (GibCursor) tr_29_163_260;
    GibBoxedTag tmpval_1299 = *(GibBoxedTag *) tr_29_163_260;
    GibCursor tmpcur_1300 = tr_29_163_260 + 1;


  switch_1307:
    ;
    switch (tmpval_1299) {

      case 0:
        {
            GibCursor field_cur_970 = (GibCursor) tmpcur_1300;
            GibCursor case_661 = (GibCursor) field_cur_970;
            GibInt tmpval_1301 = *(GibInt *) case_661;
            GibCursor tmpcur_1302 = case_661 + sizeof(GibInt);
            GibInt n_30_164_261 = (GibInt) tmpval_1301;
            GibCursor end_n_30_164_261 = (GibCursor) tmpcur_1302;
            GibCursor jump_869 = case_661 + 8;

            return (GibCursorGibIntProd) {jump_869, n_30_164_261};
            break;
        }

      case 1:
        {
            GibCursor field_cur_972 = (GibCursor) tmpcur_1300;
            GibCursor case_662 = (GibCursor) field_cur_972;
            GibCursor x_31_165_262 = (GibCursor) case_662;
            GibCursorGibIntProd tmp_struct_5 =
                                 sumtree(end_r_598, x_31_165_262);
            GibCursor pvrtmp_1303 = tmp_struct_5.field0;
            GibInt pvrtmp_1304 = tmp_struct_5.field1;
            GibCursor endof_870 = (GibCursor) pvrtmp_1303;
            GibInt sumx_33_167_264 = (GibInt) pvrtmp_1304;
            GibCursor case_663 = (GibCursor) endof_870;
            GibCursor y_32_166_263 = (GibCursor) case_663;
            GibCursorGibIntProd tmp_struct_6 =
                                 sumtree(end_r_598, y_32_166_263);
            GibCursor pvrtmp_1305 = tmp_struct_6.field0;
            GibInt pvrtmp_1306 = tmp_struct_6.field1;
            GibCursor endof_871 = (GibCursor) pvrtmp_1305;
            GibInt sumy_34_168_265 = (GibInt) pvrtmp_1306;
            GibInt tailprim_872 = sumx_33_167_264 + sumy_34_168_265;

            return (GibCursorGibIntProd) {endof_871, tailprim_872};
            break;
        }

      case 255:
        {
            GibCursor tmpcur_1589 = *(GibCursor *) tmpcur_1300;
            GibCursor tmpaftercur_1590 = tmpcur_1300 + 8;
            GibBoxedTag tagtmp_1591 = *(GibBoxedTag *) tmpcur_1589;
            GibCursor tailtmp_1592 = tmpcur_1589 + 1;

            tmpval_1299 = tagtmp_1591;
            tmpcur_1300 = tailtmp_1592;
            goto switch_1307;
            break;
        }

      case 254:
        {
            GibCursor tmpcur_1589 = *(GibCursor *) tmpcur_1300;
            GibCursor tmpaftercur_1590 = tmpcur_1300 + 8;
            GibBoxedTag tagtmp_1591 = *(GibBoxedTag *) tmpcur_1589;
            GibCursor tailtmp_1592 = tmpcur_1589 + 1;

            tmpval_1299 = tagtmp_1591;
            tmpcur_1300 = tailtmp_1592;
            goto switch_1307;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1299");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorProd buildtree(GibCursor end_r_600,
                                          GibCursor loc_599,
                                          GibInt n_35_169_266)
{
    if (loc_599 + 32 > end_r_600) {
        GibChunk new_chunk_9 = gib_alloc_chunk(end_r_600);
        GibCursor chunk_start_10 = new_chunk_9.chunk_start;
        GibCursor chunk_end_11 = new_chunk_9.chunk_end;

        end_r_600 = chunk_end_11;
        *(GibBoxedTag *) loc_599 = 255;

        GibCursor redir = loc_599 + 1;

        *(GibCursor *) redir = chunk_start_10;
        loc_599 = chunk_start_10;
    }

    GibBool fltIf_240_267 = n_35_169_266 == 0;

    if (fltIf_240_267) {
        *(GibBoxedTag *) loc_599 = 0;

        GibCursor writetag_975 = loc_599 + 1;

        *(GibInt *) writetag_975 = 1;

        GibCursor writecur_976 = writetag_975 + sizeof(GibInt);
        GibCursor pvrtmp_1309 = (GibCursor) writecur_976;
        GibCursor pvrtmp_1308 = (GibCursor) loc_599;
        GibCursor taildc_873 = (GibCursor) pvrtmp_1308;
        GibCursor end_taildc_873 = (GibCursor) pvrtmp_1309;
        GibCursor pvrtmp_1311 = (GibCursor) end_taildc_873;
        GibCursor pvrtmp_1310 = (GibCursor) taildc_873;
        GibCursor fltPrd_1171 = (GibCursor) pvrtmp_1310;
        GibCursor fltPrd_1172 = (GibCursor) pvrtmp_1311;

        return (GibCursorGibCursorGibCursorProd) {end_r_600, fltPrd_1171,
                                                  fltPrd_1172};
    } else {
        GibInt fltAppE_242_268 = n_35_169_266 - 1;
        GibCursor loc_671 = loc_599 + 1;
        GibCursorGibCursorGibCursorProd tmp_struct_7 =
                                         buildtree(end_r_600, loc_671, fltAppE_242_268);
        GibCursor pvrtmp_1312 = tmp_struct_7.field0;
        GibCursor pvrtmp_1313 = tmp_struct_7.field1;
        GibCursor pvrtmp_1314 = tmp_struct_7.field2;
        GibCursor fltPrd_1173 = (GibCursor) pvrtmp_1313;
        GibCursor fltPrd_1174 = (GibCursor) pvrtmp_1314;
        GibCursor pvrtmp_1316 = (GibCursor) fltPrd_1174;
        GibCursor pvrtmp_1315 = (GibCursor) fltPrd_1173;
        GibCursor fltPkd_241_269 = (GibCursor) pvrtmp_1315;
        GibCursor fltPrd_1175 = (GibCursor) pvrtmp_1313;
        GibCursor fltPrd_1176 = (GibCursor) pvrtmp_1314;
        GibCursor pvrtmp_1318 = (GibCursor) fltPrd_1176;
        GibCursor pvrtmp_1317 = (GibCursor) fltPrd_1175;
        GibCursor end_fltPkd_241_269 = (GibCursor) pvrtmp_1318;
        GibCursor end_r_600__943 = (GibCursor) pvrtmp_1312;
        GibCursor loc_672 = (GibCursor) end_fltPkd_241_269;
        GibInt fltAppE_244_270 = n_35_169_266 - 1;
        GibCursorGibCursorGibCursorProd tmp_struct_8 =
                                         buildtree(end_r_600__943, loc_672, fltAppE_244_270);
        GibCursor pvrtmp_1319 = tmp_struct_8.field0;
        GibCursor pvrtmp_1320 = tmp_struct_8.field1;
        GibCursor pvrtmp_1321 = tmp_struct_8.field2;
        GibCursor fltPrd_1177 = (GibCursor) pvrtmp_1320;
        GibCursor fltPrd_1178 = (GibCursor) pvrtmp_1321;
        GibCursor pvrtmp_1323 = (GibCursor) fltPrd_1178;
        GibCursor pvrtmp_1322 = (GibCursor) fltPrd_1177;
        GibCursor fltPkd_243_271 = (GibCursor) pvrtmp_1322;
        GibCursor fltPrd_1179 = (GibCursor) pvrtmp_1320;
        GibCursor fltPrd_1180 = (GibCursor) pvrtmp_1321;
        GibCursor pvrtmp_1325 = (GibCursor) fltPrd_1180;
        GibCursor pvrtmp_1324 = (GibCursor) fltPrd_1179;
        GibCursor end_fltPkd_243_271 = (GibCursor) pvrtmp_1325;
        GibCursor end_r_600__943__944 = (GibCursor) pvrtmp_1319;

        *(GibBoxedTag *) loc_599 = 1;

        GibCursor writetag_980 = loc_599 + 1;
        GibCursor writecur_981 = (GibCursor) end_fltPkd_241_269;
        GibCursor writecur_982 = (GibCursor) end_fltPkd_243_271;
        GibCursor pvrtmp_1327 = (GibCursor) writecur_982;
        GibCursor pvrtmp_1326 = (GibCursor) loc_599;
        GibCursor taildc_874 = (GibCursor) pvrtmp_1326;
        GibCursor end_taildc_874 = (GibCursor) pvrtmp_1327;
        GibCursor pvrtmp_1329 = (GibCursor) end_taildc_874;
        GibCursor pvrtmp_1328 = (GibCursor) taildc_874;
        GibCursor fltPrd_1181 = (GibCursor) pvrtmp_1328;
        GibCursor fltPrd_1182 = (GibCursor) pvrtmp_1329;

        return (GibCursorGibCursorGibCursorProd) {end_r_600__943__944,
                                                  fltPrd_1181, fltPrd_1182};
    }
}
GibCursorGibCursorGibCursorGibCursorProd reverse(GibCursor end_r_604, // input region (xs)
                                                 GibCursor end_r_605, // input region (ys)
                                                 GibCursor end_r_606, // output region
                                                 GibCursor loc_603, // output location
                                                 GibCursor xs_36_170_272, // input location
                                                 GibCursor ys_37_171_273 // output location
                                                )
{
    GibRegionMeta *region_1330 =
                  gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_692 = region_1330->reg_heap;
    GibInt sizeof_end_r_692_1331 = gib_get_inf_init_chunk_size();
    GibCursor end_r_692 = r_692 + sizeof_end_r_692_1331;
    GibCursor loc_601 = (GibCursor) xs_36_170_272;
    GibCursor loc_602 = (GibCursor) ys_37_171_273;

    if (loc_603 + 32 > end_r_606) {
        GibChunk new_chunk_13 = gib_alloc_chunk(end_r_606);
        GibCursor chunk_start_14 = new_chunk_13.chunk_start;
        GibCursor chunk_end_15 = new_chunk_13.chunk_end;

        end_r_606 = chunk_end_15;
        *(GibBoxedTag *) loc_603 = 255;

        GibCursor redir = loc_603 + 1;

        *(GibCursor *) redir = chunk_start_14;
        loc_603 = chunk_start_14;
    }

    GibCursor loc_690 = (GibCursor) r_692;
    GibCursor loc_680 = loc_690 + 1;
    GibCursor loc_681 = loc_680 + 8;
    GibBoxedTag tmpval_1332 = *(GibBoxedTag *) xs_36_170_272;
    GibCursor tmpcur_1333 = xs_36_170_272 + 1;


  switch_1354:
    ;
    switch (tmpval_1332) {

      case 0:
        {
            GibCursor field_cur_984 = (GibCursor) tmpcur_1333;
            GibCursor jump_875 = loc_601 + 1;

            gib_bump_refcount(end_r_606, end_r_605);
            *(GibBoxedTag *) loc_603 = 254;

            GibCursor writetag_985 = loc_603 + 1;

            *(GibCursor *) writetag_985 = loc_602;

            GibCursor writecur_986 = writetag_985 + 8;
            GibCursor pvrtmp_1335 = (GibCursor) writecur_986;
            GibCursor pvrtmp_1334 = (GibCursor) loc_603;
            GibCursor indirection_863 = (GibCursor) pvrtmp_1334;
            GibCursor end_indirection_863 = (GibCursor) pvrtmp_1335;
            GibCursor pvrtmp_1337 = (GibCursor) end_indirection_863;
            GibCursor pvrtmp_1336 = (GibCursor) indirection_863;
            GibCursor fltPrd_1183 = (GibCursor) pvrtmp_1336;
            GibCursor fltPrd_1184 = (GibCursor) pvrtmp_1337;

            gib_free_region(end_r_692);
            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_606,
                                                               jump_875,
                                                               fltPrd_1183,
                                                               fltPrd_1184};
            break;
        }

      case 1:
        {
            GibCursor field_cur_988 = (GibCursor) tmpcur_1333;
            GibCursor case_677 = (GibCursor) field_cur_988;
            GibInt tmpval_1338 = *(GibInt *) case_677;
            GibCursor tmpcur_1339 = case_677 + sizeof(GibInt);
            GibInt z_38_172_274 = (GibInt) tmpval_1338;
            GibCursor end_z_38_172_274 = (GibCursor) tmpcur_1339;
            GibCursor case_678 = (GibCursor) end_z_38_172_274;
            GibCursor zs_39_173_275 = (GibCursor) case_678;
            GibCursor jump_876 = case_677 + 8;

            gib_bump_refcount(end_r_692, end_r_605);
            *(GibBoxedTag *) loc_681 = 254;

            GibCursor writetag_990 = loc_681 + 1;

            *(GibCursor *) writetag_990 = loc_602;

            GibCursor writecur_991 = writetag_990 + 8;
            GibCursor pvrtmp_1341 = (GibCursor) writecur_991;
            GibCursor pvrtmp_1340 = (GibCursor) loc_681;
            GibCursor cpy_684 = (GibCursor) pvrtmp_1340;
            GibCursor end_cpy_684 = (GibCursor) pvrtmp_1341;

            *(GibBoxedTag *) loc_690 = 1;

            GibCursor writetag_993 = loc_690 + 1;

            *(GibInt *) writetag_993 = z_38_172_274;

            GibCursor writecur_994 = writetag_993 + sizeof(GibInt);
            GibCursor writecur_995 = (GibCursor) end_cpy_684;
            GibCursor pvrtmp_1343 = (GibCursor) writecur_995;
            GibCursor pvrtmp_1342 = (GibCursor) loc_690;
            GibCursor fltAppE_245_276 = (GibCursor) pvrtmp_1342;
            GibCursor end_fltAppE_245_276 = (GibCursor) pvrtmp_1343;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_12 =
                                                      reverse(end_r_604, end_r_692, end_r_606, loc_603, zs_39_173_275, fltAppE_245_276);
            GibCursor pvrtmp_1344 = tmp_struct_12.field0;
            GibCursor pvrtmp_1345 = tmp_struct_12.field1;
            GibCursor pvrtmp_1346 = tmp_struct_12.field2;
            GibCursor pvrtmp_1347 = tmp_struct_12.field3;
            GibCursor fltPrd_1185 = (GibCursor) pvrtmp_1346;
            GibCursor fltPrd_1186 = (GibCursor) pvrtmp_1347;
            GibCursor pvrtmp_1349 = (GibCursor) fltPrd_1186;
            GibCursor pvrtmp_1348 = (GibCursor) fltPrd_1185;
            GibCursor tailapp_877 = (GibCursor) pvrtmp_1348;
            GibCursor fltPrd_1187 = (GibCursor) pvrtmp_1346;
            GibCursor fltPrd_1188 = (GibCursor) pvrtmp_1347;
            GibCursor pvrtmp_1351 = (GibCursor) fltPrd_1188;
            GibCursor pvrtmp_1350 = (GibCursor) fltPrd_1187;
            GibCursor end_tailapp_877 = (GibCursor) pvrtmp_1351;
            GibCursor end_r_606__945 = (GibCursor) pvrtmp_1344;
            GibCursor endof_878 = (GibCursor) pvrtmp_1345;
            GibCursor pvrtmp_1353 = (GibCursor) end_tailapp_877;
            GibCursor pvrtmp_1352 = (GibCursor) tailapp_877;
            GibCursor fltPrd_1189 = (GibCursor) pvrtmp_1352;
            GibCursor fltPrd_1190 = (GibCursor) pvrtmp_1353;

            gib_free_region(end_r_692);
            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_606__945,
                                                               endof_878,
                                                               fltPrd_1189,
                                                               fltPrd_1190};
            break;
        }

      case 255:
        {
            GibCursor tmpcur_1593 = *(GibCursor *) tmpcur_1333;
            GibCursor tmpaftercur_1594 = tmpcur_1333 + 8;
            GibBoxedTag tagtmp_1595 = *(GibBoxedTag *) tmpcur_1593;
            GibCursor tailtmp_1596 = tmpcur_1593 + 1;

            tmpval_1332 = tagtmp_1595;
            tmpcur_1333 = tailtmp_1596;
            goto switch_1354;
            break;
        }

      case 254:
        {
            GibCursor tmpcur_1593 = *(GibCursor *) tmpcur_1333;
            GibCursor tmpaftercur_1594 = tmpcur_1333 + 8;
            GibBoxedTag tagtmp_1595 = *(GibBoxedTag *) tmpcur_1593;
            GibCursor tailtmp_1596 = tmpcur_1593 + 1;

            tmpval_1332 = tagtmp_1595;
            tmpcur_1333 = tailtmp_1596;
            goto switch_1354;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1332");
            exit(1);
        }
    }
}
GibInt do_reverse()
{
    GibRegionMeta *region_1355 =
                  gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_720 = region_1355->reg_heap;
    GibInt sizeof_end_r_720_1356 = gib_get_inf_init_chunk_size();
    GibCursor end_r_720 = r_720 + sizeof_end_r_720_1356;
    GibRegionMeta *region_1357 =
                  gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_721 = region_1357->reg_heap;
    GibInt sizeof_end_r_721_1358 = gib_get_inf_init_chunk_size();
    GibCursor end_r_721 = r_721 + sizeof_end_r_721_1358;
    GibRegionMeta *region_1359 =
                  gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_719 = region_1359->reg_heap;
    GibInt sizeof_end_r_719_1360 = gib_get_inf_init_chunk_size();
    GibCursor end_r_719 = r_719 + sizeof_end_r_719_1360;
    GibCursor loc_715 = (GibCursor) r_720;
    GibCursor loc_713 = (GibCursor) r_721;
    GibCursor loc_704 = loc_713 + 1;
    GibCursor loc_705 = loc_704 + 8;
    GibCursor loc_700 = loc_705 + 1;
    GibCursor loc_701 = loc_700 + 8;
    GibCursor loc_696 = loc_701 + 1;
    GibCursor loc_697 = loc_696 + 8;

    *(GibBoxedTag *) loc_697 = 0;

    GibCursor writetag_998 = loc_697 + 1;
    GibCursor pvrtmp_1362 = (GibCursor) writetag_998;
    GibCursor pvrtmp_1361 = (GibCursor) loc_697;
    GibCursor fltPkd_248_277 = (GibCursor) pvrtmp_1361;
    GibCursor end_fltPkd_248_277 = (GibCursor) pvrtmp_1362;

    *(GibBoxedTag *) loc_701 = 1;

    GibCursor writetag_1000 = loc_701 + 1;

    *(GibInt *) writetag_1000 = 3;

    GibCursor writecur_1001 = writetag_1000 + sizeof(GibInt);
    GibCursor writecur_1002 = (GibCursor) end_fltPkd_248_277;
    GibCursor pvrtmp_1364 = (GibCursor) writecur_1002;
    GibCursor pvrtmp_1363 = (GibCursor) loc_701;
    GibCursor fltPkd_247_278 = (GibCursor) pvrtmp_1363;
    GibCursor end_fltPkd_247_278 = (GibCursor) pvrtmp_1364;

    *(GibBoxedTag *) loc_705 = 1;

    GibCursor writetag_1004 = loc_705 + 1;

    *(GibInt *) writetag_1004 = 2;

    GibCursor writecur_1005 = writetag_1004 + sizeof(GibInt);
    GibCursor writecur_1006 = (GibCursor) end_fltPkd_247_278;
    GibCursor pvrtmp_1366 = (GibCursor) writecur_1006;
    GibCursor pvrtmp_1365 = (GibCursor) loc_705;
    GibCursor fltPkd_246_279 = (GibCursor) pvrtmp_1365;
    GibCursor end_fltPkd_246_279 = (GibCursor) pvrtmp_1366;

    *(GibBoxedTag *) loc_713 = 1;

    GibCursor writetag_1008 = loc_713 + 1;

    *(GibInt *) writetag_1008 = 1;

    GibCursor writecur_1009 = writetag_1008 + sizeof(GibInt);
    GibCursor writecur_1010 = (GibCursor) end_fltPkd_246_279;
    GibCursor pvrtmp_1368 = (GibCursor) writecur_1010;
    GibCursor pvrtmp_1367 = (GibCursor) loc_713;
    GibCursor xs_21_174_280 = (GibCursor) pvrtmp_1367;
    GibCursor end_xs_21_174_280 = (GibCursor) pvrtmp_1368;

    *(GibBoxedTag *) loc_715 = 0;

    GibCursor writetag_1012 = loc_715 + 1;
    GibCursor pvrtmp_1370 = (GibCursor) writetag_1012;
    GibCursor pvrtmp_1369 = (GibCursor) loc_715;
    GibCursor fltAppE_249_281 = (GibCursor) pvrtmp_1369;
    GibCursor end_fltAppE_249_281 = (GibCursor) pvrtmp_1370;
    GibCursor loc_718 = (GibCursor) r_719;
    GibCursorGibCursorGibCursorGibCursorProd tmp_struct_16 =
                                              reverse(end_r_721, end_r_720, end_r_719, loc_718, xs_21_174_280, fltAppE_249_281);
    GibCursor pvrtmp_1371 = tmp_struct_16.field0;
    GibCursor pvrtmp_1372 = tmp_struct_16.field1;
    GibCursor pvrtmp_1373 = tmp_struct_16.field2;
    GibCursor pvrtmp_1374 = tmp_struct_16.field3;
    GibCursor fltPrd_1191 = (GibCursor) pvrtmp_1373;
    GibCursor fltPrd_1192 = (GibCursor) pvrtmp_1374;
    GibCursor pvrtmp_1376 = (GibCursor) fltPrd_1192;
    GibCursor pvrtmp_1375 = (GibCursor) fltPrd_1191;
    GibCursor ys_22_175_282 = (GibCursor) pvrtmp_1375;
    GibCursor fltPrd_1193 = (GibCursor) pvrtmp_1373;
    GibCursor fltPrd_1194 = (GibCursor) pvrtmp_1374;
    GibCursor pvrtmp_1378 = (GibCursor) fltPrd_1194;
    GibCursor pvrtmp_1377 = (GibCursor) fltPrd_1193;
    GibCursor end_ys_22_175_282 = (GibCursor) pvrtmp_1378;
    GibCursor end_r_719__946 = (GibCursor) pvrtmp_1371;
    GibCursor endof_879 = (GibCursor) pvrtmp_1372;
    GibCursorGibIntProd tmp_struct_17 =
                         sum_list(end_r_719__946, ys_22_175_282);
    GibCursor pvrtmp_1379 = tmp_struct_17.field0;
    GibInt pvrtmp_1380 = tmp_struct_17.field1;
    GibCursor endof_881 = (GibCursor) pvrtmp_1379;
    GibInt tailapp_880 = (GibInt) pvrtmp_1380;

    gib_free_region(end_r_719);
    gib_free_region(end_r_721);
    gib_free_region(end_r_720);
    return tailapp_880;
}
GibInt do_tree()
{
    GibRegionMeta *region_1381 =
                  gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_731 = region_1381->reg_heap;
    GibInt sizeof_end_r_731_1382 = gib_get_inf_init_chunk_size();
    GibCursor end_r_731 = r_731 + sizeof_end_r_731_1382;
    GibRegionMeta *region_1383 =
                  gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_730 = region_1383->reg_heap;
    GibInt sizeof_end_r_730_1384 = gib_get_inf_init_chunk_size();
    GibCursor end_r_730 = r_730 + sizeof_end_r_730_1384;
    GibCursor loc_726 = (GibCursor) r_731;
    GibCursorGibCursorGibCursorProd tmp_struct_18 =
                                     buildtree(end_r_731, loc_726, 10);
    GibCursor pvrtmp_1385 = tmp_struct_18.field0;
    GibCursor pvrtmp_1386 = tmp_struct_18.field1;
    GibCursor pvrtmp_1387 = tmp_struct_18.field2;
    GibCursor fltPrd_1195 = (GibCursor) pvrtmp_1386;
    GibCursor fltPrd_1196 = (GibCursor) pvrtmp_1387;
    GibCursor pvrtmp_1389 = (GibCursor) fltPrd_1196;
    GibCursor pvrtmp_1388 = (GibCursor) fltPrd_1195;
    GibCursor tr0_23_176_283 = (GibCursor) pvrtmp_1388;
    GibCursor fltPrd_1197 = (GibCursor) pvrtmp_1386;
    GibCursor fltPrd_1198 = (GibCursor) pvrtmp_1387;
    GibCursor pvrtmp_1391 = (GibCursor) fltPrd_1198;
    GibCursor pvrtmp_1390 = (GibCursor) fltPrd_1197;
    GibCursor end_tr0_23_176_283 = (GibCursor) pvrtmp_1391;
    GibCursor end_r_731__947 = (GibCursor) pvrtmp_1385;
    GibCursor loc_729 = (GibCursor) r_730;
    GibCursorGibCursorGibCursorGibCursorProd tmp_struct_19 =
                                              add1(end_r_731__947, end_r_730, loc_729, tr0_23_176_283);
    GibCursor pvrtmp_1392 = tmp_struct_19.field0;
    GibCursor pvrtmp_1393 = tmp_struct_19.field1;
    GibCursor pvrtmp_1394 = tmp_struct_19.field2;
    GibCursor pvrtmp_1395 = tmp_struct_19.field3;
    GibCursor fltPrd_1199 = (GibCursor) pvrtmp_1394;
    GibCursor fltPrd_1200 = (GibCursor) pvrtmp_1395;
    GibCursor pvrtmp_1397 = (GibCursor) fltPrd_1200;
    GibCursor pvrtmp_1396 = (GibCursor) fltPrd_1199;
    GibCursor tr1_24_177_284 = (GibCursor) pvrtmp_1396;
    GibCursor fltPrd_1201 = (GibCursor) pvrtmp_1394;
    GibCursor fltPrd_1202 = (GibCursor) pvrtmp_1395;
    GibCursor pvrtmp_1399 = (GibCursor) fltPrd_1202;
    GibCursor pvrtmp_1398 = (GibCursor) fltPrd_1201;
    GibCursor end_tr1_24_177_284 = (GibCursor) pvrtmp_1399;
    GibCursor end_r_730__948 = (GibCursor) pvrtmp_1392;
    GibCursor endof_882 = (GibCursor) pvrtmp_1393;
    GibCursorGibIntProd tmp_struct_20 =
                         sumtree(end_r_730__948, tr1_24_177_284);
    GibCursor pvrtmp_1400 = tmp_struct_20.field0;
    GibInt pvrtmp_1401 = tmp_struct_20.field1;
    GibCursor endof_884 = (GibCursor) pvrtmp_1400;
    GibInt tailapp_883 = (GibInt) pvrtmp_1401;

    gib_free_region(end_r_730);
    gib_free_region(end_r_731);
    return tailapp_883;
}
GibCursorGibIntProd sum_list(GibCursor end_r_608, GibCursor xs_40_178_285)
{
    GibCursor loc_607 = (GibCursor) xs_40_178_285;
    GibBoxedTag tmpval_1402 = *(GibBoxedTag *) xs_40_178_285;
    GibCursor tmpcur_1403 = xs_40_178_285 + 1;


  switch_1408:
    ;
    switch (tmpval_1402) {

      case 0:
        {
            GibCursor field_cur_1019 = (GibCursor) tmpcur_1403;
            GibCursor jump_886 = loc_607 + 1;
            GibInt fltScalar_885 = (GibInt) 0;

            return (GibCursorGibIntProd) {jump_886, fltScalar_885};
            break;
        }

      case 1:
        {
            GibCursor field_cur_1020 = (GibCursor) tmpcur_1403;
            GibCursor case_734 = (GibCursor) field_cur_1020;
            GibInt tmpval_1404 = *(GibInt *) case_734;
            GibCursor tmpcur_1405 = case_734 + sizeof(GibInt);
            GibInt y_41_179_286 = (GibInt) tmpval_1404;
            GibCursor end_y_41_179_286 = (GibCursor) tmpcur_1405;
            GibCursor case_735 = (GibCursor) end_y_41_179_286;
            GibCursor ys_42_180_287 = (GibCursor) case_735;
            GibCursor jump_887 = case_734 + 8;
            GibCursorGibIntProd tmp_struct_21 =
                                 sum_list(end_r_608, ys_42_180_287);
            GibCursor pvrtmp_1406 = tmp_struct_21.field0;
            GibInt pvrtmp_1407 = tmp_struct_21.field1;
            GibCursor endof_888 = (GibCursor) pvrtmp_1406;
            GibInt fltPrm_250_288 = (GibInt) pvrtmp_1407;
            GibInt tailprim_889 = y_41_179_286 + fltPrm_250_288;

            return (GibCursorGibIntProd) {endof_888, tailprim_889};
            break;
        }

      case 255:
        {
            GibCursor tmpcur_1597 = *(GibCursor *) tmpcur_1403;
            GibCursor tmpaftercur_1598 = tmpcur_1403 + 8;
            GibBoxedTag tagtmp_1599 = *(GibBoxedTag *) tmpcur_1597;
            GibCursor tailtmp_1600 = tmpcur_1597 + 1;

            tmpval_1402 = tagtmp_1599;
            tmpcur_1403 = tailtmp_1600;
            goto switch_1408;
            break;
        }

      case 254:
        {
            GibCursor tmpcur_1597 = *(GibCursor *) tmpcur_1403;
            GibCursor tmpaftercur_1598 = tmpcur_1403 + 8;
            GibBoxedTag tagtmp_1599 = *(GibBoxedTag *) tmpcur_1597;
            GibCursor tailtmp_1600 = tmpcur_1597 + 1;

            tmpval_1402 = tagtmp_1599;
            tmpcur_1403 = tailtmp_1600;
            goto switch_1408;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1402");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd _copy_Tree(GibCursor end_r_611, // input region
                                                    GibCursor end_r_612, // output region
                                                    GibCursor loc_610, // output location
                                                    GibCursor arg_103_181_289 // input location
                                                   )
{
    GibCursor loc_609 = (GibCursor) arg_103_181_289;

    if (loc_610 + 32 > end_r_612) {
        GibChunk new_chunk_24 = gib_alloc_chunk(end_r_612);
        GibCursor chunk_start_25 = new_chunk_24.chunk_start;
        GibCursor chunk_end_26 = new_chunk_24.chunk_end;

        end_r_612 = chunk_end_26;
        *(GibBoxedTag *) loc_610 = 255;

        GibCursor redir = loc_610 + 1;

        *(GibCursor *) redir = chunk_start_25;
        loc_610 = chunk_start_25;
    }

    GibBoxedTag tmpval_1409 = *(GibBoxedTag *) arg_103_181_289;
    GibCursor tmpcur_1410 = arg_103_181_289 + 1;


  switch_1437:
    ;
    switch (tmpval_1409) {

      case 0:
        {
            GibCursor field_cur_1023 = (GibCursor) tmpcur_1410;
            GibCursor case_740 = (GibCursor) field_cur_1023;
            GibInt tmpval_1411 = *(GibInt *) case_740;
            GibCursor tmpcur_1412 = case_740 + sizeof(GibInt);
            GibInt x_104_182_290 = (GibInt) tmpval_1411;
            GibCursor end_x_104_182_290 = (GibCursor) tmpcur_1412;
            GibCursor jump_890 = case_740 + 8;

            *(GibBoxedTag *) loc_610 = 0;

            GibCursor writetag_1025 = loc_610 + 1;

            *(GibInt *) writetag_1025 = x_104_182_290;

            GibCursor writecur_1026 = writetag_1025 + sizeof(GibInt);
            GibCursor pvrtmp_1414 = (GibCursor) writecur_1026;
            GibCursor pvrtmp_1413 = (GibCursor) loc_610;
            GibCursor taildc_891 = (GibCursor) pvrtmp_1413;
            GibCursor end_taildc_891 = (GibCursor) pvrtmp_1414;
            GibCursor pvrtmp_1416 = (GibCursor) end_taildc_891;
            GibCursor pvrtmp_1415 = (GibCursor) taildc_891;
            GibCursor fltPrd_1203 = (GibCursor) pvrtmp_1415;
            GibCursor fltPrd_1204 = (GibCursor) pvrtmp_1416;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_612,
                                                               jump_890,
                                                               fltPrd_1203,
                                                               fltPrd_1204};
            break;
        }

      case 1:
        {
            GibCursor field_cur_1028 = (GibCursor) tmpcur_1410;
            GibCursor case_744 = (GibCursor) field_cur_1028;
            GibCursor x_106_184_292 = (GibCursor) case_744;
            GibCursor loc_752 = loc_610 + 1;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_22 =
                                                      _copy_Tree(end_r_611, end_r_612, loc_752, x_106_184_292);
            GibCursor pvrtmp_1417 = tmp_struct_22.field0;
            GibCursor pvrtmp_1418 = tmp_struct_22.field1;
            GibCursor pvrtmp_1419 = tmp_struct_22.field2;
            GibCursor pvrtmp_1420 = tmp_struct_22.field3;
            GibCursor fltPrd_1205 = (GibCursor) pvrtmp_1419;
            GibCursor fltPrd_1206 = (GibCursor) pvrtmp_1420;
            GibCursor pvrtmp_1422 = (GibCursor) fltPrd_1206;
            GibCursor pvrtmp_1421 = (GibCursor) fltPrd_1205;
            GibCursor y_108_186_294 = (GibCursor) pvrtmp_1421;
            GibCursor fltPrd_1207 = (GibCursor) pvrtmp_1419;
            GibCursor fltPrd_1208 = (GibCursor) pvrtmp_1420;
            GibCursor pvrtmp_1424 = (GibCursor) fltPrd_1208;
            GibCursor pvrtmp_1423 = (GibCursor) fltPrd_1207;
            GibCursor end_y_108_186_294 = (GibCursor) pvrtmp_1424;
            GibCursor end_r_612__949 = (GibCursor) pvrtmp_1417;
            GibCursor endof_892 = (GibCursor) pvrtmp_1418;
            GibCursor case_745 = (GibCursor) endof_892;
            GibCursor x_107_185_293 = (GibCursor) case_745;
            GibCursor loc_753 = (GibCursor) end_y_108_186_294;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_23 =
                                                      _copy_Tree(end_r_611, end_r_612__949, loc_753, x_107_185_293);
            GibCursor pvrtmp_1425 = tmp_struct_23.field0;
            GibCursor pvrtmp_1426 = tmp_struct_23.field1;
            GibCursor pvrtmp_1427 = tmp_struct_23.field2;
            GibCursor pvrtmp_1428 = tmp_struct_23.field3;
            GibCursor fltPrd_1209 = (GibCursor) pvrtmp_1427;
            GibCursor fltPrd_1210 = (GibCursor) pvrtmp_1428;
            GibCursor pvrtmp_1430 = (GibCursor) fltPrd_1210;
            GibCursor pvrtmp_1429 = (GibCursor) fltPrd_1209;
            GibCursor y_109_187_295 = (GibCursor) pvrtmp_1429;
            GibCursor fltPrd_1211 = (GibCursor) pvrtmp_1427;
            GibCursor fltPrd_1212 = (GibCursor) pvrtmp_1428;
            GibCursor pvrtmp_1432 = (GibCursor) fltPrd_1212;
            GibCursor pvrtmp_1431 = (GibCursor) fltPrd_1211;
            GibCursor end_y_109_187_295 = (GibCursor) pvrtmp_1432;
            GibCursor end_r_612__949__950 = (GibCursor) pvrtmp_1425;
            GibCursor endof_893 = (GibCursor) pvrtmp_1426;

            *(GibBoxedTag *) loc_610 = 1;

            GibCursor writetag_1031 = loc_610 + 1;
            GibCursor writecur_1032 = (GibCursor) end_y_108_186_294;
            GibCursor writecur_1033 = (GibCursor) end_y_109_187_295;
            GibCursor pvrtmp_1434 = (GibCursor) writecur_1033;
            GibCursor pvrtmp_1433 = (GibCursor) loc_610;
            GibCursor taildc_894 = (GibCursor) pvrtmp_1433;
            GibCursor end_taildc_894 = (GibCursor) pvrtmp_1434;
            GibCursor pvrtmp_1436 = (GibCursor) end_taildc_894;
            GibCursor pvrtmp_1435 = (GibCursor) taildc_894;
            GibCursor fltPrd_1213 = (GibCursor) pvrtmp_1435;
            GibCursor fltPrd_1214 = (GibCursor) pvrtmp_1436;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_612__949__950,
                                                               endof_893,
                                                               fltPrd_1213,
                                                               fltPrd_1214};
            break;
        }

      case 255:
        {
            GibCursor tmpcur_1601 = *(GibCursor *) tmpcur_1410;
            GibCursor tmpaftercur_1602 = tmpcur_1410 + 8;
            GibBoxedTag tagtmp_1603 = *(GibBoxedTag *) tmpcur_1601;
            GibCursor tailtmp_1604 = tmpcur_1601 + 1;

            tmpval_1409 = tagtmp_1603;
            tmpcur_1410 = tailtmp_1604;
            goto switch_1437;
            break;
        }

      case 254:
        {
            GibCursor tmpcur_1601 = *(GibCursor *) tmpcur_1410;
            GibCursor tmpaftercur_1602 = tmpcur_1410 + 8;
            GibBoxedTag tagtmp_1603 = *(GibBoxedTag *) tmpcur_1601;
            GibCursor tailtmp_1604 = tmpcur_1601 + 1;

            tmpval_1409 = tagtmp_1603;
            tmpcur_1410 = tailtmp_1604;
            goto switch_1437;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1409");
            exit(1);
        }
    }
}
GibCursorProd _traverse_Tree(GibCursor end_r_618, GibCursor arg_117_195_303)
{
    GibCursor loc_617 = (GibCursor) arg_117_195_303;
    GibBoxedTag tmpval_1467 = *(GibBoxedTag *) arg_117_195_303;
    GibCursor tmpcur_1468 = arg_117_195_303 + 1;


  switch_1473:
    ;
    switch (tmpval_1467) {

      case 0:
        {
            GibCursor field_cur_1047 = (GibCursor) tmpcur_1468;
            GibCursor case_776 = (GibCursor) field_cur_1047;
            GibInt tmpval_1469 = *(GibInt *) case_776;
            GibCursor tmpcur_1470 = case_776 + sizeof(GibInt);
            GibInt x_118_196_304 = (GibInt) tmpval_1469;
            GibCursor end_x_118_196_304 = (GibCursor) tmpcur_1470;
            GibCursor jump_900 = case_776 + 8;

            return (GibCursorProd) {jump_900};
            break;
        }

      case 1:
        {
            GibCursor field_cur_1049 = (GibCursor) tmpcur_1468;
            GibCursor case_777 = (GibCursor) field_cur_1049;
            GibCursor x_120_197_305 = (GibCursor) case_777;
            GibCursorProd tmp_struct_29 =
                           _traverse_Tree(end_r_618, x_120_197_305);
            GibCursor pvrtmp_1471 = tmp_struct_29.field0;
            GibCursor endof_902 = (GibCursor) pvrtmp_1471;
            GibCursor case_778 = (GibCursor) endof_902;
            GibCursor x_121_198_306 = (GibCursor) case_778;
            GibCursorProd tmp_struct_30 =
                           _traverse_Tree(end_r_618, x_121_198_306);
            GibCursor pvrtmp_1472 = tmp_struct_30.field0;
            GibCursor endof_903 = (GibCursor) pvrtmp_1472;

            return (GibCursorProd) {endof_903};
            break;
        }

      case 255:
        {
            GibCursor tmpcur_1609 = *(GibCursor *) tmpcur_1468;
            GibCursor tmpaftercur_1610 = tmpcur_1468 + 8;
            GibBoxedTag tagtmp_1611 = *(GibBoxedTag *) tmpcur_1609;
            GibCursor tailtmp_1612 = tmpcur_1609 + 1;

            tmpval_1467 = tagtmp_1611;
            tmpcur_1468 = tailtmp_1612;
            goto switch_1473;
            break;
        }

      case 254:
        {
            GibCursor tmpcur_1609 = *(GibCursor *) tmpcur_1468;
            GibCursor tmpaftercur_1610 = tmpcur_1468 + 8;
            GibBoxedTag tagtmp_1611 = *(GibBoxedTag *) tmpcur_1609;
            GibCursor tailtmp_1612 = tmpcur_1609 + 1;

            tmpval_1467 = tagtmp_1611;
            tmpcur_1468 = tailtmp_1612;
            goto switch_1473;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1467");
            exit(1);
        }
    }
}
GibCursorProd _print_Tree(GibCursor end_r_620, GibCursor arg_124_201_309)
{
    GibCursor loc_619 = (GibCursor) arg_124_201_309;
    GibBoxedTag tmpval_1474 = *(GibBoxedTag *) arg_124_201_309;
    GibCursor tmpcur_1475 = arg_124_201_309 + 1;


  switch_1480:
    ;
    switch (tmpval_1474) {

      case 0:
        {
            GibCursor field_cur_1052 = (GibCursor) tmpcur_1475;
            GibCursor case_785 = (GibCursor) field_cur_1052;
            GibInt tmpval_1476 = *(GibInt *) case_785;
            GibCursor tmpcur_1477 = case_785 + sizeof(GibInt);
            GibInt x_125_202_310 = (GibInt) tmpval_1476;
            GibCursor end_x_125_202_310 = (GibCursor) tmpcur_1477;
            GibCursor jump_905 = case_785 + 8;
            unsigned char wildcard_127_203_311 = gib_print_symbol(1266);
            unsigned char y_126_204_312 = printf("%ld", x_125_202_310);
            unsigned char wildcard_128_205_313 = gib_print_symbol(1263);

            return (GibCursorProd) {jump_905};
            break;
        }

      case 1:
        {
            GibCursor field_cur_1054 = (GibCursor) tmpcur_1475;
            GibCursor case_786 = (GibCursor) field_cur_1054;
            GibCursor x_129_206_314 = (GibCursor) case_786;
            unsigned char wildcard_133_208_316 = gib_print_symbol(1264);
            GibCursorProd tmp_struct_31 =
                           _print_Tree(end_r_620, x_129_206_314);
            GibCursor pvrtmp_1478 = tmp_struct_31.field0;
            GibCursor endof_907 = (GibCursor) pvrtmp_1478;
            GibCursor case_787 = (GibCursor) endof_907;
            GibCursor x_130_207_315 = (GibCursor) case_787;
            GibCursorProd tmp_struct_32 =
                           _print_Tree(end_r_620, x_130_207_315);
            GibCursor pvrtmp_1479 = tmp_struct_32.field0;
            GibCursor endof_908 = (GibCursor) pvrtmp_1479;
            unsigned char wildcard_134_211_319 = gib_print_symbol(1263);

            return (GibCursorProd) {endof_908};
            break;
        }

      case 255:
        {
            printf(" ->r ");

            GibCursor tmpcur_1613 = *(GibCursor *) tmpcur_1475;
            GibCursor tmpaftercur_1614 = tmpcur_1475 + 8;
            GibBoxedTag tagtmp_1615 = *(GibBoxedTag *) tmpcur_1613;
            GibCursor tailtmp_1616 = tmpcur_1613 + 1;

            tmpval_1474 = tagtmp_1615;
            tmpcur_1475 = tailtmp_1616;
            goto switch_1480;
            break;
        }

      case 254:
        {
            printf(" ->i ");

            GibCursor tmpcur_1613 = *(GibCursor *) tmpcur_1475;
            GibCursor tmpaftercur_1614 = tmpcur_1475 + 8;
            GibBoxedTag tagtmp_1615 = *(GibBoxedTag *) tmpcur_1613;
            GibCursor tailtmp_1616 = tmpcur_1613 + 1;

            tmpval_1474 = tagtmp_1615;
            tmpcur_1475 = tailtmp_1616;
            goto switch_1480;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1474");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd _copy_List(GibCursor end_r_623,
                                                    GibCursor end_r_624,
                                                    GibCursor loc_622,
                                                    GibCursor arg_135_212_320)
{
    GibCursor loc_621 = (GibCursor) arg_135_212_320;

    if (loc_622 + 32 > end_r_624) {
        GibChunk new_chunk_34 = gib_alloc_chunk(end_r_624);
        GibCursor chunk_start_35 = new_chunk_34.chunk_start;
        GibCursor chunk_end_36 = new_chunk_34.chunk_end;

        end_r_624 = chunk_end_36;
        *(GibBoxedTag *) loc_622 = 255;

        GibCursor redir = loc_622 + 1;

        *(GibCursor *) redir = chunk_start_35;
        loc_622 = chunk_start_35;
    }

    GibCursor loc_800 = loc_622 + 1;
    GibCursor loc_801 = loc_800 + 8;
    GibBoxedTag tmpval_1481 = *(GibBoxedTag *) arg_135_212_320;
    GibCursor tmpcur_1482 = arg_135_212_320 + 1;


  switch_1501:
    ;
    switch (tmpval_1481) {

      case 0:
        {
            GibCursor field_cur_1057 = (GibCursor) tmpcur_1482;
            GibCursor jump_910 = loc_621 + 1;

            *(GibBoxedTag *) loc_622 = 0;

            GibCursor writetag_1058 = loc_622 + 1;
            GibCursor pvrtmp_1484 = (GibCursor) writetag_1058;
            GibCursor pvrtmp_1483 = (GibCursor) loc_622;
            GibCursor taildc_911 = (GibCursor) pvrtmp_1483;
            GibCursor end_taildc_911 = (GibCursor) pvrtmp_1484;
            GibCursor pvrtmp_1486 = (GibCursor) end_taildc_911;
            GibCursor pvrtmp_1485 = (GibCursor) taildc_911;
            GibCursor fltPrd_1227 = (GibCursor) pvrtmp_1485;
            GibCursor fltPrd_1228 = (GibCursor) pvrtmp_1486;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_624,
                                                               jump_910,
                                                               fltPrd_1227,
                                                               fltPrd_1228};
            break;
        }

      case 1:
        {
            GibCursor field_cur_1060 = (GibCursor) tmpcur_1482;
            GibCursor case_795 = (GibCursor) field_cur_1060;
            GibInt tmpval_1487 = *(GibInt *) case_795;
            GibCursor tmpcur_1488 = case_795 + sizeof(GibInt);
            GibInt x_136_213_321 = (GibInt) tmpval_1487;
            GibCursor end_x_136_213_321 = (GibCursor) tmpcur_1488;
            GibCursor case_796 = (GibCursor) end_x_136_213_321;
            GibCursor x_137_214_322 = (GibCursor) case_796;
            GibCursor jump_912 = case_795 + 8;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_33 =
                                                      _copy_List(end_r_623, end_r_624, loc_801, x_137_214_322);
            GibCursor pvrtmp_1489 = tmp_struct_33.field0;
            GibCursor pvrtmp_1490 = tmp_struct_33.field1;
            GibCursor pvrtmp_1491 = tmp_struct_33.field2;
            GibCursor pvrtmp_1492 = tmp_struct_33.field3;
            GibCursor fltPrd_1229 = (GibCursor) pvrtmp_1491;
            GibCursor fltPrd_1230 = (GibCursor) pvrtmp_1492;
            GibCursor pvrtmp_1494 = (GibCursor) fltPrd_1230;
            GibCursor pvrtmp_1493 = (GibCursor) fltPrd_1229;
            GibCursor y_139_216_324 = (GibCursor) pvrtmp_1493;
            GibCursor fltPrd_1231 = (GibCursor) pvrtmp_1491;
            GibCursor fltPrd_1232 = (GibCursor) pvrtmp_1492;
            GibCursor pvrtmp_1496 = (GibCursor) fltPrd_1232;
            GibCursor pvrtmp_1495 = (GibCursor) fltPrd_1231;
            GibCursor end_y_139_216_324 = (GibCursor) pvrtmp_1496;
            GibCursor end_r_624__953 = (GibCursor) pvrtmp_1489;
            GibCursor endof_913 = (GibCursor) pvrtmp_1490;

            *(GibBoxedTag *) loc_622 = 1;

            GibCursor writetag_1063 = loc_622 + 1;

            *(GibInt *) writetag_1063 = x_136_213_321;

            GibCursor writecur_1064 = writetag_1063 + sizeof(GibInt);
            GibCursor writecur_1065 = (GibCursor) end_y_139_216_324;
            GibCursor pvrtmp_1498 = (GibCursor) writecur_1065;
            GibCursor pvrtmp_1497 = (GibCursor) loc_622;
            GibCursor taildc_914 = (GibCursor) pvrtmp_1497;
            GibCursor end_taildc_914 = (GibCursor) pvrtmp_1498;
            GibCursor pvrtmp_1500 = (GibCursor) end_taildc_914;
            GibCursor pvrtmp_1499 = (GibCursor) taildc_914;
            GibCursor fltPrd_1233 = (GibCursor) pvrtmp_1499;
            GibCursor fltPrd_1234 = (GibCursor) pvrtmp_1500;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_624__953,
                                                               endof_913,
                                                               fltPrd_1233,
                                                               fltPrd_1234};
            break;
        }

      case 255:
        {
            GibCursor tmpcur_1617 = *(GibCursor *) tmpcur_1482;
            GibCursor tmpaftercur_1618 = tmpcur_1482 + 8;
            GibBoxedTag tagtmp_1619 = *(GibBoxedTag *) tmpcur_1617;
            GibCursor tailtmp_1620 = tmpcur_1617 + 1;

            tmpval_1481 = tagtmp_1619;
            tmpcur_1482 = tailtmp_1620;
            goto switch_1501;
            break;
        }

      case 254:
        {
            GibCursor tmpcur_1617 = *(GibCursor *) tmpcur_1482;
            GibCursor tmpaftercur_1618 = tmpcur_1482 + 8;
            GibBoxedTag tagtmp_1619 = *(GibBoxedTag *) tmpcur_1617;
            GibCursor tailtmp_1620 = tmpcur_1617 + 1;

            tmpval_1481 = tagtmp_1619;
            tmpcur_1482 = tailtmp_1620;
            goto switch_1501;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1481");
            exit(1);
        }
    }
}
GibCursorProd _traverse_List(GibCursor end_r_630, GibCursor arg_145_222_330)
{
    GibCursor loc_629 = (GibCursor) arg_145_222_330;
    GibBoxedTag tmpval_1523 = *(GibBoxedTag *) arg_145_222_330;
    GibCursor tmpcur_1524 = arg_145_222_330 + 1;


  switch_1528:
    ;
    switch (tmpval_1523) {

      case 0:
        {
            GibCursor field_cur_1077 = (GibCursor) tmpcur_1524;
            GibCursor jump_920 = loc_629 + 1;

            return (GibCursorProd) {jump_920};
            break;
        }

      case 1:
        {
            GibCursor field_cur_1078 = (GibCursor) tmpcur_1524;
            GibCursor case_820 = (GibCursor) field_cur_1078;
            GibInt tmpval_1525 = *(GibInt *) case_820;
            GibCursor tmpcur_1526 = case_820 + sizeof(GibInt);
            GibInt x_146_223_331 = (GibInt) tmpval_1525;
            GibCursor end_x_146_223_331 = (GibCursor) tmpcur_1526;
            GibCursor case_821 = (GibCursor) end_x_146_223_331;
            GibCursor x_147_224_332 = (GibCursor) case_821;
            GibCursor jump_922 = case_820 + 8;
            GibCursorProd tmp_struct_38 =
                           _traverse_List(end_r_630, x_147_224_332);
            GibCursor pvrtmp_1527 = tmp_struct_38.field0;
            GibCursor endof_923 = (GibCursor) pvrtmp_1527;

            return (GibCursorProd) {endof_923};
            break;
        }

      case 255:
        {
            GibCursor tmpcur_1625 = *(GibCursor *) tmpcur_1524;
            GibCursor tmpaftercur_1626 = tmpcur_1524 + 8;
            GibBoxedTag tagtmp_1627 = *(GibBoxedTag *) tmpcur_1625;
            GibCursor tailtmp_1628 = tmpcur_1625 + 1;

            tmpval_1523 = tagtmp_1627;
            tmpcur_1524 = tailtmp_1628;
            goto switch_1528;
            break;
        }

      case 254:
        {
            GibCursor tmpcur_1625 = *(GibCursor *) tmpcur_1524;
            GibCursor tmpaftercur_1626 = tmpcur_1524 + 8;
            GibBoxedTag tagtmp_1627 = *(GibBoxedTag *) tmpcur_1625;
            GibCursor tailtmp_1628 = tmpcur_1625 + 1;

            tmpval_1523 = tagtmp_1627;
            tmpcur_1524 = tailtmp_1628;
            goto switch_1528;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1523");
            exit(1);
        }
    }
}
GibCursorProd _print_List(GibCursor end_r_632, GibCursor arg_150_226_334)
{
    GibCursor loc_631 = (GibCursor) arg_150_226_334;
    GibBoxedTag tmpval_1529 = *(GibBoxedTag *) arg_150_226_334;
    GibCursor tmpcur_1530 = arg_150_226_334 + 1;


  switch_1534:
    ;
    switch (tmpval_1529) {

      case 0:
        {
            GibCursor field_cur_1081 = (GibCursor) tmpcur_1530;
            GibCursor jump_925 = loc_631 + 1;
            unsigned char wildcard_151_227_335 = gib_print_symbol(1265);
            unsigned char wildcard_152_228_336 = gib_print_symbol(1263);

            return (GibCursorProd) {jump_925};
            break;
        }

      case 1:
        {
            GibCursor field_cur_1082 = (GibCursor) tmpcur_1530;
            GibCursor case_826 = (GibCursor) field_cur_1082;
            GibInt tmpval_1531 = *(GibInt *) case_826;
            GibCursor tmpcur_1532 = case_826 + sizeof(GibInt);
            GibInt x_153_229_337 = (GibInt) tmpval_1531;
            GibCursor end_x_153_229_337 = (GibCursor) tmpcur_1532;
            GibCursor case_827 = (GibCursor) end_x_153_229_337;
            GibCursor x_154_230_338 = (GibCursor) case_827;
            GibCursor jump_927 = case_826 + 8;
            unsigned char wildcard_157_231_339 = gib_print_symbol(1267);
            unsigned char y_155_232_340 = printf("%ld", x_153_229_337);
            GibCursorProd tmp_struct_39 =
                           _print_List(end_r_632, x_154_230_338);
            GibCursor pvrtmp_1533 = tmp_struct_39.field0;
            GibCursor endof_928 = (GibCursor) pvrtmp_1533;
            unsigned char wildcard_158_234_342 = gib_print_symbol(1263);

            return (GibCursorProd) {endof_928};
            break;
        }

      case 255:
        {
            printf(" ->r ");

            GibCursor tmpcur_1629 = *(GibCursor *) tmpcur_1530;
            GibCursor tmpaftercur_1630 = tmpcur_1530 + 8;
            GibBoxedTag tagtmp_1631 = *(GibBoxedTag *) tmpcur_1629;
            GibCursor tailtmp_1632 = tmpcur_1629 + 1;

            tmpval_1529 = tagtmp_1631;
            tmpcur_1530 = tailtmp_1632;
            goto switch_1534;
            break;
        }

      case 254:
        {
            printf(" ->i ");

            GibCursor tmpcur_1629 = *(GibCursor *) tmpcur_1530;
            GibCursor tmpaftercur_1630 = tmpcur_1530 + 8;
            GibBoxedTag tagtmp_1631 = *(GibBoxedTag *) tmpcur_1629;
            GibCursor tailtmp_1632 = tmpcur_1629 + 1;

            tmpval_1529 = tagtmp_1631;
            tmpcur_1530 = tailtmp_1632;
            goto switch_1534;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1529");
            exit(1);
        }
    }
}

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Hand-written code starts here
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */


/*
 *

 * The nursery is set to 4KiB and every alloc_region requests space
 * just under 2*KiB. Therefore the third allocation on every thread should
 * be malloc'd, indicated on the stdout by MALLOC!!!.


 * Compile:
 * ~~~~~~~~~~


1) Compile the Rust RTS:

cd $GIBBONDIR/gibbon-rts && cargo build --release


2) Compile the C RTS:

gcc -std=gnu11  -fcilkplus -D_GIBBON_PARALLEL  -Wno-unused-variable -Wno-unused-label -Wall -Wextra -Wpedantic  -O3  -flto \
-I $GIBBONDIR/gibbon-compiler/cbits  -L$GIBBONDIR/gibbon-rts/target/release -Wl,-rpath=$GIBBONDIR/gibbon-rts/target/release \
-c $GIBBONDIR/gibbon-compiler/cbits/gibbon_rts.c -o $GIBBONDIR/gibbon-compiler/cbits/gibbon_rts.o  -lm -lgibbon_rts


3) Compile this program:

gcc -std=gnu11  -fcilkplus -D_GIBBON_PARALLEL  -Wno-unused-variable -Wno-unused-label -Wall -Wextra -Wpedantic  -O3  -flto \
$GIBBONDIR/gibbon-compiler/cbits/gibbon_rts.o -I$GIBBONDIR/gibbon-compiler/cbits  -L$GIBBONDIR/gibbon-rts/target/release \
-Wl,-rpath=$GIBBONDIR/gibbon-rts/target/release $GIBBONDIR/gibbon-compiler/examples/test_new_rts.c \
-o $GIBBONDIR/gibbon-compiler/examples/test_new_rts.exe -lm -lgibbon_rts


 * Run:
 * ~~~~~~~~~~

CILK_NWORKERS=3 $GIBBONDIR/gibbon-compiler/examples/test_new_rts.exe


 */

GibInt fib_seq(GibInt n)
{
    if (n == 0) {
        return 0;
    } else {
        if (n == 1) {
            return 1;
        } else {
            GibInt x =  fib_seq(n - 1);
            GibInt y =  fib_seq(n - 2);
            return (x + y);
        }
    }
}

void go_alloc_region(void)
{
    int worker;
#ifdef _GIBBON_PARALLEL
     worker = __cilkrts_get_worker_number();
#else
     worker = 0;
#endif

    // A dummy computation to make Cilk schedule this function on
    // different threads.
    GibInt x = fib_seq(25);
    // Allocate a region.
    GibCursorPair *cursors = gib_alloc_region2(2*KB-1);
    printf("alloc_region: worker=%d, start=%p, end=%p, x=%" PRId64 "\n", worker, cursors->cp_start, cursors->cp_end, x);
    return;
}

// assumption: NURSERY_REGION_MAX_SIZE is (2 * KB).
void test_alloc_region(void)
{
    // sequential.
    printf("\nSequential.\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n");
    for (int i = 0; i < 3; i++) {
        go_alloc_region();
    }

    // // reset.
    // printf("\nResetting the nursery.\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n\n");
    // gib_reset_nursery();

    // // parallel.
    // printf("\nParallel.\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n");
    // cilk_for (int i = 0; i < 3; i++) {
    //     go_alloc_region();
    // }

    return;
}

void test_info_table()
{
    int error = 0;
    error = gib_init_info_table();
    if (error < 0) {
        fprintf(stderr, "Couldn't initialize info table, errorno=%d", error);
        exit(1);
    }
    GibDatatype field_tys[10];

    field_tys[0] = GibInt_T;
    error = gib_insert_dcon_into_info_table(
        Tree_T,
        0, // Leaf tag
        1, // num_scalars
        0, // num_packed
        field_tys,
        1);
    if (error < 0) {
        fprintf(stderr, "Couldn't insert datacon, errorno=%d", error);
        exit(1);
    }
    field_tys[0] = Tree_T;
    field_tys[1] = Tree_T;
    error = gib_insert_dcon_into_info_table(
        Tree_T,
        1, // Node tag
        0, // num_scalars
        2, // num_packed
        field_tys,
        2);
    if (error < 0) {
        fprintf(stderr, "Couldn't insert datacon, errorno=%d", error);
        exit(1);
    }

    printf("test info tables done.\n");
}

int gib_main_expr(void)
{
    init_info_table();
    init_symbol_table();

    test_alloc_region();
    uint32_t sz = sizeof(GibDatatype);
    printf("sizeof(enum): %d\n", sz);
    test_info_table();

    // GibInt fltPrd_235_251 =  do_reverse();
    // GibInt fltPrd_236_252 =  do_tree();
    // GibInt pvrtmp_1269 = (GibInt) fltPrd_236_252;
    // GibInt pvrtmp_1268 = (GibInt) fltPrd_235_251;

    // printf("'#(");
    // printf("%ld", pvrtmp_1268);
    // printf(" ");
    // printf("%ld", pvrtmp_1269);
    // printf(")");
    // printf("\n");
    // gib_free_symtable();
    return 0;
}
