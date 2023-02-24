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
typedef struct GibFloatProd_struct {
            GibFloat field0;
        } GibFloatProd;
typedef struct GibFloatGibFloatProd_struct {
            GibFloat field0;
            GibFloat field1;
        } GibFloatGibFloatProd;
typedef struct GibFloatGibFloatGibFloatProd_struct {
            GibFloat field0;
            GibFloat field1;
            GibFloat field2;
        } GibFloatGibFloatGibFloatProd;
typedef struct GibFloatGibFloatGibFloatGibFloatProd_struct {
            GibFloat field0;
            GibFloat field1;
            GibFloat field2;
            GibFloat field3;
        } GibFloatGibFloatGibFloatGibFloatProd;
typedef struct GibFloatGibFloatGibFloatGibFloatGibFloatProd_struct {
            GibFloat field0;
            GibFloat field1;
            GibFloat field2;
            GibFloat field3;
            GibFloat field4;
        } GibFloatGibFloatGibFloatGibFloatGibFloatProd;
typedef struct GibFloatGibCursorProd_struct {
            GibFloat field0;
            GibCursor field1;
        } GibFloatGibCursorProd;
typedef struct GibBoolProd_struct {
            GibBool field0;
        } GibBoolProd;
typedef struct GibBoolGibIntProd_struct {
            GibBool field0;
            GibInt field1;
        } GibBoolGibIntProd;
typedef struct GibPackedTagGibCursorProd_struct {
            GibPackedTag field0;
            GibCursor field1;
        } GibPackedTagGibCursorProd;
typedef struct GibCursorProd_struct {
            GibCursor field0;
        } GibCursorProd;
typedef struct GibCursorGibIntProd_struct {
            GibCursor field0;
            GibInt field1;
        } GibCursorGibIntProd;
typedef struct GibCursorGibFloatProd_struct {
            GibCursor field0;
            GibFloat field1;
        } GibCursorGibFloatProd;
typedef struct GibCursorGibFloatGibFloatProd_struct {
            GibCursor field0;
            GibFloat field1;
            GibFloat field2;
        } GibCursorGibFloatGibFloatProd;
typedef struct GibCursorGibFloatGibFloatGibFloatProd_struct {
            GibCursor field0;
            GibFloat field1;
            GibFloat field2;
            GibFloat field3;
        } GibCursorGibFloatGibFloatGibFloatProd;
typedef struct GibCursorGibCursorProd_struct {
            GibCursor field0;
            GibCursor field1;
        } GibCursorGibCursorProd;
typedef struct GibCursorGibCursorGibIntProd_struct {
            GibCursor field0;
            GibCursor field1;
            GibInt field2;
        } GibCursorGibCursorGibIntProd;
typedef struct GibCursorGibCursorGibFloatProd_struct {
            GibCursor field0;
            GibCursor field1;
            GibFloat field2;
        } GibCursorGibCursorGibFloatProd;
typedef struct GibCursorGibCursorGibFloatGibFloatGibFloatProd_struct {
            GibCursor field0;
            GibCursor field1;
            GibFloat field2;
            GibFloat field3;
            GibFloat field4;
        } GibCursorGibCursorGibFloatGibFloatGibFloatProd;
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
typedef struct GibCursorGibVectorProd_struct {
            GibCursor field0;
            GibVector *field1;
        } GibCursorGibVectorProd;
typedef struct GibVectorProd_struct {
            GibVector *field0;
        } GibVectorProd;
unsigned char bench_seqbuildkdtree();
unsigned char bench_seqfoldconstants();
unsigned char bench_seqbhut();
unsigned char bench_seqbuildquadtree();
unsigned char bench_seqnearest();
unsigned char bench_seqcountcorr();
GibCursorGibCursorProd check_buildkdtree(GibCursor end_r_10655,
                                         GibVector *pts_154_4643_7587,
                                         GibCursor tr_155_4644_7588);
GibCursorGibCursorGibCursorProd mkKdTree_seq(GibCursor end_r_10657,
                                             GibCursor loc_10656,
                                             GibVector *pts_165_4654_7600);
unsigned char check_countcorr(GibVector *pts_166_4655_7601,
                              GibFloatGibFloatGibFloatProd query_167_4656_7602,
                              GibInt actual_168_4657_7603,
                              GibFloat radius_169_4658_7604);
GibCursorGibVectorProd allCountCorr_seq(GibCursor end_r_10659,
                                        GibFloat radius_183_4667_7619,
                                        GibCursor tr_184_4668_7620,
                                        GibVector *ls_185_4669_7621);
unsigned char check_nearest(GibVector *pts_191_4670_7626,
                            GibVector *actual_192_4671_7627);
GibCursorGibVectorProd allNearest_seq(GibCursor end_r_10661,
                                      GibCursor tr_207_4678_7645,
                                      GibVector *ls_208_4679_7646);
GibCursorGibCursorProd check_buildquadtree(GibCursor end_r_10663,
                                           GibVector *mpts_210_4680_7650,
                                           GibCursor bht_211_4681_7651);
GibCursorGibCursorGibCursorProd buildQtree_seq(GibCursor end_r_10665,
                                               GibCursor loc_10664,
                                               GibFloatGibFloatGibFloatGibFloatProd box_227_4697_7670,
                                               GibVector *mpts_228_4698_7671);
GibFloat maxFloat(GibFloat a_265_4730_7722, GibFloat b_266_4731_7723);
GibFloat minFloat(GibFloat a_267_4732_7725, GibFloat b_268_4733_7726);
GibCursorGibVectorProd oneStep_seq(GibCursor end_r_10667,
                                   GibCursor bht_274_4734_7728,
                                   GibVector *mpts_275_4735_7729,
                                   GibVector *ps_276_4736_7730);
GibCursorGibCursorGibIntProd sumExp(GibCursor end_r_10669,
                                    GibCursor exp_282_4738_7740);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
foldConstants2(GibCursor end_r_10672, GibCursor end_r_10673,
               GibCursor loc_10671, GibCursor exp_286_4742_7746);
GibCursorGibCursorGibCursorProd buildExp(GibCursor end_r_10675,
                                         GibCursor loc_10674,
                                         GibInt n_298_4754_7772);
GibFloat sumList(GibVector *ls_299_4755_7780);
GibCursorGibCursorGibFloatProd sumKdTree(GibCursor end_r_10677,
                                         GibCursor tr_326_4776_7784);
GibCursorGibIntProd countCorr_seq(GibCursor end_r_10679,
                                  GibFloatGibFloatGibFloatProd probe_359_4809_7808,
                                  GibFloat radius_360_4810_7809,
                                  GibCursor tr_361_4811_7810);
GibFloatGibFloatGibFloatProd
least_dist_point3d(GibFloatGibFloatGibFloatProd a_396_4846_7875,
                   GibFloatGibFloatGibFloatProd b_397_4847_7876,
                   GibFloatGibFloatGibFloatProd c_398_4848_7877);
GibCursorGibCursorGibFloatGibFloatGibFloatProd
find_nearest(GibCursor end_r_10682, GibCursor end_r_10683,
             GibFloatGibFloatGibFloatProd pivot_401_4851_7881,
             GibFloatGibFloatGibFloatProd query_402_4852_7882,
             GibFloat tst_pivot_403_4853_7883, GibFloat tst_query_404_4854_7884,
             GibCursor good_side_405_4855_7885,
             GibCursor other_side_406_4856_7886);
GibCursorGibFloatGibFloatGibFloatProd nearest(GibCursor end_r_10685,
                                              GibCursor tr_412_4862_7895,
                                              GibFloatGibFloatGibFloatProd query_413_4863_7896);
GibCursorGibCursorGibCursorProd mkKdTreeWithAxis_seq(GibCursor end_r_10687,
                                                     GibCursor loc_10686,
                                                     GibInt axis_434_4884_7918,
                                                     GibVector *pts_435_4885_7919);
GibCursorGibIntProd get_total_points_kdtree(GibCursor end_r_10689,
                                            GibCursor tr_514_4964_7979);
GibCursorGibFloatProd get_maxz_kdtree(GibCursor end_r_10691,
                                      GibCursor tr_532_4982_7997);
GibCursorGibFloatProd get_minz_kdtree(GibCursor end_r_10693,
                                      GibCursor tr_550_5000_8015);
GibCursorGibFloatProd get_maxy_kdtree(GibCursor end_r_10695,
                                      GibCursor tr_568_5018_8033);
GibCursorGibFloatProd get_miny_kdtree(GibCursor end_r_10697,
                                      GibCursor tr_586_5036_8051);
GibCursorGibFloatProd get_maxx_kdtree(GibCursor end_r_10699,
                                      GibCursor tr_604_5054_8069);
GibCursorGibFloatProd get_minx_kdtree(GibCursor end_r_10701,
                                      GibCursor tr_622_5072_8087);
GibFloat get_coord_point3d(GibInt axis_701_5151_8105,
                           GibFloatGibFloatGibFloatProd pt_702_5152_8106);
GibInt getNextAxis_3d(GibInt i_707_5157_8113);
GibVector *sort_point3d(GibInt axis_708_5158_8115, GibVector *ls_709_5159_8116);
GibFloat dist_point3d(GibFloatGibFloatGibFloatProd a_711_5161_8125,
                      GibFloatGibFloatGibFloatProd b_712_5162_8126);
unsigned char print_check(GibBool b_726_5174_8142);
GibFloat float_abs(GibFloat f_729_5177_8145);
GibBool eq_point3d(GibFloatGibFloatGibFloatProd a_730_5178_8148,
                   GibFloatGibFloatGibFloatProd b_731_5179_8149);
GibVector
*masspointsInBox_seq(GibFloatGibFloatGibFloatGibFloatProd box_780_5202_8162,
                     GibVector *mpts_781_5203_8163);
GibFloatGibFloatGibFloatProd calcCentroid_seq(GibVector *mpts_796_5214_8171);
GibCursorGibFloatGibFloatProd calcAccel_seq(GibCursor end_r_10703,
                                            GibFloatGibFloatGibFloatProd mpt_813_5220_8182,
                                            GibCursor tr_814_5221_8183);
GibCursorGibIntProd getTotalPoints_qtree(GibCursor end_r_10705,
                                         GibCursor tr_872_5279_8287);
GibFloat sum_mass_points(GibVector *mpts_939_5346_8300);
GibCursorGibCursorGibIntProd countLeavesQtree(GibCursor end_r_10707,
                                              GibCursor tr_946_5347_8304);
GibCursorGibCursorGibFloatProd sumQtree(GibCursor end_r_10709,
                                        GibCursor tr_959_5360_8323);
static inline
GibCursorGibFloatProd maybeLit(GibCursor end_r_10711,
                               GibCursor exp_1044_5429_8355);
static inline
GibCursorGibCursorProd trav_exp(GibCursor end_r_10713,
                                GibCursor exp_1057_5442_8359);
GibInt maxInt(GibInt a_1071_5456_8365, GibInt b_1072_5457_8366);
GibInt cmpz_point3d_original(GibFloatGibFloatGibFloatProd a_1340_5534_8368,
                             GibFloatGibFloatGibFloatProd b_1341_5535_8369);
int cmpz_point3d(const void *a_1340_5534_8368, const void *b_1341_5535_8369);
GibInt cmpy_point3d_original(GibFloatGibFloatGibFloatProd a_1346_5540_8378,
                             GibFloatGibFloatGibFloatProd b_1347_5541_8379);
int cmpy_point3d(const void *a_1346_5540_8378, const void *b_1347_5541_8379);
GibInt cmpx_point3d_original(GibFloatGibFloatGibFloatProd a_1352_5546_8388,
                             GibFloatGibFloatGibFloatProd b_1353_5547_8389);
int cmpx_point3d(const void *a_1352_5546_8388, const void *b_1353_5547_8389);
GibVector *filter_loop_2379(GibVector *idxs_1073_5607_8398,
                            GibInt write_at_1074_5608_8399,
                            GibInt start_1075_5609_8400,
                            GibInt end_1076_5610_8401,
                            GibVector *from_1077_5611_8402,
                            GibVector *to_1078_5612_8403);
GibInt foldl_loop_2380_3709(GibInt idx_1162_5962_8477,
                            GibInt end_1163_5963_8478,
                            GibInt acc_1165_5964_8479,
                            GibVector *vec_1166_5965_8480);
GibCursorGibVectorProd generate_loop_2377_3710(GibCursor end_r_10715,
                                               GibVector *vec_1194_5967_8488,
                                               GibInt idx_1195_5968_8489,
                                               GibInt end_1196_5969_8490,
                                               GibCursor bht_274_5970_8491,
                                               GibVector *mpts_275_5971_8492,
                                               GibVector *ps_276_5972_8493);
GibVector *generate_loop_2376_3711(GibVector *vec_1194_5974_8505,
                                   GibInt idx_1195_5975_8506,
                                   GibInt end_1196_5976_8507,
                                   GibVector *vec_1191_5977_8508);
GibVector *generate_loop_2374_3714(GibVector *vec_1194_5996_8515,
                                   GibInt idx_1195_5997_8516,
                                   GibInt end_1196_5998_8517);
GibVector *generate_loop_2374_3717(GibVector *vec_1194_6010_8523,
                                   GibInt idx_1195_6011_8524,
                                   GibInt end_1196_6012_8525,
                                   GibVector *vec_1028_6013_8526,
                                   GibFloatGibFloatGibFloatGibFloatProd box_780_6014_8527);
GibCursorGibVectorProd generate_loop_2376_3720(GibCursor end_r_10717,
                                               GibVector *vec_1194_6025_8543,
                                               GibInt idx_1195_6026_8544,
                                               GibInt end_1196_6027_8545,
                                               GibVector *vec_270_6028_8546,
                                               GibCursor tr_207_6029_8547);
GibCursorGibVectorProd generate_loop_2374_3723(GibCursor end_r_10719,
                                               GibVector *vec_1194_6042_8563,
                                               GibInt idx_1195_6043_8564,
                                               GibInt end_1196_6044_8565,
                                               GibVector *vec_270_6045_8566,
                                               GibFloat radius_183_6046_8567,
                                               GibCursor tr_184_6047_8568);
GibVector *generate_loop_2377_3726(GibVector *vec_1194_6057_8583,
                                   GibInt idx_1195_6058_8584,
                                   GibInt end_1196_6059_8585,
                                   GibVector *vec_270_6060_8586);
GibVector *generate_loop_2377_3729(GibVector *vec_1194_6070_8599,
                                   GibInt idx_1195_6071_8600,
                                   GibInt end_1196_6072_8601,
                                   GibVector *vec_270_6073_8602);
GibVector *generate_loop_2376_3732(GibVector *vec_1194_6083_8615,
                                   GibInt idx_1195_6084_8616,
                                   GibInt end_1196_6085_8617,
                                   GibVector *vec_270_6086_8618);
GibVector *generate_loop_2376_3735(GibVector *vec_1194_6096_8631,
                                   GibInt idx_1195_6097_8632,
                                   GibInt end_1196_6098_8633,
                                   GibVector *vec_270_6099_8634);
GibFloatGibFloatGibFloatProd foldl_loop_2371_3737(GibInt idx_1162_6109_8642,
                                                  GibInt end_1163_6110_8643,
                                                  GibFloatGibFloatGibFloatProd acc_1165_6111_8644,
                                                  GibVector *vec_1166_6112_8645);
GibFloat foldl_loop_2370_3738(GibInt idx_1162_6116_8664,
                              GibInt end_1163_6117_8665,
                              GibFloat acc_1165_6118_8666,
                              GibVector *vec_1166_6119_8667);
GibFloat foldl_loop_2370_3739(GibInt idx_1162_6123_8679,
                              GibInt end_1163_6124_8680,
                              GibFloat acc_1165_6125_8681,
                              GibVector *vec_1166_6126_8682);
GibInt foldl_loop_2369_3740(GibInt idx_1162_6128_8694,
                            GibInt end_1163_6129_8695,
                            GibInt acc_1165_6130_8696,
                            GibVector *vec_1166_6131_8697,
                            GibFloatGibFloatGibFloatProd query_167_6132_8698,
                            GibFloat radius_sq_170_6133_8699);
GibFloat foldl_loop_2368_3741(GibInt idx_1162_6137_8709,
                              GibInt end_1163_6138_8710,
                              GibFloat acc_1165_6139_8711,
                              GibVector *vec_1166_6140_8712);
GibFloat foldl_loop_2368_3742(GibInt idx_1162_6144_8719,
                              GibInt end_1163_6145_8720,
                              GibFloat acc_1165_6146_8721,
                              GibVector *vec_1166_6147_8722);
GibFloat foldl_loop_2368_3743(GibInt idx_1162_6151_8729,
                              GibInt end_1163_6152_8730,
                              GibFloat acc_1165_6153_8731,
                              GibVector *vec_1166_6154_8732);
GibFloat foldl_loop_2368_3744(GibInt idx_1162_6158_8739,
                              GibInt end_1163_6159_8740,
                              GibFloat acc_1165_6160_8741,
                              GibVector *vec_1166_6161_8742);
GibFloat foldl_loop_2368_3745(GibInt idx_1162_6165_8749,
                              GibInt end_1163_6166_8750,
                              GibFloat acc_1165_6167_8751,
                              GibVector *vec_1166_6168_8752);
GibFloat foldl_loop_2368_3746(GibInt idx_1162_6172_8759,
                              GibInt end_1163_6173_8760,
                              GibFloat acc_1165_6174_8761,
                              GibVector *vec_1166_6175_8762);
GibFloat foldl_loop_2368_3747(GibInt idx_1162_6179_8769,
                              GibInt end_1163_6180_8770,
                              GibFloat acc_1165_6181_8771,
                              GibVector *vec_1166_6182_8772);
GibFloat foldl_loop_2368_3748(GibInt idx_1162_6186_8779,
                              GibInt end_1163_6187_8780,
                              GibFloat acc_1165_6188_8781,
                              GibVector *vec_1166_6189_8782);
GibBoolGibIntProd foldl_loop_2367_3749(GibInt idx_1162_6191_8789,
                                       GibInt end_1163_6192_8790,
                                       GibBoolGibIntProd acc_1165_6193_8791,
                                       GibVector *vec_1166_6194_8792,
                                       GibVector *pts_191_6195_8793,
                                       GibVector *actual_192_6196_8794);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_KdTree(GibCursor end_r_10722, GibCursor end_r_10723, GibCursor loc_10721,
             GibCursor arg_4208_6198_8812);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_KdTree(GibCursor end_r_10726, GibCursor end_r_10727,
                          GibCursor loc_10725, GibCursor arg_4243_6233_8847);
GibCursorGibCursorProd _traverse_KdTree(GibCursor end_r_10729,
                                        GibCursor arg_4278_6268_8882);
GibCursorGibCursorProd _print_KdTree(GibCursor end_r_10731,
                                     GibCursor arg_4313_6288_8902);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_BH_Tree(GibCursor end_r_10734, GibCursor end_r_10735, GibCursor loc_10733,
              GibCursor arg_4388_6380_8994);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_BH_Tree(GibCursor end_r_10738, GibCursor end_r_10739,
                           GibCursor loc_10737, GibCursor arg_4413_6405_9019);
GibCursorGibCursorProd _traverse_BH_Tree(GibCursor end_r_10741,
                                         GibCursor arg_4438_6430_9044);
GibCursorGibCursorProd _print_BH_Tree(GibCursor end_r_10743,
                                      GibCursor arg_4463_6447_9061);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_Exp(GibCursor end_r_10746, GibCursor end_r_10747, GibCursor loc_10745,
          GibCursor arg_4518_6514_9128);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_Exp(GibCursor end_r_10750, GibCursor end_r_10751,
                       GibCursor loc_10749, GibCursor arg_4533_6529_9143);
GibCursorGibCursorProd _traverse_Exp(GibCursor end_r_10753,
                                     GibCursor arg_4548_6544_9158);
GibCursorGibCursorProd _print_Exp(GibCursor end_r_10755,
                                  GibCursor arg_4563_6558_9172);
typedef enum {
            GibInt_T,
            GibFloat_T,
            GibSym_T,
            GibBool_T,
            GibVector_T,
            GibList_T,
            GibCursor_T,
            BH_Tree_T,
            Exp_T,
            KdTree_T,
        } GibDatatype;
void info_table_initialize(void)
{
    int error = gib_info_table_initialize(10);

    if (error < 0) {
        fprintf(stderr, "Couldn't initialize info table, errorno=%d", error);
        exit(1);
    }

    GibDatatype field_tys[14];

    error = gib_info_table_insert_packed_dcon(BH_Tree_T, 0, 0, 0, 0, 0,
                                              field_tys, 0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, BH_Tree_T, 0);
        exit(1);
    }
    error = gib_info_table_insert_packed_dcon(BH_Tree_T, 1, 12, 0, 3, 0,
                                              field_tys, 0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, BH_Tree_T, 1);
        exit(1);
    }
    field_tys[0] = BH_Tree_T;
    field_tys[1] = BH_Tree_T;
    field_tys[2] = BH_Tree_T;
    field_tys[3] = BH_Tree_T;
    error = gib_info_table_insert_packed_dcon(BH_Tree_T, 2, 24, 0, 5, 4,
                                              field_tys, 4);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, BH_Tree_T, 2);
        exit(1);
    }
    field_tys[0] = BH_Tree_T;
    field_tys[1] = BH_Tree_T;
    field_tys[2] = BH_Tree_T;
    field_tys[3] = BH_Tree_T;
    error = gib_info_table_insert_packed_dcon(BH_Tree_T, 3, 24, 3, 5, 4,
                                              field_tys, 4);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, BH_Tree_T, 3);
        exit(1);
    }
    field_tys[0] = Exp_T;
    field_tys[1] = Exp_T;
    error = gib_info_table_insert_packed_dcon(Exp_T, 4, 0, 0, 0, 2, field_tys,
                                              2);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, Exp_T, 4);
        exit(1);
    }
    error = gib_info_table_insert_packed_dcon(Exp_T, 0, 8, 0, 1, 0, field_tys,
                                              0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, Exp_T, 0);
        exit(1);
    }
    error = gib_info_table_insert_packed_dcon(Exp_T, 2, 0, 0, 0, 0, field_tys,
                                              0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, Exp_T, 2);
        exit(1);
    }
    error = gib_info_table_insert_packed_dcon(Exp_T, 1, 0, 0, 0, 0, field_tys,
                                              0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, Exp_T, 1);
        exit(1);
    }
    field_tys[0] = Exp_T;
    field_tys[1] = Exp_T;
    error = gib_info_table_insert_packed_dcon(Exp_T, 5, 0, 0, 0, 2, field_tys,
                                              2);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, Exp_T, 5);
        exit(1);
    }
    field_tys[0] = Exp_T;
    field_tys[1] = Exp_T;
    error = gib_info_table_insert_packed_dcon(Exp_T, 3, 0, 0, 0, 2, field_tys,
                                              2);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, Exp_T, 3);
        exit(1);
    }
    error = gib_info_table_insert_packed_dcon(KdTree_T, 2, 0, 0, 0, 0,
                                              field_tys, 0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, KdTree_T, 2);
        exit(1);
    }
    error = gib_info_table_insert_packed_dcon(KdTree_T, 0, 12, 0, 3, 0,
                                              field_tys, 0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, KdTree_T, 0);
        exit(1);
    }
    field_tys[0] = KdTree_T;
    field_tys[1] = KdTree_T;
    error = gib_info_table_insert_packed_dcon(KdTree_T, 1, 56, 0, 12, 2,
                                              field_tys, 2);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, KdTree_T, 1);
        exit(1);
    }
    field_tys[0] = KdTree_T;
    field_tys[1] = KdTree_T;
    error = gib_info_table_insert_packed_dcon(KdTree_T, 3, 56, 1, 12, 2,
                                              field_tys, 2);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, KdTree_T, 3);
        exit(1);
    }
    gib_info_table_finalize();
}
void symbol_table_initialize(void)
{
    gib_add_symbol(15839,
                   "benchrunner: select benchmark to run with --bench-prog\n");
    gib_add_symbol(15840, "actual= ");
    gib_add_symbol(15841, "Sum: expected= ");
    gib_add_symbol(15842, "OK\n");
    gib_add_symbol(15843, "Expected: ");
    gib_add_symbol(15844, "Err\n");
    gib_add_symbol(15845, "Counts: ");
    gib_add_symbol(15846, "Actual: ");
    gib_add_symbol(15847, ", ");
    gib_add_symbol(15848, ")");
    gib_add_symbol(15849, "(Plus");
    gib_add_symbol(15850, "(Or");
    gib_add_symbol(15851, "(MkTrue");
    gib_add_symbol(15852, "(MkFalse");
    gib_add_symbol(15853, "(Lit");
    gib_add_symbol(15854, "(KdNode");
    gib_add_symbol(15855, "(KdLeaf");
    gib_add_symbol(15856, "(KdEmpty");
    gib_add_symbol(15857, "(BH_Node");
    gib_add_symbol(15858, "(BH_Leaf");
    gib_add_symbol(15859, "(BH_Empty");
    gib_add_symbol(15860, "(And");
    gib_add_symbol(15861, " ->r ");
    gib_add_symbol(15862, " ->i ");
    gib_add_symbol(15863, " ");
    gib_add_symbol(15864, "\n");
}
unsigned char bench_seqbuildkdtree()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibVector *pts_83_4604_7504 =
              gib_vector_alloc(gib_read_arrayfile_length_param(),
                               sizeof(GibFloatGibFloatGibFloatProd));
    GibFloatGibFloatGibFloatProd arr_elem_7;

    FILE * fp_8;

    char *line_9 = NULL;

    size_t(len_10);
    len_10 = 0;
    ssize_t(read_11);
    fp_8 = fopen(gib_read_arrayfile_param(), "r");
    if (fp_8 == NULL) {
        fprintf(stderr, "fopen failed\n");
        abort();
    }

    GibFloat tmp_13;
    GibFloat tmp_14;
    GibFloat tmp_15;
    GibInt i_12 = 0;

    while ((read_11 = getline(&line_9, &len_10, fp_8)) != -1) {
        int xxxx = sscanf(line_9, "%f %f %f", &tmp_13, &tmp_14, &tmp_15);

        arr_elem_7.field0 = tmp_13;
        arr_elem_7.field1 = tmp_14;
        arr_elem_7.field2 = tmp_15;
        gib_vector_inplace_update(pts_83_4604_7504, i_12, &arr_elem_7);
        i_12++;
    }

    GibInt n_84_4605_7505 = gib_get_size_param();
    GibFloat radius_85_4606_7506 = (GibFloat) n_84_4605_7505;
    GibChunk region_15865 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_10762 = region_15865.start;
    GibCursor end_r_10762 = region_15865.end;
    GibCursor pvrtmp_15875;
    GibCursor pvrtmp_15876;
    GibCursor pvrtmp_15877;
    GibVector *times_4 = gib_vector_alloc(gib_get_iters_param(),
                                          sizeof(double));
    struct timespec begin_pvrtmp_15875;
    struct timespec end_pvrtmp_15875;

    for (long long iters_pvrtmp_15875 = 0; iters_pvrtmp_15875 <
         gib_get_iters_param(); iters_pvrtmp_15875++) {
        if (iters_pvrtmp_15875 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_save_state();
            gib_ptr_bumpalloc_save_state();
        }
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_15875);

        GibCursorGibCursorGibCursorProd tmp_struct_0 =
                                         mkKdTree_seq(end_r_10762, r_10762, pts_83_4604_7504);
        GibCursor pvrtmp_15866 = tmp_struct_0.field0;
        GibCursor pvrtmp_15867 = tmp_struct_0.field1;
        GibCursor pvrtmp_15868 = tmp_struct_0.field2;

        pvrtmp_15875 = pvrtmp_15866;
        pvrtmp_15876 = pvrtmp_15867;
        pvrtmp_15877 = pvrtmp_15868;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_15875);
        if (iters_pvrtmp_15875 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_restore_state();
            gib_ptr_bumpalloc_restore_state();
        }

        double itertime_1 = gib_difftimespecs(&begin_pvrtmp_15875,
                                              &end_pvrtmp_15875);

        printf("itertime: %lf\n", itertime_1);
        gib_vector_inplace_update(times_4, iters_pvrtmp_15875, &itertime_1);
    }
    gib_vector_inplace_sort(times_4, gib_compare_doubles);

    double *tmp_5 = (double *) gib_vector_nth(times_4, gib_get_iters_param() /
                                              2);
    double selftimed_3 = *tmp_5;
    double batchtime_2 = gib_sum_timing_array(times_4);

    gib_print_timing_array(times_4);
    gib_vector_free(times_4);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_2);
    printf("SELFTIMED: %e\n", selftimed_3);

    GibCursorGibCursorProd tmp_struct_6 =
                            check_buildkdtree(end_r_10762, pts_83_4604_7504, pvrtmp_15876);
    GibCursor pvrtmp_15885 = tmp_struct_6.field0;
    GibCursor pvrtmp_15886 = tmp_struct_6.field1;

    return 0;
}
unsigned char bench_seqfoldconstants()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibInt fltAppE_7189_7508 = gib_get_size_param();
    GibChunk region_15887 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_10774 = region_15887.start;
    GibCursor end_r_10774 = region_15887.end;
    GibCursorGibCursorGibCursorProd tmp_struct_16 =
                                     buildExp(end_r_10774, r_10774, fltAppE_7189_7508);
    GibCursor pvrtmp_15888 = tmp_struct_16.field0;
    GibCursor pvrtmp_15889 = tmp_struct_16.field1;
    GibCursor pvrtmp_15890 = tmp_struct_16.field2;

    gib_shadowstack_push(rstack, pvrtmp_15889, pvrtmp_15888, Stk, Exp_T);

    GibChunk region_15895 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_10773 = region_15895.start;
    GibCursor end_r_10773 = region_15895.end;

    frame = gib_shadowstack_pop(rstack);
    pvrtmp_15889 = frame->ptr;
    pvrtmp_15888 = frame->endptr;

    GibCursor pvrtmp_15907;
    GibCursor pvrtmp_15908;
    GibCursor pvrtmp_15909;
    GibVector *times_21 = gib_vector_alloc(gib_get_iters_param(),
                                           sizeof(double));
    struct timespec begin_pvrtmp_15907;
    struct timespec end_pvrtmp_15907;

    for (long long iters_pvrtmp_15907 = 0; iters_pvrtmp_15907 <
         gib_get_iters_param(); iters_pvrtmp_15907++) {
        if (iters_pvrtmp_15907 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_save_state();
            gib_ptr_bumpalloc_save_state();
        }
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_15907);

        GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_17 =
                                                           foldConstants2(pvrtmp_15888, end_r_10773, r_10773, pvrtmp_15889);
        GibCursor pvrtmp_15896 = tmp_struct_17.field0;
        GibCursor pvrtmp_15897 = tmp_struct_17.field1;
        GibCursor pvrtmp_15898 = tmp_struct_17.field2;
        GibCursor pvrtmp_15899 = tmp_struct_17.field3;
        GibCursor pvrtmp_15900 = tmp_struct_17.field4;

        pvrtmp_15907 = pvrtmp_15897;
        pvrtmp_15908 = pvrtmp_15899;
        pvrtmp_15909 = pvrtmp_15900;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_15907);
        if (iters_pvrtmp_15907 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_restore_state();
            gib_ptr_bumpalloc_restore_state();
        }

        double itertime_18 = gib_difftimespecs(&begin_pvrtmp_15907,
                                               &end_pvrtmp_15907);

        printf("itertime: %lf\n", itertime_18);
        gib_vector_inplace_update(times_21, iters_pvrtmp_15907, &itertime_18);
    }
    gib_vector_inplace_sort(times_21, gib_compare_doubles);

    double *tmp_22 = (double *) gib_vector_nth(times_21, gib_get_iters_param() /
                                               2);
    double selftimed_20 = *tmp_22;
    double batchtime_19 = gib_sum_timing_array(times_21);

    gib_print_timing_array(times_21);
    gib_vector_free(times_21);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_19);
    printf("SELFTIMED: %e\n", selftimed_20);

    GibCursorGibCursorGibIntProd tmp_struct_23 =
                                  sumExp(end_r_10773, pvrtmp_15908);
    GibCursor pvrtmp_15917 = tmp_struct_23.field0;
    GibCursor pvrtmp_15918 = tmp_struct_23.field1;
    GibInt pvrtmp_15919 = tmp_struct_23.field2;
    unsigned char wildcard__76_90_4611_7512 = printf("%ld", pvrtmp_15919);

    return 0;
}
unsigned char bench_seqbhut()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibVector *pts_91_4612_7513 =
              gib_vector_alloc(gib_read_arrayfile_length_param(),
                               sizeof(GibFloatGibFloatProd));
    GibFloatGibFloatProd arr_elem_29;

    FILE * fp_30;

    char *line_31 = NULL;

    size_t(len_32);
    len_32 = 0;
    ssize_t(read_33);
    fp_30 = fopen(gib_read_arrayfile_param(), "r");
    if (fp_30 == NULL) {
        fprintf(stderr, "fopen failed\n");
        abort();
    }

    GibFloat tmp_35;
    GibFloat tmp_36;
    GibInt i_34 = 0;

    while ((read_33 = getline(&line_31, &len_32, fp_30)) != -1) {
        int xxxx = sscanf(line_31, "%f %f", &tmp_35, &tmp_36);

        arr_elem_29.field0 = tmp_35;
        arr_elem_29.field1 = tmp_36;
        gib_vector_inplace_update(pts_91_4612_7513, i_34, &arr_elem_29);
        i_34++;
    }

    GibInt fltAppE_7190_7515 = gib_vector_length(pts_91_4612_7513);
    GibInt n__743_6054_8580_9222 =  maxInt(fltAppE_7190_7515, 0);
    GibInt tmp_28 = sizeof(GibFloatGibFloatGibFloatGibFloatGibFloatProd);
    GibVector *vec_744_6055_8581_9223 = gib_vector_alloc(n__743_6054_8580_9222,
                                                         tmp_28);
    GibVector *vec1_745_6056_8582_9224 =
               generate_loop_2377_3726(vec_744_6055_8581_9223, 0, n__743_6054_8580_9222, pts_91_4612_7513);
    GibInt fltAppE_7191_7518 = gib_vector_length(pts_91_4612_7513);
    GibInt n__743_6080_8612_9227 =  maxInt(fltAppE_7191_7518, 0);
    GibInt tmp_27 = sizeof(GibFloatGibFloatGibFloatProd);
    GibVector *vec_744_6081_8613_9228 = gib_vector_alloc(n__743_6080_8612_9227,
                                                         tmp_27);
    GibVector *vec1_745_6082_8614_9229 =
               generate_loop_2376_3732(vec_744_6081_8613_9228, 0, n__743_6080_8612_9227, pts_91_4612_7513);
    GibInt fltAppE_7192_7522 = gib_vector_length(pts_91_4612_7513);
    GibFloat llx_104_4615_7523 =
              foldl_loop_2368_3741(0, fltAppE_7192_7522, 100000.0, pts_91_4612_7513);
    GibInt fltAppE_7193_7526 = gib_vector_length(pts_91_4612_7513);
    GibFloat lly_107_4616_7527 =
              foldl_loop_2368_3742(0, fltAppE_7193_7526, 100000.0, pts_91_4612_7513);
    GibFloat fltPrm_7194_7528 = 0.0 - 1.0;
    GibFloat acc_261_6149_6612_7529 = fltPrm_7194_7528 * 100000.0;
    GibInt fltAppE_7195_7531 = gib_vector_length(pts_91_4612_7513);
    GibFloat rux_110_4617_7532 =
              foldl_loop_2368_3743(0, fltAppE_7195_7531, acc_261_6149_6612_7529, pts_91_4612_7513);
    GibFloat fltPrm_7196_7533 = 0.0 - 1.0;
    GibFloat acc_261_6156_6614_7534 = fltPrm_7196_7533 * 100000.0;
    GibInt fltAppE_7197_7536 = gib_vector_length(pts_91_4612_7513);
    GibFloat ruy_113_4618_7537 =
              foldl_loop_2368_3744(0, fltAppE_7197_7536, acc_261_6156_6614_7534, pts_91_4612_7513);
    GibChunk region_15924 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_10781 = region_15924.start;
    GibCursor end_r_10781 = region_15924.end;
    GibCursorGibCursorGibCursorProd tmp_struct_24 =
                                     buildQtree_seq(end_r_10781, r_10781, (GibFloatGibFloatGibFloatGibFloatProd) {llx_104_4615_7523, lly_107_4616_7527, rux_110_4617_7532, ruy_113_4618_7537}, vec1_745_6082_8614_9229);
    GibCursor pvrtmp_15929 = tmp_struct_24.field0;
    GibCursor pvrtmp_15930 = tmp_struct_24.field1;
    GibCursor pvrtmp_15931 = tmp_struct_24.field2;
    GibCursorGibCursorProd tmp_struct_25 =
                            check_buildquadtree(pvrtmp_15929, vec1_745_6082_8614_9229, pvrtmp_15930);
    GibCursor pvrtmp_15936 = tmp_struct_25.field0;
    GibCursor pvrtmp_15937 = tmp_struct_25.field1;
    GibCursorGibVectorProd tmp_struct_26 =
                            oneStep_seq(pvrtmp_15929, pvrtmp_15930, vec1_745_6082_8614_9229, vec1_745_6056_8582_9224);
    GibCursor pvrtmp_15938 = tmp_struct_26.field0;
    GibVector *pvrtmp_15939 = tmp_struct_26.field1;

    return 0;
}
unsigned char bench_seqbuildquadtree()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibVector *pts_118_4623_7542 =
              gib_vector_alloc(gib_read_arrayfile_length_param(),
                               sizeof(GibFloatGibFloatProd));
    GibFloatGibFloatProd arr_elem_46;

    FILE * fp_47;

    char *line_48 = NULL;

    size_t(len_49);
    len_49 = 0;
    ssize_t(read_50);
    fp_47 = fopen(gib_read_arrayfile_param(), "r");
    if (fp_47 == NULL) {
        fprintf(stderr, "fopen failed\n");
        abort();
    }

    GibFloat tmp_52;
    GibFloat tmp_53;
    GibInt i_51 = 0;

    while ((read_50 = getline(&line_48, &len_49, fp_47)) != -1) {
        int xxxx = sscanf(line_48, "%f %f", &tmp_52, &tmp_53);

        arr_elem_46.field0 = tmp_52;
        arr_elem_46.field1 = tmp_53;
        gib_vector_inplace_update(pts_118_4623_7542, i_51, &arr_elem_46);
        i_51++;
    }

    GibInt fltAppE_7198_7544 = gib_vector_length(pts_118_4623_7542);
    GibInt n__743_6067_8596_9232 =  maxInt(fltAppE_7198_7544, 0);
    GibInt tmp_45 = sizeof(GibFloatGibFloatGibFloatGibFloatGibFloatProd);
    GibVector *vec_744_6068_8597_9233 = gib_vector_alloc(n__743_6067_8596_9232,
                                                         tmp_45);
    GibVector *vec1_745_6069_8598_9234 =
               generate_loop_2377_3729(vec_744_6068_8597_9233, 0, n__743_6067_8596_9232, pts_118_4623_7542);
    GibInt fltAppE_7199_7547 = gib_vector_length(pts_118_4623_7542);
    GibInt n__743_6093_8628_9237 =  maxInt(fltAppE_7199_7547, 0);
    GibInt tmp_44 = sizeof(GibFloatGibFloatGibFloatProd);
    GibVector *vec_744_6094_8629_9238 = gib_vector_alloc(n__743_6093_8628_9237,
                                                         tmp_44);
    GibVector *vec1_745_6095_8630_9239 =
               generate_loop_2376_3735(vec_744_6094_8629_9238, 0, n__743_6093_8628_9237, pts_118_4623_7542);
    GibInt fltAppE_7200_7551 = gib_vector_length(pts_118_4623_7542);
    GibFloat llx_131_4626_7552 =
              foldl_loop_2368_3745(0, fltAppE_7200_7551, 100000.0, pts_118_4623_7542);
    GibInt fltAppE_7201_7555 = gib_vector_length(pts_118_4623_7542);
    GibFloat lly_134_4627_7556 =
              foldl_loop_2368_3746(0, fltAppE_7201_7555, 100000.0, pts_118_4623_7542);
    GibFloat fltPrm_7202_7557 = 0.0 - 1.0;
    GibFloat acc_261_6177_6622_7558 = fltPrm_7202_7557 * 100000.0;
    GibInt fltAppE_7203_7560 = gib_vector_length(pts_118_4623_7542);
    GibFloat rux_137_4628_7561 =
              foldl_loop_2368_3747(0, fltAppE_7203_7560, acc_261_6177_6622_7558, pts_118_4623_7542);
    GibFloat fltPrm_7204_7562 = 0.0 - 1.0;
    GibFloat acc_261_6184_6624_7563 = fltPrm_7204_7562 * 100000.0;
    GibInt fltAppE_7205_7565 = gib_vector_length(pts_118_4623_7542);
    GibFloat ruy_140_4629_7566 =
              foldl_loop_2368_3748(0, fltAppE_7205_7565, acc_261_6184_6624_7563, pts_118_4623_7542);
    GibChunk region_15944 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_10788 = region_15944.start;
    GibCursor end_r_10788 = region_15944.end;
    GibCursor pvrtmp_15958;
    GibCursor pvrtmp_15959;
    GibCursor pvrtmp_15960;
    GibVector *times_41 = gib_vector_alloc(gib_get_iters_param(),
                                           sizeof(double));
    struct timespec begin_pvrtmp_15958;
    struct timespec end_pvrtmp_15958;

    for (long long iters_pvrtmp_15958 = 0; iters_pvrtmp_15958 <
         gib_get_iters_param(); iters_pvrtmp_15958++) {
        if (iters_pvrtmp_15958 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_save_state();
            gib_ptr_bumpalloc_save_state();
        }
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_15958);

        GibCursorGibCursorGibCursorProd tmp_struct_37 =
                                         buildQtree_seq(end_r_10788, r_10788, (GibFloatGibFloatGibFloatGibFloatProd) {llx_131_4626_7552, lly_134_4627_7556, rux_137_4628_7561, ruy_140_4629_7566}, vec1_745_6095_8630_9239);
        GibCursor pvrtmp_15949 = tmp_struct_37.field0;
        GibCursor pvrtmp_15950 = tmp_struct_37.field1;
        GibCursor pvrtmp_15951 = tmp_struct_37.field2;

        pvrtmp_15958 = pvrtmp_15949;
        pvrtmp_15959 = pvrtmp_15950;
        pvrtmp_15960 = pvrtmp_15951;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_15958);
        if (iters_pvrtmp_15958 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_restore_state();
            gib_ptr_bumpalloc_restore_state();
        }

        double itertime_38 = gib_difftimespecs(&begin_pvrtmp_15958,
                                               &end_pvrtmp_15958);

        printf("itertime: %lf\n", itertime_38);
        gib_vector_inplace_update(times_41, iters_pvrtmp_15958, &itertime_38);
    }
    gib_vector_inplace_sort(times_41, gib_compare_doubles);

    double *tmp_42 = (double *) gib_vector_nth(times_41, gib_get_iters_param() /
                                               2);
    double selftimed_40 = *tmp_42;
    double batchtime_39 = gib_sum_timing_array(times_41);

    gib_print_timing_array(times_41);
    gib_vector_free(times_41);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_39);
    printf("SELFTIMED: %e\n", selftimed_40);

    GibCursorGibCursorProd tmp_struct_43 =
                            check_buildquadtree(end_r_10788, vec1_745_6095_8630_9239, pvrtmp_15959);
    GibCursor pvrtmp_15968 = tmp_struct_43.field0;
    GibCursor pvrtmp_15969 = tmp_struct_43.field1;

    return 0;
}
unsigned char bench_seqnearest()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibVector *pts_143_4632_7569 =
              gib_vector_alloc(gib_read_arrayfile_length_param(),
                               sizeof(GibFloatGibFloatGibFloatProd));
    GibFloatGibFloatGibFloatProd arr_elem_61;

    FILE * fp_62;

    char *line_63 = NULL;

    size_t(len_64);
    len_64 = 0;
    ssize_t(read_65);
    fp_62 = fopen(gib_read_arrayfile_param(), "r");
    if (fp_62 == NULL) {
        fprintf(stderr, "fopen failed\n");
        abort();
    }

    GibFloat tmp_67;
    GibFloat tmp_68;
    GibFloat tmp_69;
    GibInt i_66 = 0;

    while ((read_65 = getline(&line_63, &len_64, fp_62)) != -1) {
        int xxxx = sscanf(line_63, "%f %f %f", &tmp_67, &tmp_68, &tmp_69);

        arr_elem_61.field0 = tmp_67;
        arr_elem_61.field1 = tmp_68;
        arr_elem_61.field2 = tmp_69;
        gib_vector_inplace_update(pts_143_4632_7569, i_66, &arr_elem_61);
        i_66++;
    }

    GibChunk region_15970 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_10794 = region_15970.start;
    GibCursor end_r_10794 = region_15970.end;
    GibCursorGibCursorGibCursorProd tmp_struct_54 =
                                     mkKdTree_seq(end_r_10794, r_10794, pts_143_4632_7569);
    GibCursor pvrtmp_15971 = tmp_struct_54.field0;
    GibCursor pvrtmp_15972 = tmp_struct_54.field1;
    GibCursor pvrtmp_15973 = tmp_struct_54.field2;
    GibVector *timed_15409;
    GibVector *times_59 = gib_vector_alloc(gib_get_iters_param(),
                                           sizeof(double));
    struct timespec begin_timed_15409;
    struct timespec end_timed_15409;

    for (long long iters_timed_15409 = 0; iters_timed_15409 <
         gib_get_iters_param(); iters_timed_15409++) {
        if (iters_timed_15409 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_save_state();
            gib_ptr_bumpalloc_save_state();
        }
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed_15409);

        GibCursorGibVectorProd tmp_struct_55 =
                                allNearest_seq(pvrtmp_15971, pvrtmp_15972, pts_143_4632_7569);
        GibCursor pvrtmp_15978 = tmp_struct_55.field0;
        GibVector *pvrtmp_15979 = tmp_struct_55.field1;

        timed_15409 = pvrtmp_15979;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed_15409);
        if (iters_timed_15409 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_restore_state();
            gib_ptr_bumpalloc_restore_state();
        }

        double itertime_56 = gib_difftimespecs(&begin_timed_15409,
                                               &end_timed_15409);

        printf("itertime: %lf\n", itertime_56);
        gib_vector_inplace_update(times_59, iters_timed_15409, &itertime_56);
    }
    gib_vector_inplace_sort(times_59, gib_compare_doubles);

    double *tmp_60 = (double *) gib_vector_nth(times_59, gib_get_iters_param() /
                                               2);
    double selftimed_58 = *tmp_60;
    double batchtime_57 = gib_sum_timing_array(times_59);

    gib_print_timing_array(times_59);
    gib_vector_free(times_59);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_57);
    printf("SELFTIMED: %e\n", selftimed_58);

    unsigned char tailapp_11938 =
                   check_nearest(pts_143_4632_7569, timed_15409);

    return tailapp_11938;
}
unsigned char bench_seqcountcorr()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibVector *pts_146_4635_7572 =
              gib_vector_alloc(gib_read_arrayfile_length_param(),
                               sizeof(GibFloatGibFloatGibFloatProd));
    GibFloatGibFloatGibFloatProd arr_elem_79;

    FILE * fp_80;

    char *line_81 = NULL;

    size_t(len_82);
    len_82 = 0;
    ssize_t(read_83);
    fp_80 = fopen(gib_read_arrayfile_param(), "r");
    if (fp_80 == NULL) {
        fprintf(stderr, "fopen failed\n");
        abort();
    }

    GibFloat tmp_85;
    GibFloat tmp_86;
    GibFloat tmp_87;
    GibInt i_84 = 0;

    while ((read_83 = getline(&line_81, &len_82, fp_80)) != -1) {
        int xxxx = sscanf(line_81, "%f %f %f", &tmp_85, &tmp_86, &tmp_87);

        arr_elem_79.field0 = tmp_85;
        arr_elem_79.field1 = tmp_86;
        arr_elem_79.field2 = tmp_87;
        gib_vector_inplace_update(pts_146_4635_7572, i_84, &arr_elem_79);
        i_84++;
    }

    GibInt n_147_4636_7573 = gib_get_size_param();
    GibChunk region_15980 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_10800 = region_15980.start;
    GibCursor end_r_10800 = region_15980.end;
    GibCursorGibCursorGibCursorProd tmp_struct_70 =
                                     mkKdTree_seq(end_r_10800, r_10800, pts_146_4635_7572);
    GibCursor pvrtmp_15981 = tmp_struct_70.field0;
    GibCursor pvrtmp_15982 = tmp_struct_70.field1;
    GibCursor pvrtmp_15983 = tmp_struct_70.field2;
    GibVector *pts__150_4639_7579 = gib_vector_slice(0, n_147_4636_7573,
                                                     pts_146_4635_7572);
    GibVector *timed_15410;
    GibVector *times_75 = gib_vector_alloc(gib_get_iters_param(),
                                           sizeof(double));
    struct timespec begin_timed_15410;
    struct timespec end_timed_15410;

    for (long long iters_timed_15410 = 0; iters_timed_15410 <
         gib_get_iters_param(); iters_timed_15410++) {
        if (iters_timed_15410 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_save_state();
            gib_ptr_bumpalloc_save_state();
        }
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed_15410);

        GibCursorGibVectorProd tmp_struct_71 =
                                allCountCorr_seq(pvrtmp_15981, 100.0, pvrtmp_15982, pts__150_4639_7579);
        GibCursor pvrtmp_15988 = tmp_struct_71.field0;
        GibVector *pvrtmp_15989 = tmp_struct_71.field1;

        timed_15410 = pvrtmp_15989;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed_15410);
        if (iters_timed_15410 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_restore_state();
            gib_ptr_bumpalloc_restore_state();
        }

        double itertime_72 = gib_difftimespecs(&begin_timed_15410,
                                               &end_timed_15410);

        printf("itertime: %lf\n", itertime_72);
        gib_vector_inplace_update(times_75, iters_timed_15410, &itertime_72);
    }
    gib_vector_inplace_sort(times_75, gib_compare_doubles);

    double *tmp_76 = (double *) gib_vector_nth(times_75, gib_get_iters_param() /
                                               2);
    double selftimed_74 = *tmp_76;
    double batchtime_73 = gib_sum_timing_array(times_75);

    gib_print_timing_array(times_75);
    gib_vector_free(times_75);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_73);
    printf("SELFTIMED: %e\n", selftimed_74);

    GibFloatGibFloatGibFloatProd *tmp_78;

    tmp_78 = (GibFloatGibFloatGibFloatProd *) gib_vector_nth(pts__150_4639_7579,
                                                             4);

    GibFloatGibFloatGibFloatProd query_152_4641_7583 = *tmp_78;
    GibInt *tmp_77;

    tmp_77 = (GibInt *) gib_vector_nth(timed_15410, 4);

    GibInt count_153_4642_7586 = *tmp_77;
    unsigned char tailapp_11940 =
                   check_countcorr(pts__150_4639_7579, (GibFloatGibFloatGibFloatProd) {query_152_4641_7583.field0, query_152_4641_7583.field1, query_152_4641_7583.field2}, count_153_4642_7586, 100.0);

    return tailapp_11940;
}
GibCursorGibCursorProd check_buildkdtree(GibCursor end_r_10655,
                                         GibVector *pts_154_4643_7587,
                                         GibCursor tr_155_4644_7588)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibFloat expected_156_4645_7589 =  sumList(pts_154_4643_7587);
    GibCursorGibCursorGibFloatProd tmp_struct_88 =
                                    sumKdTree(end_r_10655, tr_155_4644_7588);
    GibCursor pvrtmp_15993 = tmp_struct_88.field0;
    GibCursor pvrtmp_15994 = tmp_struct_88.field1;
    GibFloat pvrtmp_15995 = tmp_struct_88.field2;
    GibFloat err_158_4647_7591 = expected_156_4645_7589 - pvrtmp_15995;
    unsigned char wildcard__617_159_4648_7592 = gib_print_symbol(15843);
    unsigned char wildcard__615_160_4649_7593 = printf("%.2f",
                                                       expected_156_4645_7589);
    unsigned char wildcard__613_161_4650_7594 = gib_print_symbol(15864);
    unsigned char wildcard__611_162_4651_7595 = gib_print_symbol(15846);
    unsigned char wildcard__609_163_4652_7596 = printf("%.2f", pvrtmp_15995);
    unsigned char wildcard__607_164_4653_7597 = gib_print_symbol(15864);
    GibFloat fltPrm_7207_7598 =  float_abs(err_158_4647_7591);
    GibBool fltAppE_7206_7599 = fltPrm_7207_7598 < 0.1;
    unsigned char tailapp_11942 =  print_check(fltAppE_7206_7599);

    return (GibCursorGibCursorProd) {pvrtmp_15993, pvrtmp_15994};
}
GibCursorGibCursorGibCursorProd mkKdTree_seq(GibCursor end_r_10657,
                                             GibCursor loc_10656,
                                             GibVector *pts_165_4654_7600)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_10656 + 74 > end_r_10657) {
        gib_grow_region(&loc_10656, &end_r_10657);
    }

    GibCursorGibCursorGibCursorProd tmp_struct_89 =
                                     mkKdTreeWithAxis_seq(end_r_10657, loc_10656, 0, pts_165_4654_7600);
    GibCursor pvrtmp_15996 = tmp_struct_89.field0;
    GibCursor pvrtmp_15997 = tmp_struct_89.field1;
    GibCursor pvrtmp_15998 = tmp_struct_89.field2;

    return (GibCursorGibCursorGibCursorProd) {pvrtmp_15996, pvrtmp_15997,
                                              pvrtmp_15998};
}
unsigned char check_countcorr(GibVector *pts_166_4655_7601,
                              GibFloatGibFloatGibFloatProd query_167_4656_7602,
                              GibInt actual_168_4657_7603,
                              GibFloat radius_169_4658_7604)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibFloat radius_sq_170_4659_7605 = radius_169_4658_7604 *
             radius_169_4658_7604;
    GibInt fltAppE_7208_7610 = gib_vector_length(pts_166_4655_7601);
    GibInt expected_173_4660_7611 =
            foldl_loop_2369_3740(0, fltAppE_7208_7610, 0, pts_166_4655_7601, (GibFloatGibFloatGibFloatProd) {query_167_4656_7602.field0, query_167_4656_7602.field1, query_167_4656_7602.field2}, radius_sq_170_4659_7605);
    unsigned char wildcard__636_174_4661_7612 = gib_print_symbol(15843);
    unsigned char wildcard__634_175_4662_7613 = printf("%ld",
                                                       expected_173_4660_7611);
    unsigned char wildcard__632_176_4663_7614 = gib_print_symbol(15864);
    unsigned char wildcard__630_177_4664_7615 = gib_print_symbol(15846);
    unsigned char wildcard__628_178_4665_7616 = printf("%ld",
                                                       actual_168_4657_7603);
    unsigned char wildcard__626_179_4666_7617 = gib_print_symbol(15864);
    GibBool fltAppE_7209_7618 = expected_173_4660_7611 == actual_168_4657_7603;
    unsigned char tailapp_11944 =  print_check(fltAppE_7209_7618);

    return tailapp_11944;
}
GibCursorGibVectorProd allCountCorr_seq(GibCursor end_r_10659,
                                        GibFloat radius_183_4667_7619,
                                        GibCursor tr_184_4668_7620,
                                        GibVector *ls_185_4669_7621)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibInt fltAppE_7210_7625 = gib_vector_length(ls_185_4669_7621);
    GibInt n__743_6039_8560_9244 =  maxInt(fltAppE_7210_7625, 0);
    GibInt tmp_94 = sizeof(GibInt);
    GibVector *vec_744_6040_8561_9245 = gib_vector_alloc(n__743_6039_8560_9244,
                                                         tmp_94);
    GibCursorGibVectorProd tmp_struct_93 =
                            generate_loop_2374_3723(end_r_10659, vec_744_6040_8561_9245, 0, n__743_6039_8560_9244, ls_185_4669_7621, radius_183_4667_7619, tr_184_4668_7620);
    GibCursor pvrtmp_16008 = tmp_struct_93.field0;
    GibVector *pvrtmp_16009 = tmp_struct_93.field1;

    return (GibCursorGibVectorProd) {pvrtmp_16008, pvrtmp_16009};
}
unsigned char check_nearest(GibVector *pts_191_4670_7626,
                            GibVector *actual_192_4671_7627)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibInt n_193_4672_7629 = gib_vector_length(pts_191_4670_7626);
    GibInt n__743_5993_6642_7631 =  maxInt(n_193_4672_7629, 0);
    GibInt tmp_96 = sizeof(GibInt);
    GibVector *vec_744_5994_6643_7632 = gib_vector_alloc(n__743_5993_6642_7631,
                                                         tmp_96);
    GibVector *vec1_745_5995_6644_7633 =
               generate_loop_2374_3714(vec_744_5994_6643_7632, 0, n__743_5993_6642_7631);
    GibInt fltAppE_7212_7640 = gib_vector_length(vec1_745_5995_6644_7633);
    GibBoolGibIntProd tmp_struct_95 =
                       foldl_loop_2367_3749(0, fltAppE_7212_7640, (GibBoolGibIntProd) {true, 0}, vec1_745_5995_6644_7633, pts_191_4670_7626, actual_192_4671_7627);
    GibBool pvrtmp_16014 = tmp_struct_95.field0;
    GibInt pvrtmp_16015 = tmp_struct_95.field1;
    unsigned char tailapp_11945 =  print_check(pvrtmp_16014);

    return tailapp_11945;
}
GibCursorGibVectorProd allNearest_seq(GibCursor end_r_10661,
                                      GibCursor tr_207_4678_7645,
                                      GibVector *ls_208_4679_7646)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibInt fltAppE_7213_7649 = gib_vector_length(ls_208_4679_7646);
    GibInt n__743_6022_8540_9250 =  maxInt(fltAppE_7213_7649, 0);
    GibInt tmp_98 = sizeof(GibFloatGibFloatGibFloatProd);
    GibVector *vec_744_6023_8541_9251 = gib_vector_alloc(n__743_6022_8540_9250,
                                                         tmp_98);
    GibCursorGibVectorProd tmp_struct_97 =
                            generate_loop_2376_3720(end_r_10661, vec_744_6023_8541_9251, 0, n__743_6022_8540_9250, ls_208_4679_7646, tr_207_4678_7645);
    GibCursor pvrtmp_16016 = tmp_struct_97.field0;
    GibVector *pvrtmp_16017 = tmp_struct_97.field1;

    return (GibCursorGibVectorProd) {pvrtmp_16016, pvrtmp_16017};
}
GibCursorGibCursorProd check_buildquadtree(GibCursor end_r_10663,
                                           GibVector *mpts_210_4680_7650,
                                           GibCursor bht_211_4681_7651)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibFloat expected_212_4682_7652 =  sum_mass_points(mpts_210_4680_7650);
    GibCursorGibCursorGibFloatProd tmp_struct_99 =
                                    sumQtree(end_r_10663, bht_211_4681_7651);
    GibCursor pvrtmp_16018 = tmp_struct_99.field0;
    GibCursor pvrtmp_16019 = tmp_struct_99.field1;
    GibFloat pvrtmp_16020 = tmp_struct_99.field2;
    GibCursorGibCursorGibIntProd tmp_struct_100 =
                                  countLeavesQtree(end_r_10663, bht_211_4681_7651);
    GibCursor pvrtmp_16021 = tmp_struct_100.field0;
    GibCursor pvrtmp_16022 = tmp_struct_100.field1;
    GibInt pvrtmp_16023 = tmp_struct_100.field2;
    GibCursorGibIntProd tmp_struct_101 =
                         getTotalPoints_qtree(end_r_10663, bht_211_4681_7651);
    GibCursor pvrtmp_16024 = tmp_struct_101.field0;
    GibInt pvrtmp_16025 = tmp_struct_101.field1;
    unsigned char wildcard__424_216_4686_7656 = gib_print_symbol(15841);
    unsigned char wildcard__422_217_4687_7657 = printf("%.2f",
                                                       expected_212_4682_7652);
    unsigned char wildcard__420_218_4688_7658 = gib_print_symbol(15847);
    unsigned char wildcard__418_219_4689_7659 = gib_print_symbol(15840);
    unsigned char wildcard__416_220_4690_7660 = printf("%.2f", pvrtmp_16020);
    unsigned char wildcard__414_221_4691_7661 = gib_print_symbol(15864);
    unsigned char wildcard__412_222_4692_7662 = gib_print_symbol(15845);
    unsigned char wildcard__410_223_4693_7663 = printf("%ld", pvrtmp_16023);
    unsigned char wildcard__408_224_4694_7664 = gib_print_symbol(15847);
    unsigned char wildcard__406_225_4695_7665 = printf("%ld", pvrtmp_16025);
    unsigned char wildcard__404_226_4696_7666 = gib_print_symbol(15864);
    GibFloat fltAppE_7216_7667 = expected_212_4682_7652 - pvrtmp_16020;
    GibFloat fltPrm_7215_7668 =  float_abs(fltAppE_7216_7667);
    GibBool fltAppE_7214_7669 = fltPrm_7215_7668 < 1.0e-2;
    unsigned char tailapp_11948 =  print_check(fltAppE_7214_7669);

    return (GibCursorGibCursorProd) {pvrtmp_16024, pvrtmp_16022};
}
GibCursorGibCursorGibCursorProd buildQtree_seq(GibCursor end_r_10665,
                                               GibCursor loc_10664,
                                               GibFloatGibFloatGibFloatGibFloatProd box_227_4697_7670,
                                               GibVector *mpts_228_4698_7671)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_10664 + 58 > end_r_10665) {
        gib_grow_region(&loc_10664, &end_r_10665);
    }

    GibInt len_229_4699_7673 = gib_vector_length(mpts_228_4698_7671);
    GibBool fltIf_7217_7679 = len_229_4699_7673 == 0;

    if (fltIf_7217_7679) {
        *(GibPackedTag *) loc_10664 = 0;

        GibCursor writetag_13599 = loc_10664 + 1;
        GibCursor after_tag_13600 = loc_10664 + 1;

        return (GibCursorGibCursorGibCursorProd) {end_r_10665, loc_10664,
                                                  after_tag_13600};
    } else {
        GibBool fltIf_7218_7680 = len_229_4699_7673 == 1;

        if (fltIf_7218_7680) {
            GibFloatGibFloatGibFloatProd tmp_struct_102 =
                                          calcCentroid_seq(mpts_228_4698_7671);
            GibFloat pvrtmp_16030 = tmp_struct_102.field0;
            GibFloat pvrtmp_16031 = tmp_struct_102.field1;
            GibFloat pvrtmp_16032 = tmp_struct_102.field2;

            *(GibPackedTag *) loc_10664 = 1;

            GibCursor writetag_13606 = loc_10664 + 1;
            GibCursor after_tag_13607 = loc_10664 + 1;

            *(GibFloat *) after_tag_13607 = pvrtmp_16030;

            GibCursor writecur_13611 = after_tag_13607 + sizeof(GibFloat);

            *(GibFloat *) writecur_13611 = pvrtmp_16031;

            GibCursor writecur_13612 = writecur_13611 + sizeof(GibFloat);

            *(GibFloat *) writecur_13612 = pvrtmp_16032;

            GibCursor writecur_13613 = writecur_13612 + sizeof(GibFloat);

            return (GibCursorGibCursorGibCursorProd) {end_r_10665, loc_10664,
                                                      writecur_13613};
        } else {
            GibFloatGibFloatGibFloatProd tmp_struct_103 =
                                          calcCentroid_seq(mpts_228_4698_7671);
            GibFloat pvrtmp_16037 = tmp_struct_103.field0;
            GibFloat pvrtmp_16038 = tmp_struct_103.field1;
            GibFloat pvrtmp_16039 = tmp_struct_103.field2;
            GibFloat fltPrm_7219_7686 = box_227_4697_7670.field0 +
                     box_227_4697_7670.field2;
            GibFloat midx_240_4710_7687 = fltPrm_7219_7686 / 2.0;
            GibFloat fltPrm_7220_7688 = box_227_4697_7670.field1 +
                     box_227_4697_7670.field3;
            GibFloat midy_241_4711_7689 = fltPrm_7220_7688 / 2.0;
            GibVector *p1_246_4716_7694 =
                       masspointsInBox_seq((GibFloatGibFloatGibFloatGibFloatProd) {box_227_4697_7670.field0, box_227_4697_7670.field1, midx_240_4710_7687, midy_241_4711_7689}, mpts_228_4698_7671);
            GibCursor loc_10849 = loc_10664 + 49;

            *(GibPackedTag *) loc_10664 = 3;

            GibCursor writetag_13632 = loc_10664 + 1;
            GibCursorGibCursorGibCursorProd tmp_struct_104 =
                                             buildQtree_seq(end_r_10665, loc_10849, (GibFloatGibFloatGibFloatGibFloatProd) {box_227_4697_7670.field0, box_227_4697_7670.field1, midx_240_4710_7687, midy_241_4711_7689}, p1_246_4716_7694);
            GibCursor pvrtmp_16064 = tmp_struct_104.field0;
            GibCursor pvrtmp_16065 = tmp_struct_104.field1;
            GibCursor pvrtmp_16066 = tmp_struct_104.field2;
            GibVector *p2_248_4718_7696 =
                       masspointsInBox_seq((GibFloatGibFloatGibFloatGibFloatProd) {box_227_4697_7670.field0, midy_241_4711_7689, midx_240_4710_7687, box_227_4697_7670.field3}, mpts_228_4698_7671);
            GibCursorGibCursorGibCursorProd tmp_struct_105 =
                                             buildQtree_seq(pvrtmp_16064, pvrtmp_16066, (GibFloatGibFloatGibFloatGibFloatProd) {box_227_4697_7670.field0, midy_241_4711_7689, midx_240_4710_7687, box_227_4697_7670.field3}, p2_248_4718_7696);
            GibCursor pvrtmp_16079 = tmp_struct_105.field0;
            GibCursor pvrtmp_16080 = tmp_struct_105.field1;
            GibCursor pvrtmp_16081 = tmp_struct_105.field2;
            GibVector *p3_250_4720_7698 =
                       masspointsInBox_seq((GibFloatGibFloatGibFloatGibFloatProd) {midx_240_4710_7687, midy_241_4711_7689, box_227_4697_7670.field2, box_227_4697_7670.field3}, mpts_228_4698_7671);
            GibCursorGibCursorGibCursorProd tmp_struct_106 =
                                             buildQtree_seq(pvrtmp_16079, pvrtmp_16081, (GibFloatGibFloatGibFloatGibFloatProd) {midx_240_4710_7687, midy_241_4711_7689, box_227_4697_7670.field2, box_227_4697_7670.field3}, p3_250_4720_7698);
            GibCursor pvrtmp_16094 = tmp_struct_106.field0;
            GibCursor pvrtmp_16095 = tmp_struct_106.field1;
            GibCursor pvrtmp_16096 = tmp_struct_106.field2;
            GibVector *p4_252_4722_7700 =
                       masspointsInBox_seq((GibFloatGibFloatGibFloatGibFloatProd) {midx_240_4710_7687, box_227_4697_7670.field1, box_227_4697_7670.field2, midy_241_4711_7689}, mpts_228_4698_7671);
            GibCursorGibCursorGibCursorProd tmp_struct_107 =
                                             buildQtree_seq(pvrtmp_16094, pvrtmp_16096, (GibFloatGibFloatGibFloatGibFloatProd) {midx_240_4710_7687, box_227_4697_7670.field1, box_227_4697_7670.field2, midy_241_4711_7689}, p4_252_4722_7700);
            GibCursor pvrtmp_16109 = tmp_struct_107.field0;
            GibCursor pvrtmp_16110 = tmp_struct_107.field1;
            GibCursor pvrtmp_16111 = tmp_struct_107.field2;
            GibCursorGibIntProd tmp_struct_108 =
                                 getTotalPoints_qtree(pvrtmp_16109, pvrtmp_16065);
            GibCursor pvrtmp_16116 = tmp_struct_108.field0;
            GibInt pvrtmp_16117 = tmp_struct_108.field1;
            GibCursorGibIntProd tmp_struct_109 =
                                 getTotalPoints_qtree(pvrtmp_16116, pvrtmp_16080);
            GibCursor pvrtmp_16118 = tmp_struct_109.field0;
            GibInt pvrtmp_16119 = tmp_struct_109.field1;
            GibInt fltPrm_7222_7704 = pvrtmp_16117 + pvrtmp_16119;
            GibCursorGibIntProd tmp_struct_110 =
                                 getTotalPoints_qtree(pvrtmp_16118, pvrtmp_16095);
            GibCursor pvrtmp_16120 = tmp_struct_110.field0;
            GibInt pvrtmp_16121 = tmp_struct_110.field1;
            GibInt fltPrm_7221_7706 = fltPrm_7222_7704 + pvrtmp_16121;
            GibCursorGibIntProd tmp_struct_111 =
                                 getTotalPoints_qtree(pvrtmp_16120, pvrtmp_16110);
            GibCursor pvrtmp_16122 = tmp_struct_111.field0;
            GibInt pvrtmp_16123 = tmp_struct_111.field1;
            GibInt total_points_254_4724_7708 = fltPrm_7221_7706 + pvrtmp_16123;
            GibFloat fltAppE_7227_7715 = box_227_4697_7670.field2 -
                     box_227_4697_7670.field0;
            GibFloat fltAppE_7228_7716 = box_227_4697_7670.field3 -
                     box_227_4697_7670.field1;
            GibFloat width_255_4725_7717 =
                      maxFloat(fltAppE_7227_7715, fltAppE_7228_7716);
            uint16_t offset_114 = pvrtmp_16064 - pvrtmp_16066;
            uintptr_t ran_10522 = GIB_STORE_TAG(pvrtmp_16066, offset_114);
            uint16_t offset_113 = pvrtmp_16079 - pvrtmp_16081;
            uintptr_t ran_10523 = GIB_STORE_TAG(pvrtmp_16081, offset_113);
            uint16_t offset_112 = pvrtmp_16094 - pvrtmp_16096;
            uintptr_t ran_10524 = GIB_STORE_TAG(pvrtmp_16096, offset_112);
            GibCursor after_tag_13633 = loc_10664 + 1;

            *(uintptr_t *) after_tag_13633 = ran_10522;

            GibCursor writecur_13637 = after_tag_13633 + 8;

            *(uintptr_t *) writecur_13637 = ran_10523;

            GibCursor writecur_13638 = writecur_13637 + 8;

            *(uintptr_t *) writecur_13638 = ran_10524;

            GibCursor writecur_13639 = writecur_13638 + 8;

            *(GibFloat *) writecur_13639 = pvrtmp_16037;

            GibCursor writecur_13640 = writecur_13639 + sizeof(GibFloat);

            *(GibFloat *) writecur_13640 = pvrtmp_16038;

            GibCursor writecur_13641 = writecur_13640 + sizeof(GibFloat);

            *(GibFloat *) writecur_13641 = pvrtmp_16039;

            GibCursor writecur_13642 = writecur_13641 + sizeof(GibFloat);

            *(GibInt *) writecur_13642 = total_points_254_4724_7708;

            GibCursor writecur_13643 = writecur_13642 + sizeof(GibInt);

            *(GibFloat *) writecur_13643 = width_255_4725_7717;

            GibCursor writecur_13644 = writecur_13643 + sizeof(GibFloat);

            return (GibCursorGibCursorGibCursorProd) {pvrtmp_16120, loc_10664,
                                                      pvrtmp_16111};
        }
    }
}
GibFloat maxFloat(GibFloat a_265_4730_7722, GibFloat b_266_4731_7723)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_7229_7724 = a_265_4730_7722 > b_266_4731_7723;

    if (fltIf_7229_7724) {
        return a_265_4730_7722;
    } else {
        return b_266_4731_7723;
    }
}
GibFloat minFloat(GibFloat a_267_4732_7725, GibFloat b_268_4733_7726)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_7230_7727 = a_267_4732_7725 < b_268_4733_7726;

    if (fltIf_7230_7727) {
        return a_267_4732_7725;
    } else {
        return b_268_4733_7726;
    }
}
GibCursorGibVectorProd oneStep_seq(GibCursor end_r_10667,
                                   GibCursor bht_274_4734_7728,
                                   GibVector *mpts_275_4735_7729,
                                   GibVector *ps_276_4736_7730)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibCursor pvrtmp_16130;
    GibVector *pvrtmp_16131;
    GibVector *times_123 = gib_vector_alloc(gib_get_iters_param(),
                                            sizeof(double));
    struct timespec begin_pvrtmp_16130;
    struct timespec end_pvrtmp_16130;

    for (long long iters_pvrtmp_16130 = 0; iters_pvrtmp_16130 <
         gib_get_iters_param(); iters_pvrtmp_16130++) {
        if (iters_pvrtmp_16130 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_save_state();
            gib_ptr_bumpalloc_save_state();
        }
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_16130);

        GibInt n_740_5698_6659_7732 = gib_vector_length(ps_276_4736_7730);
        GibInt n__743_5702_6663_7736 =  maxInt(n_740_5698_6659_7732, 0);
        GibInt tmp_119 = sizeof(GibFloatGibFloatGibFloatGibFloatGibFloatProd);
        GibVector *vec_744_5703_6664_7737 =
                  gib_vector_alloc(n__743_5702_6663_7736, tmp_119);
        GibCursorGibVectorProd tmp_struct_118 =
                                generate_loop_2377_3710(end_r_10667, vec_744_5703_6664_7737, 0, n__743_5702_6663_7736, bht_274_4734_7728, mpts_275_4735_7729, ps_276_4736_7730);
        GibCursor pvrtmp_16128 = tmp_struct_118.field0;
        GibVector *pvrtmp_16129 = tmp_struct_118.field1;

        pvrtmp_16130 = pvrtmp_16128;
        pvrtmp_16131 = pvrtmp_16129;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_16130);
        if (iters_pvrtmp_16130 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_restore_state();
            gib_ptr_bumpalloc_restore_state();
        }

        double itertime_120 = gib_difftimespecs(&begin_pvrtmp_16130,
                                                &end_pvrtmp_16130);

        printf("itertime: %lf\n", itertime_120);
        gib_vector_inplace_update(times_123, iters_pvrtmp_16130, &itertime_120);
    }
    gib_vector_inplace_sort(times_123, gib_compare_doubles);

    double *tmp_124 = (double *) gib_vector_nth(times_123,
                                                gib_get_iters_param() / 2);
    double selftimed_122 = *tmp_124;
    double batchtime_121 = gib_sum_timing_array(times_123);

    gib_print_timing_array(times_123);
    gib_vector_free(times_123);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_121);
    printf("SELFTIMED: %e\n", selftimed_122);
    return (GibCursorGibVectorProd) {end_r_10667, pvrtmp_16131};
}
GibCursorGibCursorGibIntProd sumExp(GibCursor end_r_10669,
                                    GibCursor exp_282_4738_7740)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_16134 = *(GibPackedTag *) exp_282_4738_7740;
    GibCursor tmpcur_16135 = exp_282_4738_7740 + 1;


  switch_16156:
    ;
    switch (tmpval_16134) {

      case 0:
        {
            GibInt tmpval_16136 = *(GibInt *) tmpcur_16135;
            GibCursor tmpcur_16137 = tmpcur_16135 + sizeof(GibInt);
            GibCursor jump_11952 = tmpcur_16135 + 8;

            return (GibCursorGibCursorGibIntProd) {end_r_10669, jump_11952,
                                                   tmpval_16136};
            break;
        }

      case 3:
        {
            GibCursorGibCursorGibIntProd tmp_struct_125 =
                                          sumExp(end_r_10669, tmpcur_16135);
            GibCursor pvrtmp_16138 = tmp_struct_125.field0;
            GibCursor pvrtmp_16139 = tmp_struct_125.field1;
            GibInt pvrtmp_16140 = tmp_struct_125.field2;
            GibCursorGibCursorGibIntProd tmp_struct_126 =
                                          sumExp(pvrtmp_16138, pvrtmp_16139);
            GibCursor pvrtmp_16141 = tmp_struct_126.field0;
            GibCursor pvrtmp_16142 = tmp_struct_126.field1;
            GibInt pvrtmp_16143 = tmp_struct_126.field2;
            GibInt tailprim_11955 = pvrtmp_16140 + pvrtmp_16143;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_16141, pvrtmp_16142,
                                                   tailprim_11955};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_128 = *(uintptr_t *) tmpcur_16135;
            GibCursor tmpcur_16144 = GIB_UNTAG(tagged_tmpcur_128);
            GibCursor tmpaftercur_16145 = tmpcur_16135 + 8;
            uint16_t tmptag_16146 = GIB_GET_TAG(tagged_tmpcur_128);
            GibCursor end_from_tagged_indr_12533 = tmpcur_16144 + tmptag_16146;
            GibCursor jump_12535 = tmpcur_16135 + 8;
            GibCursorGibCursorGibIntProd tmp_struct_127 =
                                          sumExp(end_from_tagged_indr_12533, tmpcur_16144);
            GibCursor pvrtmp_16147 = tmp_struct_127.field0;
            GibCursor pvrtmp_16148 = tmp_struct_127.field1;
            GibInt pvrtmp_16149 = tmp_struct_127.field2;

            return (GibCursorGibCursorGibIntProd) {end_r_10669, jump_12535,
                                                   pvrtmp_16149};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_130 = *(uintptr_t *) tmpcur_16135;
            GibCursor tmpcur_16150 = GIB_UNTAG(tagged_tmpcur_130);
            GibCursor tmpaftercur_16151 = tmpcur_16135 + 8;
            uint16_t tmptag_16152 = GIB_GET_TAG(tagged_tmpcur_130);
            GibCursor end_from_tagged_indr_12533 = tmpcur_16150 + tmptag_16152;
            GibCursorGibCursorGibIntProd tmp_struct_129 =
                                          sumExp(end_from_tagged_indr_12533, tmpcur_16150);
            GibCursor pvrtmp_16153 = tmp_struct_129.field0;
            GibCursor pvrtmp_16154 = tmp_struct_129.field1;
            GibInt pvrtmp_16155 = tmp_struct_129.field2;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_16153, pvrtmp_16154,
                                                   pvrtmp_16155};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_16134");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd foldConstants2(GibCursor end_r_10672,
                                                                 GibCursor end_r_10673,
                                                                 GibCursor loc_10671,
                                                                 GibCursor exp_286_4742_7746)
{
    // GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    // GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    // GibShadowstackFrame *frame;

    if (loc_10671 + 18 > end_r_10673) {
        gib_grow_region(&loc_10671, &end_r_10673);
    }

    GibPackedTag tmpval_16157 = *(GibPackedTag *) exp_286_4742_7746;
    GibCursor tmpcur_16158 = exp_286_4742_7746 + 1;


  switch_16254:
    ;
    switch (tmpval_16157) {

      case 0:
        {
            GibInt tmpval_16159 = *(GibInt *) tmpcur_16158;
            GibCursor tmpcur_16160 = tmpcur_16158 + sizeof(GibInt);
            GibCursor jump_11956 = tmpcur_16158 + 8;

            *(GibPackedTag *) loc_10671 = 0;

            GibCursor writetag_13674 = loc_10671 + 1;
            GibCursor after_tag_13675 = loc_10671 + 1;

            *(GibInt *) after_tag_13675 = tmpval_16159;

            GibCursor writecur_13679 = after_tag_13675 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_10672,
                                                                        end_r_10673,
                                                                        jump_11956,
                                                                        loc_10671,
                                                                        writecur_13679};
            break;
        }

      case 1:
        {
            GibCursor jump_11958 = exp_286_4742_7746 + 1;

            *(GibPackedTag *) loc_10671 = 1;

            GibCursor writetag_13683 = loc_10671 + 1;
            GibCursor after_tag_13684 = loc_10671 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_10672,
                                                                        end_r_10673,
                                                                        jump_11958,
                                                                        loc_10671,
                                                                        after_tag_13684};
            break;
        }

      case 2:
        {
            GibCursor jump_11960 = exp_286_4742_7746 + 1;

            *(GibPackedTag *) loc_10671 = 2;

            GibCursor writetag_13691 = loc_10671 + 1;
            GibCursor after_tag_13692 = loc_10671 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_10672,
                                                                        end_r_10673,
                                                                        jump_11960,
                                                                        loc_10671,
                                                                        after_tag_13692};
            break;
        }

      case 3:
        {
            GibCursorGibFloatProd tmp_struct_131 =
                                   maybeLit(end_r_10672, tmpcur_16158);
            GibCursor pvrtmp_16173 = tmp_struct_131.field0;
            GibFloat pvrtmp_16174 = tmp_struct_131.field1;
            GibFloat fltPrm_7236_7752 = 0.0 - 3.14;
            GibFloat fltPrm_7235_7753 = pvrtmp_16174 - fltPrm_7236_7752;
            GibBool fltIf_7234_7754 = fltPrm_7235_7753 < 1.0e-2;
            GibBool fltIf_7233_7755;

            if (fltIf_7234_7754) {
                fltIf_7233_7755 = false;
            } else {
                fltIf_7233_7755 = true;
            }
            if (fltIf_7233_7755) {
                GibCursorGibCursorProd tmp_struct_132 =
                                        trav_exp(end_r_10672, tmpcur_16158);
                GibCursor pvrtmp_16177 = tmp_struct_132.field0;
                GibCursor pvrtmp_16178 = tmp_struct_132.field1;
                GibCursorGibFloatProd tmp_struct_133 =
                                       maybeLit(pvrtmp_16177, pvrtmp_16178);
                GibCursor pvrtmp_16179 = tmp_struct_133.field0;
                GibFloat pvrtmp_16180 = tmp_struct_133.field1;
                GibFloat fltPrm_7240_7759 = 0.0 - 3.14;
                GibFloat fltPrm_7239_7760 = pvrtmp_16180 - fltPrm_7240_7759;
                GibBool fltIf_7238_7761 = fltPrm_7239_7760 < 1.0e-2;
                GibBool fltIf_7237_7762;

                if (fltIf_7238_7761) {
                    fltIf_7237_7762 = false;
                } else {
                    fltIf_7237_7762 = true;
                }
                if (fltIf_7237_7762) {
                    GibCursorGibCursorProd tmp_struct_134 =
                                            trav_exp(pvrtmp_16177, pvrtmp_16178);
                    GibCursor pvrtmp_16183 = tmp_struct_134.field0;
                    GibCursor pvrtmp_16184 = tmp_struct_134.field1;
                    GibInt fltPrm_7242_7764 = (GibInt) pvrtmp_16174;
                    GibInt fltPrm_7243_7765 = (GibInt) pvrtmp_16180;
                    GibInt fltPkd_7241_7766 = fltPrm_7242_7764 +
                           fltPrm_7243_7765;

                    *(GibPackedTag *) loc_10671 = 0;

                    GibCursor writetag_13707 = loc_10671 + 1;
                    GibCursor after_tag_13708 = loc_10671 + 1;

                    *(GibInt *) after_tag_13708 = fltPkd_7241_7766;

                    GibCursor writecur_13712 = after_tag_13708 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_16183,
                                                                                end_r_10673,
                                                                                pvrtmp_16184,
                                                                                loc_10671,
                                                                                writecur_13712};
                } else {
                    GibInt fltPkd_7244_7767 = (GibInt) pvrtmp_16174;
                    GibCursor loc_10912 = loc_10671 + 1;

                    *(GibPackedTag *) loc_10671 = 3;

                    GibCursor writetag_13726 = loc_10671 + 1;

                    *(GibPackedTag *) loc_10912 = 0;

                    GibCursor writetag_13715 = loc_10912 + 1;
                    GibCursor after_tag_13716 = loc_10912 + 1;

                    *(GibInt *) after_tag_13716 = fltPkd_7244_7767;

                    GibCursor writecur_13720 = after_tag_13716 + sizeof(GibInt);
                    GibCursorGibCursorGibCursorGibCursorGibCursorProd
                    tmp_struct_135 =
                     foldConstants2(pvrtmp_16177, end_r_10673, writecur_13720, pvrtmp_16178);
                    GibCursor pvrtmp_16191 = tmp_struct_135.field0;
                    GibCursor pvrtmp_16192 = tmp_struct_135.field1;
                    GibCursor pvrtmp_16193 = tmp_struct_135.field2;
                    GibCursor pvrtmp_16194 = tmp_struct_135.field3;
                    GibCursor pvrtmp_16195 = tmp_struct_135.field4;
                    GibCursor after_tag_13727 = loc_10671 + 1;

                    return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_16191,
                                                                                pvrtmp_16192,
                                                                                pvrtmp_16193,
                                                                                loc_10671,
                                                                                pvrtmp_16195};
                }
            } else {
                GibCursor loc_10912 = loc_10671 + 1;

                *(GibPackedTag *) loc_10671 = 3;

                GibCursor writetag_13742 = loc_10671 + 1;
                GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_136
                                                                  =
                                                                   foldConstants2(end_r_10672, end_r_10673, loc_10912, tmpcur_16158);
                GibCursor pvrtmp_16204 = tmp_struct_136.field0;
                GibCursor pvrtmp_16205 = tmp_struct_136.field1;
                GibCursor pvrtmp_16206 = tmp_struct_136.field2;
                GibCursor pvrtmp_16207 = tmp_struct_136.field3;
                GibCursor pvrtmp_16208 = tmp_struct_136.field4;
                GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_137
                                                                  =
                                                                   foldConstants2(pvrtmp_16204, pvrtmp_16205, pvrtmp_16208, pvrtmp_16206);
                GibCursor pvrtmp_16213 = tmp_struct_137.field0;
                GibCursor pvrtmp_16214 = tmp_struct_137.field1;
                GibCursor pvrtmp_16215 = tmp_struct_137.field2;
                GibCursor pvrtmp_16216 = tmp_struct_137.field3;
                GibCursor pvrtmp_16217 = tmp_struct_137.field4;
                GibCursor after_tag_13743 = loc_10671 + 1;

                return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_16213,
                                                                            pvrtmp_16214,
                                                                            pvrtmp_16215,
                                                                            loc_10671,
                                                                            pvrtmp_16217};
            }
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_139 = *(uintptr_t *) tmpcur_16158;
            GibCursor tmpcur_16226 = GIB_UNTAG(tagged_tmpcur_139);
            GibCursor tmpaftercur_16227 = tmpcur_16158 + 8;
            uint16_t tmptag_16228 = GIB_GET_TAG(tagged_tmpcur_139);
            GibCursor end_from_tagged_indr_12539 = tmpcur_16226 + tmptag_16228;
            GibCursor jump_12541 = tmpcur_16158 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_138 =
                                                               foldConstants2(end_from_tagged_indr_12539, end_r_10673, loc_10671, tmpcur_16226);
            GibCursor pvrtmp_16229 = tmp_struct_138.field0;
            GibCursor pvrtmp_16230 = tmp_struct_138.field1;
            GibCursor pvrtmp_16231 = tmp_struct_138.field2;
            GibCursor pvrtmp_16232 = tmp_struct_138.field3;
            GibCursor pvrtmp_16233 = tmp_struct_138.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_10672,
                                                                        pvrtmp_16230,
                                                                        jump_12541,
                                                                        pvrtmp_16232,
                                                                        pvrtmp_16233};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_141 = *(uintptr_t *) tmpcur_16158;
            GibCursor tmpcur_16240 = GIB_UNTAG(tagged_tmpcur_141);
            GibCursor tmpaftercur_16241 = tmpcur_16158 + 8;
            uint16_t tmptag_16242 = GIB_GET_TAG(tagged_tmpcur_141);
            GibCursor end_from_tagged_indr_12539 = tmpcur_16240 + tmptag_16242;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_140 =
                                                               foldConstants2(end_from_tagged_indr_12539, end_r_10673, loc_10671, tmpcur_16240);
            GibCursor pvrtmp_16243 = tmp_struct_140.field0;
            GibCursor pvrtmp_16244 = tmp_struct_140.field1;
            GibCursor pvrtmp_16245 = tmp_struct_140.field2;
            GibCursor pvrtmp_16246 = tmp_struct_140.field3;
            GibCursor pvrtmp_16247 = tmp_struct_140.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_16243,
                                                                        pvrtmp_16244,
                                                                        pvrtmp_16245,
                                                                        pvrtmp_16246,
                                                                        pvrtmp_16247};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_16157");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorProd buildExp(GibCursor end_r_10675,
                                         GibCursor loc_10674,
                                         GibInt n_298_4754_7772)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_10674 + 18 > end_r_10675) {
        gib_grow_region(&loc_10674, &end_r_10675);
    }

    GibBool fltIf_7245_7773 = n_298_4754_7772 == 0;

    if (fltIf_7245_7773) {
        GibCursor loc_10930 = loc_10674 + 1;

        *(GibPackedTag *) loc_10674 = 3;

        GibCursor writetag_13778 = loc_10674 + 1;

        *(GibPackedTag *) loc_10930 = 0;

        GibCursor writetag_13762 = loc_10930 + 1;
        GibCursor after_tag_13763 = loc_10930 + 1;

        *(GibInt *) after_tag_13763 = 0;

        GibCursor writecur_13767 = after_tag_13763 + sizeof(GibInt);

        *(GibPackedTag *) writecur_13767 = 0;

        GibCursor writetag_13770 = writecur_13767 + 1;
        GibCursor after_tag_13771 = writecur_13767 + 1;

        *(GibInt *) after_tag_13771 = 1;

        GibCursor writecur_13775 = after_tag_13771 + sizeof(GibInt);
        GibCursor after_tag_13779 = loc_10674 + 1;

        return (GibCursorGibCursorGibCursorProd) {end_r_10675, loc_10674,
                                                  writecur_13775};
    } else {
        GibInt fltAppE_7249_7776 = n_298_4754_7772 - 1;
        GibCursor loc_10930 = loc_10674 + 1;

        *(GibPackedTag *) loc_10674 = 3;

        GibCursor writetag_13792 = loc_10674 + 1;
        GibCursorGibCursorGibCursorProd tmp_struct_145 =
                                         buildExp(end_r_10675, loc_10930, fltAppE_7249_7776);
        GibCursor pvrtmp_16263 = tmp_struct_145.field0;
        GibCursor pvrtmp_16264 = tmp_struct_145.field1;
        GibCursor pvrtmp_16265 = tmp_struct_145.field2;
        GibInt fltAppE_7251_7778 = n_298_4754_7772 - 1;
        GibCursorGibCursorGibCursorProd tmp_struct_146 =
                                         buildExp(pvrtmp_16263, pvrtmp_16265, fltAppE_7251_7778);
        GibCursor pvrtmp_16270 = tmp_struct_146.field0;
        GibCursor pvrtmp_16271 = tmp_struct_146.field1;
        GibCursor pvrtmp_16272 = tmp_struct_146.field2;
        GibCursor after_tag_13793 = loc_10674 + 1;

        return (GibCursorGibCursorGibCursorProd) {pvrtmp_16270, loc_10674,
                                                  pvrtmp_16272};
    }
}
GibFloat sumList(GibVector *ls_299_4755_7780)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibInt fltAppE_7252_7783 = gib_vector_length(ls_299_4755_7780);
    GibFloat tailapp_11972 =
              foldl_loop_2370_3738(0, fltAppE_7252_7783, 0.0, ls_299_4755_7780);

    return tailapp_11972;
}
GibCursorGibCursorGibFloatProd sumKdTree(GibCursor end_r_10677,
                                         GibCursor tr_326_4776_7784)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_16281 = *(GibPackedTag *) tr_326_4776_7784;
    GibCursor tmpcur_16282 = tr_326_4776_7784 + 1;


  switch_16334:
    ;
    switch (tmpval_16281) {

      case 2:
        {
            GibCursor jump_11974 = tr_326_4776_7784 + 1;

            return (GibCursorGibCursorGibFloatProd) {end_r_10677, jump_11974,
                                                     0.0};
            break;
        }

      case 0:
        {
            GibFloat tmpval_16283 = *(GibFloat *) tmpcur_16282;
            GibCursor tmpcur_16284 = tmpcur_16282 + sizeof(GibFloat);
            GibFloat tmpval_16285 = *(GibFloat *) tmpcur_16284;
            GibCursor tmpcur_16286 = tmpcur_16284 + sizeof(GibFloat);
            GibFloat tmpval_16287 = *(GibFloat *) tmpcur_16286;
            GibCursor tmpcur_16288 = tmpcur_16286 + sizeof(GibFloat);
            GibCursor jump_11977 = tmpcur_16286 + 4;
            GibFloat fltPrm_7253_7788 = tmpval_16283 + tmpval_16285;
            GibFloat tailprim_11978 = fltPrm_7253_7788 + tmpval_16287;

            return (GibCursorGibCursorGibFloatProd) {end_r_10677, jump_11977,
                                                     tailprim_11978};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_152 = *(uintptr_t *) tmpcur_16282;
            GibCursor tmpcur_16289 = GIB_UNTAG(tagged_tmpcur_152);
            GibCursor tmpaftercur_16290 = tmpcur_16282 + 8;
            uint16_t tmptag_16291 = GIB_GET_TAG(tagged_tmpcur_152);
            GibCursor end_from_tagged_absran_10525 = tmpcur_16289 +
                      tmptag_16291;
            GibFloat tmpval_16292 = *(GibFloat *) tmpaftercur_16290;
            GibCursor tmpcur_16293 = tmpaftercur_16290 + sizeof(GibFloat);
            GibFloat tmpval_16294 = *(GibFloat *) tmpcur_16293;
            GibCursor tmpcur_16295 = tmpcur_16293 + sizeof(GibFloat);
            GibFloat tmpval_16296 = *(GibFloat *) tmpcur_16295;
            GibCursor tmpcur_16297 = tmpcur_16295 + sizeof(GibFloat);
            GibInt tmpval_16298 = *(GibInt *) tmpcur_16297;
            GibCursor tmpcur_16299 = tmpcur_16297 + sizeof(GibInt);
            GibInt tmpval_16300 = *(GibInt *) tmpcur_16299;
            GibCursor tmpcur_16301 = tmpcur_16299 + sizeof(GibInt);
            GibFloat tmpval_16302 = *(GibFloat *) tmpcur_16301;
            GibCursor tmpcur_16303 = tmpcur_16301 + sizeof(GibFloat);
            GibFloat tmpval_16304 = *(GibFloat *) tmpcur_16303;
            GibCursor tmpcur_16305 = tmpcur_16303 + sizeof(GibFloat);
            GibFloat tmpval_16306 = *(GibFloat *) tmpcur_16305;
            GibCursor tmpcur_16307 = tmpcur_16305 + sizeof(GibFloat);
            GibFloat tmpval_16308 = *(GibFloat *) tmpcur_16307;
            GibCursor tmpcur_16309 = tmpcur_16307 + sizeof(GibFloat);
            GibFloat tmpval_16310 = *(GibFloat *) tmpcur_16309;
            GibCursor tmpcur_16311 = tmpcur_16309 + sizeof(GibFloat);
            GibFloat tmpval_16312 = *(GibFloat *) tmpcur_16311;
            GibCursor tmpcur_16313 = tmpcur_16311 + sizeof(GibFloat);
            GibFloat tmpval_16314 = *(GibFloat *) tmpcur_16313;
            GibCursor tmpcur_16315 = tmpcur_16313 + sizeof(GibFloat);
            GibCursorGibCursorGibFloatProd tmp_struct_150 =
                                            sumKdTree(end_r_10677, tmpcur_16315);
            GibCursor pvrtmp_16316 = tmp_struct_150.field0;
            GibCursor pvrtmp_16317 = tmp_struct_150.field1;
            GibFloat pvrtmp_16318 = tmp_struct_150.field2;
            GibCursorGibCursorGibFloatProd tmp_struct_151 =
                                            sumKdTree(end_from_tagged_absran_10525, tmpcur_16289);
            GibCursor pvrtmp_16319 = tmp_struct_151.field0;
            GibCursor pvrtmp_16320 = tmp_struct_151.field1;
            GibFloat pvrtmp_16321 = tmp_struct_151.field2;
            GibFloat fltPrm_7256_7805 = tmpval_16292 + tmpval_16294;
            GibFloat fltPrm_7255_7806 = fltPrm_7256_7805 + tmpval_16296;
            GibFloat fltPrm_7254_7807 = fltPrm_7255_7806 + pvrtmp_16318;
            GibFloat tailprim_11994 = fltPrm_7254_7807 + pvrtmp_16321;

            return (GibCursorGibCursorGibFloatProd) {pvrtmp_16319, pvrtmp_16320,
                                                     tailprim_11994};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_154 = *(uintptr_t *) tmpcur_16282;
            GibCursor tmpcur_16322 = GIB_UNTAG(tagged_tmpcur_154);
            GibCursor tmpaftercur_16323 = tmpcur_16282 + 8;
            uint16_t tmptag_16324 = GIB_GET_TAG(tagged_tmpcur_154);
            GibCursor end_from_tagged_indr_12545 = tmpcur_16322 + tmptag_16324;
            GibCursor jump_12547 = tmpcur_16282 + 8;
            GibCursorGibCursorGibFloatProd tmp_struct_153 =
                                            sumKdTree(end_from_tagged_indr_12545, tmpcur_16322);
            GibCursor pvrtmp_16325 = tmp_struct_153.field0;
            GibCursor pvrtmp_16326 = tmp_struct_153.field1;
            GibFloat pvrtmp_16327 = tmp_struct_153.field2;

            return (GibCursorGibCursorGibFloatProd) {end_r_10677, jump_12547,
                                                     pvrtmp_16327};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_156 = *(uintptr_t *) tmpcur_16282;
            GibCursor tmpcur_16328 = GIB_UNTAG(tagged_tmpcur_156);
            GibCursor tmpaftercur_16329 = tmpcur_16282 + 8;
            uint16_t tmptag_16330 = GIB_GET_TAG(tagged_tmpcur_156);
            GibCursor end_from_tagged_indr_12545 = tmpcur_16328 + tmptag_16330;
            GibCursorGibCursorGibFloatProd tmp_struct_155 =
                                            sumKdTree(end_from_tagged_indr_12545, tmpcur_16328);
            GibCursor pvrtmp_16331 = tmp_struct_155.field0;
            GibCursor pvrtmp_16332 = tmp_struct_155.field1;
            GibFloat pvrtmp_16333 = tmp_struct_155.field2;

            return (GibCursorGibCursorGibFloatProd) {pvrtmp_16331, pvrtmp_16332,
                                                     pvrtmp_16333};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_16281");
            exit(1);
        }
    }
}
GibCursorGibIntProd countCorr_seq(GibCursor end_r_10679,
                                  GibFloatGibFloatGibFloatProd probe_359_4809_7808,
                                  GibFloat radius_360_4810_7809,
                                  GibCursor tr_361_4811_7810)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_16335 = *(GibPackedTag *) tr_361_4811_7810;
    GibCursor tmpcur_16336 = tr_361_4811_7810 + 1;


  switch_16423:
    ;
    switch (tmpval_16335) {

      case 2:
        {
            return (GibCursorGibIntProd) {end_r_10679, 0};
            break;
        }

      case 0:
        {
            GibFloat tmpval_16337 = *(GibFloat *) tmpcur_16336;
            GibCursor tmpcur_16338 = tmpcur_16336 + sizeof(GibFloat);
            GibFloat tmpval_16339 = *(GibFloat *) tmpcur_16338;
            GibCursor tmpcur_16340 = tmpcur_16338 + sizeof(GibFloat);
            GibFloat tmpval_16341 = *(GibFloat *) tmpcur_16340;
            GibCursor tmpcur_16342 = tmpcur_16340 + sizeof(GibFloat);
            GibFloat fltPrm_7258_7815 =
                      dist_point3d((GibFloatGibFloatGibFloatProd) {probe_359_4809_7808.field0, probe_359_4809_7808.field1, probe_359_4809_7808.field2}, (GibFloatGibFloatGibFloatProd) {tmpval_16337, tmpval_16339, tmpval_16341});
            GibFloat fltPrm_7260_7816 = radius_360_4810_7809 *
                     radius_360_4810_7809;
            GibBool fltIf_7257_7817 = fltPrm_7258_7815 < fltPrm_7260_7816;

            if (fltIf_7257_7817) {
                return (GibCursorGibIntProd) {end_r_10679, 1};
            } else {
                return (GibCursorGibIntProd) {end_r_10679, 0};
            }
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_159 = *(uintptr_t *) tmpcur_16336;
            GibCursor tmpcur_16352 = GIB_UNTAG(tagged_tmpcur_159);
            GibCursor tmpaftercur_16353 = tmpcur_16336 + 8;
            uint16_t tmptag_16354 = GIB_GET_TAG(tagged_tmpcur_159);
            GibCursor end_from_tagged_absran_10528 = tmpcur_16352 +
                      tmptag_16354;
            GibFloat tmpval_16355 = *(GibFloat *) tmpaftercur_16353;
            GibCursor tmpcur_16356 = tmpaftercur_16353 + sizeof(GibFloat);
            GibFloat tmpval_16357 = *(GibFloat *) tmpcur_16356;
            GibCursor tmpcur_16358 = tmpcur_16356 + sizeof(GibFloat);
            GibFloat tmpval_16359 = *(GibFloat *) tmpcur_16358;
            GibCursor tmpcur_16360 = tmpcur_16358 + sizeof(GibFloat);
            GibInt tmpval_16361 = *(GibInt *) tmpcur_16360;
            GibCursor tmpcur_16362 = tmpcur_16360 + sizeof(GibInt);
            GibInt tmpval_16363 = *(GibInt *) tmpcur_16362;
            GibCursor tmpcur_16364 = tmpcur_16362 + sizeof(GibInt);
            GibFloat tmpval_16365 = *(GibFloat *) tmpcur_16364;
            GibCursor tmpcur_16366 = tmpcur_16364 + sizeof(GibFloat);
            GibFloat tmpval_16367 = *(GibFloat *) tmpcur_16366;
            GibCursor tmpcur_16368 = tmpcur_16366 + sizeof(GibFloat);
            GibFloat tmpval_16369 = *(GibFloat *) tmpcur_16368;
            GibCursor tmpcur_16370 = tmpcur_16368 + sizeof(GibFloat);
            GibFloat tmpval_16371 = *(GibFloat *) tmpcur_16370;
            GibCursor tmpcur_16372 = tmpcur_16370 + sizeof(GibFloat);
            GibFloat tmpval_16373 = *(GibFloat *) tmpcur_16372;
            GibCursor tmpcur_16374 = tmpcur_16372 + sizeof(GibFloat);
            GibFloat tmpval_16375 = *(GibFloat *) tmpcur_16374;
            GibCursor tmpcur_16376 = tmpcur_16374 + sizeof(GibFloat);
            GibFloat tmpval_16377 = *(GibFloat *) tmpcur_16376;
            GibCursor tmpcur_16378 = tmpcur_16376 + sizeof(GibFloat);
            GibFloat fltPrm_7261_7832 = tmpval_16367 + tmpval_16369;
            GibFloat center_x_379_4829_7833 = fltPrm_7261_7832 / 2.0;
            GibFloat fltPrm_7262_7834 = tmpval_16371 + tmpval_16373;
            GibFloat center_y_380_4830_7835 = fltPrm_7262_7834 / 2.0;
            GibFloat fltPrm_7263_7836 = tmpval_16375 + tmpval_16377;
            GibFloat center_z_381_4831_7837 = fltPrm_7263_7836 / 2.0;
            GibFloat d_x_386_4836_7842 = probe_359_4809_7808.field0 -
                     center_x_379_4829_7833;
            GibFloat d_y_387_4837_7843 = probe_359_4809_7808.field1 -
                     center_y_380_4830_7835;
            GibFloat d_z_388_4838_7844 = probe_359_4809_7808.field2 -
                     center_z_381_4831_7837;
            GibFloat fltPrm_7264_7845 = tmpval_16369 - tmpval_16367;
            GibFloat boxdist_x_389_4839_7846 = fltPrm_7264_7845 / 2.0;
            GibFloat fltPrm_7265_7847 = tmpval_16373 - tmpval_16371;
            GibFloat boxdist_y_390_4840_7848 = fltPrm_7265_7847 / 2.0;
            GibFloat fltPrm_7266_7849 = tmpval_16377 - tmpval_16375;
            GibFloat boxdist_z_391_4841_7850 = fltPrm_7266_7849 / 2.0;
            GibFloat fltPrm_7268_7851 = d_x_386_4836_7842 * d_x_386_4836_7842;
            GibFloat fltPrm_7269_7852 = d_y_387_4837_7843 * d_y_387_4837_7843;
            GibFloat fltPrm_7267_7853 = fltPrm_7268_7851 + fltPrm_7269_7852;
            GibFloat fltPrm_7270_7854 = d_z_388_4838_7844 * d_z_388_4838_7844;
            GibFloat sum_392_4842_7855 = fltPrm_7267_7853 + fltPrm_7270_7854;
            GibFloat fltPrm_7272_7856 = boxdist_x_389_4839_7846 *
                     boxdist_x_389_4839_7846;
            GibFloat fltPrm_7273_7857 = boxdist_y_390_4840_7848 *
                     boxdist_y_390_4840_7848;
            GibFloat fltPrm_7271_7858 = fltPrm_7272_7856 + fltPrm_7273_7857;
            GibFloat fltPrm_7274_7859 = boxdist_z_391_4841_7850 *
                     boxdist_z_391_4841_7850;
            GibFloat boxsum_393_4843_7860 = fltPrm_7271_7858 + fltPrm_7274_7859;
            GibFloat fltPrm_7276_7861 = sum_392_4842_7855 -
                     boxsum_393_4843_7860;
            GibFloat fltPrm_7277_7862 = radius_360_4810_7809 *
                     radius_360_4810_7809;
            GibBool fltIf_7275_7863 = fltPrm_7276_7861 < fltPrm_7277_7862;

            if (fltIf_7275_7863) {
                GibCursorGibIntProd tmp_struct_157 =
                                     countCorr_seq(end_r_10679, (GibFloatGibFloatGibFloatProd) {probe_359_4809_7808.field0, probe_359_4809_7808.field1, probe_359_4809_7808.field2}, radius_360_4810_7809, tmpcur_16378);
                GibCursor pvrtmp_16382 = tmp_struct_157.field0;
                GibInt pvrtmp_16383 = tmp_struct_157.field1;
                GibCursorGibIntProd tmp_struct_158 =
                                     countCorr_seq(end_from_tagged_absran_10528, (GibFloatGibFloatGibFloatProd) {probe_359_4809_7808.field0, probe_359_4809_7808.field1, probe_359_4809_7808.field2}, radius_360_4810_7809, tmpcur_16352);
                GibCursor pvrtmp_16387 = tmp_struct_158.field0;
                GibInt pvrtmp_16388 = tmp_struct_158.field1;
                GibFloat fltPrm_7279_7867 =
                          dist_point3d((GibFloatGibFloatGibFloatProd) {probe_359_4809_7808.field0, probe_359_4809_7808.field1, probe_359_4809_7808.field2}, (GibFloatGibFloatGibFloatProd) {tmpval_16355, tmpval_16357, tmpval_16359});
                GibFloat fltPrm_7281_7868 = radius_360_4810_7809 *
                         radius_360_4810_7809;
                GibBool fltIf_7278_7869 = fltPrm_7279_7867 < fltPrm_7281_7868;

                if (fltIf_7278_7869) {
                    GibInt fltPrm_7282_7870 = pvrtmp_16383 + pvrtmp_16388;
                    GibInt tailprim_12017 = fltPrm_7282_7870 + 1;

                    return (GibCursorGibIntProd) {pvrtmp_16387, tailprim_12017};
                } else {
                    GibInt tailprim_12018 = pvrtmp_16383 + pvrtmp_16388;

                    return (GibCursorGibIntProd) {pvrtmp_16387, tailprim_12018};
                }
            } else {
                GibFloat fltPrm_7284_7872 =
                          dist_point3d((GibFloatGibFloatGibFloatProd) {probe_359_4809_7808.field0, probe_359_4809_7808.field1, probe_359_4809_7808.field2}, (GibFloatGibFloatGibFloatProd) {tmpval_16355, tmpval_16357, tmpval_16359});
                GibFloat fltPrm_7286_7873 = radius_360_4810_7809 *
                         radius_360_4810_7809;
                GibBool fltIf_7283_7874 = fltPrm_7284_7872 < fltPrm_7286_7873;

                if (fltIf_7283_7874) {
                    return (GibCursorGibIntProd) {end_r_10679, 1};
                } else {
                    return (GibCursorGibIntProd) {end_r_10679, 0};
                }
            }
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_161 = *(uintptr_t *) tmpcur_16336;
            GibCursor tmpcur_16407 = GIB_UNTAG(tagged_tmpcur_161);
            GibCursor tmpaftercur_16408 = tmpcur_16336 + 8;
            uint16_t tmptag_16409 = GIB_GET_TAG(tagged_tmpcur_161);
            GibCursor end_from_tagged_indr_12551 = tmpcur_16407 + tmptag_16409;
            GibCursor jump_12553 = tmpcur_16336 + 8;
            GibCursorGibIntProd tmp_struct_160 =
                                 countCorr_seq(end_from_tagged_indr_12551, (GibFloatGibFloatGibFloatProd) {probe_359_4809_7808.field0, probe_359_4809_7808.field1, probe_359_4809_7808.field2}, radius_360_4810_7809, tmpcur_16407);
            GibCursor pvrtmp_16413 = tmp_struct_160.field0;
            GibInt pvrtmp_16414 = tmp_struct_160.field1;

            return (GibCursorGibIntProd) {end_r_10679, pvrtmp_16414};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_163 = *(uintptr_t *) tmpcur_16336;
            GibCursor tmpcur_16415 = GIB_UNTAG(tagged_tmpcur_163);
            GibCursor tmpaftercur_16416 = tmpcur_16336 + 8;
            uint16_t tmptag_16417 = GIB_GET_TAG(tagged_tmpcur_163);
            GibCursor end_from_tagged_indr_12551 = tmpcur_16415 + tmptag_16417;
            GibCursorGibIntProd tmp_struct_162 =
                                 countCorr_seq(end_from_tagged_indr_12551, (GibFloatGibFloatGibFloatProd) {probe_359_4809_7808.field0, probe_359_4809_7808.field1, probe_359_4809_7808.field2}, radius_360_4810_7809, tmpcur_16415);
            GibCursor pvrtmp_16421 = tmp_struct_162.field0;
            GibInt pvrtmp_16422 = tmp_struct_162.field1;

            return (GibCursorGibIntProd) {pvrtmp_16421, pvrtmp_16422};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_16335");
            exit(1);
        }
    }
}
GibFloatGibFloatGibFloatProd least_dist_point3d(GibFloatGibFloatGibFloatProd a_396_4846_7875,
                                                GibFloatGibFloatGibFloatProd b_397_4847_7876,
                                                GibFloatGibFloatGibFloatProd c_398_4848_7877)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibFloat d1_399_4849_7878 =
              dist_point3d((GibFloatGibFloatGibFloatProd) {a_396_4846_7875.field0, a_396_4846_7875.field1, a_396_4846_7875.field2}, (GibFloatGibFloatGibFloatProd) {b_397_4847_7876.field0, b_397_4847_7876.field1, b_397_4847_7876.field2});
    GibFloat d2_400_4850_7879 =
              dist_point3d((GibFloatGibFloatGibFloatProd) {a_396_4846_7875.field0, a_396_4846_7875.field1, a_396_4846_7875.field2}, (GibFloatGibFloatGibFloatProd) {c_398_4848_7877.field0, c_398_4848_7877.field1, c_398_4848_7877.field2});
    GibBool fltIf_7287_7880 = d1_399_4849_7878 < d2_400_4850_7879;

    if (fltIf_7287_7880) {
        return b_397_4847_7876;
    } else {
        return c_398_4848_7877;
    }
}
GibCursorGibCursorGibFloatGibFloatGibFloatProd find_nearest(GibCursor end_r_10682,
                                                            GibCursor end_r_10683,
                                                            GibFloatGibFloatGibFloatProd pivot_401_4851_7881,
                                                            GibFloatGibFloatGibFloatProd query_402_4852_7882,
                                                            GibFloat tst_pivot_403_4853_7883,
                                                            GibFloat tst_query_404_4854_7884,
                                                            GibCursor good_side_405_4855_7885,
                                                            GibCursor other_side_406_4856_7886)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibCursorGibFloatGibFloatGibFloatProd tmp_struct_164 =
                                           nearest(end_r_10682, good_side_405_4855_7885, (GibFloatGibFloatGibFloatProd) {query_402_4852_7882.field0, query_402_4852_7882.field1, query_402_4852_7882.field2});
    GibCursor pvrtmp_16439 = tmp_struct_164.field0;
    GibFloat pvrtmp_16440 = tmp_struct_164.field1;
    GibFloat pvrtmp_16441 = tmp_struct_164.field2;
    GibFloat pvrtmp_16442 = tmp_struct_164.field3;
    GibFloatGibFloatGibFloatProd tmp_struct_165 =
                                  least_dist_point3d((GibFloatGibFloatGibFloatProd) {query_402_4852_7882.field0, query_402_4852_7882.field1, query_402_4852_7882.field2}, (GibFloatGibFloatGibFloatProd) {pvrtmp_16440, pvrtmp_16441, pvrtmp_16442}, (GibFloatGibFloatGibFloatProd) {pivot_401_4851_7881.field0, pivot_401_4851_7881.field1, pivot_401_4851_7881.field2});
    GibFloat pvrtmp_16455 = tmp_struct_165.field0;
    GibFloat pvrtmp_16456 = tmp_struct_165.field1;
    GibFloat pvrtmp_16457 = tmp_struct_165.field2;
    GibFloat nearest_other_side_409_4859_7889 = tst_query_404_4854_7884 -
             tst_pivot_403_4853_7883;
    GibFloat fltPrm_7289_7890 = nearest_other_side_409_4859_7889 *
             nearest_other_side_409_4859_7889;
    GibFloat fltPrm_7290_7891 =
              dist_point3d((GibFloatGibFloatGibFloatProd) {query_402_4852_7882.field0, query_402_4852_7882.field1, query_402_4852_7882.field2}, (GibFloatGibFloatGibFloatProd) {pvrtmp_16455, pvrtmp_16456, pvrtmp_16457});
    GibBool fltIf_7288_7892 = fltPrm_7289_7890 <= fltPrm_7290_7891;

    if (fltIf_7288_7892) {
        GibCursorGibFloatGibFloatGibFloatProd tmp_struct_166 =
                                               nearest(end_r_10683, other_side_406_4856_7886, (GibFloatGibFloatGibFloatProd) {query_402_4852_7882.field0, query_402_4852_7882.field1, query_402_4852_7882.field2});
        GibCursor pvrtmp_16467 = tmp_struct_166.field0;
        GibFloat pvrtmp_16468 = tmp_struct_166.field1;
        GibFloat pvrtmp_16469 = tmp_struct_166.field2;
        GibFloat pvrtmp_16470 = tmp_struct_166.field3;
        GibFloatGibFloatGibFloatProd tmp_struct_167 =
                                      least_dist_point3d((GibFloatGibFloatGibFloatProd) {query_402_4852_7882.field0, query_402_4852_7882.field1, query_402_4852_7882.field2}, (GibFloatGibFloatGibFloatProd) {pvrtmp_16455, pvrtmp_16456, pvrtmp_16457}, (GibFloatGibFloatGibFloatProd) {pvrtmp_16468, pvrtmp_16469, pvrtmp_16470});
        GibFloat pvrtmp_16483 = tmp_struct_167.field0;
        GibFloat pvrtmp_16484 = tmp_struct_167.field1;
        GibFloat pvrtmp_16485 = tmp_struct_167.field2;

        return (GibCursorGibCursorGibFloatGibFloatGibFloatProd) {pvrtmp_16439,
                                                                 pvrtmp_16467,
                                                                 pvrtmp_16483,
                                                                 pvrtmp_16484,
                                                                 pvrtmp_16485};
    } else {
        return (GibCursorGibCursorGibFloatGibFloatGibFloatProd) {pvrtmp_16439,
                                                                 end_r_10683,
                                                                 pvrtmp_16455,
                                                                 pvrtmp_16456,
                                                                 pvrtmp_16457};
    }
}
GibCursorGibFloatGibFloatGibFloatProd nearest(GibCursor end_r_10685,
                                              GibCursor tr_412_4862_7895,
                                              GibFloatGibFloatGibFloatProd query_413_4863_7896)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_16486 = *(GibPackedTag *) tr_412_4862_7895;
    GibCursor tmpcur_16487 = tr_412_4862_7895 + 1;


  switch_16590:
    ;
    switch (tmpval_16486) {

      case 2:
        {
            return (GibCursorGibFloatGibFloatGibFloatProd) {end_r_10685, 0.0,
                                                            0.0, 0.0};
            break;
        }

      case 0:
        {
            GibFloat tmpval_16491 = *(GibFloat *) tmpcur_16487;
            GibCursor tmpcur_16492 = tmpcur_16487 + sizeof(GibFloat);
            GibFloat tmpval_16493 = *(GibFloat *) tmpcur_16492;
            GibCursor tmpcur_16494 = tmpcur_16492 + sizeof(GibFloat);
            GibFloat tmpval_16495 = *(GibFloat *) tmpcur_16494;
            GibCursor tmpcur_16496 = tmpcur_16494 + sizeof(GibFloat);

            return (GibCursorGibFloatGibFloatGibFloatProd) {end_r_10685,
                                                            tmpval_16491,
                                                            tmpval_16493,
                                                            tmpval_16495};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_170 = *(uintptr_t *) tmpcur_16487;
            GibCursor tmpcur_16500 = GIB_UNTAG(tagged_tmpcur_170);
            GibCursor tmpaftercur_16501 = tmpcur_16487 + 8;
            uint16_t tmptag_16502 = GIB_GET_TAG(tagged_tmpcur_170);
            GibCursor end_from_tagged_absran_10531 = tmpcur_16500 +
                      tmptag_16502;
            GibFloat tmpval_16503 = *(GibFloat *) tmpaftercur_16501;
            GibCursor tmpcur_16504 = tmpaftercur_16501 + sizeof(GibFloat);
            GibFloat tmpval_16505 = *(GibFloat *) tmpcur_16504;
            GibCursor tmpcur_16506 = tmpcur_16504 + sizeof(GibFloat);
            GibFloat tmpval_16507 = *(GibFloat *) tmpcur_16506;
            GibCursor tmpcur_16508 = tmpcur_16506 + sizeof(GibFloat);
            GibInt tmpval_16509 = *(GibInt *) tmpcur_16508;
            GibCursor tmpcur_16510 = tmpcur_16508 + sizeof(GibInt);
            GibInt tmpval_16511 = *(GibInt *) tmpcur_16510;
            GibCursor tmpcur_16512 = tmpcur_16510 + sizeof(GibInt);
            GibFloat tmpval_16513 = *(GibFloat *) tmpcur_16512;
            GibCursor tmpcur_16514 = tmpcur_16512 + sizeof(GibFloat);
            GibFloat tmpval_16515 = *(GibFloat *) tmpcur_16514;
            GibCursor tmpcur_16516 = tmpcur_16514 + sizeof(GibFloat);
            GibFloat tmpval_16517 = *(GibFloat *) tmpcur_16516;
            GibCursor tmpcur_16518 = tmpcur_16516 + sizeof(GibFloat);
            GibFloat tmpval_16519 = *(GibFloat *) tmpcur_16518;
            GibCursor tmpcur_16520 = tmpcur_16518 + sizeof(GibFloat);
            GibFloat tmpval_16521 = *(GibFloat *) tmpcur_16520;
            GibCursor tmpcur_16522 = tmpcur_16520 + sizeof(GibFloat);
            GibFloat tmpval_16523 = *(GibFloat *) tmpcur_16522;
            GibCursor tmpcur_16524 = tmpcur_16522 + sizeof(GibFloat);
            GibFloat tmpval_16525 = *(GibFloat *) tmpcur_16524;
            GibCursor tmpcur_16526 = tmpcur_16524 + sizeof(GibFloat);
            GibFloat tst_query_432_4882_7915 =
                      get_coord_point3d(tmpval_16511, (GibFloatGibFloatGibFloatProd) {query_413_4863_7896.field0, query_413_4863_7896.field1, query_413_4863_7896.field2});
            GibFloat tst_pivot_433_4883_7916 =
                      get_coord_point3d(tmpval_16511, (GibFloatGibFloatGibFloatProd) {tmpval_16503, tmpval_16505, tmpval_16507});
            GibBool fltIf_7291_7917 = tst_query_432_4882_7915 <
                    tst_pivot_433_4883_7916;

            if (fltIf_7291_7917) {
                GibCursorGibCursorGibFloatGibFloatGibFloatProd tmp_struct_168 =
                                                                find_nearest(end_r_10685, end_from_tagged_absran_10531, (GibFloatGibFloatGibFloatProd) {tmpval_16503, tmpval_16505, tmpval_16507}, (GibFloatGibFloatGibFloatProd) {query_413_4863_7896.field0, query_413_4863_7896.field1, query_413_4863_7896.field2}, tst_pivot_433_4883_7916, tst_query_432_4882_7915, tmpcur_16526, tmpcur_16500);
                GibCursor pvrtmp_16542 = tmp_struct_168.field0;
                GibCursor pvrtmp_16543 = tmp_struct_168.field1;
                GibFloat pvrtmp_16544 = tmp_struct_168.field2;
                GibFloat pvrtmp_16545 = tmp_struct_168.field3;
                GibFloat pvrtmp_16546 = tmp_struct_168.field4;

                return (GibCursorGibFloatGibFloatGibFloatProd) {pvrtmp_16543,
                                                                pvrtmp_16544,
                                                                pvrtmp_16545,
                                                                pvrtmp_16546};
            } else {
                GibCursorGibCursorGibFloatGibFloatGibFloatProd tmp_struct_169 =
                                                                find_nearest(end_from_tagged_absran_10531, end_r_10685, (GibFloatGibFloatGibFloatProd) {tmpval_16503, tmpval_16505, tmpval_16507}, (GibFloatGibFloatGibFloatProd) {query_413_4863_7896.field0, query_413_4863_7896.field1, query_413_4863_7896.field2}, tst_pivot_433_4883_7916, tst_query_432_4882_7915, tmpcur_16500, tmpcur_16526);
                GibCursor pvrtmp_16556 = tmp_struct_169.field0;
                GibCursor pvrtmp_16557 = tmp_struct_169.field1;
                GibFloat pvrtmp_16558 = tmp_struct_169.field2;
                GibFloat pvrtmp_16559 = tmp_struct_169.field3;
                GibFloat pvrtmp_16560 = tmp_struct_169.field4;

                return (GibCursorGibFloatGibFloatGibFloatProd) {pvrtmp_16556,
                                                                pvrtmp_16558,
                                                                pvrtmp_16559,
                                                                pvrtmp_16560};
            }
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_172 = *(uintptr_t *) tmpcur_16487;
            GibCursor tmpcur_16564 = GIB_UNTAG(tagged_tmpcur_172);
            GibCursor tmpaftercur_16565 = tmpcur_16487 + 8;
            uint16_t tmptag_16566 = GIB_GET_TAG(tagged_tmpcur_172);
            GibCursor end_from_tagged_indr_12556 = tmpcur_16564 + tmptag_16566;
            GibCursor jump_12558 = tmpcur_16487 + 8;
            GibCursorGibFloatGibFloatGibFloatProd tmp_struct_171 =
                                                   nearest(end_from_tagged_indr_12556, tmpcur_16564, (GibFloatGibFloatGibFloatProd) {query_413_4863_7896.field0, query_413_4863_7896.field1, query_413_4863_7896.field2});
            GibCursor pvrtmp_16570 = tmp_struct_171.field0;
            GibFloat pvrtmp_16571 = tmp_struct_171.field1;
            GibFloat pvrtmp_16572 = tmp_struct_171.field2;
            GibFloat pvrtmp_16573 = tmp_struct_171.field3;

            return (GibCursorGibFloatGibFloatGibFloatProd) {end_r_10685,
                                                            pvrtmp_16571,
                                                            pvrtmp_16572,
                                                            pvrtmp_16573};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_174 = *(uintptr_t *) tmpcur_16487;
            GibCursor tmpcur_16577 = GIB_UNTAG(tagged_tmpcur_174);
            GibCursor tmpaftercur_16578 = tmpcur_16487 + 8;
            uint16_t tmptag_16579 = GIB_GET_TAG(tagged_tmpcur_174);
            GibCursor end_from_tagged_indr_12556 = tmpcur_16577 + tmptag_16579;
            GibCursorGibFloatGibFloatGibFloatProd tmp_struct_173 =
                                                   nearest(end_from_tagged_indr_12556, tmpcur_16577, (GibFloatGibFloatGibFloatProd) {query_413_4863_7896.field0, query_413_4863_7896.field1, query_413_4863_7896.field2});
            GibCursor pvrtmp_16583 = tmp_struct_173.field0;
            GibFloat pvrtmp_16584 = tmp_struct_173.field1;
            GibFloat pvrtmp_16585 = tmp_struct_173.field2;
            GibFloat pvrtmp_16586 = tmp_struct_173.field3;

            return (GibCursorGibFloatGibFloatGibFloatProd) {pvrtmp_16583,
                                                            pvrtmp_16584,
                                                            pvrtmp_16585,
                                                            pvrtmp_16586};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_16486");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorProd mkKdTreeWithAxis_seq(GibCursor end_r_10687,
                                                     GibCursor loc_10686,
                                                     GibInt axis_434_4884_7918,
                                                     GibVector *pts_435_4885_7919)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_10686 + 74 > end_r_10687) {
        gib_grow_region(&loc_10686, &end_r_10687);
    }

    GibInt len_436_4886_7920 = gib_vector_length(pts_435_4885_7919);
    GibBool fltIf_7292_7921 = len_436_4886_7920 == 0;

    if (fltIf_7292_7921) {
        *(GibPackedTag *) loc_10686 = 2;

        GibCursor writetag_13901 = loc_10686 + 1;
        GibCursor after_tag_13902 = loc_10686 + 1;

        return (GibCursorGibCursorGibCursorProd) {end_r_10687, loc_10686,
                                                  after_tag_13902};
    } else {
        GibBool fltIf_7293_7922 = len_436_4886_7920 == 1;

        if (fltIf_7293_7922) {
            GibFloatGibFloatGibFloatProd *tmp_175;

            tmp_175 =
                (GibFloatGibFloatGibFloatProd *) gib_vector_nth(pts_435_4885_7919,
                                                                0);

            GibFloatGibFloatGibFloatProd tup_407_437_4887_7925 = *tmp_175;

            *(GibPackedTag *) loc_10686 = 0;

            GibCursor writetag_13908 = loc_10686 + 1;
            GibCursor after_tag_13909 = loc_10686 + 1;

            *(GibFloat *) after_tag_13909 = tup_407_437_4887_7925.field0;

            GibCursor writecur_13913 = after_tag_13909 + sizeof(GibFloat);

            *(GibFloat *) writecur_13913 = tup_407_437_4887_7925.field1;

            GibCursor writecur_13914 = writecur_13913 + sizeof(GibFloat);

            *(GibFloat *) writecur_13914 = tup_407_437_4887_7925.field2;

            GibCursor writecur_13915 = writecur_13914 + sizeof(GibFloat);

            return (GibCursorGibCursorGibCursorProd) {end_r_10687, loc_10686,
                                                      writecur_13915};
        } else {
            GibVector *sorted_pts_441_4891_7929 =
                       sort_point3d(axis_434_4884_7918, pts_435_4885_7919);
            GibInt pivot_idx_442_4892_7930 = len_436_4886_7920 / 2;
            GibFloatGibFloatGibFloatProd *tmp_193;

            tmp_193 =
                (GibFloatGibFloatGibFloatProd *) gib_vector_nth(sorted_pts_441_4891_7929,
                                                                pivot_idx_442_4892_7930);

            GibFloatGibFloatGibFloatProd pivot_443_4893_7933 = *tmp_193;
            GibVector *left_pts_448_4898_7941 = gib_vector_slice(0,
                                                                 pivot_idx_442_4892_7930,
                                                                 sorted_pts_441_4891_7929);
            GibInt i_187_5618_6680_7942 = pivot_idx_442_4892_7930 + 1;
            GibInt fltPrm_7294_7943 = len_436_4886_7920 -
                   pivot_idx_442_4892_7930;
            GibInt n_188_5619_6681_7944 = fltPrm_7294_7943 - 1;
            GibVector *right_pts_449_4899_7946 =
                      gib_vector_slice(i_187_5618_6680_7942,
                                       n_188_5619_6681_7944,
                                       sorted_pts_441_4891_7929);
            GibInt next_axis_450_4900_7947 =
                    getNextAxis_3d(axis_434_4884_7918);
            GibCursor loc_11075 = loc_10686 + 65;

            *(GibPackedTag *) loc_10686 = 3;

            GibCursor writetag_13950 = loc_10686 + 1;
            GibCursorGibCursorGibCursorProd tmp_struct_176 =
                                             mkKdTreeWithAxis_seq(end_r_10687, loc_11075, next_axis_450_4900_7947, left_pts_448_4898_7941);
            GibCursor pvrtmp_16599 = tmp_struct_176.field0;
            GibCursor pvrtmp_16600 = tmp_struct_176.field1;
            GibCursor pvrtmp_16601 = tmp_struct_176.field2;
            GibCursorGibCursorGibCursorProd tmp_struct_177 =
                                             mkKdTreeWithAxis_seq(pvrtmp_16599, pvrtmp_16601, next_axis_450_4900_7947, right_pts_449_4899_7946);
            GibCursor pvrtmp_16606 = tmp_struct_177.field0;
            GibCursor pvrtmp_16607 = tmp_struct_177.field1;
            GibCursor pvrtmp_16608 = tmp_struct_177.field2;
            GibCursorGibFloatProd tmp_struct_178 =
                                   get_minx_kdtree(pvrtmp_16606, pvrtmp_16600);
            GibCursor pvrtmp_16613 = tmp_struct_178.field0;
            GibFloat pvrtmp_16614 = tmp_struct_178.field1;
            GibCursorGibFloatProd tmp_struct_179 =
                                   get_minx_kdtree(pvrtmp_16613, pvrtmp_16607);
            GibCursor pvrtmp_16615 = tmp_struct_179.field0;
            GibFloat pvrtmp_16616 = tmp_struct_179.field1;
            GibFloat fltAppE_7295_7952 =  minFloat(pvrtmp_16614, pvrtmp_16616);
            GibFloat min_x_453_4903_7953 =
                      minFloat(pivot_443_4893_7933.field0, fltAppE_7295_7952);
            GibCursorGibFloatProd tmp_struct_180 =
                                   get_maxx_kdtree(pvrtmp_16606, pvrtmp_16600);
            GibCursor pvrtmp_16617 = tmp_struct_180.field0;
            GibFloat pvrtmp_16618 = tmp_struct_180.field1;
            GibCursorGibFloatProd tmp_struct_181 =
                                   get_maxx_kdtree(pvrtmp_16617, pvrtmp_16607);
            GibCursor pvrtmp_16619 = tmp_struct_181.field0;
            GibFloat pvrtmp_16620 = tmp_struct_181.field1;
            GibFloat fltAppE_7298_7956 =  maxFloat(pvrtmp_16618, pvrtmp_16620);
            GibFloat max_x_454_4904_7957 =
                      maxFloat(pivot_443_4893_7933.field0, fltAppE_7298_7956);
            GibCursorGibFloatProd tmp_struct_182 =
                                   get_miny_kdtree(pvrtmp_16606, pvrtmp_16600);
            GibCursor pvrtmp_16621 = tmp_struct_182.field0;
            GibFloat pvrtmp_16622 = tmp_struct_182.field1;
            GibCursorGibFloatProd tmp_struct_183 =
                                   get_miny_kdtree(pvrtmp_16621, pvrtmp_16607);
            GibCursor pvrtmp_16623 = tmp_struct_183.field0;
            GibFloat pvrtmp_16624 = tmp_struct_183.field1;
            GibFloat fltAppE_7301_7960 =  minFloat(pvrtmp_16622, pvrtmp_16624);
            GibFloat min_y_455_4905_7961 =
                      minFloat(pivot_443_4893_7933.field1, fltAppE_7301_7960);
            GibCursorGibFloatProd tmp_struct_184 =
                                   get_maxy_kdtree(pvrtmp_16606, pvrtmp_16600);
            GibCursor pvrtmp_16625 = tmp_struct_184.field0;
            GibFloat pvrtmp_16626 = tmp_struct_184.field1;
            GibCursorGibFloatProd tmp_struct_185 =
                                   get_maxy_kdtree(pvrtmp_16625, pvrtmp_16607);
            GibCursor pvrtmp_16627 = tmp_struct_185.field0;
            GibFloat pvrtmp_16628 = tmp_struct_185.field1;
            GibFloat fltAppE_7304_7964 =  maxFloat(pvrtmp_16626, pvrtmp_16628);
            GibFloat max_y_456_4906_7965 =
                      maxFloat(pivot_443_4893_7933.field1, fltAppE_7304_7964);
            GibCursorGibFloatProd tmp_struct_186 =
                                   get_minz_kdtree(pvrtmp_16606, pvrtmp_16600);
            GibCursor pvrtmp_16629 = tmp_struct_186.field0;
            GibFloat pvrtmp_16630 = tmp_struct_186.field1;
            GibCursorGibFloatProd tmp_struct_187 =
                                   get_minz_kdtree(pvrtmp_16629, pvrtmp_16607);
            GibCursor pvrtmp_16631 = tmp_struct_187.field0;
            GibFloat pvrtmp_16632 = tmp_struct_187.field1;
            GibFloat fltAppE_7307_7968 =  minFloat(pvrtmp_16630, pvrtmp_16632);
            GibFloat min_z_457_4907_7969 =
                      minFloat(pivot_443_4893_7933.field2, fltAppE_7307_7968);
            GibCursorGibFloatProd tmp_struct_188 =
                                   get_maxz_kdtree(pvrtmp_16606, pvrtmp_16600);
            GibCursor pvrtmp_16633 = tmp_struct_188.field0;
            GibFloat pvrtmp_16634 = tmp_struct_188.field1;
            GibCursorGibFloatProd tmp_struct_189 =
                                   get_maxz_kdtree(pvrtmp_16633, pvrtmp_16607);
            GibCursor pvrtmp_16635 = tmp_struct_189.field0;
            GibFloat pvrtmp_16636 = tmp_struct_189.field1;
            GibFloat fltAppE_7310_7972 =  maxFloat(pvrtmp_16634, pvrtmp_16636);
            GibFloat max_z_458_4908_7973 =
                      maxFloat(pivot_443_4893_7933.field2, fltAppE_7310_7972);
            GibCursorGibIntProd tmp_struct_190 =
                                 get_total_points_kdtree(pvrtmp_16606, pvrtmp_16600);
            GibCursor pvrtmp_16637 = tmp_struct_190.field0;
            GibInt pvrtmp_16638 = tmp_struct_190.field1;
            GibCursorGibIntProd tmp_struct_191 =
                                 get_total_points_kdtree(pvrtmp_16637, pvrtmp_16607);
            GibCursor pvrtmp_16639 = tmp_struct_191.field0;
            GibInt pvrtmp_16640 = tmp_struct_191.field1;
            GibInt fltPrm_7313_7976 = pvrtmp_16638 + pvrtmp_16640;
            GibInt total_points_459_4909_7977 = fltPrm_7313_7976 + 1;
            GibFloat fltPkd_7316_7978 =
                      get_coord_point3d(axis_434_4884_7918, (GibFloatGibFloatGibFloatProd) {pivot_443_4893_7933.field0, pivot_443_4893_7933.field1, pivot_443_4893_7933.field2});
            uint16_t offset_192 = pvrtmp_16599 - pvrtmp_16601;
            uintptr_t ran_10534 = GIB_STORE_TAG(pvrtmp_16601, offset_192);
            GibCursor after_tag_13951 = loc_10686 + 1;

            *(uintptr_t *) after_tag_13951 = ran_10534;

            GibCursor writecur_13955 = after_tag_13951 + 8;

            *(GibFloat *) writecur_13955 = pivot_443_4893_7933.field0;

            GibCursor writecur_13956 = writecur_13955 + sizeof(GibFloat);

            *(GibFloat *) writecur_13956 = pivot_443_4893_7933.field1;

            GibCursor writecur_13957 = writecur_13956 + sizeof(GibFloat);

            *(GibFloat *) writecur_13957 = pivot_443_4893_7933.field2;

            GibCursor writecur_13958 = writecur_13957 + sizeof(GibFloat);

            *(GibInt *) writecur_13958 = total_points_459_4909_7977;

            GibCursor writecur_13959 = writecur_13958 + sizeof(GibInt);

            *(GibInt *) writecur_13959 = axis_434_4884_7918;

            GibCursor writecur_13960 = writecur_13959 + sizeof(GibInt);

            *(GibFloat *) writecur_13960 = fltPkd_7316_7978;

            GibCursor writecur_13961 = writecur_13960 + sizeof(GibFloat);

            *(GibFloat *) writecur_13961 = min_x_453_4903_7953;

            GibCursor writecur_13962 = writecur_13961 + sizeof(GibFloat);

            *(GibFloat *) writecur_13962 = max_x_454_4904_7957;

            GibCursor writecur_13963 = writecur_13962 + sizeof(GibFloat);

            *(GibFloat *) writecur_13963 = min_y_455_4905_7961;

            GibCursor writecur_13964 = writecur_13963 + sizeof(GibFloat);

            *(GibFloat *) writecur_13964 = max_y_456_4906_7965;

            GibCursor writecur_13965 = writecur_13964 + sizeof(GibFloat);

            *(GibFloat *) writecur_13965 = min_z_457_4907_7969;

            GibCursor writecur_13966 = writecur_13965 + sizeof(GibFloat);

            *(GibFloat *) writecur_13966 = max_z_458_4908_7973;

            GibCursor writecur_13967 = writecur_13966 + sizeof(GibFloat);

            return (GibCursorGibCursorGibCursorProd) {pvrtmp_16637, loc_10686,
                                                      pvrtmp_16608};
        }
    }
}
GibCursorGibIntProd get_total_points_kdtree(GibCursor end_r_10689,
                                            GibCursor tr_514_4964_7979)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_16648 = *(GibPackedTag *) tr_514_4964_7979;
    GibCursor tmpcur_16649 = tr_514_4964_7979 + 1;


  switch_16693:
    ;
    switch (tmpval_16648) {

      case 2:
        {
            return (GibCursorGibIntProd) {end_r_10689, 0};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_197 = *(uintptr_t *) tmpcur_16649;
            GibCursor tmpcur_16650 = GIB_UNTAG(tagged_tmpcur_197);
            GibCursor tmpaftercur_16651 = tmpcur_16649 + 8;
            uint16_t tmptag_16652 = GIB_GET_TAG(tagged_tmpcur_197);
            GibCursor end_from_tagged_absran_10535 = tmpcur_16650 +
                      tmptag_16652;
            GibFloat tmpval_16653 = *(GibFloat *) tmpaftercur_16651;
            GibCursor tmpcur_16654 = tmpaftercur_16651 + sizeof(GibFloat);
            GibFloat tmpval_16655 = *(GibFloat *) tmpcur_16654;
            GibCursor tmpcur_16656 = tmpcur_16654 + sizeof(GibFloat);
            GibFloat tmpval_16657 = *(GibFloat *) tmpcur_16656;
            GibCursor tmpcur_16658 = tmpcur_16656 + sizeof(GibFloat);
            GibInt tmpval_16659 = *(GibInt *) tmpcur_16658;
            GibCursor tmpcur_16660 = tmpcur_16658 + sizeof(GibInt);
            GibInt tmpval_16661 = *(GibInt *) tmpcur_16660;
            GibCursor tmpcur_16662 = tmpcur_16660 + sizeof(GibInt);
            GibFloat tmpval_16663 = *(GibFloat *) tmpcur_16662;
            GibCursor tmpcur_16664 = tmpcur_16662 + sizeof(GibFloat);
            GibFloat tmpval_16665 = *(GibFloat *) tmpcur_16664;
            GibCursor tmpcur_16666 = tmpcur_16664 + sizeof(GibFloat);
            GibFloat tmpval_16667 = *(GibFloat *) tmpcur_16666;
            GibCursor tmpcur_16668 = tmpcur_16666 + sizeof(GibFloat);
            GibFloat tmpval_16669 = *(GibFloat *) tmpcur_16668;
            GibCursor tmpcur_16670 = tmpcur_16668 + sizeof(GibFloat);
            GibFloat tmpval_16671 = *(GibFloat *) tmpcur_16670;
            GibCursor tmpcur_16672 = tmpcur_16670 + sizeof(GibFloat);
            GibFloat tmpval_16673 = *(GibFloat *) tmpcur_16672;
            GibCursor tmpcur_16674 = tmpcur_16672 + sizeof(GibFloat);
            GibFloat tmpval_16675 = *(GibFloat *) tmpcur_16674;
            GibCursor tmpcur_16676 = tmpcur_16674 + sizeof(GibFloat);

            return (GibCursorGibIntProd) {end_r_10689, tmpval_16659};
            break;
        }

      case 0:
        {
            GibFloat tmpval_16677 = *(GibFloat *) tmpcur_16649;
            GibCursor tmpcur_16678 = tmpcur_16649 + sizeof(GibFloat);
            GibFloat tmpval_16679 = *(GibFloat *) tmpcur_16678;
            GibCursor tmpcur_16680 = tmpcur_16678 + sizeof(GibFloat);
            GibFloat tmpval_16681 = *(GibFloat *) tmpcur_16680;
            GibCursor tmpcur_16682 = tmpcur_16680 + sizeof(GibFloat);

            return (GibCursorGibIntProd) {end_r_10689, 1};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_199 = *(uintptr_t *) tmpcur_16649;
            GibCursor tmpcur_16683 = GIB_UNTAG(tagged_tmpcur_199);
            GibCursor tmpaftercur_16684 = tmpcur_16649 + 8;
            uint16_t tmptag_16685 = GIB_GET_TAG(tagged_tmpcur_199);
            GibCursor end_from_tagged_indr_12561 = tmpcur_16683 + tmptag_16685;
            GibCursor jump_12563 = tmpcur_16649 + 8;
            GibCursorGibIntProd tmp_struct_198 =
                                 get_total_points_kdtree(end_from_tagged_indr_12561, tmpcur_16683);
            GibCursor pvrtmp_16686 = tmp_struct_198.field0;
            GibInt pvrtmp_16687 = tmp_struct_198.field1;

            return (GibCursorGibIntProd) {end_r_10689, pvrtmp_16687};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_201 = *(uintptr_t *) tmpcur_16649;
            GibCursor tmpcur_16688 = GIB_UNTAG(tagged_tmpcur_201);
            GibCursor tmpaftercur_16689 = tmpcur_16649 + 8;
            uint16_t tmptag_16690 = GIB_GET_TAG(tagged_tmpcur_201);
            GibCursor end_from_tagged_indr_12561 = tmpcur_16688 + tmptag_16690;
            GibCursorGibIntProd tmp_struct_200 =
                                 get_total_points_kdtree(end_from_tagged_indr_12561, tmpcur_16688);
            GibCursor pvrtmp_16691 = tmp_struct_200.field0;
            GibInt pvrtmp_16692 = tmp_struct_200.field1;

            return (GibCursorGibIntProd) {pvrtmp_16691, pvrtmp_16692};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_16648");
            exit(1);
        }
    }
}
GibCursorGibFloatProd get_maxz_kdtree(GibCursor end_r_10691,
                                      GibCursor tr_532_4982_7997)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_16694 = *(GibPackedTag *) tr_532_4982_7997;
    GibCursor tmpcur_16695 = tr_532_4982_7997 + 1;


  switch_16739:
    ;
    switch (tmpval_16694) {

      case 2:
        {
            return (GibCursorGibFloatProd) {end_r_10691, 0.0};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_202 = *(uintptr_t *) tmpcur_16695;
            GibCursor tmpcur_16696 = GIB_UNTAG(tagged_tmpcur_202);
            GibCursor tmpaftercur_16697 = tmpcur_16695 + 8;
            uint16_t tmptag_16698 = GIB_GET_TAG(tagged_tmpcur_202);
            GibCursor end_from_tagged_absran_10538 = tmpcur_16696 +
                      tmptag_16698;
            GibFloat tmpval_16699 = *(GibFloat *) tmpaftercur_16697;
            GibCursor tmpcur_16700 = tmpaftercur_16697 + sizeof(GibFloat);
            GibFloat tmpval_16701 = *(GibFloat *) tmpcur_16700;
            GibCursor tmpcur_16702 = tmpcur_16700 + sizeof(GibFloat);
            GibFloat tmpval_16703 = *(GibFloat *) tmpcur_16702;
            GibCursor tmpcur_16704 = tmpcur_16702 + sizeof(GibFloat);
            GibInt tmpval_16705 = *(GibInt *) tmpcur_16704;
            GibCursor tmpcur_16706 = tmpcur_16704 + sizeof(GibInt);
            GibInt tmpval_16707 = *(GibInt *) tmpcur_16706;
            GibCursor tmpcur_16708 = tmpcur_16706 + sizeof(GibInt);
            GibFloat tmpval_16709 = *(GibFloat *) tmpcur_16708;
            GibCursor tmpcur_16710 = tmpcur_16708 + sizeof(GibFloat);
            GibFloat tmpval_16711 = *(GibFloat *) tmpcur_16710;
            GibCursor tmpcur_16712 = tmpcur_16710 + sizeof(GibFloat);
            GibFloat tmpval_16713 = *(GibFloat *) tmpcur_16712;
            GibCursor tmpcur_16714 = tmpcur_16712 + sizeof(GibFloat);
            GibFloat tmpval_16715 = *(GibFloat *) tmpcur_16714;
            GibCursor tmpcur_16716 = tmpcur_16714 + sizeof(GibFloat);
            GibFloat tmpval_16717 = *(GibFloat *) tmpcur_16716;
            GibCursor tmpcur_16718 = tmpcur_16716 + sizeof(GibFloat);
            GibFloat tmpval_16719 = *(GibFloat *) tmpcur_16718;
            GibCursor tmpcur_16720 = tmpcur_16718 + sizeof(GibFloat);
            GibFloat tmpval_16721 = *(GibFloat *) tmpcur_16720;
            GibCursor tmpcur_16722 = tmpcur_16720 + sizeof(GibFloat);

            return (GibCursorGibFloatProd) {end_r_10691, tmpval_16721};
            break;
        }

      case 0:
        {
            GibFloat tmpval_16723 = *(GibFloat *) tmpcur_16695;
            GibCursor tmpcur_16724 = tmpcur_16695 + sizeof(GibFloat);
            GibFloat tmpval_16725 = *(GibFloat *) tmpcur_16724;
            GibCursor tmpcur_16726 = tmpcur_16724 + sizeof(GibFloat);
            GibFloat tmpval_16727 = *(GibFloat *) tmpcur_16726;
            GibCursor tmpcur_16728 = tmpcur_16726 + sizeof(GibFloat);

            return (GibCursorGibFloatProd) {end_r_10691, tmpval_16727};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_204 = *(uintptr_t *) tmpcur_16695;
            GibCursor tmpcur_16729 = GIB_UNTAG(tagged_tmpcur_204);
            GibCursor tmpaftercur_16730 = tmpcur_16695 + 8;
            uint16_t tmptag_16731 = GIB_GET_TAG(tagged_tmpcur_204);
            GibCursor end_from_tagged_indr_12566 = tmpcur_16729 + tmptag_16731;
            GibCursor jump_12568 = tmpcur_16695 + 8;
            GibCursorGibFloatProd tmp_struct_203 =
                                   get_maxz_kdtree(end_from_tagged_indr_12566, tmpcur_16729);
            GibCursor pvrtmp_16732 = tmp_struct_203.field0;
            GibFloat pvrtmp_16733 = tmp_struct_203.field1;

            return (GibCursorGibFloatProd) {end_r_10691, pvrtmp_16733};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_206 = *(uintptr_t *) tmpcur_16695;
            GibCursor tmpcur_16734 = GIB_UNTAG(tagged_tmpcur_206);
            GibCursor tmpaftercur_16735 = tmpcur_16695 + 8;
            uint16_t tmptag_16736 = GIB_GET_TAG(tagged_tmpcur_206);
            GibCursor end_from_tagged_indr_12566 = tmpcur_16734 + tmptag_16736;
            GibCursorGibFloatProd tmp_struct_205 =
                                   get_maxz_kdtree(end_from_tagged_indr_12566, tmpcur_16734);
            GibCursor pvrtmp_16737 = tmp_struct_205.field0;
            GibFloat pvrtmp_16738 = tmp_struct_205.field1;

            return (GibCursorGibFloatProd) {pvrtmp_16737, pvrtmp_16738};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_16694");
            exit(1);
        }
    }
}
GibCursorGibFloatProd get_minz_kdtree(GibCursor end_r_10693,
                                      GibCursor tr_550_5000_8015)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_16740 = *(GibPackedTag *) tr_550_5000_8015;
    GibCursor tmpcur_16741 = tr_550_5000_8015 + 1;


  switch_16785:
    ;
    switch (tmpval_16740) {

      case 2:
        {
            return (GibCursorGibFloatProd) {end_r_10693, 0.0};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_207 = *(uintptr_t *) tmpcur_16741;
            GibCursor tmpcur_16742 = GIB_UNTAG(tagged_tmpcur_207);
            GibCursor tmpaftercur_16743 = tmpcur_16741 + 8;
            uint16_t tmptag_16744 = GIB_GET_TAG(tagged_tmpcur_207);
            GibCursor end_from_tagged_absran_10541 = tmpcur_16742 +
                      tmptag_16744;
            GibFloat tmpval_16745 = *(GibFloat *) tmpaftercur_16743;
            GibCursor tmpcur_16746 = tmpaftercur_16743 + sizeof(GibFloat);
            GibFloat tmpval_16747 = *(GibFloat *) tmpcur_16746;
            GibCursor tmpcur_16748 = tmpcur_16746 + sizeof(GibFloat);
            GibFloat tmpval_16749 = *(GibFloat *) tmpcur_16748;
            GibCursor tmpcur_16750 = tmpcur_16748 + sizeof(GibFloat);
            GibInt tmpval_16751 = *(GibInt *) tmpcur_16750;
            GibCursor tmpcur_16752 = tmpcur_16750 + sizeof(GibInt);
            GibInt tmpval_16753 = *(GibInt *) tmpcur_16752;
            GibCursor tmpcur_16754 = tmpcur_16752 + sizeof(GibInt);
            GibFloat tmpval_16755 = *(GibFloat *) tmpcur_16754;
            GibCursor tmpcur_16756 = tmpcur_16754 + sizeof(GibFloat);
            GibFloat tmpval_16757 = *(GibFloat *) tmpcur_16756;
            GibCursor tmpcur_16758 = tmpcur_16756 + sizeof(GibFloat);
            GibFloat tmpval_16759 = *(GibFloat *) tmpcur_16758;
            GibCursor tmpcur_16760 = tmpcur_16758 + sizeof(GibFloat);
            GibFloat tmpval_16761 = *(GibFloat *) tmpcur_16760;
            GibCursor tmpcur_16762 = tmpcur_16760 + sizeof(GibFloat);
            GibFloat tmpval_16763 = *(GibFloat *) tmpcur_16762;
            GibCursor tmpcur_16764 = tmpcur_16762 + sizeof(GibFloat);
            GibFloat tmpval_16765 = *(GibFloat *) tmpcur_16764;
            GibCursor tmpcur_16766 = tmpcur_16764 + sizeof(GibFloat);
            GibFloat tmpval_16767 = *(GibFloat *) tmpcur_16766;
            GibCursor tmpcur_16768 = tmpcur_16766 + sizeof(GibFloat);

            return (GibCursorGibFloatProd) {end_r_10693, tmpval_16765};
            break;
        }

      case 0:
        {
            GibFloat tmpval_16769 = *(GibFloat *) tmpcur_16741;
            GibCursor tmpcur_16770 = tmpcur_16741 + sizeof(GibFloat);
            GibFloat tmpval_16771 = *(GibFloat *) tmpcur_16770;
            GibCursor tmpcur_16772 = tmpcur_16770 + sizeof(GibFloat);
            GibFloat tmpval_16773 = *(GibFloat *) tmpcur_16772;
            GibCursor tmpcur_16774 = tmpcur_16772 + sizeof(GibFloat);

            return (GibCursorGibFloatProd) {end_r_10693, tmpval_16773};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_209 = *(uintptr_t *) tmpcur_16741;
            GibCursor tmpcur_16775 = GIB_UNTAG(tagged_tmpcur_209);
            GibCursor tmpaftercur_16776 = tmpcur_16741 + 8;
            uint16_t tmptag_16777 = GIB_GET_TAG(tagged_tmpcur_209);
            GibCursor end_from_tagged_indr_12571 = tmpcur_16775 + tmptag_16777;
            GibCursor jump_12573 = tmpcur_16741 + 8;
            GibCursorGibFloatProd tmp_struct_208 =
                                   get_minz_kdtree(end_from_tagged_indr_12571, tmpcur_16775);
            GibCursor pvrtmp_16778 = tmp_struct_208.field0;
            GibFloat pvrtmp_16779 = tmp_struct_208.field1;

            return (GibCursorGibFloatProd) {end_r_10693, pvrtmp_16779};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_211 = *(uintptr_t *) tmpcur_16741;
            GibCursor tmpcur_16780 = GIB_UNTAG(tagged_tmpcur_211);
            GibCursor tmpaftercur_16781 = tmpcur_16741 + 8;
            uint16_t tmptag_16782 = GIB_GET_TAG(tagged_tmpcur_211);
            GibCursor end_from_tagged_indr_12571 = tmpcur_16780 + tmptag_16782;
            GibCursorGibFloatProd tmp_struct_210 =
                                   get_minz_kdtree(end_from_tagged_indr_12571, tmpcur_16780);
            GibCursor pvrtmp_16783 = tmp_struct_210.field0;
            GibFloat pvrtmp_16784 = tmp_struct_210.field1;

            return (GibCursorGibFloatProd) {pvrtmp_16783, pvrtmp_16784};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_16740");
            exit(1);
        }
    }
}
GibCursorGibFloatProd get_maxy_kdtree(GibCursor end_r_10695,
                                      GibCursor tr_568_5018_8033)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_16786 = *(GibPackedTag *) tr_568_5018_8033;
    GibCursor tmpcur_16787 = tr_568_5018_8033 + 1;


  switch_16831:
    ;
    switch (tmpval_16786) {

      case 2:
        {
            return (GibCursorGibFloatProd) {end_r_10695, 0.0};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_212 = *(uintptr_t *) tmpcur_16787;
            GibCursor tmpcur_16788 = GIB_UNTAG(tagged_tmpcur_212);
            GibCursor tmpaftercur_16789 = tmpcur_16787 + 8;
            uint16_t tmptag_16790 = GIB_GET_TAG(tagged_tmpcur_212);
            GibCursor end_from_tagged_absran_10544 = tmpcur_16788 +
                      tmptag_16790;
            GibFloat tmpval_16791 = *(GibFloat *) tmpaftercur_16789;
            GibCursor tmpcur_16792 = tmpaftercur_16789 + sizeof(GibFloat);
            GibFloat tmpval_16793 = *(GibFloat *) tmpcur_16792;
            GibCursor tmpcur_16794 = tmpcur_16792 + sizeof(GibFloat);
            GibFloat tmpval_16795 = *(GibFloat *) tmpcur_16794;
            GibCursor tmpcur_16796 = tmpcur_16794 + sizeof(GibFloat);
            GibInt tmpval_16797 = *(GibInt *) tmpcur_16796;
            GibCursor tmpcur_16798 = tmpcur_16796 + sizeof(GibInt);
            GibInt tmpval_16799 = *(GibInt *) tmpcur_16798;
            GibCursor tmpcur_16800 = tmpcur_16798 + sizeof(GibInt);
            GibFloat tmpval_16801 = *(GibFloat *) tmpcur_16800;
            GibCursor tmpcur_16802 = tmpcur_16800 + sizeof(GibFloat);
            GibFloat tmpval_16803 = *(GibFloat *) tmpcur_16802;
            GibCursor tmpcur_16804 = tmpcur_16802 + sizeof(GibFloat);
            GibFloat tmpval_16805 = *(GibFloat *) tmpcur_16804;
            GibCursor tmpcur_16806 = tmpcur_16804 + sizeof(GibFloat);
            GibFloat tmpval_16807 = *(GibFloat *) tmpcur_16806;
            GibCursor tmpcur_16808 = tmpcur_16806 + sizeof(GibFloat);
            GibFloat tmpval_16809 = *(GibFloat *) tmpcur_16808;
            GibCursor tmpcur_16810 = tmpcur_16808 + sizeof(GibFloat);
            GibFloat tmpval_16811 = *(GibFloat *) tmpcur_16810;
            GibCursor tmpcur_16812 = tmpcur_16810 + sizeof(GibFloat);
            GibFloat tmpval_16813 = *(GibFloat *) tmpcur_16812;
            GibCursor tmpcur_16814 = tmpcur_16812 + sizeof(GibFloat);

            return (GibCursorGibFloatProd) {end_r_10695, tmpval_16809};
            break;
        }

      case 0:
        {
            GibFloat tmpval_16815 = *(GibFloat *) tmpcur_16787;
            GibCursor tmpcur_16816 = tmpcur_16787 + sizeof(GibFloat);
            GibFloat tmpval_16817 = *(GibFloat *) tmpcur_16816;
            GibCursor tmpcur_16818 = tmpcur_16816 + sizeof(GibFloat);
            GibFloat tmpval_16819 = *(GibFloat *) tmpcur_16818;
            GibCursor tmpcur_16820 = tmpcur_16818 + sizeof(GibFloat);

            return (GibCursorGibFloatProd) {end_r_10695, tmpval_16817};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_214 = *(uintptr_t *) tmpcur_16787;
            GibCursor tmpcur_16821 = GIB_UNTAG(tagged_tmpcur_214);
            GibCursor tmpaftercur_16822 = tmpcur_16787 + 8;
            uint16_t tmptag_16823 = GIB_GET_TAG(tagged_tmpcur_214);
            GibCursor end_from_tagged_indr_12576 = tmpcur_16821 + tmptag_16823;
            GibCursor jump_12578 = tmpcur_16787 + 8;
            GibCursorGibFloatProd tmp_struct_213 =
                                   get_maxy_kdtree(end_from_tagged_indr_12576, tmpcur_16821);
            GibCursor pvrtmp_16824 = tmp_struct_213.field0;
            GibFloat pvrtmp_16825 = tmp_struct_213.field1;

            return (GibCursorGibFloatProd) {end_r_10695, pvrtmp_16825};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_216 = *(uintptr_t *) tmpcur_16787;
            GibCursor tmpcur_16826 = GIB_UNTAG(tagged_tmpcur_216);
            GibCursor tmpaftercur_16827 = tmpcur_16787 + 8;
            uint16_t tmptag_16828 = GIB_GET_TAG(tagged_tmpcur_216);
            GibCursor end_from_tagged_indr_12576 = tmpcur_16826 + tmptag_16828;
            GibCursorGibFloatProd tmp_struct_215 =
                                   get_maxy_kdtree(end_from_tagged_indr_12576, tmpcur_16826);
            GibCursor pvrtmp_16829 = tmp_struct_215.field0;
            GibFloat pvrtmp_16830 = tmp_struct_215.field1;

            return (GibCursorGibFloatProd) {pvrtmp_16829, pvrtmp_16830};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_16786");
            exit(1);
        }
    }
}
GibCursorGibFloatProd get_miny_kdtree(GibCursor end_r_10697,
                                      GibCursor tr_586_5036_8051)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_16832 = *(GibPackedTag *) tr_586_5036_8051;
    GibCursor tmpcur_16833 = tr_586_5036_8051 + 1;


  switch_16877:
    ;
    switch (tmpval_16832) {

      case 2:
        {
            return (GibCursorGibFloatProd) {end_r_10697, 0.0};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_217 = *(uintptr_t *) tmpcur_16833;
            GibCursor tmpcur_16834 = GIB_UNTAG(tagged_tmpcur_217);
            GibCursor tmpaftercur_16835 = tmpcur_16833 + 8;
            uint16_t tmptag_16836 = GIB_GET_TAG(tagged_tmpcur_217);
            GibCursor end_from_tagged_absran_10547 = tmpcur_16834 +
                      tmptag_16836;
            GibFloat tmpval_16837 = *(GibFloat *) tmpaftercur_16835;
            GibCursor tmpcur_16838 = tmpaftercur_16835 + sizeof(GibFloat);
            GibFloat tmpval_16839 = *(GibFloat *) tmpcur_16838;
            GibCursor tmpcur_16840 = tmpcur_16838 + sizeof(GibFloat);
            GibFloat tmpval_16841 = *(GibFloat *) tmpcur_16840;
            GibCursor tmpcur_16842 = tmpcur_16840 + sizeof(GibFloat);
            GibInt tmpval_16843 = *(GibInt *) tmpcur_16842;
            GibCursor tmpcur_16844 = tmpcur_16842 + sizeof(GibInt);
            GibInt tmpval_16845 = *(GibInt *) tmpcur_16844;
            GibCursor tmpcur_16846 = tmpcur_16844 + sizeof(GibInt);
            GibFloat tmpval_16847 = *(GibFloat *) tmpcur_16846;
            GibCursor tmpcur_16848 = tmpcur_16846 + sizeof(GibFloat);
            GibFloat tmpval_16849 = *(GibFloat *) tmpcur_16848;
            GibCursor tmpcur_16850 = tmpcur_16848 + sizeof(GibFloat);
            GibFloat tmpval_16851 = *(GibFloat *) tmpcur_16850;
            GibCursor tmpcur_16852 = tmpcur_16850 + sizeof(GibFloat);
            GibFloat tmpval_16853 = *(GibFloat *) tmpcur_16852;
            GibCursor tmpcur_16854 = tmpcur_16852 + sizeof(GibFloat);
            GibFloat tmpval_16855 = *(GibFloat *) tmpcur_16854;
            GibCursor tmpcur_16856 = tmpcur_16854 + sizeof(GibFloat);
            GibFloat tmpval_16857 = *(GibFloat *) tmpcur_16856;
            GibCursor tmpcur_16858 = tmpcur_16856 + sizeof(GibFloat);
            GibFloat tmpval_16859 = *(GibFloat *) tmpcur_16858;
            GibCursor tmpcur_16860 = tmpcur_16858 + sizeof(GibFloat);

            return (GibCursorGibFloatProd) {end_r_10697, tmpval_16853};
            break;
        }

      case 0:
        {
            GibFloat tmpval_16861 = *(GibFloat *) tmpcur_16833;
            GibCursor tmpcur_16862 = tmpcur_16833 + sizeof(GibFloat);
            GibFloat tmpval_16863 = *(GibFloat *) tmpcur_16862;
            GibCursor tmpcur_16864 = tmpcur_16862 + sizeof(GibFloat);
            GibFloat tmpval_16865 = *(GibFloat *) tmpcur_16864;
            GibCursor tmpcur_16866 = tmpcur_16864 + sizeof(GibFloat);

            return (GibCursorGibFloatProd) {end_r_10697, tmpval_16863};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_219 = *(uintptr_t *) tmpcur_16833;
            GibCursor tmpcur_16867 = GIB_UNTAG(tagged_tmpcur_219);
            GibCursor tmpaftercur_16868 = tmpcur_16833 + 8;
            uint16_t tmptag_16869 = GIB_GET_TAG(tagged_tmpcur_219);
            GibCursor end_from_tagged_indr_12581 = tmpcur_16867 + tmptag_16869;
            GibCursor jump_12583 = tmpcur_16833 + 8;
            GibCursorGibFloatProd tmp_struct_218 =
                                   get_miny_kdtree(end_from_tagged_indr_12581, tmpcur_16867);
            GibCursor pvrtmp_16870 = tmp_struct_218.field0;
            GibFloat pvrtmp_16871 = tmp_struct_218.field1;

            return (GibCursorGibFloatProd) {end_r_10697, pvrtmp_16871};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_221 = *(uintptr_t *) tmpcur_16833;
            GibCursor tmpcur_16872 = GIB_UNTAG(tagged_tmpcur_221);
            GibCursor tmpaftercur_16873 = tmpcur_16833 + 8;
            uint16_t tmptag_16874 = GIB_GET_TAG(tagged_tmpcur_221);
            GibCursor end_from_tagged_indr_12581 = tmpcur_16872 + tmptag_16874;
            GibCursorGibFloatProd tmp_struct_220 =
                                   get_miny_kdtree(end_from_tagged_indr_12581, tmpcur_16872);
            GibCursor pvrtmp_16875 = tmp_struct_220.field0;
            GibFloat pvrtmp_16876 = tmp_struct_220.field1;

            return (GibCursorGibFloatProd) {pvrtmp_16875, pvrtmp_16876};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_16832");
            exit(1);
        }
    }
}
GibCursorGibFloatProd get_maxx_kdtree(GibCursor end_r_10699,
                                      GibCursor tr_604_5054_8069)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_16878 = *(GibPackedTag *) tr_604_5054_8069;
    GibCursor tmpcur_16879 = tr_604_5054_8069 + 1;


  switch_16923:
    ;
    switch (tmpval_16878) {

      case 2:
        {
            return (GibCursorGibFloatProd) {end_r_10699, 0.0};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_222 = *(uintptr_t *) tmpcur_16879;
            GibCursor tmpcur_16880 = GIB_UNTAG(tagged_tmpcur_222);
            GibCursor tmpaftercur_16881 = tmpcur_16879 + 8;
            uint16_t tmptag_16882 = GIB_GET_TAG(tagged_tmpcur_222);
            GibCursor end_from_tagged_absran_10550 = tmpcur_16880 +
                      tmptag_16882;
            GibFloat tmpval_16883 = *(GibFloat *) tmpaftercur_16881;
            GibCursor tmpcur_16884 = tmpaftercur_16881 + sizeof(GibFloat);
            GibFloat tmpval_16885 = *(GibFloat *) tmpcur_16884;
            GibCursor tmpcur_16886 = tmpcur_16884 + sizeof(GibFloat);
            GibFloat tmpval_16887 = *(GibFloat *) tmpcur_16886;
            GibCursor tmpcur_16888 = tmpcur_16886 + sizeof(GibFloat);
            GibInt tmpval_16889 = *(GibInt *) tmpcur_16888;
            GibCursor tmpcur_16890 = tmpcur_16888 + sizeof(GibInt);
            GibInt tmpval_16891 = *(GibInt *) tmpcur_16890;
            GibCursor tmpcur_16892 = tmpcur_16890 + sizeof(GibInt);
            GibFloat tmpval_16893 = *(GibFloat *) tmpcur_16892;
            GibCursor tmpcur_16894 = tmpcur_16892 + sizeof(GibFloat);
            GibFloat tmpval_16895 = *(GibFloat *) tmpcur_16894;
            GibCursor tmpcur_16896 = tmpcur_16894 + sizeof(GibFloat);
            GibFloat tmpval_16897 = *(GibFloat *) tmpcur_16896;
            GibCursor tmpcur_16898 = tmpcur_16896 + sizeof(GibFloat);
            GibFloat tmpval_16899 = *(GibFloat *) tmpcur_16898;
            GibCursor tmpcur_16900 = tmpcur_16898 + sizeof(GibFloat);
            GibFloat tmpval_16901 = *(GibFloat *) tmpcur_16900;
            GibCursor tmpcur_16902 = tmpcur_16900 + sizeof(GibFloat);
            GibFloat tmpval_16903 = *(GibFloat *) tmpcur_16902;
            GibCursor tmpcur_16904 = tmpcur_16902 + sizeof(GibFloat);
            GibFloat tmpval_16905 = *(GibFloat *) tmpcur_16904;
            GibCursor tmpcur_16906 = tmpcur_16904 + sizeof(GibFloat);

            return (GibCursorGibFloatProd) {end_r_10699, tmpval_16897};
            break;
        }

      case 0:
        {
            GibFloat tmpval_16907 = *(GibFloat *) tmpcur_16879;
            GibCursor tmpcur_16908 = tmpcur_16879 + sizeof(GibFloat);
            GibFloat tmpval_16909 = *(GibFloat *) tmpcur_16908;
            GibCursor tmpcur_16910 = tmpcur_16908 + sizeof(GibFloat);
            GibFloat tmpval_16911 = *(GibFloat *) tmpcur_16910;
            GibCursor tmpcur_16912 = tmpcur_16910 + sizeof(GibFloat);

            return (GibCursorGibFloatProd) {end_r_10699, tmpval_16907};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_224 = *(uintptr_t *) tmpcur_16879;
            GibCursor tmpcur_16913 = GIB_UNTAG(tagged_tmpcur_224);
            GibCursor tmpaftercur_16914 = tmpcur_16879 + 8;
            uint16_t tmptag_16915 = GIB_GET_TAG(tagged_tmpcur_224);
            GibCursor end_from_tagged_indr_12586 = tmpcur_16913 + tmptag_16915;
            GibCursor jump_12588 = tmpcur_16879 + 8;
            GibCursorGibFloatProd tmp_struct_223 =
                                   get_maxx_kdtree(end_from_tagged_indr_12586, tmpcur_16913);
            GibCursor pvrtmp_16916 = tmp_struct_223.field0;
            GibFloat pvrtmp_16917 = tmp_struct_223.field1;

            return (GibCursorGibFloatProd) {end_r_10699, pvrtmp_16917};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_226 = *(uintptr_t *) tmpcur_16879;
            GibCursor tmpcur_16918 = GIB_UNTAG(tagged_tmpcur_226);
            GibCursor tmpaftercur_16919 = tmpcur_16879 + 8;
            uint16_t tmptag_16920 = GIB_GET_TAG(tagged_tmpcur_226);
            GibCursor end_from_tagged_indr_12586 = tmpcur_16918 + tmptag_16920;
            GibCursorGibFloatProd tmp_struct_225 =
                                   get_maxx_kdtree(end_from_tagged_indr_12586, tmpcur_16918);
            GibCursor pvrtmp_16921 = tmp_struct_225.field0;
            GibFloat pvrtmp_16922 = tmp_struct_225.field1;

            return (GibCursorGibFloatProd) {pvrtmp_16921, pvrtmp_16922};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_16878");
            exit(1);
        }
    }
}
GibCursorGibFloatProd get_minx_kdtree(GibCursor end_r_10701,
                                      GibCursor tr_622_5072_8087)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_16924 = *(GibPackedTag *) tr_622_5072_8087;
    GibCursor tmpcur_16925 = tr_622_5072_8087 + 1;


  switch_16969:
    ;
    switch (tmpval_16924) {

      case 2:
        {
            return (GibCursorGibFloatProd) {end_r_10701, 0.0};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_227 = *(uintptr_t *) tmpcur_16925;
            GibCursor tmpcur_16926 = GIB_UNTAG(tagged_tmpcur_227);
            GibCursor tmpaftercur_16927 = tmpcur_16925 + 8;
            uint16_t tmptag_16928 = GIB_GET_TAG(tagged_tmpcur_227);
            GibCursor end_from_tagged_absran_10553 = tmpcur_16926 +
                      tmptag_16928;
            GibFloat tmpval_16929 = *(GibFloat *) tmpaftercur_16927;
            GibCursor tmpcur_16930 = tmpaftercur_16927 + sizeof(GibFloat);
            GibFloat tmpval_16931 = *(GibFloat *) tmpcur_16930;
            GibCursor tmpcur_16932 = tmpcur_16930 + sizeof(GibFloat);
            GibFloat tmpval_16933 = *(GibFloat *) tmpcur_16932;
            GibCursor tmpcur_16934 = tmpcur_16932 + sizeof(GibFloat);
            GibInt tmpval_16935 = *(GibInt *) tmpcur_16934;
            GibCursor tmpcur_16936 = tmpcur_16934 + sizeof(GibInt);
            GibInt tmpval_16937 = *(GibInt *) tmpcur_16936;
            GibCursor tmpcur_16938 = tmpcur_16936 + sizeof(GibInt);
            GibFloat tmpval_16939 = *(GibFloat *) tmpcur_16938;
            GibCursor tmpcur_16940 = tmpcur_16938 + sizeof(GibFloat);
            GibFloat tmpval_16941 = *(GibFloat *) tmpcur_16940;
            GibCursor tmpcur_16942 = tmpcur_16940 + sizeof(GibFloat);
            GibFloat tmpval_16943 = *(GibFloat *) tmpcur_16942;
            GibCursor tmpcur_16944 = tmpcur_16942 + sizeof(GibFloat);
            GibFloat tmpval_16945 = *(GibFloat *) tmpcur_16944;
            GibCursor tmpcur_16946 = tmpcur_16944 + sizeof(GibFloat);
            GibFloat tmpval_16947 = *(GibFloat *) tmpcur_16946;
            GibCursor tmpcur_16948 = tmpcur_16946 + sizeof(GibFloat);
            GibFloat tmpval_16949 = *(GibFloat *) tmpcur_16948;
            GibCursor tmpcur_16950 = tmpcur_16948 + sizeof(GibFloat);
            GibFloat tmpval_16951 = *(GibFloat *) tmpcur_16950;
            GibCursor tmpcur_16952 = tmpcur_16950 + sizeof(GibFloat);

            return (GibCursorGibFloatProd) {end_r_10701, tmpval_16941};
            break;
        }

      case 0:
        {
            GibFloat tmpval_16953 = *(GibFloat *) tmpcur_16925;
            GibCursor tmpcur_16954 = tmpcur_16925 + sizeof(GibFloat);
            GibFloat tmpval_16955 = *(GibFloat *) tmpcur_16954;
            GibCursor tmpcur_16956 = tmpcur_16954 + sizeof(GibFloat);
            GibFloat tmpval_16957 = *(GibFloat *) tmpcur_16956;
            GibCursor tmpcur_16958 = tmpcur_16956 + sizeof(GibFloat);

            return (GibCursorGibFloatProd) {end_r_10701, tmpval_16953};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_229 = *(uintptr_t *) tmpcur_16925;
            GibCursor tmpcur_16959 = GIB_UNTAG(tagged_tmpcur_229);
            GibCursor tmpaftercur_16960 = tmpcur_16925 + 8;
            uint16_t tmptag_16961 = GIB_GET_TAG(tagged_tmpcur_229);
            GibCursor end_from_tagged_indr_12591 = tmpcur_16959 + tmptag_16961;
            GibCursor jump_12593 = tmpcur_16925 + 8;
            GibCursorGibFloatProd tmp_struct_228 =
                                   get_minx_kdtree(end_from_tagged_indr_12591, tmpcur_16959);
            GibCursor pvrtmp_16962 = tmp_struct_228.field0;
            GibFloat pvrtmp_16963 = tmp_struct_228.field1;

            return (GibCursorGibFloatProd) {end_r_10701, pvrtmp_16963};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_231 = *(uintptr_t *) tmpcur_16925;
            GibCursor tmpcur_16964 = GIB_UNTAG(tagged_tmpcur_231);
            GibCursor tmpaftercur_16965 = tmpcur_16925 + 8;
            uint16_t tmptag_16966 = GIB_GET_TAG(tagged_tmpcur_231);
            GibCursor end_from_tagged_indr_12591 = tmpcur_16964 + tmptag_16966;
            GibCursorGibFloatProd tmp_struct_230 =
                                   get_minx_kdtree(end_from_tagged_indr_12591, tmpcur_16964);
            GibCursor pvrtmp_16967 = tmp_struct_230.field0;
            GibFloat pvrtmp_16968 = tmp_struct_230.field1;

            return (GibCursorGibFloatProd) {pvrtmp_16967, pvrtmp_16968};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_16924");
            exit(1);
        }
    }
}
GibFloat get_coord_point3d(GibInt axis_701_5151_8105,
                           GibFloatGibFloatGibFloatProd pt_702_5152_8106)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_7317_8111 = axis_701_5151_8105 == 0;

    if (fltIf_7317_8111) {
        return pt_702_5152_8106.field0;
    } else {
        GibBool fltIf_7318_8112 = axis_701_5151_8105 == 1;

        if (fltIf_7318_8112) {
            return pt_702_5152_8106.field1;
        } else {
            return pt_702_5152_8106.field2;
        }
    }
}
GibInt getNextAxis_3d(GibInt i_707_5157_8113)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibInt fltPrm_7319_8114 = i_707_5157_8113 + 1;
    GibInt tailprim_12170 = fltPrm_7319_8114 % 3;

    return tailprim_12170;
}
GibVector *sort_point3d(GibInt axis_708_5158_8115, GibVector *ls_709_5159_8116)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibInt fltAppE_7320_8118 = gib_vector_length(ls_709_5159_8116);
    GibInt n__743_5792_8465_9255 =  maxInt(fltAppE_7320_8118, 0);
    GibInt tmp_232 = sizeof(GibFloatGibFloatGibFloatProd);
    GibVector *vec_744_5793_8466_9256 = gib_vector_alloc(n__743_5792_8465_9255,
                                                         tmp_232);
    GibVector *vec1_745_5794_8467_9257 =
               generate_loop_2376_3711(vec_744_5793_8466_9256, 0, n__743_5792_8465_9255, ls_709_5159_8116);
    GibBool fltIf_7321_8120 = axis_708_5158_8115 == 0;

    if (fltIf_7321_8120) {
        GibVector *tailprim_12171 =
                  gib_vector_inplace_sort(vec1_745_5794_8467_9257,
                                          cmpx_point3d);

        return tailprim_12171;
    } else {
        GibBool fltIf_7322_8122 = axis_708_5158_8115 == 1;

        if (fltIf_7322_8122) {
            GibVector *tailprim_12172 =
                      gib_vector_inplace_sort(vec1_745_5794_8467_9257,
                                              cmpy_point3d);

            return tailprim_12172;
        } else {
            GibVector *tailprim_12173 =
                      gib_vector_inplace_sort(vec1_745_5794_8467_9257,
                                              cmpz_point3d);

            return tailprim_12173;
        }
    }
}
GibFloat dist_point3d(GibFloatGibFloatGibFloatProd a_711_5161_8125,
                      GibFloatGibFloatGibFloatProd b_712_5162_8126)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibFloat d1_721_5171_8135 = a_711_5161_8125.field0 - b_712_5162_8126.field0;
    GibFloat d2_722_5172_8136 = a_711_5161_8125.field1 - b_712_5162_8126.field1;
    GibFloat d3_723_5173_8137 = a_711_5161_8125.field2 - b_712_5162_8126.field2;
    GibFloat fltPrm_7324_8138 = d1_721_5171_8135 * d1_721_5171_8135;
    GibFloat fltPrm_7325_8139 = d2_722_5172_8136 * d2_722_5172_8136;
    GibFloat fltPrm_7323_8140 = fltPrm_7324_8138 + fltPrm_7325_8139;
    GibFloat fltPrm_7326_8141 = d3_723_5173_8137 * d3_723_5173_8137;
    GibFloat tailprim_12174 = fltPrm_7323_8140 + fltPrm_7326_8141;

    return tailprim_12174;
}
unsigned char print_check(GibBool b_726_5174_8142)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (b_726_5174_8142) {
        unsigned char wildcard__14_727_5175_8143 = gib_print_symbol(15842);

        return 0;
    } else {
        unsigned char wildcard__16_728_5176_8144 = gib_print_symbol(15844);

        return 0;
    }
}
GibFloat float_abs(GibFloat f_729_5177_8145)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_7327_8146 = f_729_5177_8145 < 0.0;

    if (fltIf_7327_8146) {
        GibFloat fltPrm_7328_8147 = 0.0 - 1.0;
        GibFloat tailprim_12177 = f_729_5177_8145 * fltPrm_7328_8147;

        return tailprim_12177;
    } else {
        return f_729_5177_8145;
    }
}
GibBool eq_point3d(GibFloatGibFloatGibFloatProd a_730_5178_8148,
                   GibFloatGibFloatGibFloatProd b_731_5179_8149)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltPrm_7329_8158 = a_730_5178_8148.field0 == b_731_5179_8149.field0;
    GibBool fltPrm_7331_8159 = a_730_5178_8148.field1 == b_731_5179_8149.field1;
    GibBool fltPrm_7332_8160 = a_730_5178_8148.field2 == b_731_5179_8149.field2;
    GibBool fltPrm_7330_8161 = fltPrm_7331_8159 && fltPrm_7332_8160;
    GibBool tailprim_12178 = fltPrm_7329_8158 && fltPrm_7330_8161;

    return tailprim_12178;
}
GibVector *masspointsInBox_seq(GibFloatGibFloatGibFloatGibFloatProd box_780_5202_8162,
                               GibVector *mpts_781_5203_8163)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibInt fltAppE_7333_8166 = gib_vector_length(mpts_781_5203_8163);
    GibInt n__743_5957_8471_9261 =  maxInt(fltAppE_7333_8166, 0);
    GibInt tmp_234 = sizeof(GibInt);
    GibVector *vec_744_5958_8472_9262 = gib_vector_alloc(n__743_5957_8471_9261,
                                                         tmp_234);
    GibVector *vec1_745_5959_8473_9263 =
               generate_loop_2374_3717(vec_744_5958_8472_9262, 0, n__743_5957_8471_9261, mpts_781_5203_8163, (GibFloatGibFloatGibFloatGibFloatProd) {box_780_5202_8162.field0, box_780_5202_8162.field1, box_780_5202_8162.field2, box_780_5202_8162.field3});
    GibInt fltAppE_7405_8476_9266 = gib_vector_length(vec1_745_5959_8473_9263);
    GibInt num_ones_1034_5753_6693_8168 =
            foldl_loop_2380_3709(0, fltAppE_7405_8476_9266, 0, vec1_745_5959_8473_9263);
    GibInt tmp_233 = sizeof(GibFloatGibFloatGibFloatProd);
    GibVector *to_1035_5754_6694_8169 =
              gib_vector_alloc(num_ones_1034_5753_6693_8168, tmp_233);
    GibInt len_idxs_1036_5755_6695_8170 =
           gib_vector_length(vec1_745_5959_8473_9263);
    GibVector *tailapp_12179 =
               filter_loop_2379(vec1_745_5959_8473_9263, 0, 0, len_idxs_1036_5755_6695_8170, mpts_781_5203_8163, to_1035_5754_6694_8169);

    return tailapp_12179;
}
GibFloatGibFloatGibFloatProd calcCentroid_seq(GibVector *mpts_796_5214_8171)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibInt fltAppE_7334_8174 = gib_vector_length(mpts_796_5214_8171);
    GibFloatGibFloatGibFloatProd tmp_struct_235 =
                                  foldl_loop_2371_3737(0, fltAppE_7334_8174, (GibFloatGibFloatGibFloatProd) {0.0, 0.0, 0.0}, mpts_796_5214_8171);
    GibFloat pvrtmp_16980 = tmp_struct_235.field0;
    GibFloat pvrtmp_16981 = tmp_struct_235.field1;
    GibFloat pvrtmp_16982 = tmp_struct_235.field2;
    GibFloat fltPrd_7335_8180 = pvrtmp_16980 / pvrtmp_16982;
    GibFloat fltPrd_7336_8181 = pvrtmp_16981 / pvrtmp_16982;

    return (GibFloatGibFloatGibFloatProd) {fltPrd_7335_8180, fltPrd_7336_8181,
                                           pvrtmp_16982};
}
GibCursorGibFloatGibFloatProd calcAccel_seq(GibCursor end_r_10703,
                                            GibFloatGibFloatGibFloatProd mpt_813_5220_8182,
                                            GibCursor tr_814_5221_8183)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_16986 = *(GibPackedTag *) tr_814_5221_8183;
    GibCursor tmpcur_16987 = tr_814_5221_8183 + 1;


  switch_17083:
    ;
    switch (tmpval_16986) {

      case 0:
        {
            return (GibCursorGibFloatGibFloatProd) {end_r_10703, 0.0, 0.0};
            break;
        }

      case 1:
        {
            GibFloat tmpval_16990 = *(GibFloat *) tmpcur_16987;
            GibCursor tmpcur_16991 = tmpcur_16987 + sizeof(GibFloat);
            GibFloat tmpval_16992 = *(GibFloat *) tmpcur_16991;
            GibCursor tmpcur_16993 = tmpcur_16991 + sizeof(GibFloat);
            GibFloat tmpval_16994 = *(GibFloat *) tmpcur_16993;
            GibCursor tmpcur_16995 = tmpcur_16993 + sizeof(GibFloat);
            GibBool fltPrm_7338_8195 = mpt_813_5220_8182.field0 == tmpval_16990;
            GibBool fltPrm_7340_8196 = mpt_813_5220_8182.field1 == tmpval_16992;
            GibBool fltPrm_7341_8197 = mpt_813_5220_8182.field2 == tmpval_16994;
            GibBool fltPrm_7339_8198 = fltPrm_7340_8196 && fltPrm_7341_8197;
            GibBool fltIf_7337_8199 = fltPrm_7338_8195 && fltPrm_7339_8198;

            if (fltIf_7337_8199) {
                return (GibCursorGibFloatGibFloatProd) {end_r_10703, 0.0, 0.0};
            } else {
                GibFloat dx_850_5257_6706_8200 = mpt_813_5220_8182.field0 -
                         tmpval_16990;
                GibFloat dy_851_5258_6707_8201 = mpt_813_5220_8182.field1 -
                         tmpval_16992;
                GibFloat fltPrm_7342_8202 = dx_850_5257_6706_8200 *
                         dx_850_5257_6706_8200;
                GibFloat fltPrm_7343_8203 = dy_851_5258_6707_8201 *
                         dy_851_5258_6707_8201;
                GibFloat rsqr_852_5259_6708_8204 = fltPrm_7342_8202 +
                         fltPrm_7343_8203;
                GibFloat r_853_5260_6709_8205 = sqrt(rsqr_852_5259_6708_8204);
                GibFloat fltPrm_7344_8206 = mpt_813_5220_8182.field2 *
                         tmpval_16994;
                GibFloat fltPrm_7345_8207 = rsqr_852_5259_6708_8204 *
                         r_853_5260_6709_8205;
                GibFloat s_854_5261_6710_8208 = fltPrm_7344_8206 /
                         fltPrm_7345_8207;
                GibFloat fltPrd_7346_8209 = dx_850_5257_6706_8200 *
                         s_854_5261_6710_8208;
                GibFloat fltPrd_7347_8210 = dy_851_5258_6707_8201 *
                         s_854_5261_6710_8208;

                return (GibCursorGibFloatGibFloatProd) {end_r_10703,
                                                        fltPrd_7346_8209,
                                                        fltPrd_7347_8210};
            }
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_242 = *(uintptr_t *) tmpcur_16987;
            GibCursor tmpcur_17000 = GIB_UNTAG(tagged_tmpcur_242);
            GibCursor tmpaftercur_17001 = tmpcur_16987 + 8;
            uint16_t tmptag_17002 = GIB_GET_TAG(tagged_tmpcur_242);
            GibCursor end_from_tagged_absran_10556 = tmpcur_17000 +
                      tmptag_17002;
            uintptr_t tagged_tmpcur_241 = *(uintptr_t *) tmpaftercur_17001;
            GibCursor tmpcur_17003 = GIB_UNTAG(tagged_tmpcur_241);
            GibCursor tmpaftercur_17004 = tmpaftercur_17001 + 8;
            uint16_t tmptag_17005 = GIB_GET_TAG(tagged_tmpcur_241);
            GibCursor end_from_tagged_absran_10557 = tmpcur_17003 +
                      tmptag_17005;
            uintptr_t tagged_tmpcur_240 = *(uintptr_t *) tmpaftercur_17004;
            GibCursor tmpcur_17006 = GIB_UNTAG(tagged_tmpcur_240);
            GibCursor tmpaftercur_17007 = tmpaftercur_17004 + 8;
            uint16_t tmptag_17008 = GIB_GET_TAG(tagged_tmpcur_240);
            GibCursor end_from_tagged_absran_10558 = tmpcur_17006 +
                      tmptag_17008;
            GibFloat tmpval_17009 = *(GibFloat *) tmpaftercur_17007;
            GibCursor tmpcur_17010 = tmpaftercur_17007 + sizeof(GibFloat);
            GibFloat tmpval_17011 = *(GibFloat *) tmpcur_17010;
            GibCursor tmpcur_17012 = tmpcur_17010 + sizeof(GibFloat);
            GibFloat tmpval_17013 = *(GibFloat *) tmpcur_17012;
            GibCursor tmpcur_17014 = tmpcur_17012 + sizeof(GibFloat);
            GibInt tmpval_17015 = *(GibInt *) tmpcur_17014;
            GibCursor tmpcur_17016 = tmpcur_17014 + sizeof(GibInt);
            GibFloat tmpval_17017 = *(GibFloat *) tmpcur_17016;
            GibCursor tmpcur_17018 = tmpcur_17016 + sizeof(GibFloat);
            GibFloat d1_1025_5426_8351_9275 = mpt_813_5220_8182.field0 -
                     tmpval_17009;
            GibFloat d2_1026_5427_8352_9276 = mpt_813_5220_8182.field1 -
                     tmpval_17011;
            GibFloat fltPrm_7384_8353_9277 = d1_1025_5426_8351_9275 *
                     d1_1025_5426_8351_9275;
            GibFloat fltPrm_7385_8354_9278 = d2_1026_5427_8352_9276 *
                     d2_1026_5427_8352_9276;
            GibFloat r2_858_5265_6714_8226 = fltPrm_7384_8353_9277 +
                     fltPrm_7385_8354_9278;
            GibFloat widthsq_859_5266_6715_8227 = tmpval_17017 * tmpval_17017;
            GibBool fltIf_7348_8228 = r2_858_5265_6714_8226 <
                    widthsq_859_5266_6715_8227;

            if (fltIf_7348_8228) {
                GibCursorGibFloatGibFloatProd tmp_struct_236 =
                                               calcAccel_seq(end_r_10703, (GibFloatGibFloatGibFloatProd) {mpt_813_5220_8182.field0, mpt_813_5220_8182.field1, mpt_813_5220_8182.field2}, tmpcur_17018);
                GibCursor pvrtmp_17026 = tmp_struct_236.field0;
                GibFloat pvrtmp_17027 = tmp_struct_236.field1;
                GibFloat pvrtmp_17028 = tmp_struct_236.field2;
                GibCursorGibFloatGibFloatProd tmp_struct_237 =
                                               calcAccel_seq(end_from_tagged_absran_10556, (GibFloatGibFloatGibFloatProd) {mpt_813_5220_8182.field0, mpt_813_5220_8182.field1, mpt_813_5220_8182.field2}, tmpcur_17000);
                GibCursor pvrtmp_17034 = tmp_struct_237.field0;
                GibFloat pvrtmp_17035 = tmp_struct_237.field1;
                GibFloat pvrtmp_17036 = tmp_struct_237.field2;
                GibCursorGibFloatGibFloatProd tmp_struct_238 =
                                               calcAccel_seq(end_from_tagged_absran_10557, (GibFloatGibFloatGibFloatProd) {mpt_813_5220_8182.field0, mpt_813_5220_8182.field1, mpt_813_5220_8182.field2}, tmpcur_17003);
                GibCursor pvrtmp_17042 = tmp_struct_238.field0;
                GibFloat pvrtmp_17043 = tmp_struct_238.field1;
                GibFloat pvrtmp_17044 = tmp_struct_238.field2;
                GibCursorGibFloatGibFloatProd tmp_struct_239 =
                                               calcAccel_seq(end_from_tagged_absran_10558, (GibFloatGibFloatGibFloatProd) {mpt_813_5220_8182.field0, mpt_813_5220_8182.field1, mpt_813_5220_8182.field2}, tmpcur_17006);
                GibCursor pvrtmp_17050 = tmp_struct_239.field0;
                GibFloat pvrtmp_17051 = tmp_struct_239.field1;
                GibFloat pvrtmp_17052 = tmp_struct_239.field2;
                GibFloat fltPrm_7351_8241 = pvrtmp_17027 + pvrtmp_17035;
                GibFloat fltPrm_7350_8242 = fltPrm_7351_8241 + pvrtmp_17043;
                GibFloat fltPrd_7349_8243 = fltPrm_7350_8242 + pvrtmp_17051;
                GibFloat fltPrm_7354_8244 = pvrtmp_17028 + pvrtmp_17036;
                GibFloat fltPrm_7353_8245 = fltPrm_7354_8244 + pvrtmp_17044;
                GibFloat fltPrd_7352_8246 = fltPrm_7353_8245 + pvrtmp_17052;

                return (GibCursorGibFloatGibFloatProd) {pvrtmp_17050,
                                                        fltPrd_7349_8243,
                                                        fltPrd_7352_8246};
            } else {
                GibBool fltPrm_7356_8255 = mpt_813_5220_8182.field0 ==
                        tmpval_17009;
                GibBool fltPrm_7358_8256 = mpt_813_5220_8182.field1 ==
                        tmpval_17011;
                GibBool fltPrm_7359_8257 = mpt_813_5220_8182.field2 ==
                        tmpval_17013;
                GibBool fltPrm_7357_8258 = fltPrm_7358_8256 && fltPrm_7359_8257;
                GibBool fltIf_7355_8259 = fltPrm_7356_8255 && fltPrm_7357_8258;

                if (fltIf_7355_8259) {
                    return (GibCursorGibFloatGibFloatProd) {end_r_10703, 0.0,
                                                            0.0};
                } else {
                    GibFloat dx_850_5257_6724_8260 = mpt_813_5220_8182.field0 -
                             tmpval_17009;
                    GibFloat dy_851_5258_6725_8261 = mpt_813_5220_8182.field1 -
                             tmpval_17011;
                    GibFloat fltPrm_7360_8262 = dx_850_5257_6724_8260 *
                             dx_850_5257_6724_8260;
                    GibFloat fltPrm_7361_8263 = dy_851_5258_6725_8261 *
                             dy_851_5258_6725_8261;
                    GibFloat rsqr_852_5259_6726_8264 = fltPrm_7360_8262 +
                             fltPrm_7361_8263;
                    GibFloat r_853_5260_6727_8265 =
                             sqrt(rsqr_852_5259_6726_8264);
                    GibFloat fltPrm_7362_8266 = mpt_813_5220_8182.field2 *
                             tmpval_17013;
                    GibFloat fltPrm_7363_8267 = rsqr_852_5259_6726_8264 *
                             r_853_5260_6727_8265;
                    GibFloat s_854_5261_6728_8268 = fltPrm_7362_8266 /
                             fltPrm_7363_8267;
                    GibFloat fltPrd_7364_8269 = dx_850_5257_6724_8260 *
                             s_854_5261_6728_8268;
                    GibFloat fltPrd_7365_8270 = dy_851_5258_6725_8261 *
                             s_854_5261_6728_8268;

                    return (GibCursorGibFloatGibFloatProd) {end_r_10703,
                                                            fltPrd_7364_8269,
                                                            fltPrd_7365_8270};
                }
            }
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_244 = *(uintptr_t *) tmpcur_16987;
            GibCursor tmpcur_17061 = GIB_UNTAG(tagged_tmpcur_244);
            GibCursor tmpaftercur_17062 = tmpcur_16987 + 8;
            uint16_t tmptag_17063 = GIB_GET_TAG(tagged_tmpcur_244);
            GibCursor end_from_tagged_indr_12596 = tmpcur_17061 + tmptag_17063;
            GibCursor jump_12598 = tmpcur_16987 + 8;
            GibCursorGibFloatGibFloatProd tmp_struct_243 =
                                           calcAccel_seq(end_from_tagged_indr_12596, (GibFloatGibFloatGibFloatProd) {mpt_813_5220_8182.field0, mpt_813_5220_8182.field1, mpt_813_5220_8182.field2}, tmpcur_17061);
            GibCursor pvrtmp_17067 = tmp_struct_243.field0;
            GibFloat pvrtmp_17068 = tmp_struct_243.field1;
            GibFloat pvrtmp_17069 = tmp_struct_243.field2;

            return (GibCursorGibFloatGibFloatProd) {end_r_10703, pvrtmp_17068,
                                                    pvrtmp_17069};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_246 = *(uintptr_t *) tmpcur_16987;
            GibCursor tmpcur_17072 = GIB_UNTAG(tagged_tmpcur_246);
            GibCursor tmpaftercur_17073 = tmpcur_16987 + 8;
            uint16_t tmptag_17074 = GIB_GET_TAG(tagged_tmpcur_246);
            GibCursor end_from_tagged_indr_12596 = tmpcur_17072 + tmptag_17074;
            GibCursorGibFloatGibFloatProd tmp_struct_245 =
                                           calcAccel_seq(end_from_tagged_indr_12596, (GibFloatGibFloatGibFloatProd) {mpt_813_5220_8182.field0, mpt_813_5220_8182.field1, mpt_813_5220_8182.field2}, tmpcur_17072);
            GibCursor pvrtmp_17078 = tmp_struct_245.field0;
            GibFloat pvrtmp_17079 = tmp_struct_245.field1;
            GibFloat pvrtmp_17080 = tmp_struct_245.field2;

            return (GibCursorGibFloatGibFloatProd) {pvrtmp_17078, pvrtmp_17079,
                                                    pvrtmp_17080};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_16986");
            exit(1);
        }
    }
}
GibCursorGibIntProd getTotalPoints_qtree(GibCursor end_r_10705,
                                         GibCursor tr_872_5279_8287)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_17084 = *(GibPackedTag *) tr_872_5279_8287;
    GibCursor tmpcur_17085 = tr_872_5279_8287 + 1;


  switch_17121:
    ;
    switch (tmpval_17084) {

      case 0:
        {
            return (GibCursorGibIntProd) {end_r_10705, 0};
            break;
        }

      case 1:
        {
            GibFloat tmpval_17086 = *(GibFloat *) tmpcur_17085;
            GibCursor tmpcur_17087 = tmpcur_17085 + sizeof(GibFloat);
            GibFloat tmpval_17088 = *(GibFloat *) tmpcur_17087;
            GibCursor tmpcur_17089 = tmpcur_17087 + sizeof(GibFloat);
            GibFloat tmpval_17090 = *(GibFloat *) tmpcur_17089;
            GibCursor tmpcur_17091 = tmpcur_17089 + sizeof(GibFloat);

            return (GibCursorGibIntProd) {end_r_10705, 1};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_249 = *(uintptr_t *) tmpcur_17085;
            GibCursor tmpcur_17092 = GIB_UNTAG(tagged_tmpcur_249);
            GibCursor tmpaftercur_17093 = tmpcur_17085 + 8;
            uint16_t tmptag_17094 = GIB_GET_TAG(tagged_tmpcur_249);
            GibCursor end_from_tagged_absran_10563 = tmpcur_17092 +
                      tmptag_17094;
            uintptr_t tagged_tmpcur_248 = *(uintptr_t *) tmpaftercur_17093;
            GibCursor tmpcur_17095 = GIB_UNTAG(tagged_tmpcur_248);
            GibCursor tmpaftercur_17096 = tmpaftercur_17093 + 8;
            uint16_t tmptag_17097 = GIB_GET_TAG(tagged_tmpcur_248);
            GibCursor end_from_tagged_absran_10564 = tmpcur_17095 +
                      tmptag_17097;
            uintptr_t tagged_tmpcur_247 = *(uintptr_t *) tmpaftercur_17096;
            GibCursor tmpcur_17098 = GIB_UNTAG(tagged_tmpcur_247);
            GibCursor tmpaftercur_17099 = tmpaftercur_17096 + 8;
            uint16_t tmptag_17100 = GIB_GET_TAG(tagged_tmpcur_247);
            GibCursor end_from_tagged_absran_10565 = tmpcur_17098 +
                      tmptag_17100;
            GibFloat tmpval_17101 = *(GibFloat *) tmpaftercur_17099;
            GibCursor tmpcur_17102 = tmpaftercur_17099 + sizeof(GibFloat);
            GibFloat tmpval_17103 = *(GibFloat *) tmpcur_17102;
            GibCursor tmpcur_17104 = tmpcur_17102 + sizeof(GibFloat);
            GibFloat tmpval_17105 = *(GibFloat *) tmpcur_17104;
            GibCursor tmpcur_17106 = tmpcur_17104 + sizeof(GibFloat);
            GibInt tmpval_17107 = *(GibInt *) tmpcur_17106;
            GibCursor tmpcur_17108 = tmpcur_17106 + sizeof(GibInt);
            GibFloat tmpval_17109 = *(GibFloat *) tmpcur_17108;
            GibCursor tmpcur_17110 = tmpcur_17108 + sizeof(GibFloat);

            return (GibCursorGibIntProd) {end_r_10705, tmpval_17107};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_251 = *(uintptr_t *) tmpcur_17085;
            GibCursor tmpcur_17111 = GIB_UNTAG(tagged_tmpcur_251);
            GibCursor tmpaftercur_17112 = tmpcur_17085 + 8;
            uint16_t tmptag_17113 = GIB_GET_TAG(tagged_tmpcur_251);
            GibCursor end_from_tagged_indr_12601 = tmpcur_17111 + tmptag_17113;
            GibCursor jump_12603 = tmpcur_17085 + 8;
            GibCursorGibIntProd tmp_struct_250 =
                                 getTotalPoints_qtree(end_from_tagged_indr_12601, tmpcur_17111);
            GibCursor pvrtmp_17114 = tmp_struct_250.field0;
            GibInt pvrtmp_17115 = tmp_struct_250.field1;

            return (GibCursorGibIntProd) {end_r_10705, pvrtmp_17115};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_253 = *(uintptr_t *) tmpcur_17085;
            GibCursor tmpcur_17116 = GIB_UNTAG(tagged_tmpcur_253);
            GibCursor tmpaftercur_17117 = tmpcur_17085 + 8;
            uint16_t tmptag_17118 = GIB_GET_TAG(tagged_tmpcur_253);
            GibCursor end_from_tagged_indr_12601 = tmpcur_17116 + tmptag_17118;
            GibCursorGibIntProd tmp_struct_252 =
                                 getTotalPoints_qtree(end_from_tagged_indr_12601, tmpcur_17116);
            GibCursor pvrtmp_17119 = tmp_struct_252.field0;
            GibInt pvrtmp_17120 = tmp_struct_252.field1;

            return (GibCursorGibIntProd) {pvrtmp_17119, pvrtmp_17120};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_17084");
            exit(1);
        }
    }
}
GibFloat sum_mass_points(GibVector *mpts_939_5346_8300)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibInt fltAppE_7370_8303 = gib_vector_length(mpts_939_5346_8300);
    GibFloat tailapp_12213 =
              foldl_loop_2370_3739(0, fltAppE_7370_8303, 0.0, mpts_939_5346_8300);

    return tailapp_12213;
}
GibCursorGibCursorGibIntProd countLeavesQtree(GibCursor end_r_10707,
                                              GibCursor tr_946_5347_8304)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_17122 = *(GibPackedTag *) tr_946_5347_8304;
    GibCursor tmpcur_17123 = tr_946_5347_8304 + 1;


  switch_17173:
    ;
    switch (tmpval_17122) {

      case 0:
        {
            GibCursor jump_12216 = tr_946_5347_8304 + 1;

            return (GibCursorGibCursorGibIntProd) {end_r_10707, jump_12216, 0};
            break;
        }

      case 1:
        {
            GibFloat tmpval_17124 = *(GibFloat *) tmpcur_17123;
            GibCursor tmpcur_17125 = tmpcur_17123 + sizeof(GibFloat);
            GibFloat tmpval_17126 = *(GibFloat *) tmpcur_17125;
            GibCursor tmpcur_17127 = tmpcur_17125 + sizeof(GibFloat);
            GibFloat tmpval_17128 = *(GibFloat *) tmpcur_17127;
            GibCursor tmpcur_17129 = tmpcur_17127 + sizeof(GibFloat);
            GibCursor jump_12219 = tmpcur_17127 + 4;

            return (GibCursorGibCursorGibIntProd) {end_r_10707, jump_12219, 1};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_260 = *(uintptr_t *) tmpcur_17123;
            GibCursor tmpcur_17130 = GIB_UNTAG(tagged_tmpcur_260);
            GibCursor tmpaftercur_17131 = tmpcur_17123 + 8;
            uint16_t tmptag_17132 = GIB_GET_TAG(tagged_tmpcur_260);
            GibCursor end_from_tagged_absran_10570 = tmpcur_17130 +
                      tmptag_17132;
            uintptr_t tagged_tmpcur_259 = *(uintptr_t *) tmpaftercur_17131;
            GibCursor tmpcur_17133 = GIB_UNTAG(tagged_tmpcur_259);
            GibCursor tmpaftercur_17134 = tmpaftercur_17131 + 8;
            uint16_t tmptag_17135 = GIB_GET_TAG(tagged_tmpcur_259);
            GibCursor end_from_tagged_absran_10571 = tmpcur_17133 +
                      tmptag_17135;
            uintptr_t tagged_tmpcur_258 = *(uintptr_t *) tmpaftercur_17134;
            GibCursor tmpcur_17136 = GIB_UNTAG(tagged_tmpcur_258);
            GibCursor tmpaftercur_17137 = tmpaftercur_17134 + 8;
            uint16_t tmptag_17138 = GIB_GET_TAG(tagged_tmpcur_258);
            GibCursor end_from_tagged_absran_10572 = tmpcur_17136 +
                      tmptag_17138;
            GibFloat tmpval_17139 = *(GibFloat *) tmpaftercur_17137;
            GibCursor tmpcur_17140 = tmpaftercur_17137 + sizeof(GibFloat);
            GibFloat tmpval_17141 = *(GibFloat *) tmpcur_17140;
            GibCursor tmpcur_17142 = tmpcur_17140 + sizeof(GibFloat);
            GibFloat tmpval_17143 = *(GibFloat *) tmpcur_17142;
            GibCursor tmpcur_17144 = tmpcur_17142 + sizeof(GibFloat);
            GibInt tmpval_17145 = *(GibInt *) tmpcur_17144;
            GibCursor tmpcur_17146 = tmpcur_17144 + sizeof(GibInt);
            GibFloat tmpval_17147 = *(GibFloat *) tmpcur_17146;
            GibCursor tmpcur_17148 = tmpcur_17146 + sizeof(GibFloat);
            GibCursorGibCursorGibIntProd tmp_struct_254 =
                                          countLeavesQtree(end_r_10707, tmpcur_17148);
            GibCursor pvrtmp_17149 = tmp_struct_254.field0;
            GibCursor pvrtmp_17150 = tmp_struct_254.field1;
            GibInt pvrtmp_17151 = tmp_struct_254.field2;
            GibCursorGibCursorGibIntProd tmp_struct_255 =
                                          countLeavesQtree(end_from_tagged_absran_10570, tmpcur_17130);
            GibCursor pvrtmp_17152 = tmp_struct_255.field0;
            GibCursor pvrtmp_17153 = tmp_struct_255.field1;
            GibInt pvrtmp_17154 = tmp_struct_255.field2;
            GibInt fltPrm_7372_8319 = pvrtmp_17151 + pvrtmp_17154;
            GibCursorGibCursorGibIntProd tmp_struct_256 =
                                          countLeavesQtree(end_from_tagged_absran_10571, tmpcur_17133);
            GibCursor pvrtmp_17155 = tmp_struct_256.field0;
            GibCursor pvrtmp_17156 = tmp_struct_256.field1;
            GibInt pvrtmp_17157 = tmp_struct_256.field2;
            GibInt fltPrm_7371_8321 = fltPrm_7372_8319 + pvrtmp_17157;
            GibCursorGibCursorGibIntProd tmp_struct_257 =
                                          countLeavesQtree(end_from_tagged_absran_10572, tmpcur_17136);
            GibCursor pvrtmp_17158 = tmp_struct_257.field0;
            GibCursor pvrtmp_17159 = tmp_struct_257.field1;
            GibInt pvrtmp_17160 = tmp_struct_257.field2;
            GibInt tailprim_12232 = fltPrm_7371_8321 + pvrtmp_17160;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_17158, pvrtmp_17159,
                                                   tailprim_12232};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_262 = *(uintptr_t *) tmpcur_17123;
            GibCursor tmpcur_17161 = GIB_UNTAG(tagged_tmpcur_262);
            GibCursor tmpaftercur_17162 = tmpcur_17123 + 8;
            uint16_t tmptag_17163 = GIB_GET_TAG(tagged_tmpcur_262);
            GibCursor end_from_tagged_indr_12606 = tmpcur_17161 + tmptag_17163;
            GibCursor jump_12608 = tmpcur_17123 + 8;
            GibCursorGibCursorGibIntProd tmp_struct_261 =
                                          countLeavesQtree(end_from_tagged_indr_12606, tmpcur_17161);
            GibCursor pvrtmp_17164 = tmp_struct_261.field0;
            GibCursor pvrtmp_17165 = tmp_struct_261.field1;
            GibInt pvrtmp_17166 = tmp_struct_261.field2;

            return (GibCursorGibCursorGibIntProd) {end_r_10707, jump_12608,
                                                   pvrtmp_17166};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_264 = *(uintptr_t *) tmpcur_17123;
            GibCursor tmpcur_17167 = GIB_UNTAG(tagged_tmpcur_264);
            GibCursor tmpaftercur_17168 = tmpcur_17123 + 8;
            uint16_t tmptag_17169 = GIB_GET_TAG(tagged_tmpcur_264);
            GibCursor end_from_tagged_indr_12606 = tmpcur_17167 + tmptag_17169;
            GibCursorGibCursorGibIntProd tmp_struct_263 =
                                          countLeavesQtree(end_from_tagged_indr_12606, tmpcur_17167);
            GibCursor pvrtmp_17170 = tmp_struct_263.field0;
            GibCursor pvrtmp_17171 = tmp_struct_263.field1;
            GibInt pvrtmp_17172 = tmp_struct_263.field2;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_17170, pvrtmp_17171,
                                                   pvrtmp_17172};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_17122");
            exit(1);
        }
    }
}
GibCursorGibCursorGibFloatProd sumQtree(GibCursor end_r_10709,
                                        GibCursor tr_959_5360_8323)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_17174 = *(GibPackedTag *) tr_959_5360_8323;
    GibCursor tmpcur_17175 = tr_959_5360_8323 + 1;


  switch_17225:
    ;
    switch (tmpval_17174) {

      case 0:
        {
            GibCursor jump_12234 = tr_959_5360_8323 + 1;

            return (GibCursorGibCursorGibFloatProd) {end_r_10709, jump_12234,
                                                     0.0};
            break;
        }

      case 1:
        {
            GibFloat tmpval_17176 = *(GibFloat *) tmpcur_17175;
            GibCursor tmpcur_17177 = tmpcur_17175 + sizeof(GibFloat);
            GibFloat tmpval_17178 = *(GibFloat *) tmpcur_17177;
            GibCursor tmpcur_17179 = tmpcur_17177 + sizeof(GibFloat);
            GibFloat tmpval_17180 = *(GibFloat *) tmpcur_17179;
            GibCursor tmpcur_17181 = tmpcur_17179 + sizeof(GibFloat);
            GibCursor jump_12237 = tmpcur_17179 + 4;
            GibFloat fltPrm_7377_8327 = tmpval_17176 + tmpval_17178;
            GibFloat tailprim_12238 = fltPrm_7377_8327 + tmpval_17180;

            return (GibCursorGibCursorGibFloatProd) {end_r_10709, jump_12237,
                                                     tailprim_12238};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_271 = *(uintptr_t *) tmpcur_17175;
            GibCursor tmpcur_17182 = GIB_UNTAG(tagged_tmpcur_271);
            GibCursor tmpaftercur_17183 = tmpcur_17175 + 8;
            uint16_t tmptag_17184 = GIB_GET_TAG(tagged_tmpcur_271);
            GibCursor end_from_tagged_absran_10577 = tmpcur_17182 +
                      tmptag_17184;
            uintptr_t tagged_tmpcur_270 = *(uintptr_t *) tmpaftercur_17183;
            GibCursor tmpcur_17185 = GIB_UNTAG(tagged_tmpcur_270);
            GibCursor tmpaftercur_17186 = tmpaftercur_17183 + 8;
            uint16_t tmptag_17187 = GIB_GET_TAG(tagged_tmpcur_270);
            GibCursor end_from_tagged_absran_10578 = tmpcur_17185 +
                      tmptag_17187;
            uintptr_t tagged_tmpcur_269 = *(uintptr_t *) tmpaftercur_17186;
            GibCursor tmpcur_17188 = GIB_UNTAG(tagged_tmpcur_269);
            GibCursor tmpaftercur_17189 = tmpaftercur_17186 + 8;
            uint16_t tmptag_17190 = GIB_GET_TAG(tagged_tmpcur_269);
            GibCursor end_from_tagged_absran_10579 = tmpcur_17188 +
                      tmptag_17190;
            GibFloat tmpval_17191 = *(GibFloat *) tmpaftercur_17189;
            GibCursor tmpcur_17192 = tmpaftercur_17189 + sizeof(GibFloat);
            GibFloat tmpval_17193 = *(GibFloat *) tmpcur_17192;
            GibCursor tmpcur_17194 = tmpcur_17192 + sizeof(GibFloat);
            GibFloat tmpval_17195 = *(GibFloat *) tmpcur_17194;
            GibCursor tmpcur_17196 = tmpcur_17194 + sizeof(GibFloat);
            GibInt tmpval_17197 = *(GibInt *) tmpcur_17196;
            GibCursor tmpcur_17198 = tmpcur_17196 + sizeof(GibInt);
            GibFloat tmpval_17199 = *(GibFloat *) tmpcur_17198;
            GibCursor tmpcur_17200 = tmpcur_17198 + sizeof(GibFloat);
            GibCursorGibCursorGibFloatProd tmp_struct_265 =
                                            sumQtree(end_r_10709, tmpcur_17200);
            GibCursor pvrtmp_17201 = tmp_struct_265.field0;
            GibCursor pvrtmp_17202 = tmp_struct_265.field1;
            GibFloat pvrtmp_17203 = tmp_struct_265.field2;
            GibCursorGibCursorGibFloatProd tmp_struct_266 =
                                            sumQtree(end_from_tagged_absran_10577, tmpcur_17182);
            GibCursor pvrtmp_17204 = tmp_struct_266.field0;
            GibCursor pvrtmp_17205 = tmp_struct_266.field1;
            GibFloat pvrtmp_17206 = tmp_struct_266.field2;
            GibFloat fltPrm_7379_8339 = pvrtmp_17203 + pvrtmp_17206;
            GibCursorGibCursorGibFloatProd tmp_struct_267 =
                                            sumQtree(end_from_tagged_absran_10578, tmpcur_17185);
            GibCursor pvrtmp_17207 = tmp_struct_267.field0;
            GibCursor pvrtmp_17208 = tmp_struct_267.field1;
            GibFloat pvrtmp_17209 = tmp_struct_267.field2;
            GibFloat fltPrm_7378_8341 = fltPrm_7379_8339 + pvrtmp_17209;
            GibCursorGibCursorGibFloatProd tmp_struct_268 =
                                            sumQtree(end_from_tagged_absran_10579, tmpcur_17188);
            GibCursor pvrtmp_17210 = tmp_struct_268.field0;
            GibCursor pvrtmp_17211 = tmp_struct_268.field1;
            GibFloat pvrtmp_17212 = tmp_struct_268.field2;
            GibFloat tailprim_12251 = fltPrm_7378_8341 + pvrtmp_17212;

            return (GibCursorGibCursorGibFloatProd) {pvrtmp_17210, pvrtmp_17211,
                                                     tailprim_12251};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_273 = *(uintptr_t *) tmpcur_17175;
            GibCursor tmpcur_17213 = GIB_UNTAG(tagged_tmpcur_273);
            GibCursor tmpaftercur_17214 = tmpcur_17175 + 8;
            uint16_t tmptag_17215 = GIB_GET_TAG(tagged_tmpcur_273);
            GibCursor end_from_tagged_indr_12612 = tmpcur_17213 + tmptag_17215;
            GibCursor jump_12614 = tmpcur_17175 + 8;
            GibCursorGibCursorGibFloatProd tmp_struct_272 =
                                            sumQtree(end_from_tagged_indr_12612, tmpcur_17213);
            GibCursor pvrtmp_17216 = tmp_struct_272.field0;
            GibCursor pvrtmp_17217 = tmp_struct_272.field1;
            GibFloat pvrtmp_17218 = tmp_struct_272.field2;

            return (GibCursorGibCursorGibFloatProd) {end_r_10709, jump_12614,
                                                     pvrtmp_17218};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_275 = *(uintptr_t *) tmpcur_17175;
            GibCursor tmpcur_17219 = GIB_UNTAG(tagged_tmpcur_275);
            GibCursor tmpaftercur_17220 = tmpcur_17175 + 8;
            uint16_t tmptag_17221 = GIB_GET_TAG(tagged_tmpcur_275);
            GibCursor end_from_tagged_indr_12612 = tmpcur_17219 + tmptag_17221;
            GibCursorGibCursorGibFloatProd tmp_struct_274 =
                                            sumQtree(end_from_tagged_indr_12612, tmpcur_17219);
            GibCursor pvrtmp_17222 = tmp_struct_274.field0;
            GibCursor pvrtmp_17223 = tmp_struct_274.field1;
            GibFloat pvrtmp_17224 = tmp_struct_274.field2;

            return (GibCursorGibCursorGibFloatProd) {pvrtmp_17222, pvrtmp_17223,
                                                     pvrtmp_17224};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_17174");
            exit(1);
        }
    }
}
static inline
GibCursorGibFloatProd maybeLit(GibCursor end_r_10711,
                               GibCursor exp_1044_5429_8355)
{
    // GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    // GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    // GibShadowstackFrame *frame;
    GibPackedTag tmpval_17226 = *(GibPackedTag *) exp_1044_5429_8355;
    GibCursor tmpcur_17227 = exp_1044_5429_8355 + 1;


  switch_17240:
    ;
    switch (tmpval_17226) {

      case 0:
        {
            GibInt tmpval_17228 = *(GibInt *) tmpcur_17227;
            GibCursor tmpcur_17229 = tmpcur_17227 + sizeof(GibInt);
            GibFloat tailprim_12253 = (GibFloat) tmpval_17228;

            return (GibCursorGibFloatProd) {end_r_10711, tailprim_12253};
            break;
        }

      case 3:
        {
            GibFloat tailprim_12254 = 0.0 - 3.14;

            return (GibCursorGibFloatProd) {end_r_10711, tailprim_12254};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_277 = *(uintptr_t *) tmpcur_17227;
            GibCursor tmpcur_17230 = GIB_UNTAG(tagged_tmpcur_277);
            GibCursor tmpaftercur_17231 = tmpcur_17227 + 8;
            uint16_t tmptag_17232 = GIB_GET_TAG(tagged_tmpcur_277);
            GibCursor end_from_tagged_indr_12618 = tmpcur_17230 + tmptag_17232;
            GibCursor jump_12620 = tmpcur_17227 + 8;
            GibCursorGibFloatProd tmp_struct_276 =
                                   maybeLit(end_from_tagged_indr_12618, tmpcur_17230);
            GibCursor pvrtmp_17233 = tmp_struct_276.field0;
            GibFloat pvrtmp_17234 = tmp_struct_276.field1;

            return (GibCursorGibFloatProd) {end_r_10711, pvrtmp_17234};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_279 = *(uintptr_t *) tmpcur_17227;
            GibCursor tmpcur_17235 = GIB_UNTAG(tagged_tmpcur_279);
            GibCursor tmpaftercur_17236 = tmpcur_17227 + 8;
            uint16_t tmptag_17237 = GIB_GET_TAG(tagged_tmpcur_279);
            GibCursor end_from_tagged_indr_12618 = tmpcur_17235 + tmptag_17237;
            GibCursorGibFloatProd tmp_struct_278 =
                                   maybeLit(end_from_tagged_indr_12618, tmpcur_17235);
            GibCursor pvrtmp_17238 = tmp_struct_278.field0;
            GibFloat pvrtmp_17239 = tmp_struct_278.field1;

            return (GibCursorGibFloatProd) {pvrtmp_17238, pvrtmp_17239};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_17226");
            exit(1);
        }
    }
}
static inline
GibCursorGibCursorProd trav_exp(GibCursor end_r_10713,
                                GibCursor exp_1057_5442_8359)
{
    // GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    // GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    // GibShadowstackFrame *frame;
    GibPackedTag tmpval_17241 = *(GibPackedTag *) exp_1057_5442_8359;
    GibCursor tmpcur_17242 = exp_1057_5442_8359 + 1;


  switch_17259:
    ;
    switch (tmpval_17241) {

      case 0:
        {
            GibInt tmpval_17243 = *(GibInt *) tmpcur_17242;
            GibCursor tmpcur_17244 = tmpcur_17242 + sizeof(GibInt);
            GibCursor jump_12255 = tmpcur_17242 + 8;

            return (GibCursorGibCursorProd) {end_r_10713, jump_12255};
            break;
        }

      case 1:
        {
            GibCursor jump_12257 = exp_1057_5442_8359 + 1;

            return (GibCursorGibCursorProd) {end_r_10713, jump_12257};
            break;
        }

      case 2:
        {
            GibCursor jump_12259 = exp_1057_5442_8359 + 1;

            return (GibCursorGibCursorProd) {end_r_10713, jump_12259};
            break;
        }

      case 3:
        {
            GibCursorGibCursorProd tmp_struct_280 =
                                    trav_exp(end_r_10713, tmpcur_17242);
            GibCursor pvrtmp_17245 = tmp_struct_280.field0;
            GibCursor pvrtmp_17246 = tmp_struct_280.field1;
            GibCursorGibCursorProd tmp_struct_281 =
                                    trav_exp(pvrtmp_17245, pvrtmp_17246);
            GibCursor pvrtmp_17247 = tmp_struct_281.field0;
            GibCursor pvrtmp_17248 = tmp_struct_281.field1;

            return (GibCursorGibCursorProd) {pvrtmp_17247, pvrtmp_17248};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_283 = *(uintptr_t *) tmpcur_17242;
            GibCursor tmpcur_17249 = GIB_UNTAG(tagged_tmpcur_283);
            GibCursor tmpaftercur_17250 = tmpcur_17242 + 8;
            uint16_t tmptag_17251 = GIB_GET_TAG(tagged_tmpcur_283);
            GibCursor end_from_tagged_indr_12623 = tmpcur_17249 + tmptag_17251;
            GibCursor jump_12625 = tmpcur_17242 + 8;
            GibCursorGibCursorProd tmp_struct_282 =
                                    trav_exp(end_from_tagged_indr_12623, tmpcur_17249);
            GibCursor pvrtmp_17252 = tmp_struct_282.field0;
            GibCursor pvrtmp_17253 = tmp_struct_282.field1;

            return (GibCursorGibCursorProd) {end_r_10713, jump_12625};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_285 = *(uintptr_t *) tmpcur_17242;
            GibCursor tmpcur_17254 = GIB_UNTAG(tagged_tmpcur_285);
            GibCursor tmpaftercur_17255 = tmpcur_17242 + 8;
            uint16_t tmptag_17256 = GIB_GET_TAG(tagged_tmpcur_285);
            GibCursor end_from_tagged_indr_12623 = tmpcur_17254 + tmptag_17256;
            GibCursorGibCursorProd tmp_struct_284 =
                                    trav_exp(end_from_tagged_indr_12623, tmpcur_17254);
            GibCursor pvrtmp_17257 = tmp_struct_284.field0;
            GibCursor pvrtmp_17258 = tmp_struct_284.field1;

            return (GibCursorGibCursorProd) {pvrtmp_17257, pvrtmp_17258};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_17241");
            exit(1);
        }
    }
}
GibInt maxInt(GibInt a_1071_5456_8365, GibInt b_1072_5457_8366)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_7386_8367 = a_1071_5456_8365 > b_1072_5457_8366;

    if (fltIf_7386_8367) {
        return a_1071_5456_8365;
    } else {
        return b_1072_5457_8366;
    }
}
GibInt cmpz_point3d_original(GibFloatGibFloatGibFloatProd a_1340_5534_8368,
                             GibFloatGibFloatGibFloatProd b_1341_5535_8369)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_7387_8376 = a_1340_5534_8368.field2 < b_1341_5535_8369.field2;

    if (fltIf_7387_8376) {
        GibInt tailprim_12266 = 0 - 1;

        return tailprim_12266;
    } else {
        GibBool fltIf_7388_8377 = a_1340_5534_8368.field2 >
                b_1341_5535_8369.field2;

        if (fltIf_7388_8377) {
            return 1;
        } else {
            return 0;
        }
    }
}
int cmpz_point3d(const void *a_1340_5534_8368, const void *b_1341_5535_8369)
{
    GibFloatGibFloatGibFloatProd fst_286 =
                                 *(GibFloatGibFloatGibFloatProd *) a_1340_5534_8368;
    GibFloatGibFloatGibFloatProd snd_287 =
                                 *(GibFloatGibFloatGibFloatProd *) b_1341_5535_8369;

    return cmpz_point3d_original(fst_286, snd_287);
}
GibInt cmpy_point3d_original(GibFloatGibFloatGibFloatProd a_1346_5540_8378,
                             GibFloatGibFloatGibFloatProd b_1347_5541_8379)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_7389_8386 = a_1346_5540_8378.field1 < b_1347_5541_8379.field1;

    if (fltIf_7389_8386) {
        GibInt tailprim_12269 = 0 - 1;

        return tailprim_12269;
    } else {
        GibBool fltIf_7390_8387 = a_1346_5540_8378.field1 >
                b_1347_5541_8379.field1;

        if (fltIf_7390_8387) {
            return 1;
        } else {
            return 0;
        }
    }
}
int cmpy_point3d(const void *a_1346_5540_8378, const void *b_1347_5541_8379)
{
    GibFloatGibFloatGibFloatProd fst_288 =
                                 *(GibFloatGibFloatGibFloatProd *) a_1346_5540_8378;
    GibFloatGibFloatGibFloatProd snd_289 =
                                 *(GibFloatGibFloatGibFloatProd *) b_1347_5541_8379;

    return cmpy_point3d_original(fst_288, snd_289);
}
GibInt cmpx_point3d_original(GibFloatGibFloatGibFloatProd a_1352_5546_8388,
                             GibFloatGibFloatGibFloatProd b_1353_5547_8389)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_7391_8396 = a_1352_5546_8388.field0 < b_1353_5547_8389.field0;

    if (fltIf_7391_8396) {
        GibInt tailprim_12272 = 0 - 1;

        return tailprim_12272;
    } else {
        GibBool fltIf_7392_8397 = a_1352_5546_8388.field0 >
                b_1353_5547_8389.field0;

        if (fltIf_7392_8397) {
            return 1;
        } else {
            return 0;
        }
    }
}
int cmpx_point3d(const void *a_1352_5546_8388, const void *b_1353_5547_8389)
{
    GibFloatGibFloatGibFloatProd fst_290 =
                                 *(GibFloatGibFloatGibFloatProd *) a_1352_5546_8388;
    GibFloatGibFloatGibFloatProd snd_291 =
                                 *(GibFloatGibFloatGibFloatProd *) b_1353_5547_8389;

    return cmpx_point3d_original(fst_290, snd_291);
}
GibVector *filter_loop_2379(GibVector *idxs_1073_5607_8398,
                            GibInt write_at_1074_5608_8399,
                            GibInt start_1075_5609_8400,
                            GibInt end_1076_5610_8401,
                            GibVector *from_1077_5611_8402,
                            GibVector *to_1078_5612_8403)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_7393_8404 = start_1075_5609_8400 == end_1076_5610_8401;

    if (fltIf_7393_8404) {
        return to_1078_5612_8403;
    } else {
        GibInt *tmp_293;

        tmp_293 = (GibInt *) gib_vector_nth(idxs_1073_5607_8398,
                                            start_1075_5609_8400);

        GibInt idx_1080_5613_8407 = *tmp_293;
        GibInt fltPrm_7395_8408 = 0 - 1;
        GibBool fltIf_7394_8409 = idx_1080_5613_8407 == fltPrm_7395_8408;

        if (fltIf_7394_8409) {
            GibInt fltAppE_7396_8410 = start_1075_5609_8400 + 1;
            GibVector *tailapp_12273 =
                       filter_loop_2379(idxs_1073_5607_8398, write_at_1074_5608_8399, fltAppE_7396_8410, end_1076_5610_8401, from_1077_5611_8402, to_1078_5612_8403);

            return tailapp_12273;
        } else {
            GibFloatGibFloatGibFloatProd *tmp_292;

            tmp_292 =
                (GibFloatGibFloatGibFloatProd *) gib_vector_nth(from_1077_5611_8402,
                                                                idx_1080_5613_8407);

            GibFloatGibFloatGibFloatProd elt_1081_5614_8413 = *tmp_292;
            GibVector *to1_1082_5615_8414 =
                      gib_vector_inplace_update(to_1078_5612_8403,
                                                write_at_1074_5608_8399,
                                                &elt_1081_5614_8413);
            GibInt fltAppE_7397_8415 = write_at_1074_5608_8399 + 1;
            GibInt fltAppE_7398_8416 = start_1075_5609_8400 + 1;
            GibVector *tailapp_12274 =
                       filter_loop_2379(idxs_1073_5607_8398, fltAppE_7397_8415, fltAppE_7398_8416, end_1076_5610_8401, from_1077_5611_8402, to1_1082_5615_8414);

            return tailapp_12274;
        }
    }
}
GibInt foldl_loop_2380_3709(GibInt idx_1162_5962_8477,
                            GibInt end_1163_5963_8478,
                            GibInt acc_1165_5964_8479,
                            GibVector *vec_1166_5965_8480)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_7406_8481 = idx_1162_5962_8477 == end_1163_5963_8478;

    if (fltIf_7406_8481) {
        return acc_1165_5964_8479;
    } else {
        GibInt *tmp_294;

        tmp_294 = (GibInt *) gib_vector_nth(vec_1166_5965_8480,
                                            idx_1162_5962_8477);

        GibInt x_1032_5953_7037_8483 = *tmp_294;
        GibInt fltPrm_7408_8484 = 0 - 1;
        GibBool fltIf_7407_8485 = x_1032_5953_7037_8483 == fltPrm_7408_8484;
        GibInt acc1_1169_5966_8486;

        if (fltIf_7407_8485) {
            acc1_1169_5966_8486 = acc_1165_5964_8479;
        } else {
            GibInt flt_17260 = acc_1165_5964_8479 + 1;

            acc1_1169_5966_8486 = flt_17260;
        }

        GibInt fltAppE_7409_8487 = idx_1162_5962_8477 + 1;
        GibInt tailapp_12275 =
                foldl_loop_2380_3709(fltAppE_7409_8487, end_1163_5963_8478, acc1_1169_5966_8486, vec_1166_5965_8480);

        return tailapp_12275;
    }
}
GibCursorGibVectorProd generate_loop_2377_3710(GibCursor end_r_10715,
                                               GibVector *vec_1194_5967_8488,
                                               GibInt idx_1195_5968_8489,
                                               GibInt end_1196_5969_8490,
                                               GibCursor bht_274_5970_8491,
                                               GibVector *mpts_275_5971_8492,
                                               GibVector *ps_276_5972_8493)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_7410_8494 = idx_1195_5968_8489 == end_1196_5969_8490;

    if (fltIf_7410_8494) {
        return (GibCursorGibVectorProd) {end_r_10715, vec_1194_5967_8488};
    } else {
        GibFloatGibFloatGibFloatGibFloatGibFloatProd *tmp_298;

        tmp_298 =
            (GibFloatGibFloatGibFloatGibFloatGibFloatProd *) gib_vector_nth(ps_276_5972_8493,
                                                                            idx_1195_5968_8489);

        GibFloatGibFloatGibFloatGibFloatGibFloatProd p_278_5695_7042_8499 =
                                                     *tmp_298;
        GibFloatGibFloatGibFloatProd *tmp_297;

        tmp_297 =
            (GibFloatGibFloatGibFloatProd *) gib_vector_nth(mpts_275_5971_8492,
                                                            idx_1195_5968_8489);

        GibFloatGibFloatGibFloatProd mpt_279_5696_7043_8500 = *tmp_297;
        GibCursorGibFloatGibFloatProd tmp_struct_295 =
                                       calcAccel_seq(end_r_10715, (GibFloatGibFloatGibFloatProd) {mpt_279_5696_7043_8500.field0, mpt_279_5696_7043_8500.field1, mpt_279_5696_7043_8500.field2}, bht_274_5970_8491);
        GibCursor pvrtmp_17264 = tmp_struct_295.field0;
        GibFloat pvrtmp_17265 = tmp_struct_295.field1;
        GibFloat pvrtmp_17266 = tmp_struct_295.field2;
        GibFloat fltPrm_7367_8283_9295 = pvrtmp_17265 * 2.0;
        GibFloat fltPrd_7366_8284_9296 = p_278_5695_7042_8499.field3 +
                 fltPrm_7367_8283_9295;
        GibFloat fltPrm_7369_8285_9297 = pvrtmp_17266 * 2.0;
        GibFloat fltPrd_7368_8286_9298 = p_278_5695_7042_8499.field4 +
                 fltPrm_7369_8285_9297;
        GibVector *vec1_1199_5973_8503 =
                  gib_vector_inplace_update(vec_1194_5967_8488,
                                            idx_1195_5968_8489,
                                            &(GibFloatGibFloatGibFloatGibFloatGibFloatProd) {p_278_5695_7042_8499.field0,
                                                                                             p_278_5695_7042_8499.field1,
                                                                                             p_278_5695_7042_8499.field2,
                                                                                             fltPrd_7366_8284_9296,
                                                                                             fltPrd_7368_8286_9298});
        GibInt fltAppE_7412_8504 = idx_1195_5968_8489 + 1;
        GibCursorGibVectorProd tmp_struct_296 =
                                generate_loop_2377_3710(end_r_10715, vec1_1199_5973_8503, fltAppE_7412_8504, end_1196_5969_8490, bht_274_5970_8491, mpts_275_5971_8492, ps_276_5972_8493);
        GibCursor pvrtmp_17274 = tmp_struct_296.field0;
        GibVector *pvrtmp_17275 = tmp_struct_296.field1;

        return (GibCursorGibVectorProd) {pvrtmp_17274, pvrtmp_17275};
    }
}
GibVector *generate_loop_2376_3711(GibVector *vec_1194_5974_8505,
                                   GibInt idx_1195_5975_8506,
                                   GibInt end_1196_5976_8507,
                                   GibVector *vec_1191_5977_8508)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_7413_8509 = idx_1195_5975_8506 == end_1196_5976_8507;

    if (fltIf_7413_8509) {
        return vec_1194_5974_8505;
    } else {
        GibFloatGibFloatGibFloatProd *tmp_299;

        tmp_299 =
            (GibFloatGibFloatGibFloatProd *) gib_vector_nth(vec_1191_5977_8508,
                                                            idx_1195_5975_8506);

        GibFloatGibFloatGibFloatProd fltPrm_7414_8512 = *tmp_299;
        GibVector *vec1_1199_5978_8513 =
                  gib_vector_inplace_update(vec_1194_5974_8505,
                                            idx_1195_5975_8506,
                                            &fltPrm_7414_8512);
        GibInt fltAppE_7415_8514 = idx_1195_5975_8506 + 1;
        GibVector *tailapp_12277 =
                   generate_loop_2376_3711(vec1_1199_5978_8513, fltAppE_7415_8514, end_1196_5976_8507, vec_1191_5977_8508);

        return tailapp_12277;
    }
}
GibVector *generate_loop_2374_3714(GibVector *vec_1194_5996_8515,
                                   GibInt idx_1195_5997_8516,
                                   GibInt end_1196_5998_8517)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_7416_8518 = idx_1195_5997_8516 == end_1196_5998_8517;

    if (fltIf_7416_8518) {
        return vec_1194_5996_8515;
    } else {
        GibVector *vec1_1199_5999_8521 =
                  gib_vector_inplace_update(vec_1194_5996_8515,
                                            idx_1195_5997_8516,
                                            &idx_1195_5997_8516);
        GibInt fltAppE_7418_8522 = idx_1195_5997_8516 + 1;
        GibVector *tailapp_12278 =
                   generate_loop_2374_3714(vec1_1199_5999_8521, fltAppE_7418_8522, end_1196_5998_8517);

        return tailapp_12278;
    }
}
GibVector *generate_loop_2374_3717(GibVector *vec_1194_6010_8523,
                                   GibInt idx_1195_6011_8524,
                                   GibInt end_1196_6012_8525,
                                   GibVector *vec_1028_6013_8526,
                                   GibFloatGibFloatGibFloatGibFloatProd box_780_6014_8527)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_7419_8528 = idx_1195_6011_8524 == end_1196_6012_8525;

    if (fltIf_7419_8528) {
        return vec_1194_6010_8523;
    } else {
        GibFloatGibFloatGibFloatProd *tmp_300;

        tmp_300 =
            (GibFloatGibFloatGibFloatProd *) gib_vector_nth(vec_1028_6013_8526,
                                                            idx_1195_6011_8524);

        GibFloatGibFloatGibFloatProd fltAppE_7422_8532 = *tmp_300;
        GibBool fltPrm_7399_8457_9318 = fltAppE_7422_8532.field0 >=
                box_780_6014_8527.field0;
        GibBool fltPrm_7401_8458_9319 = fltAppE_7422_8532.field0 <=
                box_780_6014_8527.field2;
        GibBool fltPrm_7403_8459_9320 = fltAppE_7422_8532.field1 >=
                box_780_6014_8527.field1;
        GibBool fltPrm_7404_8460_9321 = fltAppE_7422_8532.field1 <=
                box_780_6014_8527.field3;
        GibBool fltPrm_7402_8461_9322 = fltPrm_7403_8459_9320 &&
                fltPrm_7404_8460_9321;
        GibBool fltPrm_7400_8462_9323 = fltPrm_7401_8458_9319 &&
                fltPrm_7402_8461_9322;
        GibBool fltIf_7421_8533 = fltPrm_7399_8457_9318 &&
                fltPrm_7400_8462_9323;
        GibInt fltPrm_7420_8534;

        if (fltIf_7421_8533) {
            fltPrm_7420_8534 = idx_1195_6011_8524;
        } else {
            GibInt flt_17278 = 0 - 1;

            fltPrm_7420_8534 = flt_17278;
        }

        GibVector *vec1_1199_6015_8535 =
                  gib_vector_inplace_update(vec_1194_6010_8523,
                                            idx_1195_6011_8524,
                                            &fltPrm_7420_8534);
        GibInt fltAppE_7423_8536 = idx_1195_6011_8524 + 1;
        GibVector *tailapp_12279 =
                   generate_loop_2374_3717(vec1_1199_6015_8535, fltAppE_7423_8536, end_1196_6012_8525, vec_1028_6013_8526, (GibFloatGibFloatGibFloatGibFloatProd) {box_780_6014_8527.field0, box_780_6014_8527.field1, box_780_6014_8527.field2, box_780_6014_8527.field3});

        return tailapp_12279;
    }
}
GibCursorGibVectorProd generate_loop_2376_3720(GibCursor end_r_10717,
                                               GibVector *vec_1194_6025_8543,
                                               GibInt idx_1195_6026_8544,
                                               GibInt end_1196_6027_8545,
                                               GibVector *vec_270_6028_8546,
                                               GibCursor tr_207_6029_8547)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_7424_8548 = idx_1195_6026_8544 == end_1196_6027_8545;

    if (fltIf_7424_8548) {
        return (GibCursorGibVectorProd) {end_r_10717, vec_1194_6025_8543};
    } else {
        GibFloatGibFloatGibFloatProd *tmp_303;

        tmp_303 =
            (GibFloatGibFloatGibFloatProd *) gib_vector_nth(vec_270_6028_8546,
                                                            idx_1195_6026_8544);

        GibFloatGibFloatGibFloatProd fltAppE_7426_8552 = *tmp_303;
        GibCursorGibFloatGibFloatGibFloatProd tmp_struct_301 =
                                               nearest(end_r_10717, tr_207_6029_8547, (GibFloatGibFloatGibFloatProd) {fltAppE_7426_8552.field0, fltAppE_7426_8552.field1, fltAppE_7426_8552.field2});
        GibCursor pvrtmp_17286 = tmp_struct_301.field0;
        GibFloat pvrtmp_17287 = tmp_struct_301.field1;
        GibFloat pvrtmp_17288 = tmp_struct_301.field2;
        GibFloat pvrtmp_17289 = tmp_struct_301.field3;
        GibVector *vec1_1199_6030_8554 =
                  gib_vector_inplace_update(vec_1194_6025_8543,
                                            idx_1195_6026_8544,
                                            &(GibFloatGibFloatGibFloatProd) {pvrtmp_17287,
                                                                             pvrtmp_17288,
                                                                             pvrtmp_17289});
        GibInt fltAppE_7427_8555 = idx_1195_6026_8544 + 1;
        GibCursorGibVectorProd tmp_struct_302 =
                                generate_loop_2376_3720(end_r_10717, vec1_1199_6030_8554, fltAppE_7427_8555, end_1196_6027_8545, vec_270_6028_8546, tr_207_6029_8547);
        GibCursor pvrtmp_17293 = tmp_struct_302.field0;
        GibVector *pvrtmp_17294 = tmp_struct_302.field1;

        return (GibCursorGibVectorProd) {pvrtmp_17293, pvrtmp_17294};
    }
}
GibCursorGibVectorProd generate_loop_2374_3723(GibCursor end_r_10719,
                                               GibVector *vec_1194_6042_8563,
                                               GibInt idx_1195_6043_8564,
                                               GibInt end_1196_6044_8565,
                                               GibVector *vec_270_6045_8566,
                                               GibFloat radius_183_6046_8567,
                                               GibCursor tr_184_6047_8568)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_7428_8569 = idx_1195_6043_8564 == end_1196_6044_8565;

    if (fltIf_7428_8569) {
        return (GibCursorGibVectorProd) {end_r_10719, vec_1194_6042_8563};
    } else {
        GibFloatGibFloatGibFloatProd *tmp_306;

        tmp_306 =
            (GibFloatGibFloatGibFloatProd *) gib_vector_nth(vec_270_6045_8566,
                                                            idx_1195_6043_8564);

        GibFloatGibFloatGibFloatProd fltAppE_7430_8574 = *tmp_306;
        GibCursorGibIntProd tmp_struct_304 =
                             countCorr_seq(end_r_10719, (GibFloatGibFloatGibFloatProd) {fltAppE_7430_8574.field0, fltAppE_7430_8574.field1, fltAppE_7430_8574.field2}, radius_183_6046_8567, tr_184_6047_8568);
        GibCursor pvrtmp_17298 = tmp_struct_304.field0;
        GibInt pvrtmp_17299 = tmp_struct_304.field1;
        GibVector *vec1_1199_6048_8576 =
                  gib_vector_inplace_update(vec_1194_6042_8563,
                                            idx_1195_6043_8564, &pvrtmp_17299);
        GibInt fltAppE_7431_8577 = idx_1195_6043_8564 + 1;
        GibCursorGibVectorProd tmp_struct_305 =
                                generate_loop_2374_3723(end_r_10719, vec1_1199_6048_8576, fltAppE_7431_8577, end_1196_6044_8565, vec_270_6045_8566, radius_183_6046_8567, tr_184_6047_8568);
        GibCursor pvrtmp_17300 = tmp_struct_305.field0;
        GibVector *pvrtmp_17301 = tmp_struct_305.field1;

        return (GibCursorGibVectorProd) {pvrtmp_17300, pvrtmp_17301};
    }
}
GibVector *generate_loop_2377_3726(GibVector *vec_1194_6057_8583,
                                   GibInt idx_1195_6058_8584,
                                   GibInt end_1196_6059_8585,
                                   GibVector *vec_270_6060_8586)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_7432_8587 = idx_1195_6058_8584 == end_1196_6059_8585;

    if (fltIf_7432_8587) {
        return vec_1194_6057_8583;
    } else {
        GibFloatGibFloatProd *tmp_307;

        tmp_307 = (GibFloatGibFloatProd *) gib_vector_nth(vec_270_6060_8586,
                                                          idx_1195_6058_8584);

        GibFloatGibFloatProd fltAppE_7434_8590 = *tmp_307;
        GibVector *vec1_1199_6061_8592 =
                  gib_vector_inplace_update(vec_1194_6057_8583,
                                            idx_1195_6058_8584,
                                            &(GibFloatGibFloatGibFloatGibFloatGibFloatProd) {fltAppE_7434_8590.field0,
                                                                                             fltAppE_7434_8590.field1,
                                                                                             1.0,
                                                                                             0.0,
                                                                                             0.0});
        GibInt fltAppE_7435_8593 = idx_1195_6058_8584 + 1;
        GibVector *tailapp_12282 =
                   generate_loop_2377_3726(vec1_1199_6061_8592, fltAppE_7435_8593, end_1196_6059_8585, vec_270_6060_8586);

        return tailapp_12282;
    }
}
GibVector *generate_loop_2377_3729(GibVector *vec_1194_6070_8599,
                                   GibInt idx_1195_6071_8600,
                                   GibInt end_1196_6072_8601,
                                   GibVector *vec_270_6073_8602)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_7436_8603 = idx_1195_6071_8600 == end_1196_6072_8601;

    if (fltIf_7436_8603) {
        return vec_1194_6070_8599;
    } else {
        GibFloatGibFloatProd *tmp_308;

        tmp_308 = (GibFloatGibFloatProd *) gib_vector_nth(vec_270_6073_8602,
                                                          idx_1195_6071_8600);

        GibFloatGibFloatProd fltAppE_7438_8606 = *tmp_308;
        GibVector *vec1_1199_6074_8608 =
                  gib_vector_inplace_update(vec_1194_6070_8599,
                                            idx_1195_6071_8600,
                                            &(GibFloatGibFloatGibFloatGibFloatGibFloatProd) {fltAppE_7438_8606.field0,
                                                                                             fltAppE_7438_8606.field1,
                                                                                             1.0,
                                                                                             0.0,
                                                                                             0.0});
        GibInt fltAppE_7439_8609 = idx_1195_6071_8600 + 1;
        GibVector *tailapp_12283 =
                   generate_loop_2377_3729(vec1_1199_6074_8608, fltAppE_7439_8609, end_1196_6072_8601, vec_270_6073_8602);

        return tailapp_12283;
    }
}
GibVector *generate_loop_2376_3732(GibVector *vec_1194_6083_8615,
                                   GibInt idx_1195_6084_8616,
                                   GibInt end_1196_6085_8617,
                                   GibVector *vec_270_6086_8618)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_7440_8619 = idx_1195_6084_8616 == end_1196_6085_8617;

    if (fltIf_7440_8619) {
        return vec_1194_6083_8615;
    } else {
        GibFloatGibFloatProd *tmp_309;

        tmp_309 = (GibFloatGibFloatProd *) gib_vector_nth(vec_270_6086_8618,
                                                          idx_1195_6084_8616);

        GibFloatGibFloatProd fltAppE_7442_8622 = *tmp_309;
        GibVector *vec1_1199_6087_8624 =
                  gib_vector_inplace_update(vec_1194_6083_8615,
                                            idx_1195_6084_8616,
                                            &(GibFloatGibFloatGibFloatProd) {fltAppE_7442_8622.field0,
                                                                             fltAppE_7442_8622.field1,
                                                                             1.0});
        GibInt fltAppE_7443_8625 = idx_1195_6084_8616 + 1;
        GibVector *tailapp_12284 =
                   generate_loop_2376_3732(vec1_1199_6087_8624, fltAppE_7443_8625, end_1196_6085_8617, vec_270_6086_8618);

        return tailapp_12284;
    }
}
GibVector *generate_loop_2376_3735(GibVector *vec_1194_6096_8631,
                                   GibInt idx_1195_6097_8632,
                                   GibInt end_1196_6098_8633,
                                   GibVector *vec_270_6099_8634)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_7444_8635 = idx_1195_6097_8632 == end_1196_6098_8633;

    if (fltIf_7444_8635) {
        return vec_1194_6096_8631;
    } else {
        GibFloatGibFloatProd *tmp_310;

        tmp_310 = (GibFloatGibFloatProd *) gib_vector_nth(vec_270_6099_8634,
                                                          idx_1195_6097_8632);

        GibFloatGibFloatProd fltAppE_7446_8638 = *tmp_310;
        GibVector *vec1_1199_6100_8640 =
                  gib_vector_inplace_update(vec_1194_6096_8631,
                                            idx_1195_6097_8632,
                                            &(GibFloatGibFloatGibFloatProd) {fltAppE_7446_8638.field0,
                                                                             fltAppE_7446_8638.field1,
                                                                             1.0});
        GibInt fltAppE_7447_8641 = idx_1195_6097_8632 + 1;
        GibVector *tailapp_12285 =
                   generate_loop_2376_3735(vec1_1199_6100_8640, fltAppE_7447_8641, end_1196_6098_8633, vec_270_6099_8634);

        return tailapp_12285;
    }
}
GibFloatGibFloatGibFloatProd foldl_loop_2371_3737(GibInt idx_1162_6109_8642,
                                                  GibInt end_1163_6110_8643,
                                                  GibFloatGibFloatGibFloatProd acc_1165_6111_8644,
                                                  GibVector *vec_1166_6112_8645)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_7448_8646 = idx_1162_6109_8642 == end_1163_6110_8643;

    if (fltIf_7448_8646) {
        return acc_1165_6111_8644;
    } else {
        GibFloatGibFloatGibFloatProd *tmp_312;

        tmp_312 =
            (GibFloatGibFloatGibFloatProd *) gib_vector_nth(vec_1166_6112_8645,
                                                            idx_1162_6109_8642);

        GibFloatGibFloatGibFloatProd mpt_797_5741_7133_8648 = *tmp_312;
        GibFloat fltPrm_7450_8657 = mpt_797_5741_7133_8648.field0 *
                 mpt_797_5741_7133_8648.field2;
        GibFloat fltPrd_7449_8658 = acc_1165_6111_8644.field0 +
                 fltPrm_7450_8657;
        GibFloat fltPrm_7452_8659 = mpt_797_5741_7133_8648.field1 *
                 mpt_797_5741_7133_8648.field2;
        GibFloat fltPrd_7451_8660 = acc_1165_6111_8644.field1 +
                 fltPrm_7452_8659;
        GibFloat fltPrd_7453_8661 = acc_1165_6111_8644.field2 +
                 mpt_797_5741_7133_8648.field2;
        GibInt fltAppE_7454_8663 = idx_1162_6109_8642 + 1;
        GibFloatGibFloatGibFloatProd tmp_struct_311 =
                                      foldl_loop_2371_3737(fltAppE_7454_8663, end_1163_6110_8643, (GibFloatGibFloatGibFloatProd) {fltPrd_7449_8658, fltPrd_7451_8660, fltPrd_7453_8661}, vec_1166_6112_8645);
        GibFloat pvrtmp_17324 = tmp_struct_311.field0;
        GibFloat pvrtmp_17325 = tmp_struct_311.field1;
        GibFloat pvrtmp_17326 = tmp_struct_311.field2;

        return (GibFloatGibFloatGibFloatProd) {pvrtmp_17324, pvrtmp_17325,
                                               pvrtmp_17326};
    }
}
GibFloat foldl_loop_2370_3738(GibInt idx_1162_6116_8664,
                              GibInt end_1163_6117_8665,
                              GibFloat acc_1165_6118_8666,
                              GibVector *vec_1166_6119_8667)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_7455_8668 = idx_1162_6116_8664 == end_1163_6117_8665;

    if (fltIf_7455_8668) {
        return acc_1165_6118_8666;
    } else {
        GibFloatGibFloatGibFloatProd *tmp_313;

        tmp_313 =
            (GibFloatGibFloatGibFloatProd *) gib_vector_nth(vec_1166_6119_8667,
                                                            idx_1162_6116_8664);

        GibFloatGibFloatGibFloatProd pt_300_5706_7143_8670 = *tmp_313;
        GibFloat fltPrm_7457_8675 = acc_1165_6118_8666 +
                 pt_300_5706_7143_8670.field0;
        GibFloat fltPrm_7456_8676 = fltPrm_7457_8675 +
                 pt_300_5706_7143_8670.field1;
        GibFloat acc1_1169_6120_8677 = fltPrm_7456_8676 +
                 pt_300_5706_7143_8670.field2;
        GibInt fltAppE_7458_8678 = idx_1162_6116_8664 + 1;
        GibFloat tailapp_12287 =
                  foldl_loop_2370_3738(fltAppE_7458_8678, end_1163_6117_8665, acc1_1169_6120_8677, vec_1166_6119_8667);

        return tailapp_12287;
    }
}
GibFloat foldl_loop_2370_3739(GibInt idx_1162_6123_8679,
                              GibInt end_1163_6124_8680,
                              GibFloat acc_1165_6125_8681,
                              GibVector *vec_1166_6126_8682)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_7459_8683 = idx_1162_6123_8679 == end_1163_6124_8680;

    if (fltIf_7459_8683) {
        return acc_1165_6125_8681;
    } else {
        GibFloatGibFloatGibFloatProd *tmp_314;

        tmp_314 =
            (GibFloatGibFloatGibFloatProd *) gib_vector_nth(vec_1166_6126_8682,
                                                            idx_1162_6123_8679);

        GibFloatGibFloatGibFloatProd pt_940_5757_7149_8685 = *tmp_314;
        GibFloat fltPrm_7461_8690 = acc_1165_6125_8681 +
                 pt_940_5757_7149_8685.field0;
        GibFloat fltPrm_7460_8691 = fltPrm_7461_8690 +
                 pt_940_5757_7149_8685.field1;
        GibFloat acc1_1169_6127_8692 = fltPrm_7460_8691 +
                 pt_940_5757_7149_8685.field2;
        GibInt fltAppE_7462_8693 = idx_1162_6123_8679 + 1;
        GibFloat tailapp_12288 =
                  foldl_loop_2370_3739(fltAppE_7462_8693, end_1163_6124_8680, acc1_1169_6127_8692, vec_1166_6126_8682);

        return tailapp_12288;
    }
}
GibInt foldl_loop_2369_3740(GibInt idx_1162_6128_8694,
                            GibInt end_1163_6129_8695,
                            GibInt acc_1165_6130_8696,
                            GibVector *vec_1166_6131_8697,
                            GibFloatGibFloatGibFloatProd query_167_6132_8698,
                            GibFloat radius_sq_170_6133_8699)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_7463_8700 = idx_1162_6128_8694 == end_1163_6129_8695;

    if (fltIf_7463_8700) {
        return acc_1165_6130_8696;
    } else {
        GibFloatGibFloatGibFloatProd *tmp_315;

        tmp_315 =
            (GibFloatGibFloatGibFloatProd *) gib_vector_nth(vec_1166_6131_8697,
                                                            idx_1162_6128_8694);

        GibFloatGibFloatGibFloatProd pt_171_5660_7155_8702 = *tmp_315;
        GibFloat fltPrm_7465_8705 =
                  dist_point3d((GibFloatGibFloatGibFloatProd) {query_167_6132_8698.field0, query_167_6132_8698.field1, query_167_6132_8698.field2}, (GibFloatGibFloatGibFloatProd) {pt_171_5660_7155_8702.field0, pt_171_5660_7155_8702.field1, pt_171_5660_7155_8702.field2});
        GibBool fltIf_7464_8706 = fltPrm_7465_8705 < radius_sq_170_6133_8699;
        GibInt acc1_1169_6134_8707;

        if (fltIf_7464_8706) {
            GibInt flt_17333 = acc_1165_6130_8696 + 1;

            acc1_1169_6134_8707 = flt_17333;
        } else {
            acc1_1169_6134_8707 = acc_1165_6130_8696;
        }

        GibInt fltAppE_7466_8708 = idx_1162_6128_8694 + 1;
        GibInt tailapp_12289 =
                foldl_loop_2369_3740(fltAppE_7466_8708, end_1163_6129_8695, acc1_1169_6134_8707, vec_1166_6131_8697, (GibFloatGibFloatGibFloatProd) {query_167_6132_8698.field0, query_167_6132_8698.field1, query_167_6132_8698.field2}, radius_sq_170_6133_8699);

        return tailapp_12289;
    }
}
GibFloat foldl_loop_2368_3741(GibInt idx_1162_6137_8709,
                              GibInt end_1163_6138_8710,
                              GibFloat acc_1165_6139_8711,
                              GibVector *vec_1166_6140_8712)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_7467_8713 = idx_1162_6137_8709 == end_1163_6138_8710;

    if (fltIf_7467_8713) {
        return acc_1165_6139_8711;
    } else {
        GibFloatGibFloatProd *tmp_316;

        tmp_316 = (GibFloatGibFloatProd *) gib_vector_nth(vec_1166_6140_8712,
                                                          idx_1162_6137_8709);

        GibFloatGibFloatProd pt_102_5636_7159_8715 = *tmp_316;
        GibFloat acc1_1169_6141_8717 =
                  minFloat(pt_102_5636_7159_8715.field0, acc_1165_6139_8711);
        GibInt fltAppE_7469_8718 = idx_1162_6137_8709 + 1;
        GibFloat tailapp_12290 =
                  foldl_loop_2368_3741(fltAppE_7469_8718, end_1163_6138_8710, acc1_1169_6141_8717, vec_1166_6140_8712);

        return tailapp_12290;
    }
}
GibFloat foldl_loop_2368_3742(GibInt idx_1162_6144_8719,
                              GibInt end_1163_6145_8720,
                              GibFloat acc_1165_6146_8721,
                              GibVector *vec_1166_6147_8722)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_7470_8723 = idx_1162_6144_8719 == end_1163_6145_8720;

    if (fltIf_7470_8723) {
        return acc_1165_6146_8721;
    } else {
        GibFloatGibFloatProd *tmp_317;

        tmp_317 = (GibFloatGibFloatProd *) gib_vector_nth(vec_1166_6147_8722,
                                                          idx_1162_6144_8719);

        GibFloatGibFloatProd pt_105_5638_7161_8725 = *tmp_317;
        GibFloat acc1_1169_6148_8727 =
                  minFloat(pt_105_5638_7161_8725.field1, acc_1165_6146_8721);
        GibInt fltAppE_7472_8728 = idx_1162_6144_8719 + 1;
        GibFloat tailapp_12291 =
                  foldl_loop_2368_3742(fltAppE_7472_8728, end_1163_6145_8720, acc1_1169_6148_8727, vec_1166_6147_8722);

        return tailapp_12291;
    }
}
GibFloat foldl_loop_2368_3743(GibInt idx_1162_6151_8729,
                              GibInt end_1163_6152_8730,
                              GibFloat acc_1165_6153_8731,
                              GibVector *vec_1166_6154_8732)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_7473_8733 = idx_1162_6151_8729 == end_1163_6152_8730;

    if (fltIf_7473_8733) {
        return acc_1165_6153_8731;
    } else {
        GibFloatGibFloatProd *tmp_318;

        tmp_318 = (GibFloatGibFloatProd *) gib_vector_nth(vec_1166_6154_8732,
                                                          idx_1162_6151_8729);

        GibFloatGibFloatProd pt_108_5640_7163_8735 = *tmp_318;
        GibFloat acc1_1169_6155_8737 =
                  maxFloat(pt_108_5640_7163_8735.field0, acc_1165_6153_8731);
        GibInt fltAppE_7475_8738 = idx_1162_6151_8729 + 1;
        GibFloat tailapp_12292 =
                  foldl_loop_2368_3743(fltAppE_7475_8738, end_1163_6152_8730, acc1_1169_6155_8737, vec_1166_6154_8732);

        return tailapp_12292;
    }
}
GibFloat foldl_loop_2368_3744(GibInt idx_1162_6158_8739,
                              GibInt end_1163_6159_8740,
                              GibFloat acc_1165_6160_8741,
                              GibVector *vec_1166_6161_8742)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_7476_8743 = idx_1162_6158_8739 == end_1163_6159_8740;

    if (fltIf_7476_8743) {
        return acc_1165_6160_8741;
    } else {
        GibFloatGibFloatProd *tmp_319;

        tmp_319 = (GibFloatGibFloatProd *) gib_vector_nth(vec_1166_6161_8742,
                                                          idx_1162_6158_8739);

        GibFloatGibFloatProd pt_111_5642_7165_8745 = *tmp_319;
        GibFloat acc1_1169_6162_8747 =
                  maxFloat(pt_111_5642_7165_8745.field1, acc_1165_6160_8741);
        GibInt fltAppE_7478_8748 = idx_1162_6158_8739 + 1;
        GibFloat tailapp_12293 =
                  foldl_loop_2368_3744(fltAppE_7478_8748, end_1163_6159_8740, acc1_1169_6162_8747, vec_1166_6161_8742);

        return tailapp_12293;
    }
}
GibFloat foldl_loop_2368_3745(GibInt idx_1162_6165_8749,
                              GibInt end_1163_6166_8750,
                              GibFloat acc_1165_6167_8751,
                              GibVector *vec_1166_6168_8752)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_7479_8753 = idx_1162_6165_8749 == end_1163_6166_8750;

    if (fltIf_7479_8753) {
        return acc_1165_6167_8751;
    } else {
        GibFloatGibFloatProd *tmp_320;

        tmp_320 = (GibFloatGibFloatProd *) gib_vector_nth(vec_1166_6168_8752,
                                                          idx_1162_6165_8749);

        GibFloatGibFloatProd pt_129_5652_7167_8755 = *tmp_320;
        GibFloat acc1_1169_6169_8757 =
                  minFloat(pt_129_5652_7167_8755.field0, acc_1165_6167_8751);
        GibInt fltAppE_7481_8758 = idx_1162_6165_8749 + 1;
        GibFloat tailapp_12294 =
                  foldl_loop_2368_3745(fltAppE_7481_8758, end_1163_6166_8750, acc1_1169_6169_8757, vec_1166_6168_8752);

        return tailapp_12294;
    }
}
GibFloat foldl_loop_2368_3746(GibInt idx_1162_6172_8759,
                              GibInt end_1163_6173_8760,
                              GibFloat acc_1165_6174_8761,
                              GibVector *vec_1166_6175_8762)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_7482_8763 = idx_1162_6172_8759 == end_1163_6173_8760;

    if (fltIf_7482_8763) {
        return acc_1165_6174_8761;
    } else {
        GibFloatGibFloatProd *tmp_321;

        tmp_321 = (GibFloatGibFloatProd *) gib_vector_nth(vec_1166_6175_8762,
                                                          idx_1162_6172_8759);

        GibFloatGibFloatProd pt_132_5654_7169_8765 = *tmp_321;
        GibFloat acc1_1169_6176_8767 =
                  minFloat(pt_132_5654_7169_8765.field1, acc_1165_6174_8761);
        GibInt fltAppE_7484_8768 = idx_1162_6172_8759 + 1;
        GibFloat tailapp_12295 =
                  foldl_loop_2368_3746(fltAppE_7484_8768, end_1163_6173_8760, acc1_1169_6176_8767, vec_1166_6175_8762);

        return tailapp_12295;
    }
}
GibFloat foldl_loop_2368_3747(GibInt idx_1162_6179_8769,
                              GibInt end_1163_6180_8770,
                              GibFloat acc_1165_6181_8771,
                              GibVector *vec_1166_6182_8772)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_7485_8773 = idx_1162_6179_8769 == end_1163_6180_8770;

    if (fltIf_7485_8773) {
        return acc_1165_6181_8771;
    } else {
        GibFloatGibFloatProd *tmp_322;

        tmp_322 = (GibFloatGibFloatProd *) gib_vector_nth(vec_1166_6182_8772,
                                                          idx_1162_6179_8769);

        GibFloatGibFloatProd pt_135_5656_7171_8775 = *tmp_322;
        GibFloat acc1_1169_6183_8777 =
                  maxFloat(pt_135_5656_7171_8775.field0, acc_1165_6181_8771);
        GibInt fltAppE_7487_8778 = idx_1162_6179_8769 + 1;
        GibFloat tailapp_12296 =
                  foldl_loop_2368_3747(fltAppE_7487_8778, end_1163_6180_8770, acc1_1169_6183_8777, vec_1166_6182_8772);

        return tailapp_12296;
    }
}
GibFloat foldl_loop_2368_3748(GibInt idx_1162_6186_8779,
                              GibInt end_1163_6187_8780,
                              GibFloat acc_1165_6188_8781,
                              GibVector *vec_1166_6189_8782)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_7488_8783 = idx_1162_6186_8779 == end_1163_6187_8780;

    if (fltIf_7488_8783) {
        return acc_1165_6188_8781;
    } else {
        GibFloatGibFloatProd *tmp_323;

        tmp_323 = (GibFloatGibFloatProd *) gib_vector_nth(vec_1166_6189_8782,
                                                          idx_1162_6186_8779);

        GibFloatGibFloatProd pt_138_5658_7173_8785 = *tmp_323;
        GibFloat acc1_1169_6190_8787 =
                  maxFloat(pt_138_5658_7173_8785.field1, acc_1165_6188_8781);
        GibInt fltAppE_7490_8788 = idx_1162_6186_8779 + 1;
        GibFloat tailapp_12297 =
                  foldl_loop_2368_3748(fltAppE_7490_8788, end_1163_6187_8780, acc1_1169_6190_8787, vec_1166_6189_8782);

        return tailapp_12297;
    }
}
GibBoolGibIntProd foldl_loop_2367_3749(GibInt idx_1162_6191_8789,
                                       GibInt end_1163_6192_8790,
                                       GibBoolGibIntProd acc_1165_6193_8791,
                                       GibVector *vec_1166_6194_8792,
                                       GibVector *pts_191_6195_8793,
                                       GibVector *actual_192_6196_8794)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_7491_8795 = idx_1162_6191_8789 == end_1163_6192_8790;

    if (fltIf_7491_8795) {
        return acc_1165_6193_8791;
    } else {
        GibInt *tmp_327;

        tmp_327 = (GibInt *) gib_vector_nth(vec_1166_6194_8792,
                                            idx_1162_6191_8789);

        GibInt i_196_5675_7175_8797 = *tmp_327;
        GibFloatGibFloatGibFloatProd *tmp_326;

        tmp_326 =
            (GibFloatGibFloatGibFloatProd *) gib_vector_nth(pts_191_6195_8793,
                                                            i_196_5675_7175_8797);

        GibFloatGibFloatGibFloatProd pt_198_5678_7178_8800 = *tmp_326;
        GibFloatGibFloatGibFloatProd *tmp_325;

        tmp_325 =
            (GibFloatGibFloatGibFloatProd *) gib_vector_nth(actual_192_6196_8794,
                                                            i_196_5675_7175_8797);

        GibFloatGibFloatGibFloatProd nn_199_5679_7179_8801 = *tmp_325;
        GibBool fltIf_7492_8805 =
                 eq_point3d((GibFloatGibFloatGibFloatProd) {pt_198_5678_7178_8800.field0, pt_198_5678_7178_8800.field1, pt_198_5678_7178_8800.field2}, (GibFloatGibFloatGibFloatProd) {nn_199_5679_7179_8801.field0, nn_199_5679_7179_8801.field1, nn_199_5679_7179_8801.field2});
        GibBool pvrtmp_17343;
        GibInt pvrtmp_17344;

        if (fltIf_7492_8805) {
            GibBool fltPrd_7493_8807 = acc_1165_6193_8791.field0 && true;

            pvrtmp_17343 = fltPrd_7493_8807;
            pvrtmp_17344 = acc_1165_6193_8791.field1;
        } else {
            GibInt fltPrd_7496_8809 = acc_1165_6193_8791.field1 + 1;

            pvrtmp_17343 = false;
            pvrtmp_17344 = fltPrd_7496_8809;
        }

        GibInt fltAppE_7497_8811 = idx_1162_6191_8789 + 1;
        GibBoolGibIntProd tmp_struct_324 =
                           foldl_loop_2367_3749(fltAppE_7497_8811, end_1163_6192_8790, (GibBoolGibIntProd) {pvrtmp_17343, pvrtmp_17344}, vec_1166_6194_8792, pts_191_6195_8793, actual_192_6196_8794);
        GibBool pvrtmp_17347 = tmp_struct_324.field0;
        GibInt pvrtmp_17348 = tmp_struct_324.field1;

        return (GibBoolGibIntProd) {pvrtmp_17347, pvrtmp_17348};
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_KdTree(GibCursor end_r_10722,
                                                               GibCursor end_r_10723,
                                                               GibCursor loc_10721,
                                                               GibCursor arg_4208_6198_8812)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_10721 + 74 > end_r_10723) {
        gib_grow_region(&loc_10721, &end_r_10723);
    }

    GibPackedTag tmpval_17349 = *(GibPackedTag *) arg_4208_6198_8812;
    GibCursor tmpcur_17350 = arg_4208_6198_8812 + 1;


  switch_17442:
    ;
    switch (tmpval_17349) {

      case 0:
        {
            GibFloat tmpval_17351 = *(GibFloat *) tmpcur_17350;
            GibCursor tmpcur_17352 = tmpcur_17350 + sizeof(GibFloat);
            GibFloat tmpval_17353 = *(GibFloat *) tmpcur_17352;
            GibCursor tmpcur_17354 = tmpcur_17352 + sizeof(GibFloat);
            GibFloat tmpval_17355 = *(GibFloat *) tmpcur_17354;
            GibCursor tmpcur_17356 = tmpcur_17354 + sizeof(GibFloat);
            GibCursor jump_12301 = tmpcur_17354 + 4;

            *(GibPackedTag *) loc_10721 = 0;

            GibCursor writetag_14318 = loc_10721 + 1;
            GibCursor after_tag_14319 = loc_10721 + 1;

            *(GibFloat *) after_tag_14319 = tmpval_17351;

            GibCursor writecur_14323 = after_tag_14319 + sizeof(GibFloat);

            *(GibFloat *) writecur_14323 = tmpval_17353;

            GibCursor writecur_14324 = writecur_14323 + sizeof(GibFloat);

            *(GibFloat *) writecur_14324 = tmpval_17355;

            GibCursor writecur_14325 = writecur_14324 + sizeof(GibFloat);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_10722,
                                                                        end_r_10723,
                                                                        jump_12301,
                                                                        loc_10721,
                                                                        writecur_14325};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_331 = *(uintptr_t *) tmpcur_17350;
            GibCursor tmpcur_17361 = GIB_UNTAG(tagged_tmpcur_331);
            GibCursor tmpaftercur_17362 = tmpcur_17350 + 8;
            uint16_t tmptag_17363 = GIB_GET_TAG(tagged_tmpcur_331);
            GibCursor end_from_tagged_absran_10585 = tmpcur_17361 +
                      tmptag_17363;
            GibFloat tmpval_17364 = *(GibFloat *) tmpaftercur_17362;
            GibCursor tmpcur_17365 = tmpaftercur_17362 + sizeof(GibFloat);
            GibFloat tmpval_17366 = *(GibFloat *) tmpcur_17365;
            GibCursor tmpcur_17367 = tmpcur_17365 + sizeof(GibFloat);
            GibFloat tmpval_17368 = *(GibFloat *) tmpcur_17367;
            GibCursor tmpcur_17369 = tmpcur_17367 + sizeof(GibFloat);
            GibInt tmpval_17370 = *(GibInt *) tmpcur_17369;
            GibCursor tmpcur_17371 = tmpcur_17369 + sizeof(GibInt);
            GibInt tmpval_17372 = *(GibInt *) tmpcur_17371;
            GibCursor tmpcur_17373 = tmpcur_17371 + sizeof(GibInt);
            GibFloat tmpval_17374 = *(GibFloat *) tmpcur_17373;
            GibCursor tmpcur_17375 = tmpcur_17373 + sizeof(GibFloat);
            GibFloat tmpval_17376 = *(GibFloat *) tmpcur_17375;
            GibCursor tmpcur_17377 = tmpcur_17375 + sizeof(GibFloat);
            GibFloat tmpval_17378 = *(GibFloat *) tmpcur_17377;
            GibCursor tmpcur_17379 = tmpcur_17377 + sizeof(GibFloat);
            GibFloat tmpval_17380 = *(GibFloat *) tmpcur_17379;
            GibCursor tmpcur_17381 = tmpcur_17379 + sizeof(GibFloat);
            GibFloat tmpval_17382 = *(GibFloat *) tmpcur_17381;
            GibCursor tmpcur_17383 = tmpcur_17381 + sizeof(GibFloat);
            GibFloat tmpval_17384 = *(GibFloat *) tmpcur_17383;
            GibCursor tmpcur_17385 = tmpcur_17383 + sizeof(GibFloat);
            GibFloat tmpval_17386 = *(GibFloat *) tmpcur_17385;
            GibCursor tmpcur_17387 = tmpcur_17385 + sizeof(GibFloat);
            GibCursor loc_11410 = loc_10721 + 65;

            *(GibPackedTag *) loc_10721 = 3;

            GibCursor writetag_14348 = loc_10721 + 1;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_328 =
                                                               _copy_KdTree(end_r_10722, end_r_10723, loc_11410, tmpcur_17387);
            GibCursor pvrtmp_17388 = tmp_struct_328.field0;
            GibCursor pvrtmp_17389 = tmp_struct_328.field1;
            GibCursor pvrtmp_17390 = tmp_struct_328.field2;
            GibCursor pvrtmp_17391 = tmp_struct_328.field3;
            GibCursor pvrtmp_17392 = tmp_struct_328.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_329 =
                                                               _copy_KdTree(end_from_tagged_absran_10585, pvrtmp_17389, pvrtmp_17392, tmpcur_17361);
            GibCursor pvrtmp_17397 = tmp_struct_329.field0;
            GibCursor pvrtmp_17398 = tmp_struct_329.field1;
            GibCursor pvrtmp_17399 = tmp_struct_329.field2;
            GibCursor pvrtmp_17400 = tmp_struct_329.field3;
            GibCursor pvrtmp_17401 = tmp_struct_329.field4;
            uint16_t offset_330 = pvrtmp_17389 - pvrtmp_17392;
            uintptr_t ran_10588 = GIB_STORE_TAG(pvrtmp_17392, offset_330);
            GibCursor after_tag_14349 = loc_10721 + 1;

            *(uintptr_t *) after_tag_14349 = ran_10588;

            GibCursor writecur_14353 = after_tag_14349 + 8;

            *(GibFloat *) writecur_14353 = tmpval_17364;

            GibCursor writecur_14354 = writecur_14353 + sizeof(GibFloat);

            *(GibFloat *) writecur_14354 = tmpval_17366;

            GibCursor writecur_14355 = writecur_14354 + sizeof(GibFloat);

            *(GibFloat *) writecur_14355 = tmpval_17368;

            GibCursor writecur_14356 = writecur_14355 + sizeof(GibFloat);

            *(GibInt *) writecur_14356 = tmpval_17370;

            GibCursor writecur_14357 = writecur_14356 + sizeof(GibInt);

            *(GibInt *) writecur_14357 = tmpval_17372;

            GibCursor writecur_14358 = writecur_14357 + sizeof(GibInt);

            *(GibFloat *) writecur_14358 = tmpval_17374;

            GibCursor writecur_14359 = writecur_14358 + sizeof(GibFloat);

            *(GibFloat *) writecur_14359 = tmpval_17376;

            GibCursor writecur_14360 = writecur_14359 + sizeof(GibFloat);

            *(GibFloat *) writecur_14360 = tmpval_17378;

            GibCursor writecur_14361 = writecur_14360 + sizeof(GibFloat);

            *(GibFloat *) writecur_14361 = tmpval_17380;

            GibCursor writecur_14362 = writecur_14361 + sizeof(GibFloat);

            *(GibFloat *) writecur_14362 = tmpval_17382;

            GibCursor writecur_14363 = writecur_14362 + sizeof(GibFloat);

            *(GibFloat *) writecur_14363 = tmpval_17384;

            GibCursor writecur_14364 = writecur_14363 + sizeof(GibFloat);

            *(GibFloat *) writecur_14364 = tmpval_17386;

            GibCursor writecur_14365 = writecur_14364 + sizeof(GibFloat);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_17397,
                                                                        pvrtmp_17398,
                                                                        pvrtmp_17399,
                                                                        loc_10721,
                                                                        pvrtmp_17401};
            break;
        }

      case 2:
        {
            GibCursor jump_12319 = arg_4208_6198_8812 + 1;

            *(GibPackedTag *) loc_10721 = 2;

            GibCursor writetag_14372 = loc_10721 + 1;
            GibCursor after_tag_14373 = loc_10721 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_10722,
                                                                        end_r_10723,
                                                                        jump_12319,
                                                                        loc_10721,
                                                                        after_tag_14373};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_333 = *(uintptr_t *) tmpcur_17350;
            GibCursor tmpcur_17414 = GIB_UNTAG(tagged_tmpcur_333);
            GibCursor tmpaftercur_17415 = tmpcur_17350 + 8;
            uint16_t tmptag_17416 = GIB_GET_TAG(tagged_tmpcur_333);
            GibCursor end_from_tagged_indr_12629 = tmpcur_17414 + tmptag_17416;
            GibCursor jump_12631 = tmpcur_17350 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_332 =
                                                               _copy_KdTree(end_from_tagged_indr_12629, end_r_10723, loc_10721, tmpcur_17414);
            GibCursor pvrtmp_17417 = tmp_struct_332.field0;
            GibCursor pvrtmp_17418 = tmp_struct_332.field1;
            GibCursor pvrtmp_17419 = tmp_struct_332.field2;
            GibCursor pvrtmp_17420 = tmp_struct_332.field3;
            GibCursor pvrtmp_17421 = tmp_struct_332.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_10722,
                                                                        pvrtmp_17418,
                                                                        jump_12631,
                                                                        pvrtmp_17420,
                                                                        pvrtmp_17421};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_335 = *(uintptr_t *) tmpcur_17350;
            GibCursor tmpcur_17428 = GIB_UNTAG(tagged_tmpcur_335);
            GibCursor tmpaftercur_17429 = tmpcur_17350 + 8;
            uint16_t tmptag_17430 = GIB_GET_TAG(tagged_tmpcur_335);
            GibCursor end_from_tagged_indr_12629 = tmpcur_17428 + tmptag_17430;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_334 =
                                                               _copy_KdTree(end_from_tagged_indr_12629, end_r_10723, loc_10721, tmpcur_17428);
            GibCursor pvrtmp_17431 = tmp_struct_334.field0;
            GibCursor pvrtmp_17432 = tmp_struct_334.field1;
            GibCursor pvrtmp_17433 = tmp_struct_334.field2;
            GibCursor pvrtmp_17434 = tmp_struct_334.field3;
            GibCursor pvrtmp_17435 = tmp_struct_334.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_17431,
                                                                        pvrtmp_17432,
                                                                        pvrtmp_17433,
                                                                        pvrtmp_17434,
                                                                        pvrtmp_17435};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_17349");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_KdTree(GibCursor end_r_10726,
                                                                            GibCursor end_r_10727,
                                                                            GibCursor loc_10725,
                                                                            GibCursor arg_4243_6233_8847)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_17443 = *(GibPackedTag *) arg_4243_6233_8847;
    GibCursor tmpcur_17444 = arg_4243_6233_8847 + 1;


  switch_17536:
    ;
    switch (tmpval_17443) {

      case 0:
        {
            GibFloat tmpval_17445 = *(GibFloat *) tmpcur_17444;
            GibCursor tmpcur_17446 = tmpcur_17444 + sizeof(GibFloat);
            GibFloat tmpval_17447 = *(GibFloat *) tmpcur_17446;
            GibCursor tmpcur_17448 = tmpcur_17446 + sizeof(GibFloat);
            GibFloat tmpval_17449 = *(GibFloat *) tmpcur_17448;
            GibCursor tmpcur_17450 = tmpcur_17448 + sizeof(GibFloat);
            GibCursor jump_12323 = tmpcur_17448 + 4;

            *(GibPackedTag *) loc_10725 = 0;

            GibCursor writetag_14393 = loc_10725 + 1;
            GibCursor after_tag_14394 = loc_10725 + 1;

            *(GibFloat *) after_tag_14394 = tmpval_17445;

            GibCursor writecur_14398 = after_tag_14394 + sizeof(GibFloat);

            *(GibFloat *) writecur_14398 = tmpval_17447;

            GibCursor writecur_14399 = writecur_14398 + sizeof(GibFloat);

            *(GibFloat *) writecur_14399 = tmpval_17449;

            GibCursor writecur_14400 = writecur_14399 + sizeof(GibFloat);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_10726,
                                                                        end_r_10727,
                                                                        jump_12323,
                                                                        loc_10725,
                                                                        writecur_14400};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_341 = *(uintptr_t *) tmpcur_17444;
            GibCursor tmpcur_17455 = GIB_UNTAG(tagged_tmpcur_341);
            GibCursor tmpaftercur_17456 = tmpcur_17444 + 8;
            uint16_t tmptag_17457 = GIB_GET_TAG(tagged_tmpcur_341);
            GibCursor end_from_tagged_absran_10590 = tmpcur_17455 +
                      tmptag_17457;
            GibFloat tmpval_17458 = *(GibFloat *) tmpaftercur_17456;
            GibCursor tmpcur_17459 = tmpaftercur_17456 + sizeof(GibFloat);
            GibFloat tmpval_17460 = *(GibFloat *) tmpcur_17459;
            GibCursor tmpcur_17461 = tmpcur_17459 + sizeof(GibFloat);
            GibFloat tmpval_17462 = *(GibFloat *) tmpcur_17461;
            GibCursor tmpcur_17463 = tmpcur_17461 + sizeof(GibFloat);
            GibInt tmpval_17464 = *(GibInt *) tmpcur_17463;
            GibCursor tmpcur_17465 = tmpcur_17463 + sizeof(GibInt);
            GibInt tmpval_17466 = *(GibInt *) tmpcur_17465;
            GibCursor tmpcur_17467 = tmpcur_17465 + sizeof(GibInt);
            GibFloat tmpval_17468 = *(GibFloat *) tmpcur_17467;
            GibCursor tmpcur_17469 = tmpcur_17467 + sizeof(GibFloat);
            GibFloat tmpval_17470 = *(GibFloat *) tmpcur_17469;
            GibCursor tmpcur_17471 = tmpcur_17469 + sizeof(GibFloat);
            GibFloat tmpval_17472 = *(GibFloat *) tmpcur_17471;
            GibCursor tmpcur_17473 = tmpcur_17471 + sizeof(GibFloat);
            GibFloat tmpval_17474 = *(GibFloat *) tmpcur_17473;
            GibCursor tmpcur_17475 = tmpcur_17473 + sizeof(GibFloat);
            GibFloat tmpval_17476 = *(GibFloat *) tmpcur_17475;
            GibCursor tmpcur_17477 = tmpcur_17475 + sizeof(GibFloat);
            GibFloat tmpval_17478 = *(GibFloat *) tmpcur_17477;
            GibCursor tmpcur_17479 = tmpcur_17477 + sizeof(GibFloat);
            GibFloat tmpval_17480 = *(GibFloat *) tmpcur_17479;
            GibCursor tmpcur_17481 = tmpcur_17479 + sizeof(GibFloat);
            GibCursor loc_11489 = loc_10725 + 57;

            *(GibPackedTag *) loc_10725 = 1;

            GibCursor writetag_14423 = loc_10725 + 1;
            GibCursor after_tag_14424 = loc_10725 + 1;

            *(GibFloat *) after_tag_14424 = tmpval_17458;

            GibCursor writecur_14428 = after_tag_14424 + sizeof(GibFloat);

            *(GibFloat *) writecur_14428 = tmpval_17460;

            GibCursor writecur_14429 = writecur_14428 + sizeof(GibFloat);

            *(GibFloat *) writecur_14429 = tmpval_17462;

            GibCursor writecur_14430 = writecur_14429 + sizeof(GibFloat);

            *(GibInt *) writecur_14430 = tmpval_17464;

            GibCursor writecur_14431 = writecur_14430 + sizeof(GibInt);

            *(GibInt *) writecur_14431 = tmpval_17466;

            GibCursor writecur_14432 = writecur_14431 + sizeof(GibInt);

            *(GibFloat *) writecur_14432 = tmpval_17468;

            GibCursor writecur_14433 = writecur_14432 + sizeof(GibFloat);

            *(GibFloat *) writecur_14433 = tmpval_17470;

            GibCursor writecur_14434 = writecur_14433 + sizeof(GibFloat);

            *(GibFloat *) writecur_14434 = tmpval_17472;

            GibCursor writecur_14435 = writecur_14434 + sizeof(GibFloat);

            *(GibFloat *) writecur_14435 = tmpval_17474;

            GibCursor writecur_14436 = writecur_14435 + sizeof(GibFloat);

            *(GibFloat *) writecur_14436 = tmpval_17476;

            GibCursor writecur_14437 = writecur_14436 + sizeof(GibFloat);

            *(GibFloat *) writecur_14437 = tmpval_17478;

            GibCursor writecur_14438 = writecur_14437 + sizeof(GibFloat);

            *(GibFloat *) writecur_14438 = tmpval_17480;

            GibCursor writecur_14439 = writecur_14438 + sizeof(GibFloat);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_339 =
                                                               _copy_without_ptrs_KdTree(end_r_10726, end_r_10727, loc_11489, tmpcur_17481);
            GibCursor pvrtmp_17482 = tmp_struct_339.field0;
            GibCursor pvrtmp_17483 = tmp_struct_339.field1;
            GibCursor pvrtmp_17484 = tmp_struct_339.field2;
            GibCursor pvrtmp_17485 = tmp_struct_339.field3;
            GibCursor pvrtmp_17486 = tmp_struct_339.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_340 =
                                                               _copy_without_ptrs_KdTree(end_from_tagged_absran_10590, pvrtmp_17483, pvrtmp_17486, tmpcur_17455);
            GibCursor pvrtmp_17491 = tmp_struct_340.field0;
            GibCursor pvrtmp_17492 = tmp_struct_340.field1;
            GibCursor pvrtmp_17493 = tmp_struct_340.field2;
            GibCursor pvrtmp_17494 = tmp_struct_340.field3;
            GibCursor pvrtmp_17495 = tmp_struct_340.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_17491,
                                                                        pvrtmp_17492,
                                                                        pvrtmp_17493,
                                                                        loc_10725,
                                                                        pvrtmp_17495};
            break;
        }

      case 2:
        {
            GibCursor jump_12341 = arg_4243_6233_8847 + 1;

            *(GibPackedTag *) loc_10725 = 2;

            GibCursor writetag_14446 = loc_10725 + 1;
            GibCursor after_tag_14447 = loc_10725 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_10726,
                                                                        end_r_10727,
                                                                        jump_12341,
                                                                        loc_10725,
                                                                        after_tag_14447};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_343 = *(uintptr_t *) tmpcur_17444;
            GibCursor tmpcur_17508 = GIB_UNTAG(tagged_tmpcur_343);
            GibCursor tmpaftercur_17509 = tmpcur_17444 + 8;
            uint16_t tmptag_17510 = GIB_GET_TAG(tagged_tmpcur_343);
            GibCursor end_from_tagged_indr_12635 = tmpcur_17508 + tmptag_17510;
            GibCursor jump_12637 = tmpcur_17444 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_342 =
                                                               _copy_without_ptrs_KdTree(end_from_tagged_indr_12635, end_r_10727, loc_10725, tmpcur_17508);
            GibCursor pvrtmp_17511 = tmp_struct_342.field0;
            GibCursor pvrtmp_17512 = tmp_struct_342.field1;
            GibCursor pvrtmp_17513 = tmp_struct_342.field2;
            GibCursor pvrtmp_17514 = tmp_struct_342.field3;
            GibCursor pvrtmp_17515 = tmp_struct_342.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_10726,
                                                                        pvrtmp_17512,
                                                                        jump_12637,
                                                                        pvrtmp_17514,
                                                                        pvrtmp_17515};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_345 = *(uintptr_t *) tmpcur_17444;
            GibCursor tmpcur_17522 = GIB_UNTAG(tagged_tmpcur_345);
            GibCursor tmpaftercur_17523 = tmpcur_17444 + 8;
            uint16_t tmptag_17524 = GIB_GET_TAG(tagged_tmpcur_345);
            GibCursor end_from_tagged_indr_12635 = tmpcur_17522 + tmptag_17524;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_344 =
                                                               _copy_without_ptrs_KdTree(end_from_tagged_indr_12635, end_r_10727, loc_10725, tmpcur_17522);
            GibCursor pvrtmp_17525 = tmp_struct_344.field0;
            GibCursor pvrtmp_17526 = tmp_struct_344.field1;
            GibCursor pvrtmp_17527 = tmp_struct_344.field2;
            GibCursor pvrtmp_17528 = tmp_struct_344.field3;
            GibCursor pvrtmp_17529 = tmp_struct_344.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_17525,
                                                                        pvrtmp_17526,
                                                                        pvrtmp_17527,
                                                                        pvrtmp_17528,
                                                                        pvrtmp_17529};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_17443");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_KdTree(GibCursor end_r_10729,
                                        GibCursor arg_4278_6268_8882)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_17537 = *(GibPackedTag *) arg_4278_6268_8882;
    GibCursor tmpcur_17538 = arg_4278_6268_8882 + 1;


  switch_17586:
    ;
    switch (tmpval_17537) {

      case 0:
        {
            GibFloat tmpval_17539 = *(GibFloat *) tmpcur_17538;
            GibCursor tmpcur_17540 = tmpcur_17538 + sizeof(GibFloat);
            GibFloat tmpval_17541 = *(GibFloat *) tmpcur_17540;
            GibCursor tmpcur_17542 = tmpcur_17540 + sizeof(GibFloat);
            GibFloat tmpval_17543 = *(GibFloat *) tmpcur_17542;
            GibCursor tmpcur_17544 = tmpcur_17542 + sizeof(GibFloat);
            GibCursor jump_12345 = tmpcur_17542 + 4;

            return (GibCursorGibCursorProd) {end_r_10729, jump_12345};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_348 = *(uintptr_t *) tmpcur_17538;
            GibCursor tmpcur_17545 = GIB_UNTAG(tagged_tmpcur_348);
            GibCursor tmpaftercur_17546 = tmpcur_17538 + 8;
            uint16_t tmptag_17547 = GIB_GET_TAG(tagged_tmpcur_348);
            GibCursor end_from_tagged_absran_10593 = tmpcur_17545 +
                      tmptag_17547;
            GibFloat tmpval_17548 = *(GibFloat *) tmpaftercur_17546;
            GibCursor tmpcur_17549 = tmpaftercur_17546 + sizeof(GibFloat);
            GibFloat tmpval_17550 = *(GibFloat *) tmpcur_17549;
            GibCursor tmpcur_17551 = tmpcur_17549 + sizeof(GibFloat);
            GibFloat tmpval_17552 = *(GibFloat *) tmpcur_17551;
            GibCursor tmpcur_17553 = tmpcur_17551 + sizeof(GibFloat);
            GibInt tmpval_17554 = *(GibInt *) tmpcur_17553;
            GibCursor tmpcur_17555 = tmpcur_17553 + sizeof(GibInt);
            GibInt tmpval_17556 = *(GibInt *) tmpcur_17555;
            GibCursor tmpcur_17557 = tmpcur_17555 + sizeof(GibInt);
            GibFloat tmpval_17558 = *(GibFloat *) tmpcur_17557;
            GibCursor tmpcur_17559 = tmpcur_17557 + sizeof(GibFloat);
            GibFloat tmpval_17560 = *(GibFloat *) tmpcur_17559;
            GibCursor tmpcur_17561 = tmpcur_17559 + sizeof(GibFloat);
            GibFloat tmpval_17562 = *(GibFloat *) tmpcur_17561;
            GibCursor tmpcur_17563 = tmpcur_17561 + sizeof(GibFloat);
            GibFloat tmpval_17564 = *(GibFloat *) tmpcur_17563;
            GibCursor tmpcur_17565 = tmpcur_17563 + sizeof(GibFloat);
            GibFloat tmpval_17566 = *(GibFloat *) tmpcur_17565;
            GibCursor tmpcur_17567 = tmpcur_17565 + sizeof(GibFloat);
            GibFloat tmpval_17568 = *(GibFloat *) tmpcur_17567;
            GibCursor tmpcur_17569 = tmpcur_17567 + sizeof(GibFloat);
            GibFloat tmpval_17570 = *(GibFloat *) tmpcur_17569;
            GibCursor tmpcur_17571 = tmpcur_17569 + sizeof(GibFloat);
            GibCursorGibCursorProd tmp_struct_346 =
                                    _traverse_KdTree(end_r_10729, tmpcur_17571);
            GibCursor pvrtmp_17572 = tmp_struct_346.field0;
            GibCursor pvrtmp_17573 = tmp_struct_346.field1;
            GibCursorGibCursorProd tmp_struct_347 =
                                    _traverse_KdTree(end_from_tagged_absran_10593, tmpcur_17545);
            GibCursor pvrtmp_17574 = tmp_struct_347.field0;
            GibCursor pvrtmp_17575 = tmp_struct_347.field1;

            return (GibCursorGibCursorProd) {pvrtmp_17574, pvrtmp_17575};
            break;
        }

      case 2:
        {
            GibCursor jump_12363 = arg_4278_6268_8882 + 1;

            return (GibCursorGibCursorProd) {end_r_10729, jump_12363};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_350 = *(uintptr_t *) tmpcur_17538;
            GibCursor tmpcur_17576 = GIB_UNTAG(tagged_tmpcur_350);
            GibCursor tmpaftercur_17577 = tmpcur_17538 + 8;
            uint16_t tmptag_17578 = GIB_GET_TAG(tagged_tmpcur_350);
            GibCursor end_from_tagged_indr_12641 = tmpcur_17576 + tmptag_17578;
            GibCursor jump_12643 = tmpcur_17538 + 8;
            GibCursorGibCursorProd tmp_struct_349 =
                                    _traverse_KdTree(end_from_tagged_indr_12641, tmpcur_17576);
            GibCursor pvrtmp_17579 = tmp_struct_349.field0;
            GibCursor pvrtmp_17580 = tmp_struct_349.field1;

            return (GibCursorGibCursorProd) {end_r_10729, jump_12643};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_352 = *(uintptr_t *) tmpcur_17538;
            GibCursor tmpcur_17581 = GIB_UNTAG(tagged_tmpcur_352);
            GibCursor tmpaftercur_17582 = tmpcur_17538 + 8;
            uint16_t tmptag_17583 = GIB_GET_TAG(tagged_tmpcur_352);
            GibCursor end_from_tagged_indr_12641 = tmpcur_17581 + tmptag_17583;
            GibCursorGibCursorProd tmp_struct_351 =
                                    _traverse_KdTree(end_from_tagged_indr_12641, tmpcur_17581);
            GibCursor pvrtmp_17584 = tmp_struct_351.field0;
            GibCursor pvrtmp_17585 = tmp_struct_351.field1;

            return (GibCursorGibCursorProd) {pvrtmp_17584, pvrtmp_17585};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_17537");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_KdTree(GibCursor end_r_10731,
                                     GibCursor arg_4313_6288_8902)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_17587 = *(GibPackedTag *) arg_4313_6288_8902;
    GibCursor tmpcur_17588 = arg_4313_6288_8902 + 1;


  switch_17636:
    ;
    switch (tmpval_17587) {

      case 0:
        {
            GibFloat tmpval_17589 = *(GibFloat *) tmpcur_17588;
            GibCursor tmpcur_17590 = tmpcur_17588 + sizeof(GibFloat);
            GibFloat tmpval_17591 = *(GibFloat *) tmpcur_17590;
            GibCursor tmpcur_17592 = tmpcur_17590 + sizeof(GibFloat);
            GibFloat tmpval_17593 = *(GibFloat *) tmpcur_17592;
            GibCursor tmpcur_17594 = tmpcur_17592 + sizeof(GibFloat);
            GibCursor jump_12367 = tmpcur_17592 + 4;
            unsigned char wildcard_4320_6292_8906 = gib_print_symbol(15855);
            unsigned char wildcard_4327_6293_8907 = gib_print_symbol(15863);
            unsigned char y_4317_6294_8908 = printf("%.2f", tmpval_17589);
            unsigned char wildcard_4326_6295_8909 = gib_print_symbol(15863);
            unsigned char y_4317_6296_8910 = gib_print_symbol(15863);
            unsigned char wildcard_4325_6297_8911 = gib_print_symbol(15863);
            unsigned char y_4318_6298_8912 = printf("%.2f", tmpval_17591);
            unsigned char wildcard_4324_6299_8913 = gib_print_symbol(15863);
            unsigned char y_4318_6300_8914 = gib_print_symbol(15863);
            unsigned char wildcard_4323_6301_8915 = gib_print_symbol(15863);
            unsigned char y_4319_6302_8916 = printf("%.2f", tmpval_17593);
            unsigned char wildcard_4322_6303_8917 = gib_print_symbol(15863);
            unsigned char y_4319_6304_8918 = gib_print_symbol(15863);
            unsigned char wildcard_4321_6305_8919 = gib_print_symbol(15848);

            return (GibCursorGibCursorProd) {end_r_10731, jump_12367};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_355 = *(uintptr_t *) tmpcur_17588;
            GibCursor tmpcur_17595 = GIB_UNTAG(tagged_tmpcur_355);
            GibCursor tmpaftercur_17596 = tmpcur_17588 + 8;
            uint16_t tmptag_17597 = GIB_GET_TAG(tagged_tmpcur_355);
            GibCursor end_from_tagged_absran_10596 = tmpcur_17595 +
                      tmptag_17597;
            GibFloat tmpval_17598 = *(GibFloat *) tmpaftercur_17596;
            GibCursor tmpcur_17599 = tmpaftercur_17596 + sizeof(GibFloat);
            GibFloat tmpval_17600 = *(GibFloat *) tmpcur_17599;
            GibCursor tmpcur_17601 = tmpcur_17599 + sizeof(GibFloat);
            GibFloat tmpval_17602 = *(GibFloat *) tmpcur_17601;
            GibCursor tmpcur_17603 = tmpcur_17601 + sizeof(GibFloat);
            GibInt tmpval_17604 = *(GibInt *) tmpcur_17603;
            GibCursor tmpcur_17605 = tmpcur_17603 + sizeof(GibInt);
            GibInt tmpval_17606 = *(GibInt *) tmpcur_17605;
            GibCursor tmpcur_17607 = tmpcur_17605 + sizeof(GibInt);
            GibFloat tmpval_17608 = *(GibFloat *) tmpcur_17607;
            GibCursor tmpcur_17609 = tmpcur_17607 + sizeof(GibFloat);
            GibFloat tmpval_17610 = *(GibFloat *) tmpcur_17609;
            GibCursor tmpcur_17611 = tmpcur_17609 + sizeof(GibFloat);
            GibFloat tmpval_17612 = *(GibFloat *) tmpcur_17611;
            GibCursor tmpcur_17613 = tmpcur_17611 + sizeof(GibFloat);
            GibFloat tmpval_17614 = *(GibFloat *) tmpcur_17613;
            GibCursor tmpcur_17615 = tmpcur_17613 + sizeof(GibFloat);
            GibFloat tmpval_17616 = *(GibFloat *) tmpcur_17615;
            GibCursor tmpcur_17617 = tmpcur_17615 + sizeof(GibFloat);
            GibFloat tmpval_17618 = *(GibFloat *) tmpcur_17617;
            GibCursor tmpcur_17619 = tmpcur_17617 + sizeof(GibFloat);
            GibFloat tmpval_17620 = *(GibFloat *) tmpcur_17619;
            GibCursor tmpcur_17621 = tmpcur_17619 + sizeof(GibFloat);
            unsigned char wildcard_4356_6320_8934 = gib_print_symbol(15854);
            unsigned char wildcard_4385_6321_8935 = gib_print_symbol(15863);
            unsigned char y_4342_6322_8936 = printf("%.2f", tmpval_17598);
            unsigned char wildcard_4384_6323_8937 = gib_print_symbol(15863);
            unsigned char y_4342_6324_8938 = gib_print_symbol(15863);
            unsigned char wildcard_4383_6325_8939 = gib_print_symbol(15863);
            unsigned char y_4343_6326_8940 = printf("%.2f", tmpval_17600);
            unsigned char wildcard_4382_6327_8941 = gib_print_symbol(15863);
            unsigned char y_4343_6328_8942 = gib_print_symbol(15863);
            unsigned char wildcard_4381_6329_8943 = gib_print_symbol(15863);
            unsigned char y_4344_6330_8944 = printf("%.2f", tmpval_17602);
            unsigned char wildcard_4380_6331_8945 = gib_print_symbol(15863);
            unsigned char y_4344_6332_8946 = gib_print_symbol(15863);
            unsigned char wildcard_4379_6333_8947 = gib_print_symbol(15863);
            unsigned char y_4345_6334_8948 = printf("%ld", tmpval_17604);
            unsigned char wildcard_4378_6335_8949 = gib_print_symbol(15863);
            unsigned char y_4345_6336_8950 = gib_print_symbol(15863);
            unsigned char wildcard_4377_6337_8951 = gib_print_symbol(15863);
            unsigned char y_4346_6338_8952 = printf("%ld", tmpval_17606);
            unsigned char wildcard_4376_6339_8953 = gib_print_symbol(15863);
            unsigned char y_4346_6340_8954 = gib_print_symbol(15863);
            unsigned char wildcard_4375_6341_8955 = gib_print_symbol(15863);
            unsigned char y_4347_6342_8956 = printf("%.2f", tmpval_17608);
            unsigned char wildcard_4374_6343_8957 = gib_print_symbol(15863);
            unsigned char y_4347_6344_8958 = gib_print_symbol(15863);
            unsigned char wildcard_4373_6345_8959 = gib_print_symbol(15863);
            unsigned char y_4348_6346_8960 = printf("%.2f", tmpval_17610);
            unsigned char wildcard_4372_6347_8961 = gib_print_symbol(15863);
            unsigned char y_4348_6348_8962 = gib_print_symbol(15863);
            unsigned char wildcard_4371_6349_8963 = gib_print_symbol(15863);
            unsigned char y_4349_6350_8964 = printf("%.2f", tmpval_17612);
            unsigned char wildcard_4370_6351_8965 = gib_print_symbol(15863);
            unsigned char y_4349_6352_8966 = gib_print_symbol(15863);
            unsigned char wildcard_4369_6353_8967 = gib_print_symbol(15863);
            unsigned char y_4350_6354_8968 = printf("%.2f", tmpval_17614);
            unsigned char wildcard_4368_6355_8969 = gib_print_symbol(15863);
            unsigned char y_4350_6356_8970 = gib_print_symbol(15863);
            unsigned char wildcard_4367_6357_8971 = gib_print_symbol(15863);
            unsigned char y_4351_6358_8972 = printf("%.2f", tmpval_17616);
            unsigned char wildcard_4366_6359_8973 = gib_print_symbol(15863);
            unsigned char y_4351_6360_8974 = gib_print_symbol(15863);
            unsigned char wildcard_4365_6361_8975 = gib_print_symbol(15863);
            unsigned char y_4352_6362_8976 = printf("%.2f", tmpval_17618);
            unsigned char wildcard_4364_6363_8977 = gib_print_symbol(15863);
            unsigned char y_4352_6364_8978 = gib_print_symbol(15863);
            unsigned char wildcard_4363_6365_8979 = gib_print_symbol(15863);
            unsigned char y_4353_6366_8980 = printf("%.2f", tmpval_17620);
            unsigned char wildcard_4362_6367_8981 = gib_print_symbol(15863);
            unsigned char y_4353_6368_8982 = gib_print_symbol(15863);
            unsigned char wildcard_4361_6369_8983 = gib_print_symbol(15863);
            GibCursorGibCursorProd tmp_struct_353 =
                                    _print_KdTree(end_r_10731, tmpcur_17621);
            GibCursor pvrtmp_17622 = tmp_struct_353.field0;
            GibCursor pvrtmp_17623 = tmp_struct_353.field1;
            unsigned char wildcard_4360_6371_8985 = gib_print_symbol(15863);
            unsigned char y_4354_6372_8986 = gib_print_symbol(15863);
            unsigned char wildcard_4359_6373_8987 = gib_print_symbol(15863);
            GibCursorGibCursorProd tmp_struct_354 =
                                    _print_KdTree(end_from_tagged_absran_10596, tmpcur_17595);
            GibCursor pvrtmp_17624 = tmp_struct_354.field0;
            GibCursor pvrtmp_17625 = tmp_struct_354.field1;
            unsigned char wildcard_4358_6375_8989 = gib_print_symbol(15863);
            unsigned char y_4355_6376_8990 = gib_print_symbol(15863);
            unsigned char wildcard_4357_6377_8991 = gib_print_symbol(15848);

            return (GibCursorGibCursorProd) {pvrtmp_17624, pvrtmp_17625};
            break;
        }

      case 2:
        {
            GibCursor jump_12385 = arg_4313_6288_8902 + 1;
            unsigned char wildcard_4386_6378_8992 = gib_print_symbol(15856);
            unsigned char wildcard_4387_6379_8993 = gib_print_symbol(15848);

            return (GibCursorGibCursorProd) {end_r_10731, jump_12385};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_357 = *(uintptr_t *) tmpcur_17588;
            GibCursor tmpcur_17626 = GIB_UNTAG(tagged_tmpcur_357);
            GibCursor tmpaftercur_17627 = tmpcur_17588 + 8;
            uint16_t tmptag_17628 = GIB_GET_TAG(tagged_tmpcur_357);
            GibCursor end_from_tagged_indr_12647 = tmpcur_17626 + tmptag_17628;
            GibCursor jump_12649 = tmpcur_17588 + 8;
            unsigned char wildcard_12652 = gib_print_symbol(15862);
            GibCursorGibCursorProd tmp_struct_356 =
                                    _print_KdTree(end_from_tagged_indr_12647, tmpcur_17626);
            GibCursor pvrtmp_17629 = tmp_struct_356.field0;
            GibCursor pvrtmp_17630 = tmp_struct_356.field1;

            return (GibCursorGibCursorProd) {end_r_10731, jump_12649};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_359 = *(uintptr_t *) tmpcur_17588;
            GibCursor tmpcur_17631 = GIB_UNTAG(tagged_tmpcur_359);
            GibCursor tmpaftercur_17632 = tmpcur_17588 + 8;
            uint16_t tmptag_17633 = GIB_GET_TAG(tagged_tmpcur_359);
            GibCursor end_from_tagged_indr_12647 = tmpcur_17631 + tmptag_17633;
            unsigned char wildcard_12652 = gib_print_symbol(15861);
            GibCursorGibCursorProd tmp_struct_358 =
                                    _print_KdTree(end_from_tagged_indr_12647, tmpcur_17631);
            GibCursor pvrtmp_17634 = tmp_struct_358.field0;
            GibCursor pvrtmp_17635 = tmp_struct_358.field1;

            return (GibCursorGibCursorProd) {pvrtmp_17634, pvrtmp_17635};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_17587");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_BH_Tree(GibCursor end_r_10734,
                                                                GibCursor end_r_10735,
                                                                GibCursor loc_10733,
                                                                GibCursor arg_4388_6380_8994)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_10733 + 58 > end_r_10735) {
        gib_grow_region(&loc_10733, &end_r_10735);
    }

    GibPackedTag tmpval_17637 = *(GibPackedTag *) arg_4388_6380_8994;
    GibCursor tmpcur_17638 = arg_4388_6380_8994 + 1;


  switch_17740:
    ;
    switch (tmpval_17637) {

      case 0:
        {
            GibCursor jump_12387 = arg_4388_6380_8994 + 1;

            *(GibPackedTag *) loc_10733 = 0;

            GibCursor writetag_14526 = loc_10733 + 1;
            GibCursor after_tag_14527 = loc_10733 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_10734,
                                                                        end_r_10735,
                                                                        jump_12387,
                                                                        loc_10733,
                                                                        after_tag_14527};
            break;
        }

      case 1:
        {
            GibFloat tmpval_17643 = *(GibFloat *) tmpcur_17638;
            GibCursor tmpcur_17644 = tmpcur_17638 + sizeof(GibFloat);
            GibFloat tmpval_17645 = *(GibFloat *) tmpcur_17644;
            GibCursor tmpcur_17646 = tmpcur_17644 + sizeof(GibFloat);
            GibFloat tmpval_17647 = *(GibFloat *) tmpcur_17646;
            GibCursor tmpcur_17648 = tmpcur_17646 + sizeof(GibFloat);
            GibCursor jump_12391 = tmpcur_17646 + 4;

            *(GibPackedTag *) loc_10733 = 1;

            GibCursor writetag_14537 = loc_10733 + 1;
            GibCursor after_tag_14538 = loc_10733 + 1;

            *(GibFloat *) after_tag_14538 = tmpval_17643;

            GibCursor writecur_14542 = after_tag_14538 + sizeof(GibFloat);

            *(GibFloat *) writecur_14542 = tmpval_17645;

            GibCursor writecur_14543 = writecur_14542 + sizeof(GibFloat);

            *(GibFloat *) writecur_14543 = tmpval_17647;

            GibCursor writecur_14544 = writecur_14543 + sizeof(GibFloat);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_10734,
                                                                        end_r_10735,
                                                                        jump_12391,
                                                                        loc_10733,
                                                                        writecur_14544};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_369 = *(uintptr_t *) tmpcur_17638;
            GibCursor tmpcur_17653 = GIB_UNTAG(tagged_tmpcur_369);
            GibCursor tmpaftercur_17654 = tmpcur_17638 + 8;
            uint16_t tmptag_17655 = GIB_GET_TAG(tagged_tmpcur_369);
            GibCursor end_from_tagged_absran_10602 = tmpcur_17653 +
                      tmptag_17655;
            uintptr_t tagged_tmpcur_368 = *(uintptr_t *) tmpaftercur_17654;
            GibCursor tmpcur_17656 = GIB_UNTAG(tagged_tmpcur_368);
            GibCursor tmpaftercur_17657 = tmpaftercur_17654 + 8;
            uint16_t tmptag_17658 = GIB_GET_TAG(tagged_tmpcur_368);
            GibCursor end_from_tagged_absran_10603 = tmpcur_17656 +
                      tmptag_17658;
            uintptr_t tagged_tmpcur_367 = *(uintptr_t *) tmpaftercur_17657;
            GibCursor tmpcur_17659 = GIB_UNTAG(tagged_tmpcur_367);
            GibCursor tmpaftercur_17660 = tmpaftercur_17657 + 8;
            uint16_t tmptag_17661 = GIB_GET_TAG(tagged_tmpcur_367);
            GibCursor end_from_tagged_absran_10604 = tmpcur_17659 +
                      tmptag_17661;
            GibFloat tmpval_17662 = *(GibFloat *) tmpaftercur_17660;
            GibCursor tmpcur_17663 = tmpaftercur_17660 + sizeof(GibFloat);
            GibFloat tmpval_17664 = *(GibFloat *) tmpcur_17663;
            GibCursor tmpcur_17665 = tmpcur_17663 + sizeof(GibFloat);
            GibFloat tmpval_17666 = *(GibFloat *) tmpcur_17665;
            GibCursor tmpcur_17667 = tmpcur_17665 + sizeof(GibFloat);
            GibInt tmpval_17668 = *(GibInt *) tmpcur_17667;
            GibCursor tmpcur_17669 = tmpcur_17667 + sizeof(GibInt);
            GibFloat tmpval_17670 = *(GibFloat *) tmpcur_17669;
            GibCursor tmpcur_17671 = tmpcur_17669 + sizeof(GibFloat);
            GibCursor loc_11613 = loc_10733 + 49;

            *(GibPackedTag *) loc_10733 = 3;

            GibCursor writetag_14568 = loc_10733 + 1;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_360 =
                                                               _copy_BH_Tree(end_r_10734, end_r_10735, loc_11613, tmpcur_17671);
            GibCursor pvrtmp_17672 = tmp_struct_360.field0;
            GibCursor pvrtmp_17673 = tmp_struct_360.field1;
            GibCursor pvrtmp_17674 = tmp_struct_360.field2;
            GibCursor pvrtmp_17675 = tmp_struct_360.field3;
            GibCursor pvrtmp_17676 = tmp_struct_360.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_361 =
                                                               _copy_BH_Tree(end_from_tagged_absran_10602, pvrtmp_17673, pvrtmp_17676, tmpcur_17653);
            GibCursor pvrtmp_17681 = tmp_struct_361.field0;
            GibCursor pvrtmp_17682 = tmp_struct_361.field1;
            GibCursor pvrtmp_17683 = tmp_struct_361.field2;
            GibCursor pvrtmp_17684 = tmp_struct_361.field3;
            GibCursor pvrtmp_17685 = tmp_struct_361.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_362 =
                                                               _copy_BH_Tree(end_from_tagged_absran_10603, pvrtmp_17682, pvrtmp_17685, tmpcur_17656);
            GibCursor pvrtmp_17690 = tmp_struct_362.field0;
            GibCursor pvrtmp_17691 = tmp_struct_362.field1;
            GibCursor pvrtmp_17692 = tmp_struct_362.field2;
            GibCursor pvrtmp_17693 = tmp_struct_362.field3;
            GibCursor pvrtmp_17694 = tmp_struct_362.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_363 =
                                                               _copy_BH_Tree(end_from_tagged_absran_10604, pvrtmp_17691, pvrtmp_17694, tmpcur_17659);
            GibCursor pvrtmp_17699 = tmp_struct_363.field0;
            GibCursor pvrtmp_17700 = tmp_struct_363.field1;
            GibCursor pvrtmp_17701 = tmp_struct_363.field2;
            GibCursor pvrtmp_17702 = tmp_struct_363.field3;
            GibCursor pvrtmp_17703 = tmp_struct_363.field4;
            uint16_t offset_366 = pvrtmp_17673 - pvrtmp_17676;
            uintptr_t ran_10609 = GIB_STORE_TAG(pvrtmp_17676, offset_366);
            uint16_t offset_365 = pvrtmp_17682 - pvrtmp_17685;
            uintptr_t ran_10610 = GIB_STORE_TAG(pvrtmp_17685, offset_365);
            uint16_t offset_364 = pvrtmp_17691 - pvrtmp_17694;
            uintptr_t ran_10611 = GIB_STORE_TAG(pvrtmp_17694, offset_364);
            GibCursor after_tag_14569 = loc_10733 + 1;

            *(uintptr_t *) after_tag_14569 = ran_10609;

            GibCursor writecur_14573 = after_tag_14569 + 8;

            *(uintptr_t *) writecur_14573 = ran_10610;

            GibCursor writecur_14574 = writecur_14573 + 8;

            *(uintptr_t *) writecur_14574 = ran_10611;

            GibCursor writecur_14575 = writecur_14574 + 8;

            *(GibFloat *) writecur_14575 = tmpval_17662;

            GibCursor writecur_14576 = writecur_14575 + sizeof(GibFloat);

            *(GibFloat *) writecur_14576 = tmpval_17664;

            GibCursor writecur_14577 = writecur_14576 + sizeof(GibFloat);

            *(GibFloat *) writecur_14577 = tmpval_17666;

            GibCursor writecur_14578 = writecur_14577 + sizeof(GibFloat);

            *(GibInt *) writecur_14578 = tmpval_17668;

            GibCursor writecur_14579 = writecur_14578 + sizeof(GibInt);

            *(GibFloat *) writecur_14579 = tmpval_17670;

            GibCursor writecur_14580 = writecur_14579 + sizeof(GibFloat);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_17699,
                                                                        pvrtmp_17700,
                                                                        pvrtmp_17701,
                                                                        loc_10733,
                                                                        pvrtmp_17703};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_371 = *(uintptr_t *) tmpcur_17638;
            GibCursor tmpcur_17712 = GIB_UNTAG(tagged_tmpcur_371);
            GibCursor tmpaftercur_17713 = tmpcur_17638 + 8;
            uint16_t tmptag_17714 = GIB_GET_TAG(tagged_tmpcur_371);
            GibCursor end_from_tagged_indr_12653 = tmpcur_17712 + tmptag_17714;
            GibCursor jump_12655 = tmpcur_17638 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_370 =
                                                               _copy_BH_Tree(end_from_tagged_indr_12653, end_r_10735, loc_10733, tmpcur_17712);
            GibCursor pvrtmp_17715 = tmp_struct_370.field0;
            GibCursor pvrtmp_17716 = tmp_struct_370.field1;
            GibCursor pvrtmp_17717 = tmp_struct_370.field2;
            GibCursor pvrtmp_17718 = tmp_struct_370.field3;
            GibCursor pvrtmp_17719 = tmp_struct_370.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_10734,
                                                                        pvrtmp_17716,
                                                                        jump_12655,
                                                                        pvrtmp_17718,
                                                                        pvrtmp_17719};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_373 = *(uintptr_t *) tmpcur_17638;
            GibCursor tmpcur_17726 = GIB_UNTAG(tagged_tmpcur_373);
            GibCursor tmpaftercur_17727 = tmpcur_17638 + 8;
            uint16_t tmptag_17728 = GIB_GET_TAG(tagged_tmpcur_373);
            GibCursor end_from_tagged_indr_12653 = tmpcur_17726 + tmptag_17728;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_372 =
                                                               _copy_BH_Tree(end_from_tagged_indr_12653, end_r_10735, loc_10733, tmpcur_17726);
            GibCursor pvrtmp_17729 = tmp_struct_372.field0;
            GibCursor pvrtmp_17730 = tmp_struct_372.field1;
            GibCursor pvrtmp_17731 = tmp_struct_372.field2;
            GibCursor pvrtmp_17732 = tmp_struct_372.field3;
            GibCursor pvrtmp_17733 = tmp_struct_372.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_17729,
                                                                        pvrtmp_17730,
                                                                        pvrtmp_17731,
                                                                        pvrtmp_17732,
                                                                        pvrtmp_17733};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_17637");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_BH_Tree(GibCursor end_r_10738,
                                                                             GibCursor end_r_10739,
                                                                             GibCursor loc_10737,
                                                                             GibCursor arg_4413_6405_9019)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_17741 = *(GibPackedTag *) arg_4413_6405_9019;
    GibCursor tmpcur_17742 = arg_4413_6405_9019 + 1;


  switch_17844:
    ;
    switch (tmpval_17741) {

      case 0:
        {
            GibCursor jump_12406 = arg_4413_6405_9019 + 1;

            *(GibPackedTag *) loc_10737 = 0;

            GibCursor writetag_14601 = loc_10737 + 1;
            GibCursor after_tag_14602 = loc_10737 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_10738,
                                                                        end_r_10739,
                                                                        jump_12406,
                                                                        loc_10737,
                                                                        after_tag_14602};
            break;
        }

      case 1:
        {
            GibFloat tmpval_17747 = *(GibFloat *) tmpcur_17742;
            GibCursor tmpcur_17748 = tmpcur_17742 + sizeof(GibFloat);
            GibFloat tmpval_17749 = *(GibFloat *) tmpcur_17748;
            GibCursor tmpcur_17750 = tmpcur_17748 + sizeof(GibFloat);
            GibFloat tmpval_17751 = *(GibFloat *) tmpcur_17750;
            GibCursor tmpcur_17752 = tmpcur_17750 + sizeof(GibFloat);
            GibCursor jump_12410 = tmpcur_17750 + 4;

            *(GibPackedTag *) loc_10737 = 1;

            GibCursor writetag_14612 = loc_10737 + 1;
            GibCursor after_tag_14613 = loc_10737 + 1;

            *(GibFloat *) after_tag_14613 = tmpval_17747;

            GibCursor writecur_14617 = after_tag_14613 + sizeof(GibFloat);

            *(GibFloat *) writecur_14617 = tmpval_17749;

            GibCursor writecur_14618 = writecur_14617 + sizeof(GibFloat);

            *(GibFloat *) writecur_14618 = tmpval_17751;

            GibCursor writecur_14619 = writecur_14618 + sizeof(GibFloat);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_10738,
                                                                        end_r_10739,
                                                                        jump_12410,
                                                                        loc_10737,
                                                                        writecur_14619};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_383 = *(uintptr_t *) tmpcur_17742;
            GibCursor tmpcur_17757 = GIB_UNTAG(tagged_tmpcur_383);
            GibCursor tmpaftercur_17758 = tmpcur_17742 + 8;
            uint16_t tmptag_17759 = GIB_GET_TAG(tagged_tmpcur_383);
            GibCursor end_from_tagged_absran_10615 = tmpcur_17757 +
                      tmptag_17759;
            uintptr_t tagged_tmpcur_382 = *(uintptr_t *) tmpaftercur_17758;
            GibCursor tmpcur_17760 = GIB_UNTAG(tagged_tmpcur_382);
            GibCursor tmpaftercur_17761 = tmpaftercur_17758 + 8;
            uint16_t tmptag_17762 = GIB_GET_TAG(tagged_tmpcur_382);
            GibCursor end_from_tagged_absran_10616 = tmpcur_17760 +
                      tmptag_17762;
            uintptr_t tagged_tmpcur_381 = *(uintptr_t *) tmpaftercur_17761;
            GibCursor tmpcur_17763 = GIB_UNTAG(tagged_tmpcur_381);
            GibCursor tmpaftercur_17764 = tmpaftercur_17761 + 8;
            uint16_t tmptag_17765 = GIB_GET_TAG(tagged_tmpcur_381);
            GibCursor end_from_tagged_absran_10617 = tmpcur_17763 +
                      tmptag_17765;
            GibFloat tmpval_17766 = *(GibFloat *) tmpaftercur_17764;
            GibCursor tmpcur_17767 = tmpaftercur_17764 + sizeof(GibFloat);
            GibFloat tmpval_17768 = *(GibFloat *) tmpcur_17767;
            GibCursor tmpcur_17769 = tmpcur_17767 + sizeof(GibFloat);
            GibFloat tmpval_17770 = *(GibFloat *) tmpcur_17769;
            GibCursor tmpcur_17771 = tmpcur_17769 + sizeof(GibFloat);
            GibInt tmpval_17772 = *(GibInt *) tmpcur_17771;
            GibCursor tmpcur_17773 = tmpcur_17771 + sizeof(GibInt);
            GibFloat tmpval_17774 = *(GibFloat *) tmpcur_17773;
            GibCursor tmpcur_17775 = tmpcur_17773 + sizeof(GibFloat);
            GibCursor loc_11684 = loc_10737 + 25;

            *(GibPackedTag *) loc_10737 = 2;

            GibCursor writetag_14643 = loc_10737 + 1;
            GibCursor after_tag_14644 = loc_10737 + 1;

            *(GibFloat *) after_tag_14644 = tmpval_17766;

            GibCursor writecur_14648 = after_tag_14644 + sizeof(GibFloat);

            *(GibFloat *) writecur_14648 = tmpval_17768;

            GibCursor writecur_14649 = writecur_14648 + sizeof(GibFloat);

            *(GibFloat *) writecur_14649 = tmpval_17770;

            GibCursor writecur_14650 = writecur_14649 + sizeof(GibFloat);

            *(GibInt *) writecur_14650 = tmpval_17772;

            GibCursor writecur_14651 = writecur_14650 + sizeof(GibInt);

            *(GibFloat *) writecur_14651 = tmpval_17774;

            GibCursor writecur_14652 = writecur_14651 + sizeof(GibFloat);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_377 =
                                                               _copy_without_ptrs_BH_Tree(end_r_10738, end_r_10739, loc_11684, tmpcur_17775);
            GibCursor pvrtmp_17776 = tmp_struct_377.field0;
            GibCursor pvrtmp_17777 = tmp_struct_377.field1;
            GibCursor pvrtmp_17778 = tmp_struct_377.field2;
            GibCursor pvrtmp_17779 = tmp_struct_377.field3;
            GibCursor pvrtmp_17780 = tmp_struct_377.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_378 =
                                                               _copy_without_ptrs_BH_Tree(end_from_tagged_absran_10615, pvrtmp_17777, pvrtmp_17780, tmpcur_17757);
            GibCursor pvrtmp_17785 = tmp_struct_378.field0;
            GibCursor pvrtmp_17786 = tmp_struct_378.field1;
            GibCursor pvrtmp_17787 = tmp_struct_378.field2;
            GibCursor pvrtmp_17788 = tmp_struct_378.field3;
            GibCursor pvrtmp_17789 = tmp_struct_378.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_379 =
                                                               _copy_without_ptrs_BH_Tree(end_from_tagged_absran_10616, pvrtmp_17786, pvrtmp_17789, tmpcur_17760);
            GibCursor pvrtmp_17794 = tmp_struct_379.field0;
            GibCursor pvrtmp_17795 = tmp_struct_379.field1;
            GibCursor pvrtmp_17796 = tmp_struct_379.field2;
            GibCursor pvrtmp_17797 = tmp_struct_379.field3;
            GibCursor pvrtmp_17798 = tmp_struct_379.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_380 =
                                                               _copy_without_ptrs_BH_Tree(end_from_tagged_absran_10617, pvrtmp_17795, pvrtmp_17798, tmpcur_17763);
            GibCursor pvrtmp_17803 = tmp_struct_380.field0;
            GibCursor pvrtmp_17804 = tmp_struct_380.field1;
            GibCursor pvrtmp_17805 = tmp_struct_380.field2;
            GibCursor pvrtmp_17806 = tmp_struct_380.field3;
            GibCursor pvrtmp_17807 = tmp_struct_380.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_17803,
                                                                        pvrtmp_17804,
                                                                        pvrtmp_17805,
                                                                        loc_10737,
                                                                        pvrtmp_17807};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_385 = *(uintptr_t *) tmpcur_17742;
            GibCursor tmpcur_17816 = GIB_UNTAG(tagged_tmpcur_385);
            GibCursor tmpaftercur_17817 = tmpcur_17742 + 8;
            uint16_t tmptag_17818 = GIB_GET_TAG(tagged_tmpcur_385);
            GibCursor end_from_tagged_indr_12659 = tmpcur_17816 + tmptag_17818;
            GibCursor jump_12661 = tmpcur_17742 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_384 =
                                                               _copy_without_ptrs_BH_Tree(end_from_tagged_indr_12659, end_r_10739, loc_10737, tmpcur_17816);
            GibCursor pvrtmp_17819 = tmp_struct_384.field0;
            GibCursor pvrtmp_17820 = tmp_struct_384.field1;
            GibCursor pvrtmp_17821 = tmp_struct_384.field2;
            GibCursor pvrtmp_17822 = tmp_struct_384.field3;
            GibCursor pvrtmp_17823 = tmp_struct_384.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_10738,
                                                                        pvrtmp_17820,
                                                                        jump_12661,
                                                                        pvrtmp_17822,
                                                                        pvrtmp_17823};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_387 = *(uintptr_t *) tmpcur_17742;
            GibCursor tmpcur_17830 = GIB_UNTAG(tagged_tmpcur_387);
            GibCursor tmpaftercur_17831 = tmpcur_17742 + 8;
            uint16_t tmptag_17832 = GIB_GET_TAG(tagged_tmpcur_387);
            GibCursor end_from_tagged_indr_12659 = tmpcur_17830 + tmptag_17832;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_386 =
                                                               _copy_without_ptrs_BH_Tree(end_from_tagged_indr_12659, end_r_10739, loc_10737, tmpcur_17830);
            GibCursor pvrtmp_17833 = tmp_struct_386.field0;
            GibCursor pvrtmp_17834 = tmp_struct_386.field1;
            GibCursor pvrtmp_17835 = tmp_struct_386.field2;
            GibCursor pvrtmp_17836 = tmp_struct_386.field3;
            GibCursor pvrtmp_17837 = tmp_struct_386.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_17833,
                                                                        pvrtmp_17834,
                                                                        pvrtmp_17835,
                                                                        pvrtmp_17836,
                                                                        pvrtmp_17837};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_17741");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_BH_Tree(GibCursor end_r_10741,
                                         GibCursor arg_4438_6430_9044)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_17845 = *(GibPackedTag *) arg_4438_6430_9044;
    GibCursor tmpcur_17846 = arg_4438_6430_9044 + 1;


  switch_17890:
    ;
    switch (tmpval_17845) {

      case 0:
        {
            GibCursor jump_12425 = arg_4438_6430_9044 + 1;

            return (GibCursorGibCursorProd) {end_r_10741, jump_12425};
            break;
        }

      case 1:
        {
            GibFloat tmpval_17847 = *(GibFloat *) tmpcur_17846;
            GibCursor tmpcur_17848 = tmpcur_17846 + sizeof(GibFloat);
            GibFloat tmpval_17849 = *(GibFloat *) tmpcur_17848;
            GibCursor tmpcur_17850 = tmpcur_17848 + sizeof(GibFloat);
            GibFloat tmpval_17851 = *(GibFloat *) tmpcur_17850;
            GibCursor tmpcur_17852 = tmpcur_17850 + sizeof(GibFloat);
            GibCursor jump_12429 = tmpcur_17850 + 4;

            return (GibCursorGibCursorProd) {end_r_10741, jump_12429};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_394 = *(uintptr_t *) tmpcur_17846;
            GibCursor tmpcur_17853 = GIB_UNTAG(tagged_tmpcur_394);
            GibCursor tmpaftercur_17854 = tmpcur_17846 + 8;
            uint16_t tmptag_17855 = GIB_GET_TAG(tagged_tmpcur_394);
            GibCursor end_from_tagged_absran_10622 = tmpcur_17853 +
                      tmptag_17855;
            uintptr_t tagged_tmpcur_393 = *(uintptr_t *) tmpaftercur_17854;
            GibCursor tmpcur_17856 = GIB_UNTAG(tagged_tmpcur_393);
            GibCursor tmpaftercur_17857 = tmpaftercur_17854 + 8;
            uint16_t tmptag_17858 = GIB_GET_TAG(tagged_tmpcur_393);
            GibCursor end_from_tagged_absran_10623 = tmpcur_17856 +
                      tmptag_17858;
            uintptr_t tagged_tmpcur_392 = *(uintptr_t *) tmpaftercur_17857;
            GibCursor tmpcur_17859 = GIB_UNTAG(tagged_tmpcur_392);
            GibCursor tmpaftercur_17860 = tmpaftercur_17857 + 8;
            uint16_t tmptag_17861 = GIB_GET_TAG(tagged_tmpcur_392);
            GibCursor end_from_tagged_absran_10624 = tmpcur_17859 +
                      tmptag_17861;
            GibFloat tmpval_17862 = *(GibFloat *) tmpaftercur_17860;
            GibCursor tmpcur_17863 = tmpaftercur_17860 + sizeof(GibFloat);
            GibFloat tmpval_17864 = *(GibFloat *) tmpcur_17863;
            GibCursor tmpcur_17865 = tmpcur_17863 + sizeof(GibFloat);
            GibFloat tmpval_17866 = *(GibFloat *) tmpcur_17865;
            GibCursor tmpcur_17867 = tmpcur_17865 + sizeof(GibFloat);
            GibInt tmpval_17868 = *(GibInt *) tmpcur_17867;
            GibCursor tmpcur_17869 = tmpcur_17867 + sizeof(GibInt);
            GibFloat tmpval_17870 = *(GibFloat *) tmpcur_17869;
            GibCursor tmpcur_17871 = tmpcur_17869 + sizeof(GibFloat);
            GibCursorGibCursorProd tmp_struct_388 =
                                    _traverse_BH_Tree(end_r_10741, tmpcur_17871);
            GibCursor pvrtmp_17872 = tmp_struct_388.field0;
            GibCursor pvrtmp_17873 = tmp_struct_388.field1;
            GibCursorGibCursorProd tmp_struct_389 =
                                    _traverse_BH_Tree(end_from_tagged_absran_10622, tmpcur_17853);
            GibCursor pvrtmp_17874 = tmp_struct_389.field0;
            GibCursor pvrtmp_17875 = tmp_struct_389.field1;
            GibCursorGibCursorProd tmp_struct_390 =
                                    _traverse_BH_Tree(end_from_tagged_absran_10623, tmpcur_17856);
            GibCursor pvrtmp_17876 = tmp_struct_390.field0;
            GibCursor pvrtmp_17877 = tmp_struct_390.field1;
            GibCursorGibCursorProd tmp_struct_391 =
                                    _traverse_BH_Tree(end_from_tagged_absran_10624, tmpcur_17859);
            GibCursor pvrtmp_17878 = tmp_struct_391.field0;
            GibCursor pvrtmp_17879 = tmp_struct_391.field1;

            return (GibCursorGibCursorProd) {pvrtmp_17878, pvrtmp_17879};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_396 = *(uintptr_t *) tmpcur_17846;
            GibCursor tmpcur_17880 = GIB_UNTAG(tagged_tmpcur_396);
            GibCursor tmpaftercur_17881 = tmpcur_17846 + 8;
            uint16_t tmptag_17882 = GIB_GET_TAG(tagged_tmpcur_396);
            GibCursor end_from_tagged_indr_12665 = tmpcur_17880 + tmptag_17882;
            GibCursor jump_12667 = tmpcur_17846 + 8;
            GibCursorGibCursorProd tmp_struct_395 =
                                    _traverse_BH_Tree(end_from_tagged_indr_12665, tmpcur_17880);
            GibCursor pvrtmp_17883 = tmp_struct_395.field0;
            GibCursor pvrtmp_17884 = tmp_struct_395.field1;

            return (GibCursorGibCursorProd) {end_r_10741, jump_12667};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_398 = *(uintptr_t *) tmpcur_17846;
            GibCursor tmpcur_17885 = GIB_UNTAG(tagged_tmpcur_398);
            GibCursor tmpaftercur_17886 = tmpcur_17846 + 8;
            uint16_t tmptag_17887 = GIB_GET_TAG(tagged_tmpcur_398);
            GibCursor end_from_tagged_indr_12665 = tmpcur_17885 + tmptag_17887;
            GibCursorGibCursorProd tmp_struct_397 =
                                    _traverse_BH_Tree(end_from_tagged_indr_12665, tmpcur_17885);
            GibCursor pvrtmp_17888 = tmp_struct_397.field0;
            GibCursor pvrtmp_17889 = tmp_struct_397.field1;

            return (GibCursorGibCursorProd) {pvrtmp_17888, pvrtmp_17889};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_17845");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_BH_Tree(GibCursor end_r_10743,
                                      GibCursor arg_4463_6447_9061)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_17891 = *(GibPackedTag *) arg_4463_6447_9061;
    GibCursor tmpcur_17892 = arg_4463_6447_9061 + 1;


  switch_17936:
    ;
    switch (tmpval_17891) {

      case 0:
        {
            GibCursor jump_12444 = arg_4463_6447_9061 + 1;
            unsigned char wildcard_4464_6448_9062 = gib_print_symbol(15859);
            unsigned char wildcard_4465_6449_9063 = gib_print_symbol(15848);

            return (GibCursorGibCursorProd) {end_r_10743, jump_12444};
            break;
        }

      case 1:
        {
            GibFloat tmpval_17893 = *(GibFloat *) tmpcur_17892;
            GibCursor tmpcur_17894 = tmpcur_17892 + sizeof(GibFloat);
            GibFloat tmpval_17895 = *(GibFloat *) tmpcur_17894;
            GibCursor tmpcur_17896 = tmpcur_17894 + sizeof(GibFloat);
            GibFloat tmpval_17897 = *(GibFloat *) tmpcur_17896;
            GibCursor tmpcur_17898 = tmpcur_17896 + sizeof(GibFloat);
            GibCursor jump_12448 = tmpcur_17896 + 4;
            unsigned char wildcard_4472_6453_9067 = gib_print_symbol(15858);
            unsigned char wildcard_4479_6454_9068 = gib_print_symbol(15863);
            unsigned char y_4469_6455_9069 = printf("%.2f", tmpval_17893);
            unsigned char wildcard_4478_6456_9070 = gib_print_symbol(15863);
            unsigned char y_4469_6457_9071 = gib_print_symbol(15863);
            unsigned char wildcard_4477_6458_9072 = gib_print_symbol(15863);
            unsigned char y_4470_6459_9073 = printf("%.2f", tmpval_17895);
            unsigned char wildcard_4476_6460_9074 = gib_print_symbol(15863);
            unsigned char y_4470_6461_9075 = gib_print_symbol(15863);
            unsigned char wildcard_4475_6462_9076 = gib_print_symbol(15863);
            unsigned char y_4471_6463_9077 = printf("%.2f", tmpval_17897);
            unsigned char wildcard_4474_6464_9078 = gib_print_symbol(15863);
            unsigned char y_4471_6465_9079 = gib_print_symbol(15863);
            unsigned char wildcard_4473_6466_9080 = gib_print_symbol(15848);

            return (GibCursorGibCursorProd) {end_r_10743, jump_12448};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_405 = *(uintptr_t *) tmpcur_17892;
            GibCursor tmpcur_17899 = GIB_UNTAG(tagged_tmpcur_405);
            GibCursor tmpaftercur_17900 = tmpcur_17892 + 8;
            uint16_t tmptag_17901 = GIB_GET_TAG(tagged_tmpcur_405);
            GibCursor end_from_tagged_absran_10629 = tmpcur_17899 +
                      tmptag_17901;
            uintptr_t tagged_tmpcur_404 = *(uintptr_t *) tmpaftercur_17900;
            GibCursor tmpcur_17902 = GIB_UNTAG(tagged_tmpcur_404);
            GibCursor tmpaftercur_17903 = tmpaftercur_17900 + 8;
            uint16_t tmptag_17904 = GIB_GET_TAG(tagged_tmpcur_404);
            GibCursor end_from_tagged_absran_10630 = tmpcur_17902 +
                      tmptag_17904;
            uintptr_t tagged_tmpcur_403 = *(uintptr_t *) tmpaftercur_17903;
            GibCursor tmpcur_17905 = GIB_UNTAG(tagged_tmpcur_403);
            GibCursor tmpaftercur_17906 = tmpaftercur_17903 + 8;
            uint16_t tmptag_17907 = GIB_GET_TAG(tagged_tmpcur_403);
            GibCursor end_from_tagged_absran_10631 = tmpcur_17905 +
                      tmptag_17907;
            GibFloat tmpval_17908 = *(GibFloat *) tmpaftercur_17906;
            GibCursor tmpcur_17909 = tmpaftercur_17906 + sizeof(GibFloat);
            GibFloat tmpval_17910 = *(GibFloat *) tmpcur_17909;
            GibCursor tmpcur_17911 = tmpcur_17909 + sizeof(GibFloat);
            GibFloat tmpval_17912 = *(GibFloat *) tmpcur_17911;
            GibCursor tmpcur_17913 = tmpcur_17911 + sizeof(GibFloat);
            GibInt tmpval_17914 = *(GibInt *) tmpcur_17913;
            GibCursor tmpcur_17915 = tmpcur_17913 + sizeof(GibInt);
            GibFloat tmpval_17916 = *(GibFloat *) tmpcur_17915;
            GibCursor tmpcur_17917 = tmpcur_17915 + sizeof(GibFloat);
            unsigned char wildcard_4498_6476_9090 = gib_print_symbol(15857);
            unsigned char wildcard_4517_6477_9091 = gib_print_symbol(15863);
            unsigned char y_4489_6478_9092 = printf("%.2f", tmpval_17908);
            unsigned char wildcard_4516_6479_9093 = gib_print_symbol(15863);
            unsigned char y_4489_6480_9094 = gib_print_symbol(15863);
            unsigned char wildcard_4515_6481_9095 = gib_print_symbol(15863);
            unsigned char y_4490_6482_9096 = printf("%.2f", tmpval_17910);
            unsigned char wildcard_4514_6483_9097 = gib_print_symbol(15863);
            unsigned char y_4490_6484_9098 = gib_print_symbol(15863);
            unsigned char wildcard_4513_6485_9099 = gib_print_symbol(15863);
            unsigned char y_4491_6486_9100 = printf("%.2f", tmpval_17912);
            unsigned char wildcard_4512_6487_9101 = gib_print_symbol(15863);
            unsigned char y_4491_6488_9102 = gib_print_symbol(15863);
            unsigned char wildcard_4511_6489_9103 = gib_print_symbol(15863);
            unsigned char y_4492_6490_9104 = printf("%ld", tmpval_17914);
            unsigned char wildcard_4510_6491_9105 = gib_print_symbol(15863);
            unsigned char y_4492_6492_9106 = gib_print_symbol(15863);
            unsigned char wildcard_4509_6493_9107 = gib_print_symbol(15863);
            unsigned char y_4493_6494_9108 = printf("%.2f", tmpval_17916);
            unsigned char wildcard_4508_6495_9109 = gib_print_symbol(15863);
            unsigned char y_4493_6496_9110 = gib_print_symbol(15863);
            unsigned char wildcard_4507_6497_9111 = gib_print_symbol(15863);
            GibCursorGibCursorProd tmp_struct_399 =
                                    _print_BH_Tree(end_r_10743, tmpcur_17917);
            GibCursor pvrtmp_17918 = tmp_struct_399.field0;
            GibCursor pvrtmp_17919 = tmp_struct_399.field1;
            unsigned char wildcard_4506_6499_9113 = gib_print_symbol(15863);
            unsigned char y_4494_6500_9114 = gib_print_symbol(15863);
            unsigned char wildcard_4505_6501_9115 = gib_print_symbol(15863);
            GibCursorGibCursorProd tmp_struct_400 =
                                    _print_BH_Tree(end_from_tagged_absran_10629, tmpcur_17899);
            GibCursor pvrtmp_17920 = tmp_struct_400.field0;
            GibCursor pvrtmp_17921 = tmp_struct_400.field1;
            unsigned char wildcard_4504_6503_9117 = gib_print_symbol(15863);
            unsigned char y_4495_6504_9118 = gib_print_symbol(15863);
            unsigned char wildcard_4503_6505_9119 = gib_print_symbol(15863);
            GibCursorGibCursorProd tmp_struct_401 =
                                    _print_BH_Tree(end_from_tagged_absran_10630, tmpcur_17902);
            GibCursor pvrtmp_17922 = tmp_struct_401.field0;
            GibCursor pvrtmp_17923 = tmp_struct_401.field1;
            unsigned char wildcard_4502_6507_9121 = gib_print_symbol(15863);
            unsigned char y_4496_6508_9122 = gib_print_symbol(15863);
            unsigned char wildcard_4501_6509_9123 = gib_print_symbol(15863);
            GibCursorGibCursorProd tmp_struct_402 =
                                    _print_BH_Tree(end_from_tagged_absran_10631, tmpcur_17905);
            GibCursor pvrtmp_17924 = tmp_struct_402.field0;
            GibCursor pvrtmp_17925 = tmp_struct_402.field1;
            unsigned char wildcard_4500_6511_9125 = gib_print_symbol(15863);
            unsigned char y_4497_6512_9126 = gib_print_symbol(15863);
            unsigned char wildcard_4499_6513_9127 = gib_print_symbol(15848);

            return (GibCursorGibCursorProd) {pvrtmp_17924, pvrtmp_17925};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_407 = *(uintptr_t *) tmpcur_17892;
            GibCursor tmpcur_17926 = GIB_UNTAG(tagged_tmpcur_407);
            GibCursor tmpaftercur_17927 = tmpcur_17892 + 8;
            uint16_t tmptag_17928 = GIB_GET_TAG(tagged_tmpcur_407);
            GibCursor end_from_tagged_indr_12671 = tmpcur_17926 + tmptag_17928;
            GibCursor jump_12673 = tmpcur_17892 + 8;
            unsigned char wildcard_12676 = gib_print_symbol(15862);
            GibCursorGibCursorProd tmp_struct_406 =
                                    _print_BH_Tree(end_from_tagged_indr_12671, tmpcur_17926);
            GibCursor pvrtmp_17929 = tmp_struct_406.field0;
            GibCursor pvrtmp_17930 = tmp_struct_406.field1;

            return (GibCursorGibCursorProd) {end_r_10743, jump_12673};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_409 = *(uintptr_t *) tmpcur_17892;
            GibCursor tmpcur_17931 = GIB_UNTAG(tagged_tmpcur_409);
            GibCursor tmpaftercur_17932 = tmpcur_17892 + 8;
            uint16_t tmptag_17933 = GIB_GET_TAG(tagged_tmpcur_409);
            GibCursor end_from_tagged_indr_12671 = tmpcur_17931 + tmptag_17933;
            unsigned char wildcard_12676 = gib_print_symbol(15861);
            GibCursorGibCursorProd tmp_struct_408 =
                                    _print_BH_Tree(end_from_tagged_indr_12671, tmpcur_17931);
            GibCursor pvrtmp_17934 = tmp_struct_408.field0;
            GibCursor pvrtmp_17935 = tmp_struct_408.field1;

            return (GibCursorGibCursorProd) {pvrtmp_17934, pvrtmp_17935};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_17891");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_Exp(GibCursor end_r_10746,
                                                            GibCursor end_r_10747,
                                                            GibCursor loc_10745,
                                                            GibCursor arg_4518_6514_9128)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_10745 + 18 > end_r_10747) {
        gib_grow_region(&loc_10745, &end_r_10747);
    }

    GibPackedTag tmpval_17937 = *(GibPackedTag *) arg_4518_6514_9128;
    GibCursor tmpcur_17938 = arg_4518_6514_9128 + 1;


  switch_18047:
    ;
    switch (tmpval_17937) {

      case 0:
        {
            GibInt tmpval_17939 = *(GibInt *) tmpcur_17938;
            GibCursor tmpcur_17940 = tmpcur_17938 + sizeof(GibInt);
            GibCursor jump_12463 = tmpcur_17938 + 8;

            *(GibPackedTag *) loc_10745 = 0;

            GibCursor writetag_14734 = loc_10745 + 1;
            GibCursor after_tag_14735 = loc_10745 + 1;

            *(GibInt *) after_tag_14735 = tmpval_17939;

            GibCursor writecur_14739 = after_tag_14735 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_10746,
                                                                        end_r_10747,
                                                                        jump_12463,
                                                                        loc_10745,
                                                                        writecur_14739};
            break;
        }

      case 1:
        {
            GibCursor jump_12465 = arg_4518_6514_9128 + 1;

            *(GibPackedTag *) loc_10745 = 1;

            GibCursor writetag_14743 = loc_10745 + 1;
            GibCursor after_tag_14744 = loc_10745 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_10746,
                                                                        end_r_10747,
                                                                        jump_12465,
                                                                        loc_10745,
                                                                        after_tag_14744};
            break;
        }

      case 2:
        {
            GibCursor jump_12467 = arg_4518_6514_9128 + 1;

            *(GibPackedTag *) loc_10745 = 2;

            GibCursor writetag_14751 = loc_10745 + 1;
            GibCursor after_tag_14752 = loc_10745 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_10746,
                                                                        end_r_10747,
                                                                        jump_12467,
                                                                        loc_10745,
                                                                        after_tag_14752};
            break;
        }

      case 3:
        {
            GibCursor loc_11768 = loc_10745 + 1;

            *(GibPackedTag *) loc_10745 = 3;

            GibCursor writetag_14765 = loc_10745 + 1;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_410 =
                                                               _copy_Exp(end_r_10746, end_r_10747, loc_11768, tmpcur_17938);
            GibCursor pvrtmp_17953 = tmp_struct_410.field0;
            GibCursor pvrtmp_17954 = tmp_struct_410.field1;
            GibCursor pvrtmp_17955 = tmp_struct_410.field2;
            GibCursor pvrtmp_17956 = tmp_struct_410.field3;
            GibCursor pvrtmp_17957 = tmp_struct_410.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_411 =
                                                               _copy_Exp(pvrtmp_17953, pvrtmp_17954, pvrtmp_17957, pvrtmp_17955);
            GibCursor pvrtmp_17962 = tmp_struct_411.field0;
            GibCursor pvrtmp_17963 = tmp_struct_411.field1;
            GibCursor pvrtmp_17964 = tmp_struct_411.field2;
            GibCursor pvrtmp_17965 = tmp_struct_411.field3;
            GibCursor pvrtmp_17966 = tmp_struct_411.field4;
            GibCursor after_tag_14766 = loc_10745 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_17962,
                                                                        pvrtmp_17963,
                                                                        pvrtmp_17964,
                                                                        loc_10745,
                                                                        pvrtmp_17966};
            break;
        }

      case 4:
        {
            GibCursor loc_11780 = loc_10745 + 1;

            *(GibPackedTag *) loc_10745 = 4;

            GibCursor writetag_14782 = loc_10745 + 1;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_412 =
                                                               _copy_Exp(end_r_10746, end_r_10747, loc_11780, tmpcur_17938);
            GibCursor pvrtmp_17975 = tmp_struct_412.field0;
            GibCursor pvrtmp_17976 = tmp_struct_412.field1;
            GibCursor pvrtmp_17977 = tmp_struct_412.field2;
            GibCursor pvrtmp_17978 = tmp_struct_412.field3;
            GibCursor pvrtmp_17979 = tmp_struct_412.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_413 =
                                                               _copy_Exp(pvrtmp_17975, pvrtmp_17976, pvrtmp_17979, pvrtmp_17977);
            GibCursor pvrtmp_17984 = tmp_struct_413.field0;
            GibCursor pvrtmp_17985 = tmp_struct_413.field1;
            GibCursor pvrtmp_17986 = tmp_struct_413.field2;
            GibCursor pvrtmp_17987 = tmp_struct_413.field3;
            GibCursor pvrtmp_17988 = tmp_struct_413.field4;
            GibCursor after_tag_14783 = loc_10745 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_17984,
                                                                        pvrtmp_17985,
                                                                        pvrtmp_17986,
                                                                        loc_10745,
                                                                        pvrtmp_17988};
            break;
        }

      case 5:
        {
            GibCursor loc_11792 = loc_10745 + 1;

            *(GibPackedTag *) loc_10745 = 5;

            GibCursor writetag_14799 = loc_10745 + 1;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_414 =
                                                               _copy_Exp(end_r_10746, end_r_10747, loc_11792, tmpcur_17938);
            GibCursor pvrtmp_17997 = tmp_struct_414.field0;
            GibCursor pvrtmp_17998 = tmp_struct_414.field1;
            GibCursor pvrtmp_17999 = tmp_struct_414.field2;
            GibCursor pvrtmp_18000 = tmp_struct_414.field3;
            GibCursor pvrtmp_18001 = tmp_struct_414.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_415 =
                                                               _copy_Exp(pvrtmp_17997, pvrtmp_17998, pvrtmp_18001, pvrtmp_17999);
            GibCursor pvrtmp_18006 = tmp_struct_415.field0;
            GibCursor pvrtmp_18007 = tmp_struct_415.field1;
            GibCursor pvrtmp_18008 = tmp_struct_415.field2;
            GibCursor pvrtmp_18009 = tmp_struct_415.field3;
            GibCursor pvrtmp_18010 = tmp_struct_415.field4;
            GibCursor after_tag_14800 = loc_10745 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_18006,
                                                                        pvrtmp_18007,
                                                                        pvrtmp_18008,
                                                                        loc_10745,
                                                                        pvrtmp_18010};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_417 = *(uintptr_t *) tmpcur_17938;
            GibCursor tmpcur_18019 = GIB_UNTAG(tagged_tmpcur_417);
            GibCursor tmpaftercur_18020 = tmpcur_17938 + 8;
            uint16_t tmptag_18021 = GIB_GET_TAG(tagged_tmpcur_417);
            GibCursor end_from_tagged_indr_12677 = tmpcur_18019 + tmptag_18021;
            GibCursor jump_12679 = tmpcur_17938 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_416 =
                                                               _copy_Exp(end_from_tagged_indr_12677, end_r_10747, loc_10745, tmpcur_18019);
            GibCursor pvrtmp_18022 = tmp_struct_416.field0;
            GibCursor pvrtmp_18023 = tmp_struct_416.field1;
            GibCursor pvrtmp_18024 = tmp_struct_416.field2;
            GibCursor pvrtmp_18025 = tmp_struct_416.field3;
            GibCursor pvrtmp_18026 = tmp_struct_416.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_10746,
                                                                        pvrtmp_18023,
                                                                        jump_12679,
                                                                        pvrtmp_18025,
                                                                        pvrtmp_18026};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_419 = *(uintptr_t *) tmpcur_17938;
            GibCursor tmpcur_18033 = GIB_UNTAG(tagged_tmpcur_419);
            GibCursor tmpaftercur_18034 = tmpcur_17938 + 8;
            uint16_t tmptag_18035 = GIB_GET_TAG(tagged_tmpcur_419);
            GibCursor end_from_tagged_indr_12677 = tmpcur_18033 + tmptag_18035;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_418 =
                                                               _copy_Exp(end_from_tagged_indr_12677, end_r_10747, loc_10745, tmpcur_18033);
            GibCursor pvrtmp_18036 = tmp_struct_418.field0;
            GibCursor pvrtmp_18037 = tmp_struct_418.field1;
            GibCursor pvrtmp_18038 = tmp_struct_418.field2;
            GibCursor pvrtmp_18039 = tmp_struct_418.field3;
            GibCursor pvrtmp_18040 = tmp_struct_418.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_18036,
                                                                        pvrtmp_18037,
                                                                        pvrtmp_18038,
                                                                        pvrtmp_18039,
                                                                        pvrtmp_18040};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_17937");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_Exp(GibCursor end_r_10750,
                                                                         GibCursor end_r_10751,
                                                                         GibCursor loc_10749,
                                                                         GibCursor arg_4533_6529_9143)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_18048 = *(GibPackedTag *) arg_4533_6529_9143;
    GibCursor tmpcur_18049 = arg_4533_6529_9143 + 1;


  switch_18158:
    ;
    switch (tmpval_18048) {

      case 0:
        {
            GibInt tmpval_18050 = *(GibInt *) tmpcur_18049;
            GibCursor tmpcur_18051 = tmpcur_18049 + sizeof(GibInt);
            GibCursor jump_12478 = tmpcur_18049 + 8;

            *(GibPackedTag *) loc_10749 = 0;

            GibCursor writetag_14821 = loc_10749 + 1;
            GibCursor after_tag_14822 = loc_10749 + 1;

            *(GibInt *) after_tag_14822 = tmpval_18050;

            GibCursor writecur_14826 = after_tag_14822 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_10750,
                                                                        end_r_10751,
                                                                        jump_12478,
                                                                        loc_10749,
                                                                        writecur_14826};
            break;
        }

      case 1:
        {
            GibCursor jump_12480 = arg_4533_6529_9143 + 1;

            *(GibPackedTag *) loc_10749 = 1;

            GibCursor writetag_14830 = loc_10749 + 1;
            GibCursor after_tag_14831 = loc_10749 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_10750,
                                                                        end_r_10751,
                                                                        jump_12480,
                                                                        loc_10749,
                                                                        after_tag_14831};
            break;
        }

      case 2:
        {
            GibCursor jump_12482 = arg_4533_6529_9143 + 1;

            *(GibPackedTag *) loc_10749 = 2;

            GibCursor writetag_14838 = loc_10749 + 1;
            GibCursor after_tag_14839 = loc_10749 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_10750,
                                                                        end_r_10751,
                                                                        jump_12482,
                                                                        loc_10749,
                                                                        after_tag_14839};
            break;
        }

      case 3:
        {
            GibCursor loc_11812 = loc_10749 + 1;

            *(GibPackedTag *) loc_10749 = 3;

            GibCursor writetag_14852 = loc_10749 + 1;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_423 =
                                                               _copy_without_ptrs_Exp(end_r_10750, end_r_10751, loc_11812, tmpcur_18049);
            GibCursor pvrtmp_18064 = tmp_struct_423.field0;
            GibCursor pvrtmp_18065 = tmp_struct_423.field1;
            GibCursor pvrtmp_18066 = tmp_struct_423.field2;
            GibCursor pvrtmp_18067 = tmp_struct_423.field3;
            GibCursor pvrtmp_18068 = tmp_struct_423.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_424 =
                                                               _copy_without_ptrs_Exp(pvrtmp_18064, pvrtmp_18065, pvrtmp_18068, pvrtmp_18066);
            GibCursor pvrtmp_18073 = tmp_struct_424.field0;
            GibCursor pvrtmp_18074 = tmp_struct_424.field1;
            GibCursor pvrtmp_18075 = tmp_struct_424.field2;
            GibCursor pvrtmp_18076 = tmp_struct_424.field3;
            GibCursor pvrtmp_18077 = tmp_struct_424.field4;
            GibCursor after_tag_14853 = loc_10749 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_18073,
                                                                        pvrtmp_18074,
                                                                        pvrtmp_18075,
                                                                        loc_10749,
                                                                        pvrtmp_18077};
            break;
        }

      case 4:
        {
            GibCursor loc_11824 = loc_10749 + 1;

            *(GibPackedTag *) loc_10749 = 4;

            GibCursor writetag_14869 = loc_10749 + 1;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_425 =
                                                               _copy_without_ptrs_Exp(end_r_10750, end_r_10751, loc_11824, tmpcur_18049);
            GibCursor pvrtmp_18086 = tmp_struct_425.field0;
            GibCursor pvrtmp_18087 = tmp_struct_425.field1;
            GibCursor pvrtmp_18088 = tmp_struct_425.field2;
            GibCursor pvrtmp_18089 = tmp_struct_425.field3;
            GibCursor pvrtmp_18090 = tmp_struct_425.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_426 =
                                                               _copy_without_ptrs_Exp(pvrtmp_18086, pvrtmp_18087, pvrtmp_18090, pvrtmp_18088);
            GibCursor pvrtmp_18095 = tmp_struct_426.field0;
            GibCursor pvrtmp_18096 = tmp_struct_426.field1;
            GibCursor pvrtmp_18097 = tmp_struct_426.field2;
            GibCursor pvrtmp_18098 = tmp_struct_426.field3;
            GibCursor pvrtmp_18099 = tmp_struct_426.field4;
            GibCursor after_tag_14870 = loc_10749 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_18095,
                                                                        pvrtmp_18096,
                                                                        pvrtmp_18097,
                                                                        loc_10749,
                                                                        pvrtmp_18099};
            break;
        }

      case 5:
        {
            GibCursor loc_11836 = loc_10749 + 1;

            *(GibPackedTag *) loc_10749 = 5;

            GibCursor writetag_14886 = loc_10749 + 1;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_427 =
                                                               _copy_without_ptrs_Exp(end_r_10750, end_r_10751, loc_11836, tmpcur_18049);
            GibCursor pvrtmp_18108 = tmp_struct_427.field0;
            GibCursor pvrtmp_18109 = tmp_struct_427.field1;
            GibCursor pvrtmp_18110 = tmp_struct_427.field2;
            GibCursor pvrtmp_18111 = tmp_struct_427.field3;
            GibCursor pvrtmp_18112 = tmp_struct_427.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_428 =
                                                               _copy_without_ptrs_Exp(pvrtmp_18108, pvrtmp_18109, pvrtmp_18112, pvrtmp_18110);
            GibCursor pvrtmp_18117 = tmp_struct_428.field0;
            GibCursor pvrtmp_18118 = tmp_struct_428.field1;
            GibCursor pvrtmp_18119 = tmp_struct_428.field2;
            GibCursor pvrtmp_18120 = tmp_struct_428.field3;
            GibCursor pvrtmp_18121 = tmp_struct_428.field4;
            GibCursor after_tag_14887 = loc_10749 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_18117,
                                                                        pvrtmp_18118,
                                                                        pvrtmp_18119,
                                                                        loc_10749,
                                                                        pvrtmp_18121};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_430 = *(uintptr_t *) tmpcur_18049;
            GibCursor tmpcur_18130 = GIB_UNTAG(tagged_tmpcur_430);
            GibCursor tmpaftercur_18131 = tmpcur_18049 + 8;
            uint16_t tmptag_18132 = GIB_GET_TAG(tagged_tmpcur_430);
            GibCursor end_from_tagged_indr_12683 = tmpcur_18130 + tmptag_18132;
            GibCursor jump_12685 = tmpcur_18049 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_429 =
                                                               _copy_without_ptrs_Exp(end_from_tagged_indr_12683, end_r_10751, loc_10749, tmpcur_18130);
            GibCursor pvrtmp_18133 = tmp_struct_429.field0;
            GibCursor pvrtmp_18134 = tmp_struct_429.field1;
            GibCursor pvrtmp_18135 = tmp_struct_429.field2;
            GibCursor pvrtmp_18136 = tmp_struct_429.field3;
            GibCursor pvrtmp_18137 = tmp_struct_429.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_10750,
                                                                        pvrtmp_18134,
                                                                        jump_12685,
                                                                        pvrtmp_18136,
                                                                        pvrtmp_18137};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_432 = *(uintptr_t *) tmpcur_18049;
            GibCursor tmpcur_18144 = GIB_UNTAG(tagged_tmpcur_432);
            GibCursor tmpaftercur_18145 = tmpcur_18049 + 8;
            uint16_t tmptag_18146 = GIB_GET_TAG(tagged_tmpcur_432);
            GibCursor end_from_tagged_indr_12683 = tmpcur_18144 + tmptag_18146;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_431 =
                                                               _copy_without_ptrs_Exp(end_from_tagged_indr_12683, end_r_10751, loc_10749, tmpcur_18144);
            GibCursor pvrtmp_18147 = tmp_struct_431.field0;
            GibCursor pvrtmp_18148 = tmp_struct_431.field1;
            GibCursor pvrtmp_18149 = tmp_struct_431.field2;
            GibCursor pvrtmp_18150 = tmp_struct_431.field3;
            GibCursor pvrtmp_18151 = tmp_struct_431.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_18147,
                                                                        pvrtmp_18148,
                                                                        pvrtmp_18149,
                                                                        pvrtmp_18150,
                                                                        pvrtmp_18151};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_18048");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_Exp(GibCursor end_r_10753,
                                     GibCursor arg_4548_6544_9158)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_18159 = *(GibPackedTag *) arg_4548_6544_9158;
    GibCursor tmpcur_18160 = arg_4548_6544_9158 + 1;


  switch_18185:
    ;
    switch (tmpval_18159) {

      case 0:
        {
            GibInt tmpval_18161 = *(GibInt *) tmpcur_18160;
            GibCursor tmpcur_18162 = tmpcur_18160 + sizeof(GibInt);
            GibCursor jump_12493 = tmpcur_18160 + 8;

            return (GibCursorGibCursorProd) {end_r_10753, jump_12493};
            break;
        }

      case 1:
        {
            GibCursor jump_12495 = arg_4548_6544_9158 + 1;

            return (GibCursorGibCursorProd) {end_r_10753, jump_12495};
            break;
        }

      case 2:
        {
            GibCursor jump_12497 = arg_4548_6544_9158 + 1;

            return (GibCursorGibCursorProd) {end_r_10753, jump_12497};
            break;
        }

      case 3:
        {
            GibCursorGibCursorProd tmp_struct_433 =
                                    _traverse_Exp(end_r_10753, tmpcur_18160);
            GibCursor pvrtmp_18163 = tmp_struct_433.field0;
            GibCursor pvrtmp_18164 = tmp_struct_433.field1;
            GibCursorGibCursorProd tmp_struct_434 =
                                    _traverse_Exp(pvrtmp_18163, pvrtmp_18164);
            GibCursor pvrtmp_18165 = tmp_struct_434.field0;
            GibCursor pvrtmp_18166 = tmp_struct_434.field1;

            return (GibCursorGibCursorProd) {pvrtmp_18165, pvrtmp_18166};
            break;
        }

      case 4:
        {
            GibCursorGibCursorProd tmp_struct_435 =
                                    _traverse_Exp(end_r_10753, tmpcur_18160);
            GibCursor pvrtmp_18167 = tmp_struct_435.field0;
            GibCursor pvrtmp_18168 = tmp_struct_435.field1;
            GibCursorGibCursorProd tmp_struct_436 =
                                    _traverse_Exp(pvrtmp_18167, pvrtmp_18168);
            GibCursor pvrtmp_18169 = tmp_struct_436.field0;
            GibCursor pvrtmp_18170 = tmp_struct_436.field1;

            return (GibCursorGibCursorProd) {pvrtmp_18169, pvrtmp_18170};
            break;
        }

      case 5:
        {
            GibCursorGibCursorProd tmp_struct_437 =
                                    _traverse_Exp(end_r_10753, tmpcur_18160);
            GibCursor pvrtmp_18171 = tmp_struct_437.field0;
            GibCursor pvrtmp_18172 = tmp_struct_437.field1;
            GibCursorGibCursorProd tmp_struct_438 =
                                    _traverse_Exp(pvrtmp_18171, pvrtmp_18172);
            GibCursor pvrtmp_18173 = tmp_struct_438.field0;
            GibCursor pvrtmp_18174 = tmp_struct_438.field1;

            return (GibCursorGibCursorProd) {pvrtmp_18173, pvrtmp_18174};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_440 = *(uintptr_t *) tmpcur_18160;
            GibCursor tmpcur_18175 = GIB_UNTAG(tagged_tmpcur_440);
            GibCursor tmpaftercur_18176 = tmpcur_18160 + 8;
            uint16_t tmptag_18177 = GIB_GET_TAG(tagged_tmpcur_440);
            GibCursor end_from_tagged_indr_12689 = tmpcur_18175 + tmptag_18177;
            GibCursor jump_12691 = tmpcur_18160 + 8;
            GibCursorGibCursorProd tmp_struct_439 =
                                    _traverse_Exp(end_from_tagged_indr_12689, tmpcur_18175);
            GibCursor pvrtmp_18178 = tmp_struct_439.field0;
            GibCursor pvrtmp_18179 = tmp_struct_439.field1;

            return (GibCursorGibCursorProd) {end_r_10753, jump_12691};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_442 = *(uintptr_t *) tmpcur_18160;
            GibCursor tmpcur_18180 = GIB_UNTAG(tagged_tmpcur_442);
            GibCursor tmpaftercur_18181 = tmpcur_18160 + 8;
            uint16_t tmptag_18182 = GIB_GET_TAG(tagged_tmpcur_442);
            GibCursor end_from_tagged_indr_12689 = tmpcur_18180 + tmptag_18182;
            GibCursorGibCursorProd tmp_struct_441 =
                                    _traverse_Exp(end_from_tagged_indr_12689, tmpcur_18180);
            GibCursor pvrtmp_18183 = tmp_struct_441.field0;
            GibCursor pvrtmp_18184 = tmp_struct_441.field1;

            return (GibCursorGibCursorProd) {pvrtmp_18183, pvrtmp_18184};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_18159");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_Exp(GibCursor end_r_10755,
                                  GibCursor arg_4563_6558_9172)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_18186 = *(GibPackedTag *) arg_4563_6558_9172;
    GibCursor tmpcur_18187 = arg_4563_6558_9172 + 1;


  switch_18212:
    ;
    switch (tmpval_18186) {

      case 0:
        {
            GibInt tmpval_18188 = *(GibInt *) tmpcur_18187;
            GibCursor tmpcur_18189 = tmpcur_18187 + sizeof(GibInt);
            GibCursor jump_12508 = tmpcur_18187 + 8;
            unsigned char wildcard_4566_6560_9174 = gib_print_symbol(15853);
            unsigned char wildcard_4569_6561_9175 = gib_print_symbol(15863);
            unsigned char y_4565_6562_9176 = printf("%ld", tmpval_18188);
            unsigned char wildcard_4568_6563_9177 = gib_print_symbol(15863);
            unsigned char y_4565_6564_9178 = gib_print_symbol(15863);
            unsigned char wildcard_4567_6565_9179 = gib_print_symbol(15848);

            return (GibCursorGibCursorProd) {end_r_10755, jump_12508};
            break;
        }

      case 1:
        {
            GibCursor jump_12510 = arg_4563_6558_9172 + 1;
            unsigned char wildcard_4570_6566_9180 = gib_print_symbol(15851);
            unsigned char wildcard_4571_6567_9181 = gib_print_symbol(15848);

            return (GibCursorGibCursorProd) {end_r_10755, jump_12510};
            break;
        }

      case 2:
        {
            GibCursor jump_12512 = arg_4563_6558_9172 + 1;
            unsigned char wildcard_4572_6568_9182 = gib_print_symbol(15852);
            unsigned char wildcard_4573_6569_9183 = gib_print_symbol(15848);

            return (GibCursorGibCursorProd) {end_r_10755, jump_12512};
            break;
        }

      case 3:
        {
            unsigned char wildcard_4578_6572_9186 = gib_print_symbol(15849);
            unsigned char wildcard_4583_6573_9187 = gib_print_symbol(15863);
            GibCursorGibCursorProd tmp_struct_443 =
                                    _print_Exp(end_r_10755, tmpcur_18187);
            GibCursor pvrtmp_18190 = tmp_struct_443.field0;
            GibCursor pvrtmp_18191 = tmp_struct_443.field1;
            unsigned char wildcard_4582_6575_9189 = gib_print_symbol(15863);
            unsigned char y_4576_6576_9190 = gib_print_symbol(15863);
            unsigned char wildcard_4581_6577_9191 = gib_print_symbol(15863);
            GibCursorGibCursorProd tmp_struct_444 =
                                    _print_Exp(pvrtmp_18190, pvrtmp_18191);
            GibCursor pvrtmp_18192 = tmp_struct_444.field0;
            GibCursor pvrtmp_18193 = tmp_struct_444.field1;
            unsigned char wildcard_4580_6579_9193 = gib_print_symbol(15863);
            unsigned char y_4577_6580_9194 = gib_print_symbol(15863);
            unsigned char wildcard_4579_6581_9195 = gib_print_symbol(15848);

            return (GibCursorGibCursorProd) {pvrtmp_18192, pvrtmp_18193};
            break;
        }

      case 4:
        {
            unsigned char wildcard_4588_6584_9198 = gib_print_symbol(15860);
            unsigned char wildcard_4593_6585_9199 = gib_print_symbol(15863);
            GibCursorGibCursorProd tmp_struct_445 =
                                    _print_Exp(end_r_10755, tmpcur_18187);
            GibCursor pvrtmp_18194 = tmp_struct_445.field0;
            GibCursor pvrtmp_18195 = tmp_struct_445.field1;
            unsigned char wildcard_4592_6587_9201 = gib_print_symbol(15863);
            unsigned char y_4586_6588_9202 = gib_print_symbol(15863);
            unsigned char wildcard_4591_6589_9203 = gib_print_symbol(15863);
            GibCursorGibCursorProd tmp_struct_446 =
                                    _print_Exp(pvrtmp_18194, pvrtmp_18195);
            GibCursor pvrtmp_18196 = tmp_struct_446.field0;
            GibCursor pvrtmp_18197 = tmp_struct_446.field1;
            unsigned char wildcard_4590_6591_9205 = gib_print_symbol(15863);
            unsigned char y_4587_6592_9206 = gib_print_symbol(15863);
            unsigned char wildcard_4589_6593_9207 = gib_print_symbol(15848);

            return (GibCursorGibCursorProd) {pvrtmp_18196, pvrtmp_18197};
            break;
        }

      case 5:
        {
            unsigned char wildcard_4598_6596_9210 = gib_print_symbol(15850);
            unsigned char wildcard_4603_6597_9211 = gib_print_symbol(15863);
            GibCursorGibCursorProd tmp_struct_447 =
                                    _print_Exp(end_r_10755, tmpcur_18187);
            GibCursor pvrtmp_18198 = tmp_struct_447.field0;
            GibCursor pvrtmp_18199 = tmp_struct_447.field1;
            unsigned char wildcard_4602_6599_9213 = gib_print_symbol(15863);
            unsigned char y_4596_6600_9214 = gib_print_symbol(15863);
            unsigned char wildcard_4601_6601_9215 = gib_print_symbol(15863);
            GibCursorGibCursorProd tmp_struct_448 =
                                    _print_Exp(pvrtmp_18198, pvrtmp_18199);
            GibCursor pvrtmp_18200 = tmp_struct_448.field0;
            GibCursor pvrtmp_18201 = tmp_struct_448.field1;
            unsigned char wildcard_4600_6603_9217 = gib_print_symbol(15863);
            unsigned char y_4597_6604_9218 = gib_print_symbol(15863);
            unsigned char wildcard_4599_6605_9219 = gib_print_symbol(15848);

            return (GibCursorGibCursorProd) {pvrtmp_18200, pvrtmp_18201};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_450 = *(uintptr_t *) tmpcur_18187;
            GibCursor tmpcur_18202 = GIB_UNTAG(tagged_tmpcur_450);
            GibCursor tmpaftercur_18203 = tmpcur_18187 + 8;
            uint16_t tmptag_18204 = GIB_GET_TAG(tagged_tmpcur_450);
            GibCursor end_from_tagged_indr_12695 = tmpcur_18202 + tmptag_18204;
            GibCursor jump_12697 = tmpcur_18187 + 8;
            unsigned char wildcard_12700 = gib_print_symbol(15862);
            GibCursorGibCursorProd tmp_struct_449 =
                                    _print_Exp(end_from_tagged_indr_12695, tmpcur_18202);
            GibCursor pvrtmp_18205 = tmp_struct_449.field0;
            GibCursor pvrtmp_18206 = tmp_struct_449.field1;

            return (GibCursorGibCursorProd) {end_r_10755, jump_12697};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_452 = *(uintptr_t *) tmpcur_18187;
            GibCursor tmpcur_18207 = GIB_UNTAG(tagged_tmpcur_452);
            GibCursor tmpaftercur_18208 = tmpcur_18187 + 8;
            uint16_t tmptag_18209 = GIB_GET_TAG(tagged_tmpcur_452);
            GibCursor end_from_tagged_indr_12695 = tmpcur_18207 + tmptag_18209;
            unsigned char wildcard_12700 = gib_print_symbol(15861);
            GibCursorGibCursorProd tmp_struct_451 =
                                    _print_Exp(end_from_tagged_indr_12695, tmpcur_18207);
            GibCursor pvrtmp_18210 = tmp_struct_451.field0;
            GibCursor pvrtmp_18211 = tmp_struct_451.field1;

            return (GibCursorGibCursorProd) {pvrtmp_18210, pvrtmp_18211};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_18186");
            exit(1);
        }
    }
}
int main(int argc, char **argv)
{
    int init_453 = gib_init(argc, argv);

    info_table_initialize();
    symbol_table_initialize();

    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_7183_7498 = strcmp("seqbuildkdtree",
                                     gib_read_bench_prog_param()) == 0;

    if (fltIf_7183_7498) {
        unsigned char tailapp_12523 =  bench_seqbuildkdtree();

        printf("'#()");
        printf("\n");
        return 0;
    } else {
        GibBool fltIf_7184_7499 = strcmp("seqcountcorr",
                                         gib_read_bench_prog_param()) == 0;

        if (fltIf_7184_7499) {
            unsigned char tailapp_12524 =  bench_seqcountcorr();

            printf("'#()");
            printf("\n");
            return 0;
        } else {
            GibBool fltIf_7185_7500 = strcmp("seqnearest",
                                             gib_read_bench_prog_param()) == 0;

            if (fltIf_7185_7500) {
                unsigned char tailapp_12525 =  bench_seqnearest();

                printf("'#()");
                printf("\n");
                return 0;
            } else {
                GibBool fltIf_7186_7501 = strcmp("seqbuildquadtree",
                                                 gib_read_bench_prog_param()) ==
                        0;

                if (fltIf_7186_7501) {
                    unsigned char tailapp_12526 =  bench_seqbuildquadtree();

                    printf("'#()");
                    printf("\n");
                    return 0;
                } else {
                    GibBool fltIf_7187_7502 = strcmp("seqbhut",
                                                     gib_read_bench_prog_param()) ==
                            0;

                    if (fltIf_7187_7502) {
                        unsigned char tailapp_12527 =  bench_seqbhut();

                        printf("'#()");
                        printf("\n");
                        return 0;
                    } else {
                        GibBool fltIf_7188_7503 = strcmp("seqfoldconstants",
                                                         gib_read_bench_prog_param()) ==
                                0;

                        if (fltIf_7188_7503) {
                            unsigned char tailapp_12528 =
                                           bench_seqfoldconstants();

                            printf("'#()");
                            printf("\n");
                            return 0;
                        } else {
                            unsigned char tailprim_12529 =
                                          gib_print_symbol(15839);

                            printf("'#()");
                            printf("\n");
                            return 0;
                        }
                    }
                }
            }
        }
    }

    int exit_454 = gib_exit();

    return exit_454;
}
