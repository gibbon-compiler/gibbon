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
typedef struct GibIntGibIntProd_struct {
            GibInt field0;
            GibInt field1;
        } GibIntGibIntProd;
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
typedef struct GibListProd_struct {
            GibList *field0;
        } GibListProd;
unsigned char bench_seqfib();
unsigned char bench_seqfoldconstants();
unsigned char bench_seqcoins();
unsigned char bench_seqbhut();
unsigned char bench_seqbuildquadtree();
unsigned char bench_seqnearest();
unsigned char bench_seqcountcorr();
unsigned char bench_seqbuildkdtree();
unsigned char bench_seqsumtree();
unsigned char bench_seqadd1tree();
unsigned char bench_seqbuildtree();
unsigned char bench_seqbuildfib();
GibInt fib_seq(GibInt n_439_7658_12258);
GibCursorGibCursorProd check_buildfib(GibCursor end_r_15665,
                                      GibInt n_447_7666_12265,
                                      GibCursor tr_448_7667_12266);
GibCursorGibCursorGibCursorProd mkTreeFib_seq(GibCursor end_r_15667,
                                              GibCursor loc_15666,
                                              GibInt i_454_7673_12275);
GibCursorGibCursorProd check_buildtree(GibCursor end_r_15669,
                                       GibInt n_462_7681_12282,
                                       GibCursor tr_463_7682_12283);
GibCursorGibCursorGibCursorProd mkTree_seq(GibCursor end_r_15671,
                                           GibCursor loc_15670,
                                           GibInt i_469_7688_12290);
GibCursorGibCursorProd check_add1tree(GibCursor end_r_15673,
                                      GibInt n_477_7696_12296,
                                      GibCursor tr_478_7697_12297);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
add1Tree_seq(GibCursor end_r_15676, GibCursor end_r_15677, GibCursor loc_15675,
             GibCursor tr_483_7702_12303);
unsigned char check_sumtree(GibInt n_499_7718_12311,
                            GibInt actual_500_7719_12312);
GibCursorGibCursorGibIntProd sumTree_seq(GibCursor end_r_15679,
                                         GibCursor foo_505_7724_12318);
GibCursorGibCursorProd check_buildkdtree(GibCursor end_r_15681,
                                         GibVector *pts_521_7740_12325,
                                         GibCursor tr_522_7741_12326);
GibCursorGibCursorGibCursorProd mkKdTree_seq(GibCursor end_r_15683,
                                             GibCursor loc_15682,
                                             GibVector *pts_526_7745_12332);
GibCursorGibVectorProd allCountCorr_seq(GibCursor end_r_15685,
                                        GibFloat radius_532_7748_12333,
                                        GibCursor tr_533_7749_12334,
                                        GibVector *ls_534_7750_12335);
unsigned char check_nearest(GibVector *pts_545_7755_12340,
                            GibVector *actual_546_7756_12341);
GibCursorGibVectorProd allNearest_seq(GibCursor end_r_15687,
                                      GibCursor tr_561_7763_12359,
                                      GibVector *ls_562_7764_12360);
GibCursorGibCursorProd check_buildquadtree(GibCursor end_r_15689,
                                           GibVector *mpts_567_7767_12364,
                                           GibCursor bht_568_7768_12365);
GibCursorGibCursorGibCursorProd buildQtree_seq(GibCursor end_r_15691,
                                               GibCursor loc_15690,
                                               GibFloatGibFloatGibFloatGibFloatProd box_584_7784_12384,
                                               GibVector *mpts_585_7785_12385);
GibFloat maxFloat(GibFloat a_622_7817_12436, GibFloat b_623_7818_12437);
GibFloat minFloat(GibFloat a_624_7819_12439, GibFloat b_625_7820_12440);
GibCursorGibVectorProd oneStep_seq(GibCursor end_r_15693,
                                   GibCursor bht_665_7855_12442,
                                   GibVector *mpts_666_7856_12443,
                                   GibVector *ps_667_7857_12444);
GibCursorGibCursorProd check_coins(GibCursor end_r_15695,
                                   GibInt amt_682_7864_12454,
                                   GibCursor tr_683_7865_12455);
GibCursorGibCursorGibCursorProd payA_seq(GibCursor end_r_15697,
                                         GibCursor loc_15696,
                                         GibInt amt_687_7869_12464,
                                         GibList *coins_688_7870_12465);
GibCursorGibCursorGibIntProd sumExp(GibCursor end_r_15699,
                                    GibCursor exp_710_7892_12484);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
foldConstants2(GibCursor end_r_15702, GibCursor end_r_15703,
               GibCursor loc_15701, GibCursor exp_714_7896_12490);
GibCursorGibCursorGibCursorProd buildExp(GibCursor end_r_15705,
                                         GibCursor loc_15704,
                                         GibInt n_726_7908_12516);
unsigned char print_check(GibBool b_745_7915_12524);
GibFloat sumList(GibVector *ls_793_7961_12527);
GibCursorGibCursorGibFloatProd sumKdTree(GibCursor end_r_15707,
                                         GibCursor tr_820_7982_12531);
GibCursorGibIntProd countCorr_seq(GibCursor end_r_15709,
                                  GibFloatGibFloatGibFloatProd probe_906_8068_12555,
                                  GibFloat radius_907_8069_12556,
                                  GibCursor tr_908_8070_12557);
GibFloatGibFloatGibFloatProd
least_dist_point3d(GibFloatGibFloatGibFloatProd a_943_8105_12622,
                   GibFloatGibFloatGibFloatProd b_944_8106_12623,
                   GibFloatGibFloatGibFloatProd c_945_8107_12624);
GibCursorGibCursorGibFloatGibFloatGibFloatProd
find_nearest(GibCursor end_r_15712, GibCursor end_r_15713,
             GibFloatGibFloatGibFloatProd pivot_948_8110_12628,
             GibFloatGibFloatGibFloatProd query_949_8111_12629,
             GibFloat tst_pivot_950_8112_12630,
             GibFloat tst_query_951_8113_12631,
             GibCursor good_side_952_8114_12632,
             GibCursor other_side_953_8115_12633);
GibCursorGibFloatGibFloatGibFloatProd nearest(GibCursor end_r_15715,
                                              GibCursor tr_959_8121_12642,
                                              GibFloatGibFloatGibFloatProd query_960_8122_12643);
GibCursorGibCursorGibCursorProd mkKdTreeWithAxis_seq(GibCursor end_r_15717,
                                                     GibCursor loc_15716,
                                                     GibInt axis_1029_8191_12665,
                                                     GibVector *pts_1030_8192_12666);
GibCursorGibIntProd get_total_points_kdtree(GibCursor end_r_15719,
                                            GibCursor tr_1109_8271_12726);
GibCursorGibFloatProd get_maxz_kdtree(GibCursor end_r_15721,
                                      GibCursor tr_1127_8289_12744);
GibCursorGibFloatProd get_minz_kdtree(GibCursor end_r_15723,
                                      GibCursor tr_1145_8307_12762);
GibCursorGibFloatProd get_maxy_kdtree(GibCursor end_r_15725,
                                      GibCursor tr_1163_8325_12780);
GibCursorGibFloatProd get_miny_kdtree(GibCursor end_r_15727,
                                      GibCursor tr_1181_8343_12798);
GibCursorGibFloatProd get_maxx_kdtree(GibCursor end_r_15729,
                                      GibCursor tr_1199_8361_12816);
GibCursorGibFloatProd get_minx_kdtree(GibCursor end_r_15731,
                                      GibCursor tr_1217_8379_12834);
GibFloat get_coord_point3d(GibInt axis_1247_8409_12852,
                           GibFloatGibFloatGibFloatProd pt_1248_8410_12853);
GibInt getNextAxis_3d(GibInt i_1253_8415_12860);
GibVector *sort_point3d(GibInt axis_1254_8416_12862,
                        GibVector *ls_1255_8417_12863);
GibFloat dist_point3d(GibFloatGibFloatGibFloatProd a_1265_8421_12872,
                      GibFloatGibFloatGibFloatProd b_1266_8422_12873);
GibFloat float_abs(GibFloat f_1280_8434_12889);
GibBool eq_point3d(GibFloatGibFloatGibFloatProd a_1281_8435_12892,
                   GibFloatGibFloatGibFloatProd b_1282_8436_12893);
GibVector
*masspointsInBox_seq(GibFloatGibFloatGibFloatGibFloatProd box_1343_8471_12906,
                     GibVector *mpts_1344_8472_12907);
GibFloatGibFloatGibFloatProd calcCentroid_seq(GibVector *mpts_1359_8483_12915);
GibCursorGibFloatGibFloatProd calcAccel_seq(GibCursor end_r_15733,
                                            GibFloatGibFloatGibFloatProd mpt_1376_8489_12926,
                                            GibCursor tr_1377_8490_12927);
GibCursorGibIntProd getTotalPoints_qtree(GibCursor end_r_15735,
                                         GibCursor tr_1435_8548_13031);
GibFloat sum_mass_points(GibVector *mpts_1502_8615_13044);
GibCursorGibCursorGibIntProd countLeavesQtree(GibCursor end_r_15737,
                                              GibCursor tr_1509_8616_13048);
GibCursorGibCursorGibFloatProd sumQtree(GibCursor end_r_15739,
                                        GibCursor tr_1522_8629_13067);
GibCursorGibCursorGibIntProd lenA(GibCursor end_r_15741,
                                  GibCursor ls_1601_8685_13099);
GibCursorGibCursorProd trav_exp(GibCursor end_r_15743,
                                GibCursor exp_1631_8715_13106);
GibCursorGibFloatProd maybeLit(GibCursor end_r_15745,
                               GibCursor exp_1651_8735_13112);
GibInt maxInt(GibInt a_1664_8748_13116, GibInt b_1665_8749_13117);
GibInt cmpz_point3d_original(GibFloatGibFloatGibFloatProd a_2053_8837_13119,
                             GibFloatGibFloatGibFloatProd b_2054_8838_13120);
int cmpz_point3d(const void *a_2053_8837_13119, const void *b_2054_8838_13120);
GibInt cmpy_point3d_original(GibFloatGibFloatGibFloatProd a_2059_8843_13129,
                             GibFloatGibFloatGibFloatProd b_2060_8844_13130);
int cmpy_point3d(const void *a_2059_8843_13129, const void *b_2060_8844_13130);
GibInt cmpx_point3d_original(GibFloatGibFloatGibFloatProd a_2065_8849_13139,
                             GibFloatGibFloatGibFloatProd b_2066_8850_13140);
int cmpx_point3d(const void *a_2065_8849_13139, const void *b_2066_8850_13140);
GibVector *filter_loop_3498(GibVector *idxs_1676_8958_13149,
                            GibInt write_at_1677_8959_13150,
                            GibInt start_1678_8960_13151,
                            GibInt end_1679_8961_13152,
                            GibVector *from_1680_8962_13153,
                            GibVector *to_1681_8963_13154);
GibInt foldl_loop_3499_5967(GibInt idx_1765_9799_13228,
                            GibInt end_1766_9800_13229,
                            GibInt acc_1768_9801_13230,
                            GibVector *vec_1769_9802_13231);
GibCursorGibVectorProd generate_loop_3496_5968(GibCursor end_r_15747,
                                               GibVector *vec_1797_9804_13239,
                                               GibInt idx_1798_9805_13240,
                                               GibInt end_1799_9806_13241,
                                               GibCursor bht_665_9807_13242,
                                               GibVector *mpts_666_9808_13243,
                                               GibVector *ps_667_9809_13244);
GibVector *generate_loop_3495_5969(GibVector *vec_1797_9811_13256,
                                   GibInt idx_1798_9812_13257,
                                   GibInt end_1799_9813_13258,
                                   GibVector *vec_1794_9814_13259);
GibVector *generate_loop_3493_5973(GibVector *vec_1797_9841_13266,
                                   GibInt idx_1798_9842_13267,
                                   GibInt end_1799_9843_13268);
GibVector *generate_loop_3493_5975(GibVector *vec_1797_9850_13274,
                                   GibInt idx_1798_9851_13275,
                                   GibInt end_1799_9852_13276,
                                   GibVector *vec_1579_9853_13277,
                                   GibFloatGibFloatGibFloatGibFloatProd box_1343_9854_13278);
GibCursorGibVectorProd generate_loop_3495_5986(GibCursor end_r_15749,
                                               GibVector *vec_1797_9925_13294,
                                               GibInt idx_1798_9926_13295,
                                               GibInt end_1799_9927_13296,
                                               GibVector *vec_627_9928_13297,
                                               GibCursor tr_561_9929_13298);
GibCursorGibVectorProd generate_loop_3493_5989(GibCursor end_r_15751,
                                               GibVector *vec_1797_9942_13314,
                                               GibInt idx_1798_9943_13315,
                                               GibInt end_1799_9944_13316,
                                               GibVector *vec_627_9945_13317,
                                               GibFloat radius_532_9946_13318,
                                               GibCursor tr_533_9947_13319);
GibVector *generate_loop_3496_5995(GibVector *vec_1797_9970_13334,
                                   GibInt idx_1798_9971_13335,
                                   GibInt end_1799_9972_13336,
                                   GibVector *vec_627_9973_13337);
GibVector *generate_loop_3496_6001(GibVector *vec_1797_9996_13350,
                                   GibInt idx_1798_9997_13351,
                                   GibInt end_1799_9998_13352,
                                   GibVector *vec_627_9999_13353);
GibVector *generate_loop_3495_6007(GibVector *vec_1797_10022_13366,
                                   GibInt idx_1798_10023_13367,
                                   GibInt end_1799_10024_13368,
                                   GibVector *vec_627_10025_13369);
GibVector *generate_loop_3495_6013(GibVector *vec_1797_10048_13382,
                                   GibInt idx_1798_10049_13383,
                                   GibInt end_1799_10050_13384,
                                   GibVector *vec_627_10051_13385);
GibFloatGibFloatGibFloatProd foldl_loop_3488_6015(GibInt idx_1765_10061_13393,
                                                  GibInt end_1766_10062_13394,
                                                  GibFloatGibFloatGibFloatProd acc_1768_10063_13395,
                                                  GibVector *vec_1769_10064_13396);
GibFloat foldl_loop_3487_6016(GibInt idx_1765_10068_13415,
                              GibInt end_1766_10069_13416,
                              GibFloat acc_1768_10070_13417,
                              GibVector *vec_1769_10071_13418);
GibFloat foldl_loop_3487_6017(GibInt idx_1765_10075_13430,
                              GibInt end_1766_10076_13431,
                              GibFloat acc_1768_10077_13432,
                              GibVector *vec_1769_10078_13433);
GibFloat foldl_loop_3485_6023(GibInt idx_1765_10117_13445,
                              GibInt end_1766_10118_13446,
                              GibFloat acc_1768_10119_13447,
                              GibVector *vec_1769_10120_13448);
GibFloat foldl_loop_3485_6024(GibInt idx_1765_10124_13455,
                              GibInt end_1766_10125_13456,
                              GibFloat acc_1768_10126_13457,
                              GibVector *vec_1769_10127_13458);
GibFloat foldl_loop_3485_6025(GibInt idx_1765_10131_13465,
                              GibInt end_1766_10132_13466,
                              GibFloat acc_1768_10133_13467,
                              GibVector *vec_1769_10134_13468);
GibFloat foldl_loop_3485_6026(GibInt idx_1765_10138_13475,
                              GibInt end_1766_10139_13476,
                              GibFloat acc_1768_10140_13477,
                              GibVector *vec_1769_10141_13478);
GibFloat foldl_loop_3485_6031(GibInt idx_1765_10173_13485,
                              GibInt end_1766_10174_13486,
                              GibFloat acc_1768_10175_13487,
                              GibVector *vec_1769_10176_13488);
GibFloat foldl_loop_3485_6032(GibInt idx_1765_10180_13495,
                              GibInt end_1766_10181_13496,
                              GibFloat acc_1768_10182_13497,
                              GibVector *vec_1769_10183_13498);
GibFloat foldl_loop_3485_6033(GibInt idx_1765_10187_13505,
                              GibInt end_1766_10188_13506,
                              GibFloat acc_1768_10189_13507,
                              GibVector *vec_1769_10190_13508);
GibFloat foldl_loop_3485_6034(GibInt idx_1765_10194_13515,
                              GibInt end_1766_10195_13516,
                              GibFloat acc_1768_10196_13517,
                              GibVector *vec_1769_10197_13518);
GibBoolGibIntProd foldl_loop_3484_6035(GibInt idx_1765_10199_13525,
                                       GibInt end_1766_10200_13526,
                                       GibBoolGibIntProd acc_1768_10201_13527,
                                       GibVector *vec_1769_10202_13528,
                                       GibVector *pts_545_10203_13529,
                                       GibVector *actual_546_10204_13530);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_Tree(GibCursor end_r_15754, GibCursor end_r_15755, GibCursor loc_15753,
           GibCursor arg_7118_10206_13548);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_Tree(GibCursor end_r_15758, GibCursor end_r_15759,
                        GibCursor loc_15757, GibCursor arg_7127_10215_13557);
GibCursorGibCursorProd _traverse_Tree(GibCursor end_r_15761,
                                      GibCursor arg_7136_10224_13566);
GibCursorGibCursorProd _print_Tree(GibCursor end_r_15763,
                                   GibCursor arg_7145_10231_13573);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_KdTree(GibCursor end_r_15766, GibCursor end_r_15767, GibCursor loc_15765,
             GibCursor arg_7158_10244_13586);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_KdTree(GibCursor end_r_15770, GibCursor end_r_15771,
                          GibCursor loc_15769, GibCursor arg_7193_10279_13621);
GibCursorGibCursorProd _traverse_KdTree(GibCursor end_r_15773,
                                        GibCursor arg_7228_10314_13656);
GibCursorGibCursorProd _print_KdTree(GibCursor end_r_15775,
                                     GibCursor arg_7263_10334_13676);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_BH_Tree(GibCursor end_r_15778, GibCursor end_r_15779, GibCursor loc_15777,
              GibCursor arg_7304_10375_13717);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_BH_Tree(GibCursor end_r_15782, GibCursor end_r_15783,
                           GibCursor loc_15781, GibCursor arg_7329_10400_13742);
GibCursorGibCursorProd _traverse_BH_Tree(GibCursor end_r_15785,
                                         GibCursor arg_7354_10425_13767);
GibCursorGibCursorProd _print_BH_Tree(GibCursor end_r_15787,
                                      GibCursor arg_7379_10442_13784);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_AList(GibCursor end_r_15790, GibCursor end_r_15791, GibCursor loc_15789,
            GibCursor arg_7410_10473_13815);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_AList(GibCursor end_r_15794, GibCursor end_r_15795,
                         GibCursor loc_15793, GibCursor arg_7419_10482_13824);
GibCursorGibCursorProd _traverse_AList(GibCursor end_r_15797,
                                       GibCursor arg_7428_10491_13833);
GibCursorGibCursorProd _print_AList(GibCursor end_r_15799,
                                    GibCursor arg_7437_10498_13840);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_Exp(GibCursor end_r_15802, GibCursor end_r_15803, GibCursor loc_15801,
          GibCursor arg_7452_10513_13855);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_Exp(GibCursor end_r_15806, GibCursor end_r_15807,
                       GibCursor loc_15805, GibCursor arg_7467_10528_13870);
GibCursorGibCursorProd _traverse_Exp(GibCursor end_r_15809,
                                     GibCursor arg_7482_10543_13885);
GibCursorGibCursorProd _print_Exp(GibCursor end_r_15811,
                                  GibCursor arg_7497_10557_13899);
typedef enum {
            GibInt_T,
            GibFloat_T,
            GibSym_T,
            GibBool_T,
            GibVector_T,
            GibList_T,
            GibCursor_T,
            AList_T,
            BH_Tree_T,
            Exp_T,
            KdTree_T,
            Tree_T,
        } GibDatatype;
void info_table_initialize(void)
{
    int error = gib_info_table_initialize(12);

    if (error < 0) {
        fprintf(stderr, "Couldn't initialize info table, errorno=%d", error);
        exit(1);
    }

    GibDatatype field_tys[14];

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
    gib_add_symbol(21850,
                   "benchrunner: select benchmark to run with --bench-prog\n");
    gib_add_symbol(21851, "actual= ");
    gib_add_symbol(21852, "Sum: expected= ");
    gib_add_symbol(21853, "OK\n");
    gib_add_symbol(21854, "Err\n");
    gib_add_symbol(21855, "Counts: ");
    gib_add_symbol(21856, ", ");
    gib_add_symbol(21857, ")");
    gib_add_symbol(21858, "(Plus ");
    gib_add_symbol(21859, "(Or ");
    gib_add_symbol(21860, "(Node ");
    gib_add_symbol(21861, "(MkTrue ");
    gib_add_symbol(21862, "(MkFalse ");
    gib_add_symbol(21863, "(Lit ");
    gib_add_symbol(21864, "(Leaf ");
    gib_add_symbol(21865, "(KdNode ");
    gib_add_symbol(21866, "(KdLeaf ");
    gib_add_symbol(21867, "(KdEmpty ");
    gib_add_symbol(21868, "(BH_Node ");
    gib_add_symbol(21869, "(BH_Leaf ");
    gib_add_symbol(21870, "(BH_Empty ");
    gib_add_symbol(21871, "(Append ");
    gib_add_symbol(21872, "(And ");
    gib_add_symbol(21873, "(ASing ");
    gib_add_symbol(21874, "(ANil ");
    gib_add_symbol(21875, " ->r ");
    gib_add_symbol(21876, " ->i ");
    gib_add_symbol(21877, "\n");
}
unsigned char bench_seqfib()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibInt n_244_7527_12147 = gib_get_size_param();
    GibInt timed_21195;
    GibVector *times_3 = gib_vector_alloc(gib_get_iters_param(),
                                          sizeof(double));
    struct timespec begin_timed_21195;
    struct timespec end_timed_21195;

    for (long long iters_timed_21195 = 0; iters_timed_21195 <
         gib_get_iters_param(); iters_timed_21195++) {
        if (iters_timed_21195 != gib_get_iters_param() - 1)
            gib_list_bumpalloc_save_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed_21195);

        GibInt tailapp_17247 =  fib_seq(n_244_7527_12147);

        timed_21195 = tailapp_17247;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed_21195);
        if (iters_timed_21195 != gib_get_iters_param() - 1)
            gib_list_bumpalloc_restore_state();

        double itertime_0 = gib_difftimespecs(&begin_timed_21195,
                                              &end_timed_21195);

        printf("itertime: %lf\n", itertime_0);
        gib_vector_inplace_update(times_3, iters_timed_21195, &itertime_0);
    }
    gib_vector_inplace_sort(times_3, gib_compare_doubles);

    double *tmp_4 = (double *) gib_vector_nth(times_3, gib_get_iters_param() /
                                              2);
    double selftimed_2 = *tmp_4;
    double batchtime_1 = gib_sum_timing_array(times_3);

    gib_print_timing_array(times_3);
    gib_vector_free(times_3);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_1);
    printf("SELFTIMED: %e\n", selftimed_2);

    unsigned char wildcard__2_246_7529_12149 = printf("%ld", timed_21195);
    unsigned char wildcard__0_247_7530_12150 = gib_print_symbol(21877);

    return 0;
}
unsigned char bench_seqfoldconstants()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibChunk region_21878 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_15824 = region_21878.start;
    GibCursor end_r_15824 = region_21878.end;
    GibChunk region_21879 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_15823 = region_21879.start;
    GibCursor end_r_15823 = region_21879.end;
    GibInt fltAppE_11794_12151 = gib_get_size_param();
    GibCursorGibCursorGibCursorProd tmp_struct_5 =
                                     buildExp(end_r_15824, r_15824, fltAppE_11794_12151);
    GibCursor pvrtmp_21880 = tmp_struct_5.field0;
    GibCursor pvrtmp_21881 = tmp_struct_5.field1;
    GibCursor pvrtmp_21882 = tmp_struct_5.field2;

    gib_shadowstack_push(rstack, r_15824, pvrtmp_21880, Stk, Exp_T);
    frame = gib_shadowstack_pop(rstack);
    r_15824 = frame->ptr;
    pvrtmp_21880 = frame->endptr;

    GibCursor pvrtmp_21898;
    GibCursor pvrtmp_21899;
    GibCursor pvrtmp_21900;
    GibVector *times_10 = gib_vector_alloc(gib_get_iters_param(),
                                           sizeof(double));
    struct timespec begin_pvrtmp_21898;
    struct timespec end_pvrtmp_21898;

    for (long long iters_pvrtmp_21898 = 0; iters_pvrtmp_21898 <
         gib_get_iters_param(); iters_pvrtmp_21898++) {
        if (iters_pvrtmp_21898 != gib_get_iters_param() - 1)
            gib_list_bumpalloc_save_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_21898);

        GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_6 =
                                                           foldConstants2(pvrtmp_21880, end_r_15823, r_15823, pvrtmp_21881);
        GibCursor pvrtmp_21887 = tmp_struct_6.field0;
        GibCursor pvrtmp_21888 = tmp_struct_6.field1;
        GibCursor pvrtmp_21889 = tmp_struct_6.field2;
        GibCursor pvrtmp_21890 = tmp_struct_6.field3;
        GibCursor pvrtmp_21891 = tmp_struct_6.field4;

        pvrtmp_21898 = pvrtmp_21888;
        pvrtmp_21899 = pvrtmp_21890;
        pvrtmp_21900 = pvrtmp_21891;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_21898);
        if (iters_pvrtmp_21898 != gib_get_iters_param() - 1)
            gib_list_bumpalloc_restore_state();

        double itertime_7 = gib_difftimespecs(&begin_pvrtmp_21898,
                                              &end_pvrtmp_21898);

        printf("itertime: %lf\n", itertime_7);
        gib_vector_inplace_update(times_10, iters_pvrtmp_21898, &itertime_7);
    }
    gib_vector_inplace_sort(times_10, gib_compare_doubles);

    double *tmp_11 = (double *) gib_vector_nth(times_10, gib_get_iters_param() /
                                               2);
    double selftimed_9 = *tmp_11;
    double batchtime_8 = gib_sum_timing_array(times_10);

    gib_print_timing_array(times_10);
    gib_vector_free(times_10);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_8);
    printf("SELFTIMED: %e\n", selftimed_9);

    GibCursorGibCursorGibIntProd tmp_struct_12 =
                                  sumExp(end_r_15823, pvrtmp_21899);
    GibCursor pvrtmp_21908 = tmp_struct_12.field0;
    GibCursor pvrtmp_21909 = tmp_struct_12.field1;
    GibInt pvrtmp_21910 = tmp_struct_12.field2;
    unsigned char wildcard__231_255_7538_12155 = printf("%ld", pvrtmp_21910);

    return 0;
}
unsigned char bench_seqcoins()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibChunk region_21911 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_15831 = region_21911.start;
    GibCursor end_r_15831 = region_21911.end;
    GibList *coins0_265_7548_12156 = gib_list_alloc(sizeof(GibIntGibIntProd));
    GibList *coins1_266_7549_12158 = gib_list_cons(&(GibIntGibIntProd) {250,
                                                                        55},
                                                   coins0_265_7548_12156);
    GibList *coins2_267_7550_12160 = gib_list_cons(&(GibIntGibIntProd) {100,
                                                                        88},
                                                   coins1_266_7549_12158);
    GibList *coins3_268_7551_12162 = gib_list_cons(&(GibIntGibIntProd) {25, 88},
                                                   coins2_267_7550_12160);
    GibList *coins4_269_7552_12164 = gib_list_cons(&(GibIntGibIntProd) {10, 99},
                                                   coins3_268_7551_12162);
    GibList *coins5_270_7553_12166 = gib_list_cons(&(GibIntGibIntProd) {5, 122},
                                                   coins4_269_7552_12164);
    GibList *coins6_271_7554_12168 = gib_list_cons(&(GibIntGibIntProd) {1, 177},
                                                   coins5_270_7553_12166);
    GibInt amt_272_7555_12169 = gib_get_size_param();
    GibCursor pvrtmp_21933;
    GibCursor pvrtmp_21934;
    GibCursor pvrtmp_21935;
    GibVector *times_17 = gib_vector_alloc(gib_get_iters_param(),
                                           sizeof(double));
    struct timespec begin_pvrtmp_21933;
    struct timespec end_pvrtmp_21933;

    for (long long iters_pvrtmp_21933 = 0; iters_pvrtmp_21933 <
         gib_get_iters_param(); iters_pvrtmp_21933++) {
        if (iters_pvrtmp_21933 != gib_get_iters_param() - 1)
            gib_list_bumpalloc_save_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_21933);

        GibCursorGibCursorGibCursorProd tmp_struct_13 =
                                         payA_seq(end_r_15831, r_15831, amt_272_7555_12169, coins6_271_7554_12168);
        GibCursor pvrtmp_21924 = tmp_struct_13.field0;
        GibCursor pvrtmp_21925 = tmp_struct_13.field1;
        GibCursor pvrtmp_21926 = tmp_struct_13.field2;

        pvrtmp_21933 = pvrtmp_21924;
        pvrtmp_21934 = pvrtmp_21925;
        pvrtmp_21935 = pvrtmp_21926;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_21933);
        if (iters_pvrtmp_21933 != gib_get_iters_param() - 1)
            gib_list_bumpalloc_restore_state();

        double itertime_14 = gib_difftimespecs(&begin_pvrtmp_21933,
                                               &end_pvrtmp_21933);

        printf("itertime: %lf\n", itertime_14);
        gib_vector_inplace_update(times_17, iters_pvrtmp_21933, &itertime_14);
    }
    gib_vector_inplace_sort(times_17, gib_compare_doubles);

    double *tmp_18 = (double *) gib_vector_nth(times_17, gib_get_iters_param() /
                                               2);
    double selftimed_16 = *tmp_18;
    double batchtime_15 = gib_sum_timing_array(times_17);

    gib_print_timing_array(times_17);
    gib_vector_free(times_17);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_15);
    printf("SELFTIMED: %e\n", selftimed_16);

    GibCursorGibCursorProd tmp_struct_19 =
                            check_coins(end_r_15831, amt_272_7555_12169, pvrtmp_21934);
    GibCursor pvrtmp_21943 = tmp_struct_19.field0;
    GibCursor pvrtmp_21944 = tmp_struct_19.field1;

    return 0;
}
unsigned char bench_seqbhut()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibVector *pts_301_7568_12171 =
              gib_vector_alloc(gib_read_arrayfile_length_param(),
                               sizeof(GibFloatGibFloatProd));
    GibFloatGibFloatProd arr_elem_24;

    FILE * fp_25;

    char *line_26 = NULL;

    size_t(len_27);
    len_27 = 0;
    ssize_t(read_28);
    fp_25 = fopen(gib_read_arrayfile_param(), "r");
    if (fp_25 == NULL) {
        fprintf(stderr, "fopen failed\n");
        abort();
    }

    GibFloat tmp_30;
    GibFloat tmp_31;
    GibInt i_29 = 0;

    while ((read_28 = getline(&line_26, &len_27, fp_25)) != -1) {
        int xxxx = sscanf(line_26, "%f %f", &tmp_30, &tmp_31);

        arr_elem_24.field0 = tmp_30;
        arr_elem_24.field1 = tmp_31;
        gib_vector_inplace_update(pts_301_7568_12171, i_29, &arr_elem_24);
        i_29++;
    }

    GibInt fltAppE_11801_12173 = gib_vector_length(pts_301_7568_12171);
    GibInt n__1294_9967_13331_13928 =  maxInt(fltAppE_11801_12173, 0);
    GibInt tmp_23 = sizeof(GibFloatGibFloatGibFloatGibFloatGibFloatProd);
    GibVector *vec_1295_9968_13332_13929 =
              gib_vector_alloc(n__1294_9967_13331_13928, tmp_23);
    GibVector *vec1_1296_9969_13333_13930 =
               generate_loop_3496_5995(vec_1295_9968_13332_13929, 0, n__1294_9967_13331_13928, pts_301_7568_12171);
    GibInt fltAppE_11802_12176 = gib_vector_length(pts_301_7568_12171);
    GibInt n__1294_10019_13363_13933 =  maxInt(fltAppE_11802_12176, 0);
    GibInt tmp_22 = sizeof(GibFloatGibFloatGibFloatProd);
    GibVector *vec_1295_10020_13364_13934 =
              gib_vector_alloc(n__1294_10019_13363_13933, tmp_22);
    GibVector *vec1_1296_10021_13365_13935 =
               generate_loop_3495_6007(vec_1295_10020_13364_13934, 0, n__1294_10019_13363_13933, pts_301_7568_12171);
    GibInt fltAppE_11803_12180 = gib_vector_length(pts_301_7568_12171);
    GibFloat llx_314_7571_12181 =
              foldl_loop_3485_6023(0, fltAppE_11803_12180, 100000.0, pts_301_7568_12171);
    GibInt fltAppE_11804_12184 = gib_vector_length(pts_301_7568_12171);
    GibFloat lly_317_7572_12185 =
              foldl_loop_3485_6024(0, fltAppE_11804_12184, 100000.0, pts_301_7568_12171);
    GibFloat fltPrm_11805_12186 = 0.0 - 1.0;
    GibFloat acc_618_10129_10614_12187 = fltPrm_11805_12186 * 100000.0;
    GibInt fltAppE_11806_12189 = gib_vector_length(pts_301_7568_12171);
    GibFloat rux_320_7573_12190 =
              foldl_loop_3485_6025(0, fltAppE_11806_12189, acc_618_10129_10614_12187, pts_301_7568_12171);
    GibFloat fltPrm_11807_12191 = 0.0 - 1.0;
    GibFloat acc_618_10136_10616_12192 = fltPrm_11807_12191 * 100000.0;
    GibInt fltAppE_11808_12194 = gib_vector_length(pts_301_7568_12171);
    GibFloat ruy_323_7574_12195 =
              foldl_loop_3485_6026(0, fltAppE_11808_12194, acc_618_10136_10616_12192, pts_301_7568_12171);
    GibChunk region_21949 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_15836 = region_21949.start;
    GibCursor end_r_15836 = region_21949.end;
    GibCursorGibCursorGibCursorProd tmp_struct_20 =
                                     buildQtree_seq(end_r_15836, r_15836, (GibFloatGibFloatGibFloatGibFloatProd) {llx_314_7571_12181, lly_317_7572_12185, rux_320_7573_12190, ruy_323_7574_12195}, vec1_1296_10021_13365_13935);
    GibCursor pvrtmp_21954 = tmp_struct_20.field0;
    GibCursor pvrtmp_21955 = tmp_struct_20.field1;
    GibCursor pvrtmp_21956 = tmp_struct_20.field2;
    GibCursorGibVectorProd tmp_struct_21 =
                            oneStep_seq(pvrtmp_21954, pvrtmp_21955, vec1_1296_10021_13365_13935, vec1_1296_9969_13333_13930);
    GibCursor pvrtmp_21961 = tmp_struct_21.field0;
    GibVector *pvrtmp_21962 = tmp_struct_21.field1;

    return 0;
}
unsigned char bench_seqbuildquadtree()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibChunk region_21963 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_15843 = region_21963.start;
    GibCursor end_r_15843 = region_21963.end;
    GibVector *pts_353_7588_12199 =
              gib_vector_alloc(gib_read_arrayfile_length_param(),
                               sizeof(GibFloatGibFloatProd));
    GibFloatGibFloatProd arr_elem_41;

    FILE * fp_42;

    char *line_43 = NULL;

    size_t(len_44);
    len_44 = 0;
    ssize_t(read_45);
    fp_42 = fopen(gib_read_arrayfile_param(), "r");
    if (fp_42 == NULL) {
        fprintf(stderr, "fopen failed\n");
        abort();
    }

    GibFloat tmp_47;
    GibFloat tmp_48;
    GibInt i_46 = 0;

    while ((read_45 = getline(&line_43, &len_44, fp_42)) != -1) {
        int xxxx = sscanf(line_43, "%f %f", &tmp_47, &tmp_48);

        arr_elem_41.field0 = tmp_47;
        arr_elem_41.field1 = tmp_48;
        gib_vector_inplace_update(pts_353_7588_12199, i_46, &arr_elem_41);
        i_46++;
    }

    GibInt fltAppE_11809_12201 = gib_vector_length(pts_353_7588_12199);
    GibInt n__1294_9993_13347_13938 =  maxInt(fltAppE_11809_12201, 0);
    GibInt tmp_40 = sizeof(GibFloatGibFloatGibFloatGibFloatGibFloatProd);
    GibVector *vec_1295_9994_13348_13939 =
              gib_vector_alloc(n__1294_9993_13347_13938, tmp_40);
    GibVector *vec1_1296_9995_13349_13940 =
               generate_loop_3496_6001(vec_1295_9994_13348_13939, 0, n__1294_9993_13347_13938, pts_353_7588_12199);
    GibInt fltAppE_11810_12204 = gib_vector_length(pts_353_7588_12199);
    GibInt n__1294_10045_13379_13943 =  maxInt(fltAppE_11810_12204, 0);
    GibInt tmp_39 = sizeof(GibFloatGibFloatGibFloatProd);
    GibVector *vec_1295_10046_13380_13944 =
              gib_vector_alloc(n__1294_10045_13379_13943, tmp_39);
    GibVector *vec1_1296_10047_13381_13945 =
               generate_loop_3495_6013(vec_1295_10046_13380_13944, 0, n__1294_10045_13379_13943, pts_353_7588_12199);
    GibInt fltAppE_11811_12208 = gib_vector_length(pts_353_7588_12199);
    GibFloat llx_366_7591_12209 =
              foldl_loop_3485_6031(0, fltAppE_11811_12208, 100000.0, pts_353_7588_12199);
    GibInt fltAppE_11812_12212 = gib_vector_length(pts_353_7588_12199);
    GibFloat lly_369_7592_12213 =
              foldl_loop_3485_6032(0, fltAppE_11812_12212, 100000.0, pts_353_7588_12199);
    GibFloat fltPrm_11813_12214 = 0.0 - 1.0;
    GibFloat acc_618_10185_10634_12215 = fltPrm_11813_12214 * 100000.0;
    GibInt fltAppE_11814_12217 = gib_vector_length(pts_353_7588_12199);
    GibFloat rux_372_7593_12218 =
              foldl_loop_3485_6033(0, fltAppE_11814_12217, acc_618_10185_10634_12215, pts_353_7588_12199);
    GibFloat fltPrm_11815_12219 = 0.0 - 1.0;
    GibFloat acc_618_10192_10636_12220 = fltPrm_11815_12219 * 100000.0;
    GibInt fltAppE_11816_12222 = gib_vector_length(pts_353_7588_12199);
    GibFloat ruy_375_7594_12223 =
              foldl_loop_3485_6034(0, fltAppE_11816_12222, acc_618_10192_10636_12220, pts_353_7588_12199);
    GibCursor pvrtmp_21981;
    GibCursor pvrtmp_21982;
    GibCursor pvrtmp_21983;
    GibVector *times_36 = gib_vector_alloc(gib_get_iters_param(),
                                           sizeof(double));
    struct timespec begin_pvrtmp_21981;
    struct timespec end_pvrtmp_21981;

    for (long long iters_pvrtmp_21981 = 0; iters_pvrtmp_21981 <
         gib_get_iters_param(); iters_pvrtmp_21981++) {
        if (iters_pvrtmp_21981 != gib_get_iters_param() - 1)
            gib_list_bumpalloc_save_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_21981);

        GibCursorGibCursorGibCursorProd tmp_struct_32 =
                                         buildQtree_seq(end_r_15843, r_15843, (GibFloatGibFloatGibFloatGibFloatProd) {llx_366_7591_12209, lly_369_7592_12213, rux_372_7593_12218, ruy_375_7594_12223}, vec1_1296_10047_13381_13945);
        GibCursor pvrtmp_21972 = tmp_struct_32.field0;
        GibCursor pvrtmp_21973 = tmp_struct_32.field1;
        GibCursor pvrtmp_21974 = tmp_struct_32.field2;

        pvrtmp_21981 = pvrtmp_21972;
        pvrtmp_21982 = pvrtmp_21973;
        pvrtmp_21983 = pvrtmp_21974;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_21981);
        if (iters_pvrtmp_21981 != gib_get_iters_param() - 1)
            gib_list_bumpalloc_restore_state();

        double itertime_33 = gib_difftimespecs(&begin_pvrtmp_21981,
                                               &end_pvrtmp_21981);

        printf("itertime: %lf\n", itertime_33);
        gib_vector_inplace_update(times_36, iters_pvrtmp_21981, &itertime_33);
    }
    gib_vector_inplace_sort(times_36, gib_compare_doubles);

    double *tmp_37 = (double *) gib_vector_nth(times_36, gib_get_iters_param() /
                                               2);
    double selftimed_35 = *tmp_37;
    double batchtime_34 = gib_sum_timing_array(times_36);

    gib_print_timing_array(times_36);
    gib_vector_free(times_36);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_34);
    printf("SELFTIMED: %e\n", selftimed_35);

    GibCursorGibCursorProd tmp_struct_38 =
                            check_buildquadtree(end_r_15843, vec1_1296_10047_13381_13945, pvrtmp_21982);
    GibCursor pvrtmp_21991 = tmp_struct_38.field0;
    GibCursor pvrtmp_21992 = tmp_struct_38.field1;

    return 0;
}
unsigned char bench_seqnearest()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibChunk region_21993 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_15849 = region_21993.start;
    GibCursor end_r_15849 = region_21993.end;
    GibVector *pts_381_7600_12226 =
              gib_vector_alloc(gib_read_arrayfile_length_param(),
                               sizeof(GibFloatGibFloatGibFloatProd));
    GibFloatGibFloatGibFloatProd arr_elem_56;

    FILE * fp_57;

    char *line_58 = NULL;

    size_t(len_59);
    len_59 = 0;
    ssize_t(read_60);
    fp_57 = fopen(gib_read_arrayfile_param(), "r");
    if (fp_57 == NULL) {
        fprintf(stderr, "fopen failed\n");
        abort();
    }

    GibFloat tmp_62;
    GibFloat tmp_63;
    GibFloat tmp_64;
    GibInt i_61 = 0;

    while ((read_60 = getline(&line_58, &len_59, fp_57)) != -1) {
        int xxxx = sscanf(line_58, "%f %f %f", &tmp_62, &tmp_63, &tmp_64);

        arr_elem_56.field0 = tmp_62;
        arr_elem_56.field1 = tmp_63;
        arr_elem_56.field2 = tmp_64;
        gib_vector_inplace_update(pts_381_7600_12226, i_61, &arr_elem_56);
        i_61++;
    }

    GibCursorGibCursorGibCursorProd tmp_struct_49 =
                                     mkKdTree_seq(end_r_15849, r_15849, pts_381_7600_12226);
    GibCursor pvrtmp_21994 = tmp_struct_49.field0;
    GibCursor pvrtmp_21995 = tmp_struct_49.field1;
    GibCursor pvrtmp_21996 = tmp_struct_49.field2;
    GibVector *timed_21199;
    GibVector *times_54 = gib_vector_alloc(gib_get_iters_param(),
                                           sizeof(double));
    struct timespec begin_timed_21199;
    struct timespec end_timed_21199;

    for (long long iters_timed_21199 = 0; iters_timed_21199 <
         gib_get_iters_param(); iters_timed_21199++) {
        if (iters_timed_21199 != gib_get_iters_param() - 1)
            gib_list_bumpalloc_save_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed_21199);

        GibCursorGibVectorProd tmp_struct_50 =
                                allNearest_seq(pvrtmp_21994, pvrtmp_21995, pts_381_7600_12226);
        GibCursor pvrtmp_22001 = tmp_struct_50.field0;
        GibVector *pvrtmp_22002 = tmp_struct_50.field1;

        timed_21199 = pvrtmp_22002;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed_21199);
        if (iters_timed_21199 != gib_get_iters_param() - 1)
            gib_list_bumpalloc_restore_state();

        double itertime_51 = gib_difftimespecs(&begin_timed_21199,
                                               &end_timed_21199);

        printf("itertime: %lf\n", itertime_51);
        gib_vector_inplace_update(times_54, iters_timed_21199, &itertime_51);
    }
    gib_vector_inplace_sort(times_54, gib_compare_doubles);

    double *tmp_55 = (double *) gib_vector_nth(times_54, gib_get_iters_param() /
                                               2);
    double selftimed_53 = *tmp_55;
    double batchtime_52 = gib_sum_timing_array(times_54);

    gib_print_timing_array(times_54);
    gib_vector_free(times_54);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_52);
    printf("SELFTIMED: %e\n", selftimed_53);

    unsigned char tailapp_17261 =
                   check_nearest(pts_381_7600_12226, timed_21199);

    return tailapp_17261;
}
unsigned char bench_seqcountcorr()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibChunk region_22003 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_15855 = region_22003.start;
    GibCursor end_r_15855 = region_22003.end;
    GibVector *pts_393_7612_12229 =
              gib_vector_alloc(gib_read_arrayfile_length_param(),
                               sizeof(GibFloatGibFloatGibFloatProd));
    GibFloatGibFloatGibFloatProd arr_elem_74;

    FILE * fp_75;

    char *line_76 = NULL;

    size_t(len_77);
    len_77 = 0;
    ssize_t(read_78);
    fp_75 = fopen(gib_read_arrayfile_param(), "r");
    if (fp_75 == NULL) {
        fprintf(stderr, "fopen failed\n");
        abort();
    }

    GibFloat tmp_80;
    GibFloat tmp_81;
    GibFloat tmp_82;
    GibInt i_79 = 0;

    while ((read_78 = getline(&line_76, &len_77, fp_75)) != -1) {
        int xxxx = sscanf(line_76, "%f %f %f", &tmp_80, &tmp_81, &tmp_82);

        arr_elem_74.field0 = tmp_80;
        arr_elem_74.field1 = tmp_81;
        arr_elem_74.field2 = tmp_82;
        gib_vector_inplace_update(pts_393_7612_12229, i_79, &arr_elem_74);
        i_79++;
    }

    GibInt n_394_7613_12230 = gib_get_size_param();
    GibCursorGibCursorGibCursorProd tmp_struct_65 =
                                     mkKdTree_seq(end_r_15855, r_15855, pts_393_7612_12229);
    GibCursor pvrtmp_22004 = tmp_struct_65.field0;
    GibCursor pvrtmp_22005 = tmp_struct_65.field1;
    GibCursor pvrtmp_22006 = tmp_struct_65.field2;
    GibVector *pts__397_7616_12236 = gib_vector_slice(0, n_394_7613_12230,
                                                      pts_393_7612_12229);
    GibVector *timed_21200;
    GibVector *times_70 = gib_vector_alloc(gib_get_iters_param(),
                                           sizeof(double));
    struct timespec begin_timed_21200;
    struct timespec end_timed_21200;

    for (long long iters_timed_21200 = 0; iters_timed_21200 <
         gib_get_iters_param(); iters_timed_21200++) {
        if (iters_timed_21200 != gib_get_iters_param() - 1)
            gib_list_bumpalloc_save_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed_21200);

        GibCursorGibVectorProd tmp_struct_66 =
                                allCountCorr_seq(pvrtmp_22004, 100.0, pvrtmp_22005, pts__397_7616_12236);
        GibCursor pvrtmp_22011 = tmp_struct_66.field0;
        GibVector *pvrtmp_22012 = tmp_struct_66.field1;

        timed_21200 = pvrtmp_22012;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed_21200);
        if (iters_timed_21200 != gib_get_iters_param() - 1)
            gib_list_bumpalloc_restore_state();

        double itertime_67 = gib_difftimespecs(&begin_timed_21200,
                                               &end_timed_21200);

        printf("itertime: %lf\n", itertime_67);
        gib_vector_inplace_update(times_70, iters_timed_21200, &itertime_67);
    }
    gib_vector_inplace_sort(times_70, gib_compare_doubles);

    double *tmp_71 = (double *) gib_vector_nth(times_70, gib_get_iters_param() /
                                               2);
    double selftimed_69 = *tmp_71;
    double batchtime_68 = gib_sum_timing_array(times_70);

    gib_print_timing_array(times_70);
    gib_vector_free(times_70);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_68);
    printf("SELFTIMED: %e\n", selftimed_69);

    GibFloatGibFloatGibFloatProd *tmp_73;

    tmp_73 =
        (GibFloatGibFloatGibFloatProd *) gib_vector_nth(pts__397_7616_12236, 4);

    GibFloatGibFloatGibFloatProd query_399_7618_12240 = *tmp_73;
    GibInt *tmp_72;

    tmp_72 = (GibInt *) gib_vector_nth(timed_21200, 4);

    GibInt count_400_7619_12243 = *tmp_72;

    return 0;
}
unsigned char bench_seqbuildkdtree()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibChunk region_22013 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_15862 = region_22013.start;
    GibCursor end_r_15862 = region_22013.end;
    GibVector *pts_406_7625_12244 =
              gib_vector_alloc(gib_read_arrayfile_length_param(),
                               sizeof(GibFloatGibFloatGibFloatProd));
    GibFloatGibFloatGibFloatProd arr_elem_90;

    FILE * fp_91;

    char *line_92 = NULL;

    size_t(len_93);
    len_93 = 0;
    ssize_t(read_94);
    fp_91 = fopen(gib_read_arrayfile_param(), "r");
    if (fp_91 == NULL) {
        fprintf(stderr, "fopen failed\n");
        abort();
    }

    GibFloat tmp_96;
    GibFloat tmp_97;
    GibFloat tmp_98;
    GibInt i_95 = 0;

    while ((read_94 = getline(&line_92, &len_93, fp_91)) != -1) {
        int xxxx = sscanf(line_92, "%f %f %f", &tmp_96, &tmp_97, &tmp_98);

        arr_elem_90.field0 = tmp_96;
        arr_elem_90.field1 = tmp_97;
        arr_elem_90.field2 = tmp_98;
        gib_vector_inplace_update(pts_406_7625_12244, i_95, &arr_elem_90);
        i_95++;
    }

    GibInt n_407_7626_12245 = gib_get_size_param();
    GibFloat radius_408_7627_12246 = (GibFloat) n_407_7626_12245;
    GibCursor pvrtmp_22023;
    GibCursor pvrtmp_22024;
    GibCursor pvrtmp_22025;
    GibVector *times_87 = gib_vector_alloc(gib_get_iters_param(),
                                           sizeof(double));
    struct timespec begin_pvrtmp_22023;
    struct timespec end_pvrtmp_22023;

    for (long long iters_pvrtmp_22023 = 0; iters_pvrtmp_22023 <
         gib_get_iters_param(); iters_pvrtmp_22023++) {
        if (iters_pvrtmp_22023 != gib_get_iters_param() - 1)
            gib_list_bumpalloc_save_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_22023);

        GibCursorGibCursorGibCursorProd tmp_struct_83 =
                                         mkKdTree_seq(end_r_15862, r_15862, pts_406_7625_12244);
        GibCursor pvrtmp_22014 = tmp_struct_83.field0;
        GibCursor pvrtmp_22015 = tmp_struct_83.field1;
        GibCursor pvrtmp_22016 = tmp_struct_83.field2;

        pvrtmp_22023 = pvrtmp_22014;
        pvrtmp_22024 = pvrtmp_22015;
        pvrtmp_22025 = pvrtmp_22016;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_22023);
        if (iters_pvrtmp_22023 != gib_get_iters_param() - 1)
            gib_list_bumpalloc_restore_state();

        double itertime_84 = gib_difftimespecs(&begin_pvrtmp_22023,
                                               &end_pvrtmp_22023);

        printf("itertime: %lf\n", itertime_84);
        gib_vector_inplace_update(times_87, iters_pvrtmp_22023, &itertime_84);
    }
    gib_vector_inplace_sort(times_87, gib_compare_doubles);

    double *tmp_88 = (double *) gib_vector_nth(times_87, gib_get_iters_param() /
                                               2);
    double selftimed_86 = *tmp_88;
    double batchtime_85 = gib_sum_timing_array(times_87);

    gib_print_timing_array(times_87);
    gib_vector_free(times_87);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_85);
    printf("SELFTIMED: %e\n", selftimed_86);

    GibCursorGibCursorProd tmp_struct_89 =
                            check_buildkdtree(end_r_15862, pts_406_7625_12244, pvrtmp_22024);
    GibCursor pvrtmp_22033 = tmp_struct_89.field0;
    GibCursor pvrtmp_22034 = tmp_struct_89.field1;

    return 0;
}
unsigned char bench_seqsumtree()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibChunk region_22035 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_15868 = region_22035.start;
    GibCursor end_r_15868 = region_22035.end;
    GibInt n_414_7633_12248 = gib_get_size_param();
    GibCursorGibCursorGibCursorProd tmp_struct_99 =
                                     mkTree_seq(end_r_15868, r_15868, n_414_7633_12248);
    GibCursor pvrtmp_22036 = tmp_struct_99.field0;
    GibCursor pvrtmp_22037 = tmp_struct_99.field1;
    GibCursor pvrtmp_22038 = tmp_struct_99.field2;
    GibInt timed_21202;
    GibVector *times_104 = gib_vector_alloc(gib_get_iters_param(),
                                            sizeof(double));
    struct timespec begin_timed_21202;
    struct timespec end_timed_21202;

    for (long long iters_timed_21202 = 0; iters_timed_21202 <
         gib_get_iters_param(); iters_timed_21202++) {
        if (iters_timed_21202 != gib_get_iters_param() - 1)
            gib_list_bumpalloc_save_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed_21202);

        GibCursorGibCursorGibIntProd tmp_struct_100 =
                                      sumTree_seq(pvrtmp_22036, pvrtmp_22037);
        GibCursor pvrtmp_22043 = tmp_struct_100.field0;
        GibCursor pvrtmp_22044 = tmp_struct_100.field1;
        GibInt pvrtmp_22045 = tmp_struct_100.field2;

        timed_21202 = pvrtmp_22045;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed_21202);
        if (iters_timed_21202 != gib_get_iters_param() - 1)
            gib_list_bumpalloc_restore_state();

        double itertime_101 = gib_difftimespecs(&begin_timed_21202,
                                                &end_timed_21202);

        printf("itertime: %lf\n", itertime_101);
        gib_vector_inplace_update(times_104, iters_timed_21202, &itertime_101);
    }
    gib_vector_inplace_sort(times_104, gib_compare_doubles);

    double *tmp_105 = (double *) gib_vector_nth(times_104,
                                                gib_get_iters_param() / 2);
    double selftimed_103 = *tmp_105;
    double batchtime_102 = gib_sum_timing_array(times_104);

    gib_print_timing_array(times_104);
    gib_vector_free(times_104);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_102);
    printf("SELFTIMED: %e\n", selftimed_103);

    unsigned char tailapp_17269 =  check_sumtree(n_414_7633_12248, timed_21202);

    return tailapp_17269;
}
unsigned char bench_seqadd1tree()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibChunk region_22046 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_15880 = region_22046.start;
    GibCursor end_r_15880 = region_22046.end;
    GibChunk region_22047 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_15879 = region_22047.start;
    GibCursor end_r_15879 = region_22047.end;
    GibInt n_421_7640_12251 = gib_get_size_param();
    GibCursorGibCursorGibCursorProd tmp_struct_106 =
                                     mkTree_seq(end_r_15880, r_15880, n_421_7640_12251);
    GibCursor pvrtmp_22048 = tmp_struct_106.field0;
    GibCursor pvrtmp_22049 = tmp_struct_106.field1;
    GibCursor pvrtmp_22050 = tmp_struct_106.field2;

    gib_shadowstack_push(rstack, r_15880, pvrtmp_22048, Stk, Tree_T);
    frame = gib_shadowstack_pop(rstack);
    r_15880 = frame->ptr;
    pvrtmp_22048 = frame->endptr;

    GibCursor pvrtmp_22066;
    GibCursor pvrtmp_22067;
    GibCursor pvrtmp_22068;
    GibVector *times_111 = gib_vector_alloc(gib_get_iters_param(),
                                            sizeof(double));
    struct timespec begin_pvrtmp_22066;
    struct timespec end_pvrtmp_22066;

    for (long long iters_pvrtmp_22066 = 0; iters_pvrtmp_22066 <
         gib_get_iters_param(); iters_pvrtmp_22066++) {
        if (iters_pvrtmp_22066 != gib_get_iters_param() - 1)
            gib_list_bumpalloc_save_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_22066);

        GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_107 =
                                                           add1Tree_seq(pvrtmp_22048, end_r_15879, r_15879, pvrtmp_22049);
        GibCursor pvrtmp_22055 = tmp_struct_107.field0;
        GibCursor pvrtmp_22056 = tmp_struct_107.field1;
        GibCursor pvrtmp_22057 = tmp_struct_107.field2;
        GibCursor pvrtmp_22058 = tmp_struct_107.field3;
        GibCursor pvrtmp_22059 = tmp_struct_107.field4;

        pvrtmp_22066 = pvrtmp_22056;
        pvrtmp_22067 = pvrtmp_22058;
        pvrtmp_22068 = pvrtmp_22059;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_22066);
        if (iters_pvrtmp_22066 != gib_get_iters_param() - 1)
            gib_list_bumpalloc_restore_state();

        double itertime_108 = gib_difftimespecs(&begin_pvrtmp_22066,
                                                &end_pvrtmp_22066);

        printf("itertime: %lf\n", itertime_108);
        gib_vector_inplace_update(times_111, iters_pvrtmp_22066, &itertime_108);
    }
    gib_vector_inplace_sort(times_111, gib_compare_doubles);

    double *tmp_112 = (double *) gib_vector_nth(times_111,
                                                gib_get_iters_param() / 2);
    double selftimed_110 = *tmp_112;
    double batchtime_109 = gib_sum_timing_array(times_111);

    gib_print_timing_array(times_111);
    gib_vector_free(times_111);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_109);
    printf("SELFTIMED: %e\n", selftimed_110);

    GibCursorGibCursorProd tmp_struct_113 =
                            check_add1tree(end_r_15879, n_421_7640_12251, pvrtmp_22067);
    GibCursor pvrtmp_22076 = tmp_struct_113.field0;
    GibCursor pvrtmp_22077 = tmp_struct_113.field1;

    return 0;
}
unsigned char bench_seqbuildtree()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibChunk region_22078 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_15887 = region_22078.start;
    GibCursor end_r_15887 = region_22078.end;
    GibInt n_427_7646_12254 = gib_get_size_param();
    GibCursor pvrtmp_22088;
    GibCursor pvrtmp_22089;
    GibCursor pvrtmp_22090;
    GibVector *times_118 = gib_vector_alloc(gib_get_iters_param(),
                                            sizeof(double));
    struct timespec begin_pvrtmp_22088;
    struct timespec end_pvrtmp_22088;

    for (long long iters_pvrtmp_22088 = 0; iters_pvrtmp_22088 <
         gib_get_iters_param(); iters_pvrtmp_22088++) {
        if (iters_pvrtmp_22088 != gib_get_iters_param() - 1)
            gib_list_bumpalloc_save_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_22088);

        GibCursorGibCursorGibCursorProd tmp_struct_114 =
                                         mkTree_seq(end_r_15887, r_15887, n_427_7646_12254);
        GibCursor pvrtmp_22079 = tmp_struct_114.field0;
        GibCursor pvrtmp_22080 = tmp_struct_114.field1;
        GibCursor pvrtmp_22081 = tmp_struct_114.field2;

        pvrtmp_22088 = pvrtmp_22079;
        pvrtmp_22089 = pvrtmp_22080;
        pvrtmp_22090 = pvrtmp_22081;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_22088);
        if (iters_pvrtmp_22088 != gib_get_iters_param() - 1)
            gib_list_bumpalloc_restore_state();

        double itertime_115 = gib_difftimespecs(&begin_pvrtmp_22088,
                                                &end_pvrtmp_22088);

        printf("itertime: %lf\n", itertime_115);
        gib_vector_inplace_update(times_118, iters_pvrtmp_22088, &itertime_115);
    }
    gib_vector_inplace_sort(times_118, gib_compare_doubles);

    double *tmp_119 = (double *) gib_vector_nth(times_118,
                                                gib_get_iters_param() / 2);
    double selftimed_117 = *tmp_119;
    double batchtime_116 = gib_sum_timing_array(times_118);

    gib_print_timing_array(times_118);
    gib_vector_free(times_118);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_116);
    printf("SELFTIMED: %e\n", selftimed_117);

    GibCursorGibCursorProd tmp_struct_120 =
                            check_buildtree(end_r_15887, n_427_7646_12254, pvrtmp_22089);
    GibCursor pvrtmp_22098 = tmp_struct_120.field0;
    GibCursor pvrtmp_22099 = tmp_struct_120.field1;

    return 0;
}
unsigned char bench_seqbuildfib()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibChunk region_22100 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_15894 = region_22100.start;
    GibCursor end_r_15894 = region_22100.end;
    GibInt n_432_7651_12256 = gib_get_size_param();
    GibCursor pvrtmp_22110;
    GibCursor pvrtmp_22111;
    GibCursor pvrtmp_22112;
    GibVector *times_125 = gib_vector_alloc(gib_get_iters_param(),
                                            sizeof(double));
    struct timespec begin_pvrtmp_22110;
    struct timespec end_pvrtmp_22110;

    for (long long iters_pvrtmp_22110 = 0; iters_pvrtmp_22110 <
         gib_get_iters_param(); iters_pvrtmp_22110++) {
        if (iters_pvrtmp_22110 != gib_get_iters_param() - 1)
            gib_list_bumpalloc_save_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_22110);

        GibCursorGibCursorGibCursorProd tmp_struct_121 =
                                         mkTreeFib_seq(end_r_15894, r_15894, n_432_7651_12256);
        GibCursor pvrtmp_22101 = tmp_struct_121.field0;
        GibCursor pvrtmp_22102 = tmp_struct_121.field1;
        GibCursor pvrtmp_22103 = tmp_struct_121.field2;

        pvrtmp_22110 = pvrtmp_22101;
        pvrtmp_22111 = pvrtmp_22102;
        pvrtmp_22112 = pvrtmp_22103;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_22110);
        if (iters_pvrtmp_22110 != gib_get_iters_param() - 1)
            gib_list_bumpalloc_restore_state();

        double itertime_122 = gib_difftimespecs(&begin_pvrtmp_22110,
                                                &end_pvrtmp_22110);

        printf("itertime: %lf\n", itertime_122);
        gib_vector_inplace_update(times_125, iters_pvrtmp_22110, &itertime_122);
    }
    gib_vector_inplace_sort(times_125, gib_compare_doubles);

    double *tmp_126 = (double *) gib_vector_nth(times_125,
                                                gib_get_iters_param() / 2);
    double selftimed_124 = *tmp_126;
    double batchtime_123 = gib_sum_timing_array(times_125);

    gib_print_timing_array(times_125);
    gib_vector_free(times_125);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_123);
    printf("SELFTIMED: %e\n", selftimed_124);

    GibCursorGibCursorProd tmp_struct_127 =
                            check_buildfib(end_r_15894, n_432_7651_12256, pvrtmp_22111);
    GibCursor pvrtmp_22120 = tmp_struct_127.field0;
    GibCursor pvrtmp_22121 = tmp_struct_127.field1;

    return 0;
}
GibInt fib_seq(GibInt n_439_7658_12258)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_11817_12259 = n_439_7658_12258 == 0;

    if (fltIf_11817_12259) {
        return 0;
    } else {
        GibBool fltIf_11818_12260 = n_439_7658_12258 == 1;

        if (fltIf_11818_12260) {
            return 1;
        } else {
            GibInt fltAppE_11819_12261 = n_439_7658_12258 - 1;
            GibInt x_440_7659_12262 =  fib_seq(fltAppE_11819_12261);
            GibInt fltAppE_11820_12263 = n_439_7658_12258 - 2;
            GibInt y_441_7660_12264 =  fib_seq(fltAppE_11820_12263);
            GibInt tailprim_17282 = x_440_7659_12262 + y_441_7660_12264;

            return tailprim_17282;
        }
    }
}
GibCursorGibCursorProd check_buildfib(GibCursor end_r_15665,
                                      GibInt n_447_7666_12265,
                                      GibCursor tr_448_7667_12266)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibInt fltPrm_11821_12267 = gib_expll(2, n_447_7666_12265);

    gib_shadowstack_push(rstack, tr_448_7667_12266, end_r_15665, Stk, Tree_T);

    GibInt fltPrm_11822_12268 =  fib_seq(20);

    frame = gib_shadowstack_pop(rstack);
    tr_448_7667_12266 = frame->ptr;
    end_r_15665 = frame->endptr;

    GibInt expected_449_7668_12269 = fltPrm_11821_12267 * fltPrm_11822_12268;
    GibCursorGibCursorGibIntProd tmp_struct_128 =
                                  sumTree_seq(end_r_15665, tr_448_7667_12266);
    GibCursor pvrtmp_22122 = tmp_struct_128.field0;
    GibCursor pvrtmp_22123 = tmp_struct_128.field1;
    GibInt pvrtmp_22124 = tmp_struct_128.field2;
    GibBool fltAppE_11823_12271 = expected_449_7668_12269 == pvrtmp_22124;
    unsigned char wildcard__76_451_7670_12272 =
                   print_check(fltAppE_11823_12271);
    unsigned char wildcard__74_452_7671_12273 = printf("%ld", pvrtmp_22124);
    unsigned char wildcard__72_453_7672_12274 = gib_print_symbol(21877);

    return (GibCursorGibCursorProd) {pvrtmp_22122, pvrtmp_22123};
}
GibCursorGibCursorGibCursorProd mkTreeFib_seq(GibCursor end_r_15667,
                                              GibCursor loc_15666,
                                              GibInt i_454_7673_12275)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_15666 + 18 > end_r_15667) {
        gib_grow_region(&loc_15666, &end_r_15667);
    }

    GibBool fltIf_11824_12276 = i_454_7673_12275 <= 0;

    if (fltIf_11824_12276) {
        gib_shadowstack_push(wstack, loc_15666, end_r_15667, Stk, Tree_T);

        GibInt fltPkd_11825_12277 =  fib_seq(20);

        frame = gib_shadowstack_pop(wstack);
        loc_15666 = frame->ptr;
        end_r_15667 = frame->endptr;
        *(GibPackedTag *) loc_15666 = 0;

        GibCursor writetag_18892 = loc_15666 + 1;
        GibCursor after_tag_18893 = loc_15666 + 1;

        *(GibInt *) after_tag_18893 = fltPkd_11825_12277;

        GibCursor writecur_18897 = after_tag_18893 + sizeof(GibInt);

        return (GibCursorGibCursorGibCursorProd) {end_r_15667, loc_15666,
                                                  writecur_18897};
    } else {
        GibInt fltAppE_11826_12278 = i_454_7673_12275 - 1;
        GibCursor loc_15903 = loc_15666 + 9;

        *(GibPackedTag *) loc_15666 = 1;

        GibCursor writetag_18904 = loc_15666 + 1;
        GibCursor after_tag_18905 = loc_15666 + 1;

        *(GibInt *) after_tag_18905 = i_454_7673_12275;

        GibCursor writecur_18909 = after_tag_18905 + sizeof(GibInt);

        gib_shadowstack_push(rstack, loc_15666, end_r_15667, Stk, Tree_T);

        GibCursorGibCursorGibCursorProd tmp_struct_129 =
                                         mkTreeFib_seq(end_r_15667, loc_15903, fltAppE_11826_12278);
        GibCursor pvrtmp_22129 = tmp_struct_129.field0;
        GibCursor pvrtmp_22130 = tmp_struct_129.field1;
        GibCursor pvrtmp_22131 = tmp_struct_129.field2;

        frame = gib_shadowstack_pop(rstack);
        loc_15666 = frame->ptr;
        end_r_15667 = frame->endptr;

        GibInt fltAppE_11827_12280 = i_454_7673_12275 - 1;

        gib_shadowstack_push(rstack, loc_15666, pvrtmp_22129, Stk, Tree_T);

        GibCursorGibCursorGibCursorProd tmp_struct_130 =
                                         mkTreeFib_seq(pvrtmp_22129, pvrtmp_22131, fltAppE_11827_12280);
        GibCursor pvrtmp_22136 = tmp_struct_130.field0;
        GibCursor pvrtmp_22137 = tmp_struct_130.field1;
        GibCursor pvrtmp_22138 = tmp_struct_130.field2;

        frame = gib_shadowstack_pop(rstack);
        loc_15666 = frame->ptr;
        pvrtmp_22129 = frame->endptr;
        return (GibCursorGibCursorGibCursorProd) {pvrtmp_22136, loc_15666,
                                                  pvrtmp_22138};
    }
}
GibCursorGibCursorProd check_buildtree(GibCursor end_r_15669,
                                       GibInt n_462_7681_12282,
                                       GibCursor tr_463_7682_12283)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibInt expected_464_7683_12284 = gib_expll(2, n_462_7681_12282);
    GibCursorGibCursorGibIntProd tmp_struct_134 =
                                  sumTree_seq(end_r_15669, tr_463_7682_12283);
    GibCursor pvrtmp_22147 = tmp_struct_134.field0;
    GibCursor pvrtmp_22148 = tmp_struct_134.field1;
    GibInt pvrtmp_22149 = tmp_struct_134.field2;
    GibBool fltAppE_11828_12286 = expected_464_7683_12284 == pvrtmp_22149;
    unsigned char wildcard__86_466_7685_12287 =
                   print_check(fltAppE_11828_12286);
    unsigned char wildcard__84_467_7686_12288 = printf("%ld", pvrtmp_22149);
    unsigned char wildcard__82_468_7687_12289 = gib_print_symbol(21877);

    return (GibCursorGibCursorProd) {pvrtmp_22147, pvrtmp_22148};
}
GibCursorGibCursorGibCursorProd mkTree_seq(GibCursor end_r_15671,
                                           GibCursor loc_15670,
                                           GibInt i_469_7688_12290)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_15670 + 18 > end_r_15671) {
        gib_grow_region(&loc_15670, &end_r_15671);
    }

    GibBool fltIf_11829_12291 = i_469_7688_12290 <= 0;

    if (fltIf_11829_12291) {
        *(GibPackedTag *) loc_15670 = 0;

        GibCursor writetag_18917 = loc_15670 + 1;
        GibCursor after_tag_18918 = loc_15670 + 1;

        *(GibInt *) after_tag_18918 = 1;

        GibCursor writecur_18922 = after_tag_18918 + sizeof(GibInt);

        return (GibCursorGibCursorGibCursorProd) {end_r_15671, loc_15670,
                                                  writecur_18922};
    } else {
        GibInt fltAppE_11830_12292 = i_469_7688_12290 - 1;
        GibCursor loc_15915 = loc_15670 + 9;

        *(GibPackedTag *) loc_15670 = 1;

        GibCursor writetag_18929 = loc_15670 + 1;
        GibCursor after_tag_18930 = loc_15670 + 1;

        *(GibInt *) after_tag_18930 = i_469_7688_12290;

        GibCursor writecur_18934 = after_tag_18930 + sizeof(GibInt);

        gib_shadowstack_push(rstack, loc_15670, end_r_15671, Stk, Tree_T);

        GibCursorGibCursorGibCursorProd tmp_struct_135 =
                                         mkTree_seq(end_r_15671, loc_15915, fltAppE_11830_12292);
        GibCursor pvrtmp_22154 = tmp_struct_135.field0;
        GibCursor pvrtmp_22155 = tmp_struct_135.field1;
        GibCursor pvrtmp_22156 = tmp_struct_135.field2;

        frame = gib_shadowstack_pop(rstack);
        loc_15670 = frame->ptr;
        end_r_15671 = frame->endptr;

        GibInt fltAppE_11831_12294 = i_469_7688_12290 - 1;

        gib_shadowstack_push(rstack, loc_15670, pvrtmp_22154, Stk, Tree_T);

        GibCursorGibCursorGibCursorProd tmp_struct_136 =
                                         mkTree_seq(pvrtmp_22154, pvrtmp_22156, fltAppE_11831_12294);
        GibCursor pvrtmp_22161 = tmp_struct_136.field0;
        GibCursor pvrtmp_22162 = tmp_struct_136.field1;
        GibCursor pvrtmp_22163 = tmp_struct_136.field2;

        frame = gib_shadowstack_pop(rstack);
        loc_15670 = frame->ptr;
        pvrtmp_22154 = frame->endptr;
        return (GibCursorGibCursorGibCursorProd) {pvrtmp_22161, loc_15670,
                                                  pvrtmp_22163};
    }
}
GibCursorGibCursorProd check_add1tree(GibCursor end_r_15673,
                                      GibInt n_477_7696_12296,
                                      GibCursor tr_478_7697_12297)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibInt fltPrm_11832_12298 = gib_expll(2, n_477_7696_12296);
    GibInt expected_479_7698_12299 = fltPrm_11832_12298 * 2;
    GibCursorGibCursorGibIntProd tmp_struct_140 =
                                  sumTree_seq(end_r_15673, tr_478_7697_12297);
    GibCursor pvrtmp_22172 = tmp_struct_140.field0;
    GibCursor pvrtmp_22173 = tmp_struct_140.field1;
    GibInt pvrtmp_22174 = tmp_struct_140.field2;
    unsigned char wildcard__94_481_7700_12301 = printf("%ld", pvrtmp_22174);
    unsigned char wildcard__92_482_7701_12302 = gib_print_symbol(21877);

    return (GibCursorGibCursorProd) {pvrtmp_22172, pvrtmp_22173};
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd add1Tree_seq(GibCursor end_r_15676,
                                                               GibCursor end_r_15677,
                                                               GibCursor loc_15675,
                                                               GibCursor tr_483_7702_12303)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_15675 + 18 > end_r_15677) {
        gib_grow_region(&loc_15675, &end_r_15677);
    }

    GibPackedTag tmpval_22175 = *(GibPackedTag *) tr_483_7702_12303;
    GibCursor tmpcur_22176 = tr_483_7702_12303 + 1;


  switch_22235:
    ;
    switch (tmpval_22175) {

      case 0:
        {
            GibInt tmpval_22177 = *(GibInt *) tmpcur_22176;
            GibCursor tmpcur_22178 = tmpcur_22176 + sizeof(GibInt);
            GibCursor jump_17293 = tmpcur_22176 + 8;
            GibInt fltPkd_11833_12305 = tmpval_22177 + 1;

            *(GibPackedTag *) loc_15675 = 0;

            GibCursor writetag_18944 = loc_15675 + 1;
            GibCursor after_tag_18945 = loc_15675 + 1;

            *(GibInt *) after_tag_18945 = fltPkd_11833_12305;

            GibCursor writecur_18949 = after_tag_18945 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15676,
                                                                        end_r_15677,
                                                                        jump_17293,
                                                                        loc_15675,
                                                                        writecur_18949};
            break;
        }

      case 1:
        {
            GibInt tmpval_22183 = *(GibInt *) tmpcur_22176;
            GibCursor tmpcur_22184 = tmpcur_22176 + sizeof(GibInt);
            GibCursor loc_15939 = loc_15675 + 9;

            *(GibPackedTag *) loc_15675 = 1;

            GibCursor writetag_18960 = loc_15675 + 1;
            GibCursor after_tag_18961 = loc_15675 + 1;

            *(GibInt *) after_tag_18961 = tmpval_22183;

            GibCursor writecur_18965 = after_tag_18961 + sizeof(GibInt);

            gib_shadowstack_push(rstack, loc_15675, end_r_15677, Stk, Tree_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_141 =
                                                               add1Tree_seq(end_r_15676, end_r_15677, loc_15939, tmpcur_22184);
            GibCursor pvrtmp_22185 = tmp_struct_141.field0;
            GibCursor pvrtmp_22186 = tmp_struct_141.field1;
            GibCursor pvrtmp_22187 = tmp_struct_141.field2;
            GibCursor pvrtmp_22188 = tmp_struct_141.field3;
            GibCursor pvrtmp_22189 = tmp_struct_141.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_15675 = frame->ptr;
            end_r_15677 = frame->endptr;
            gib_shadowstack_push(rstack, loc_15675, pvrtmp_22186, Stk, Tree_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_142 =
                                                               add1Tree_seq(pvrtmp_22185, pvrtmp_22186, pvrtmp_22189, pvrtmp_22187);
            GibCursor pvrtmp_22194 = tmp_struct_142.field0;
            GibCursor pvrtmp_22195 = tmp_struct_142.field1;
            GibCursor pvrtmp_22196 = tmp_struct_142.field2;
            GibCursor pvrtmp_22197 = tmp_struct_142.field3;
            GibCursor pvrtmp_22198 = tmp_struct_142.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_15675 = frame->ptr;
            pvrtmp_22186 = frame->endptr;
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_22194,
                                                                        pvrtmp_22195,
                                                                        pvrtmp_22196,
                                                                        loc_15675,
                                                                        pvrtmp_22198};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_144 = *(uintptr_t *) tmpcur_22176;
            GibCursor tmpcur_22207 = GIB_UNTAG(tagged_tmpcur_144);
            GibCursor tmpaftercur_22208 = tmpcur_22176 + 8;
            uint16_t tmptag_22209 = GIB_GET_TAG(tagged_tmpcur_144);
            GibCursor end_from_tagged_indr_17970 = tmpcur_22207 + tmptag_22209;
            GibCursor jump_17972 = tmpcur_22176 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_143 =
                                                               add1Tree_seq(end_from_tagged_indr_17970, end_r_15677, loc_15675, tmpcur_22207);
            GibCursor pvrtmp_22210 = tmp_struct_143.field0;
            GibCursor pvrtmp_22211 = tmp_struct_143.field1;
            GibCursor pvrtmp_22212 = tmp_struct_143.field2;
            GibCursor pvrtmp_22213 = tmp_struct_143.field3;
            GibCursor pvrtmp_22214 = tmp_struct_143.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15676,
                                                                        pvrtmp_22211,
                                                                        jump_17972,
                                                                        pvrtmp_22213,
                                                                        pvrtmp_22214};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_146 = *(uintptr_t *) tmpcur_22176;
            GibCursor tmpcur_22221 = GIB_UNTAG(tagged_tmpcur_146);
            GibCursor tmpaftercur_22222 = tmpcur_22176 + 8;
            uint16_t tmptag_22223 = GIB_GET_TAG(tagged_tmpcur_146);
            GibCursor end_from_tagged_indr_17970 = tmpcur_22221 + tmptag_22223;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_145 =
                                                               add1Tree_seq(end_from_tagged_indr_17970, end_r_15677, loc_15675, tmpcur_22221);
            GibCursor pvrtmp_22224 = tmp_struct_145.field0;
            GibCursor pvrtmp_22225 = tmp_struct_145.field1;
            GibCursor pvrtmp_22226 = tmp_struct_145.field2;
            GibCursor pvrtmp_22227 = tmp_struct_145.field3;
            GibCursor pvrtmp_22228 = tmp_struct_145.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_22224,
                                                                        pvrtmp_22225,
                                                                        pvrtmp_22226,
                                                                        pvrtmp_22227,
                                                                        pvrtmp_22228};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_22175");
            exit(1);
        }
    }
}
unsigned char check_sumtree(GibInt n_499_7718_12311,
                            GibInt actual_500_7719_12312)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibInt expected_501_7720_12313 = gib_expll(2, n_499_7718_12311);
    GibBool fltAppE_11834_12314 = expected_501_7720_12313 ==
            actual_500_7719_12312;
    unsigned char wildcard__104_502_7721_12315 =
                   print_check(fltAppE_11834_12314);
    unsigned char wildcard__102_503_7722_12316 = printf("%ld",
                                                        actual_500_7719_12312);
    unsigned char wildcard__100_504_7723_12317 = gib_print_symbol(21877);

    return 0;
}
GibCursorGibCursorGibIntProd sumTree_seq(GibCursor end_r_15679,
                                         GibCursor foo_505_7724_12318)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_22236 = *(GibPackedTag *) foo_505_7724_12318;
    GibCursor tmpcur_22237 = foo_505_7724_12318 + 1;


  switch_22260:
    ;
    switch (tmpval_22236) {

      case 0:
        {
            GibInt tmpval_22238 = *(GibInt *) tmpcur_22237;
            GibCursor tmpcur_22239 = tmpcur_22237 + sizeof(GibInt);
            GibCursor jump_17300 = tmpcur_22237 + 8;

            return (GibCursorGibCursorGibIntProd) {end_r_15679, jump_17300,
                                                   tmpval_22238};
            break;
        }

      case 1:
        {
            GibInt tmpval_22240 = *(GibInt *) tmpcur_22237;
            GibCursor tmpcur_22241 = tmpcur_22237 + sizeof(GibInt);
            GibCursorGibCursorGibIntProd tmp_struct_150 =
                                          sumTree_seq(end_r_15679, tmpcur_22241);
            GibCursor pvrtmp_22242 = tmp_struct_150.field0;
            GibCursor pvrtmp_22243 = tmp_struct_150.field1;
            GibInt pvrtmp_22244 = tmp_struct_150.field2;
            GibCursorGibCursorGibIntProd tmp_struct_151 =
                                          sumTree_seq(pvrtmp_22242, pvrtmp_22243);
            GibCursor pvrtmp_22245 = tmp_struct_151.field0;
            GibCursor pvrtmp_22246 = tmp_struct_151.field1;
            GibInt pvrtmp_22247 = tmp_struct_151.field2;
            GibInt tailprim_17304 = pvrtmp_22244 + pvrtmp_22247;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_22245, pvrtmp_22246,
                                                   tailprim_17304};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_153 = *(uintptr_t *) tmpcur_22237;
            GibCursor tmpcur_22248 = GIB_UNTAG(tagged_tmpcur_153);
            GibCursor tmpaftercur_22249 = tmpcur_22237 + 8;
            uint16_t tmptag_22250 = GIB_GET_TAG(tagged_tmpcur_153);
            GibCursor end_from_tagged_indr_17976 = tmpcur_22248 + tmptag_22250;
            GibCursor jump_17978 = tmpcur_22237 + 8;
            GibCursorGibCursorGibIntProd tmp_struct_152 =
                                          sumTree_seq(end_from_tagged_indr_17976, tmpcur_22248);
            GibCursor pvrtmp_22251 = tmp_struct_152.field0;
            GibCursor pvrtmp_22252 = tmp_struct_152.field1;
            GibInt pvrtmp_22253 = tmp_struct_152.field2;

            return (GibCursorGibCursorGibIntProd) {end_r_15679, jump_17978,
                                                   pvrtmp_22253};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_155 = *(uintptr_t *) tmpcur_22237;
            GibCursor tmpcur_22254 = GIB_UNTAG(tagged_tmpcur_155);
            GibCursor tmpaftercur_22255 = tmpcur_22237 + 8;
            uint16_t tmptag_22256 = GIB_GET_TAG(tagged_tmpcur_155);
            GibCursor end_from_tagged_indr_17976 = tmpcur_22254 + tmptag_22256;
            GibCursorGibCursorGibIntProd tmp_struct_154 =
                                          sumTree_seq(end_from_tagged_indr_17976, tmpcur_22254);
            GibCursor pvrtmp_22257 = tmp_struct_154.field0;
            GibCursor pvrtmp_22258 = tmp_struct_154.field1;
            GibInt pvrtmp_22259 = tmp_struct_154.field2;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_22257, pvrtmp_22258,
                                                   pvrtmp_22259};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_22236");
            exit(1);
        }
    }
}
GibCursorGibCursorProd check_buildkdtree(GibCursor end_r_15681,
                                         GibVector *pts_521_7740_12325,
                                         GibCursor tr_522_7741_12326)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    gib_shadowstack_push(rstack, tr_522_7741_12326, end_r_15681, Stk, KdTree_T);

    GibFloat expected_523_7742_12327 =  sumList(pts_521_7740_12325);

    frame = gib_shadowstack_pop(rstack);
    tr_522_7741_12326 = frame->ptr;
    end_r_15681 = frame->endptr;

    GibCursorGibCursorGibFloatProd tmp_struct_156 =
                                    sumKdTree(end_r_15681, tr_522_7741_12326);
    GibCursor pvrtmp_22261 = tmp_struct_156.field0;
    GibCursor pvrtmp_22262 = tmp_struct_156.field1;
    GibFloat pvrtmp_22263 = tmp_struct_156.field2;
    GibFloat err_525_7744_12329 = expected_523_7742_12327 - pvrtmp_22263;
    GibFloat fltPrm_11836_12330 =  float_abs(err_525_7744_12329);
    GibBool fltAppE_11835_12331 = fltPrm_11836_12330 < 0.1;
    unsigned char tailapp_17306 =  print_check(fltAppE_11835_12331);

    return (GibCursorGibCursorProd) {pvrtmp_22261, pvrtmp_22262};
}
GibCursorGibCursorGibCursorProd mkKdTree_seq(GibCursor end_r_15683,
                                             GibCursor loc_15682,
                                             GibVector *pts_526_7745_12332)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_15682 + 74 > end_r_15683) {
        gib_grow_region(&loc_15682, &end_r_15683);
    }

    GibCursorGibCursorGibCursorProd tmp_struct_157 =
                                     mkKdTreeWithAxis_seq(end_r_15683, loc_15682, 0, pts_526_7745_12332);
    GibCursor pvrtmp_22264 = tmp_struct_157.field0;
    GibCursor pvrtmp_22265 = tmp_struct_157.field1;
    GibCursor pvrtmp_22266 = tmp_struct_157.field2;

    return (GibCursorGibCursorGibCursorProd) {pvrtmp_22264, pvrtmp_22265,
                                              pvrtmp_22266};
}
GibCursorGibVectorProd allCountCorr_seq(GibCursor end_r_15685,
                                        GibFloat radius_532_7748_12333,
                                        GibCursor tr_533_7749_12334,
                                        GibVector *ls_534_7750_12335)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibInt fltAppE_11837_12339 = gib_vector_length(ls_534_7750_12335);

    gib_shadowstack_push(rstack, tr_533_7749_12334, end_r_15685, Stk, KdTree_T);

    GibInt n__1294_9939_13311_13950 =  maxInt(fltAppE_11837_12339, 0);

    frame = gib_shadowstack_pop(rstack);
    tr_533_7749_12334 = frame->ptr;
    end_r_15685 = frame->endptr;

    GibInt tmp_162 = sizeof(GibInt);
    GibVector *vec_1295_9940_13312_13951 =
              gib_vector_alloc(n__1294_9939_13311_13950, tmp_162);
    GibCursorGibVectorProd tmp_struct_161 =
                            generate_loop_3493_5989(end_r_15685, vec_1295_9940_13312_13951, 0, n__1294_9939_13311_13950, ls_534_7750_12335, radius_532_7748_12333, tr_533_7749_12334);
    GibCursor pvrtmp_22273 = tmp_struct_161.field0;
    GibVector *pvrtmp_22274 = tmp_struct_161.field1;

    return (GibCursorGibVectorProd) {pvrtmp_22273, pvrtmp_22274};
}
unsigned char check_nearest(GibVector *pts_545_7755_12340,
                            GibVector *actual_546_7756_12341)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibInt n_547_7757_12343 = gib_vector_length(pts_545_7755_12340);
    GibInt n__1294_9838_10662_12345 =  maxInt(n_547_7757_12343, 0);
    GibInt tmp_164 = sizeof(GibInt);
    GibVector *vec_1295_9839_10663_12346 =
              gib_vector_alloc(n__1294_9838_10662_12345, tmp_164);
    GibVector *vec1_1296_9840_10664_12347 =
               generate_loop_3493_5973(vec_1295_9839_10663_12346, 0, n__1294_9838_10662_12345);
    GibInt fltAppE_11839_12354 = gib_vector_length(vec1_1296_9840_10664_12347);
    GibBoolGibIntProd tmp_struct_163 =
                       foldl_loop_3484_6035(0, fltAppE_11839_12354, (GibBoolGibIntProd) {true, 0}, vec1_1296_9840_10664_12347, pts_545_7755_12340, actual_546_7756_12341);
    GibBool pvrtmp_22279 = tmp_struct_163.field0;
    GibInt pvrtmp_22280 = tmp_struct_163.field1;
    unsigned char tailapp_17308 =  print_check(pvrtmp_22279);

    return tailapp_17308;
}
GibCursorGibVectorProd allNearest_seq(GibCursor end_r_15687,
                                      GibCursor tr_561_7763_12359,
                                      GibVector *ls_562_7764_12360)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibInt fltAppE_11840_12363 = gib_vector_length(ls_562_7764_12360);

    // gib_shadowstack_push(rstack, tr_561_7763_12359, end_r_15687, Stk, KdTree_T);

    GibInt n__1294_9922_13291_13956 =  maxInt(fltAppE_11840_12363, 0);

    // frame = gib_shadowstack_pop(rstack);
    // tr_561_7763_12359 = frame->ptr;
    // end_r_15687 = frame->endptr;

    GibInt tmp_166 = sizeof(GibFloatGibFloatGibFloatProd);
    GibVector *vec_1295_9923_13292_13957 =
              gib_vector_alloc(n__1294_9922_13291_13956, tmp_166);
    GibCursorGibVectorProd tmp_struct_165 =
                            generate_loop_3495_5986(end_r_15687, vec_1295_9923_13292_13957, 0, n__1294_9922_13291_13956, ls_562_7764_12360, tr_561_7763_12359);
    GibCursor pvrtmp_22281 = tmp_struct_165.field0;
    GibVector *pvrtmp_22282 = tmp_struct_165.field1;

    return (GibCursorGibVectorProd) {pvrtmp_22281, pvrtmp_22282};
}
GibCursorGibCursorProd check_buildquadtree(GibCursor end_r_15689,
                                           GibVector *mpts_567_7767_12364,
                                           GibCursor bht_568_7768_12365)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    gib_shadowstack_push(rstack, bht_568_7768_12365, end_r_15689, Stk,
                         BH_Tree_T);

    GibFloat expected_569_7769_12366 =  sum_mass_points(mpts_567_7767_12364);

    frame = gib_shadowstack_pop(rstack);
    bht_568_7768_12365 = frame->ptr;
    end_r_15689 = frame->endptr;
    gib_shadowstack_push(rstack, bht_568_7768_12365, end_r_15689, Stk,
                         BH_Tree_T);

    GibCursorGibCursorGibFloatProd tmp_struct_167 =
                                    sumQtree(end_r_15689, bht_568_7768_12365);
    GibCursor pvrtmp_22283 = tmp_struct_167.field0;
    GibCursor pvrtmp_22284 = tmp_struct_167.field1;
    GibFloat pvrtmp_22285 = tmp_struct_167.field2;

    frame = gib_shadowstack_pop(rstack);
    bht_568_7768_12365 = frame->ptr;
    end_r_15689 = frame->endptr;
    gib_shadowstack_push(rstack, bht_568_7768_12365, end_r_15689, Stk,
                         BH_Tree_T);

    GibCursorGibCursorGibIntProd tmp_struct_168 =
                                  countLeavesQtree(end_r_15689, bht_568_7768_12365);
    GibCursor pvrtmp_22286 = tmp_struct_168.field0;
    GibCursor pvrtmp_22287 = tmp_struct_168.field1;
    GibInt pvrtmp_22288 = tmp_struct_168.field2;

    frame = gib_shadowstack_pop(rstack);
    bht_568_7768_12365 = frame->ptr;
    end_r_15689 = frame->endptr;

    GibCursorGibIntProd tmp_struct_169 =
                         getTotalPoints_qtree(end_r_15689, bht_568_7768_12365);
    GibCursor pvrtmp_22289 = tmp_struct_169.field0;
    GibInt pvrtmp_22290 = tmp_struct_169.field1;
    unsigned char wildcard__475_573_7773_12370 = gib_print_symbol(21852);
    unsigned char wildcard__473_574_7774_12371 = printf("%.2f",
                                                        expected_569_7769_12366);
    unsigned char wildcard__471_575_7775_12372 = gib_print_symbol(21856);
    unsigned char wildcard__469_576_7776_12373 = gib_print_symbol(21851);
    unsigned char wildcard__467_577_7777_12374 = printf("%.2f", pvrtmp_22285);
    unsigned char wildcard__465_578_7778_12375 = gib_print_symbol(21877);
    unsigned char wildcard__463_579_7779_12376 = gib_print_symbol(21855);
    unsigned char wildcard__461_580_7780_12377 = printf("%ld", pvrtmp_22288);
    unsigned char wildcard__459_581_7781_12378 = gib_print_symbol(21856);
    unsigned char wildcard__457_582_7782_12379 = printf("%ld", pvrtmp_22290);
    unsigned char wildcard__455_583_7783_12380 = gib_print_symbol(21877);
    GibFloat fltAppE_11843_12381 = expected_569_7769_12366 - pvrtmp_22285;
    GibFloat fltPrm_11842_12382 =  float_abs(fltAppE_11843_12381);
    GibBool fltAppE_11841_12383 = fltPrm_11842_12382 < 1.0e-2;
    unsigned char tailapp_17311 =  print_check(fltAppE_11841_12383);

    return (GibCursorGibCursorProd) {pvrtmp_22289, pvrtmp_22287};
}
GibCursorGibCursorGibCursorProd buildQtree_seq(GibCursor end_r_15691,
                                               GibCursor loc_15690,
                                               GibFloatGibFloatGibFloatGibFloatProd box_584_7784_12384,
                                               GibVector *mpts_585_7785_12385)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_15690 + 58 > end_r_15691) {
        gib_grow_region(&loc_15690, &end_r_15691);
    }

    GibInt len_586_7786_12387 = gib_vector_length(mpts_585_7785_12385);
    GibBool fltIf_11844_12393 = len_586_7786_12387 == 0;

    if (fltIf_11844_12393) {
        *(GibPackedTag *) loc_15690 = 0;

        GibCursor writetag_19011 = loc_15690 + 1;
        GibCursor after_tag_19012 = loc_15690 + 1;

        return (GibCursorGibCursorGibCursorProd) {end_r_15691, loc_15690,
                                                  after_tag_19012};
    } else {
        GibBool fltIf_11845_12394 = len_586_7786_12387 == 1;

        if (fltIf_11845_12394) {
            gib_shadowstack_push(wstack, loc_15690, end_r_15691, Stk,
                                 BH_Tree_T);

            GibFloatGibFloatGibFloatProd tmp_struct_170 =
                                          calcCentroid_seq(mpts_585_7785_12385);
            GibFloat pvrtmp_22295 = tmp_struct_170.field0;
            GibFloat pvrtmp_22296 = tmp_struct_170.field1;
            GibFloat pvrtmp_22297 = tmp_struct_170.field2;

            frame = gib_shadowstack_pop(wstack);
            loc_15690 = frame->ptr;
            end_r_15691 = frame->endptr;
            *(GibPackedTag *) loc_15690 = 1;

            GibCursor writetag_19018 = loc_15690 + 1;
            GibCursor after_tag_19019 = loc_15690 + 1;

            *(GibFloat *) after_tag_19019 = pvrtmp_22295;

            GibCursor writecur_19023 = after_tag_19019 + sizeof(GibFloat);

            *(GibFloat *) writecur_19023 = pvrtmp_22296;

            GibCursor writecur_19024 = writecur_19023 + sizeof(GibFloat);

            *(GibFloat *) writecur_19024 = pvrtmp_22297;

            GibCursor writecur_19025 = writecur_19024 + sizeof(GibFloat);

            return (GibCursorGibCursorGibCursorProd) {end_r_15691, loc_15690,
                                                      writecur_19025};
        } else {
            gib_shadowstack_push(wstack, loc_15690, end_r_15691, Stk,
                                 BH_Tree_T);

            GibFloatGibFloatGibFloatProd tmp_struct_171 =
                                          calcCentroid_seq(mpts_585_7785_12385);
            GibFloat pvrtmp_22302 = tmp_struct_171.field0;
            GibFloat pvrtmp_22303 = tmp_struct_171.field1;
            GibFloat pvrtmp_22304 = tmp_struct_171.field2;

            frame = gib_shadowstack_pop(wstack);
            loc_15690 = frame->ptr;
            end_r_15691 = frame->endptr;

            GibFloat fltPrm_11846_12400 = box_584_7784_12384.field0 +
                     box_584_7784_12384.field2;
            GibFloat midx_597_7797_12401 = fltPrm_11846_12400 / 2.0;
            GibFloat fltPrm_11847_12402 = box_584_7784_12384.field1 +
                     box_584_7784_12384.field3;
            GibFloat midy_598_7798_12403 = fltPrm_11847_12402 / 2.0;

            gib_shadowstack_push(wstack, loc_15690, end_r_15691, Stk,
                                 BH_Tree_T);

            GibVector *p1_603_7803_12408 =
                       masspointsInBox_seq((GibFloatGibFloatGibFloatGibFloatProd) {box_584_7784_12384.field0, box_584_7784_12384.field1, midx_597_7797_12401, midy_598_7798_12403}, mpts_585_7785_12385);

            frame = gib_shadowstack_pop(wstack);
            loc_15690 = frame->ptr;
            end_r_15691 = frame->endptr;

            GibCursor loc_16003 = loc_15690 + 49;

            *(GibPackedTag *) loc_15690 = 3;

            GibCursor writetag_19044 = loc_15690 + 1;

            gib_shadowstack_push(rstack, loc_15690, end_r_15691, Stk,
                                 BH_Tree_T);

            GibCursorGibCursorGibCursorProd tmp_struct_172 =
                                             buildQtree_seq(end_r_15691, loc_16003, (GibFloatGibFloatGibFloatGibFloatProd) {box_584_7784_12384.field0, box_584_7784_12384.field1, midx_597_7797_12401, midy_598_7798_12403}, p1_603_7803_12408);
            GibCursor pvrtmp_22329 = tmp_struct_172.field0;
            GibCursor pvrtmp_22330 = tmp_struct_172.field1;
            GibCursor pvrtmp_22331 = tmp_struct_172.field2;

            frame = gib_shadowstack_pop(rstack);
            loc_15690 = frame->ptr;
            end_r_15691 = frame->endptr;
            gib_shadowstack_push(rstack, loc_15690, pvrtmp_22329, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, loc_16003, pvrtmp_22329, Stk,
                                 BH_Tree_T);

            GibVector *p2_605_7805_12410 =
                       masspointsInBox_seq((GibFloatGibFloatGibFloatGibFloatProd) {box_584_7784_12384.field0, midy_598_7798_12403, midx_597_7797_12401, box_584_7784_12384.field3}, mpts_585_7785_12385);

            frame = gib_shadowstack_pop(rstack);
            loc_16003 = frame->ptr;
            pvrtmp_22329 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_15690 = frame->ptr;
            pvrtmp_22329 = frame->endptr;
            gib_shadowstack_push(rstack, loc_15690, pvrtmp_22329, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, loc_16003, pvrtmp_22329, Stk,
                                 BH_Tree_T);

            GibCursorGibCursorGibCursorProd tmp_struct_173 =
                                             buildQtree_seq(pvrtmp_22329, pvrtmp_22331, (GibFloatGibFloatGibFloatGibFloatProd) {box_584_7784_12384.field0, midy_598_7798_12403, midx_597_7797_12401, box_584_7784_12384.field3}, p2_605_7805_12410);
            GibCursor pvrtmp_22344 = tmp_struct_173.field0;
            GibCursor pvrtmp_22345 = tmp_struct_173.field1;
            GibCursor pvrtmp_22346 = tmp_struct_173.field2;

            frame = gib_shadowstack_pop(rstack);
            loc_16003 = frame->ptr;
            pvrtmp_22329 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_15690 = frame->ptr;
            pvrtmp_22329 = frame->endptr;
            gib_shadowstack_push(rstack, loc_15690, pvrtmp_22344, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, pvrtmp_22331, pvrtmp_22344, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, loc_16003, pvrtmp_22344, Stk,
                                 BH_Tree_T);

            GibVector *p3_607_7807_12412 =
                       masspointsInBox_seq((GibFloatGibFloatGibFloatGibFloatProd) {midx_597_7797_12401, midy_598_7798_12403, box_584_7784_12384.field2, box_584_7784_12384.field3}, mpts_585_7785_12385);

            frame = gib_shadowstack_pop(rstack);
            loc_16003 = frame->ptr;
            pvrtmp_22344 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_22331 = frame->ptr;
            pvrtmp_22344 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_15690 = frame->ptr;
            pvrtmp_22344 = frame->endptr;
            gib_shadowstack_push(rstack, loc_15690, pvrtmp_22344, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, pvrtmp_22331, pvrtmp_22344, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, loc_16003, pvrtmp_22344, Stk,
                                 BH_Tree_T);

            GibCursorGibCursorGibCursorProd tmp_struct_174 =
                                             buildQtree_seq(pvrtmp_22344, pvrtmp_22346, (GibFloatGibFloatGibFloatGibFloatProd) {midx_597_7797_12401, midy_598_7798_12403, box_584_7784_12384.field2, box_584_7784_12384.field3}, p3_607_7807_12412);
            GibCursor pvrtmp_22359 = tmp_struct_174.field0;
            GibCursor pvrtmp_22360 = tmp_struct_174.field1;
            GibCursor pvrtmp_22361 = tmp_struct_174.field2;

            frame = gib_shadowstack_pop(rstack);
            loc_16003 = frame->ptr;
            pvrtmp_22344 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_22331 = frame->ptr;
            pvrtmp_22344 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_15690 = frame->ptr;
            pvrtmp_22344 = frame->endptr;
            gib_shadowstack_push(rstack, loc_15690, pvrtmp_22359, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, pvrtmp_22346, pvrtmp_22359, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, pvrtmp_22331, pvrtmp_22359, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, loc_16003, pvrtmp_22359, Stk,
                                 BH_Tree_T);

            GibVector *p4_609_7809_12414 =
                       masspointsInBox_seq((GibFloatGibFloatGibFloatGibFloatProd) {midx_597_7797_12401, box_584_7784_12384.field1, box_584_7784_12384.field2, midy_598_7798_12403}, mpts_585_7785_12385);

            frame = gib_shadowstack_pop(rstack);
            loc_16003 = frame->ptr;
            pvrtmp_22359 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_22331 = frame->ptr;
            pvrtmp_22359 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_22346 = frame->ptr;
            pvrtmp_22359 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_15690 = frame->ptr;
            pvrtmp_22359 = frame->endptr;
            gib_shadowstack_push(rstack, loc_15690, pvrtmp_22359, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, pvrtmp_22346, pvrtmp_22359, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, pvrtmp_22331, pvrtmp_22359, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, loc_16003, pvrtmp_22359, Stk,
                                 BH_Tree_T);

            GibCursorGibCursorGibCursorProd tmp_struct_175 =
                                             buildQtree_seq(pvrtmp_22359, pvrtmp_22361, (GibFloatGibFloatGibFloatGibFloatProd) {midx_597_7797_12401, box_584_7784_12384.field1, box_584_7784_12384.field2, midy_598_7798_12403}, p4_609_7809_12414);
            GibCursor pvrtmp_22374 = tmp_struct_175.field0;
            GibCursor pvrtmp_22375 = tmp_struct_175.field1;
            GibCursor pvrtmp_22376 = tmp_struct_175.field2;

            frame = gib_shadowstack_pop(rstack);
            loc_16003 = frame->ptr;
            pvrtmp_22359 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_22331 = frame->ptr;
            pvrtmp_22359 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_22346 = frame->ptr;
            pvrtmp_22359 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_15690 = frame->ptr;
            pvrtmp_22359 = frame->endptr;
            gib_shadowstack_push(rstack, loc_15690, pvrtmp_22374, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, pvrtmp_22361, pvrtmp_22374, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, pvrtmp_22346, pvrtmp_22374, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, pvrtmp_22331, pvrtmp_22374, Stk,
                                 BH_Tree_T);

            GibCursorGibIntProd tmp_struct_176 =
                                 getTotalPoints_qtree(pvrtmp_22374, pvrtmp_22330);
            GibCursor pvrtmp_22381 = tmp_struct_176.field0;
            GibInt pvrtmp_22382 = tmp_struct_176.field1;

            frame = gib_shadowstack_pop(rstack);
            pvrtmp_22331 = frame->ptr;
            pvrtmp_22374 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_22346 = frame->ptr;
            pvrtmp_22374 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_22361 = frame->ptr;
            pvrtmp_22374 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_15690 = frame->ptr;
            pvrtmp_22374 = frame->endptr;
            gib_shadowstack_push(rstack, loc_15690, pvrtmp_22374, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, pvrtmp_22361, pvrtmp_22381, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, pvrtmp_22346, pvrtmp_22381, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, pvrtmp_22331, pvrtmp_22381, Stk,
                                 BH_Tree_T);

            GibCursorGibIntProd tmp_struct_177 =
                                 getTotalPoints_qtree(pvrtmp_22381, pvrtmp_22345);
            GibCursor pvrtmp_22383 = tmp_struct_177.field0;
            GibInt pvrtmp_22384 = tmp_struct_177.field1;

            frame = gib_shadowstack_pop(rstack);
            pvrtmp_22331 = frame->ptr;
            pvrtmp_22381 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_22346 = frame->ptr;
            pvrtmp_22381 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_22361 = frame->ptr;
            pvrtmp_22381 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_15690 = frame->ptr;
            pvrtmp_22374 = frame->endptr;

            GibInt fltPrm_11849_12418 = pvrtmp_22382 + pvrtmp_22384;

            gib_shadowstack_push(rstack, loc_15690, pvrtmp_22374, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, pvrtmp_22361, pvrtmp_22383, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, pvrtmp_22346, pvrtmp_22383, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, pvrtmp_22331, pvrtmp_22381, Stk,
                                 BH_Tree_T);

            GibCursorGibIntProd tmp_struct_178 =
                                 getTotalPoints_qtree(pvrtmp_22383, pvrtmp_22360);
            GibCursor pvrtmp_22385 = tmp_struct_178.field0;
            GibInt pvrtmp_22386 = tmp_struct_178.field1;

            frame = gib_shadowstack_pop(rstack);
            pvrtmp_22331 = frame->ptr;
            pvrtmp_22381 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_22346 = frame->ptr;
            pvrtmp_22383 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_22361 = frame->ptr;
            pvrtmp_22383 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_15690 = frame->ptr;
            pvrtmp_22374 = frame->endptr;

            GibInt fltPrm_11848_12420 = fltPrm_11849_12418 + pvrtmp_22386;

            gib_shadowstack_push(rstack, loc_15690, pvrtmp_22374, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, pvrtmp_22361, pvrtmp_22385, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, pvrtmp_22346, pvrtmp_22383, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, pvrtmp_22331, pvrtmp_22381, Stk,
                                 BH_Tree_T);

            GibCursorGibIntProd tmp_struct_179 =
                                 getTotalPoints_qtree(pvrtmp_22385, pvrtmp_22375);
            GibCursor pvrtmp_22387 = tmp_struct_179.field0;
            GibInt pvrtmp_22388 = tmp_struct_179.field1;

            frame = gib_shadowstack_pop(rstack);
            pvrtmp_22331 = frame->ptr;
            pvrtmp_22381 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_22346 = frame->ptr;
            pvrtmp_22383 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_22361 = frame->ptr;
            pvrtmp_22385 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_15690 = frame->ptr;
            pvrtmp_22374 = frame->endptr;

            GibInt total_points_611_7811_12422 = fltPrm_11848_12420 +
                   pvrtmp_22388;
            GibFloat fltAppE_11854_12429 = box_584_7784_12384.field2 -
                     box_584_7784_12384.field0;
            GibFloat fltAppE_11855_12430 = box_584_7784_12384.field3 -
                     box_584_7784_12384.field1;

            gib_shadowstack_push(rstack, loc_15690, pvrtmp_22374, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, pvrtmp_22361, pvrtmp_22385, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, pvrtmp_22346, pvrtmp_22383, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, pvrtmp_22331, pvrtmp_22381, Stk,
                                 BH_Tree_T);

            GibFloat width_612_7812_12431 =
                      maxFloat(fltAppE_11854_12429, fltAppE_11855_12430);

            frame = gib_shadowstack_pop(rstack);
            pvrtmp_22331 = frame->ptr;
            pvrtmp_22381 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_22346 = frame->ptr;
            pvrtmp_22383 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_22361 = frame->ptr;
            pvrtmp_22385 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_15690 = frame->ptr;
            pvrtmp_22374 = frame->endptr;

            uint16_t offset_182 = pvrtmp_22329 - pvrtmp_22331;
            uintptr_t ran_15528 = GIB_STORE_TAG(pvrtmp_22331, offset_182);
            uint16_t offset_181 = pvrtmp_22344 - pvrtmp_22346;
            uintptr_t ran_15529 = GIB_STORE_TAG(pvrtmp_22346, offset_181);
            uint16_t offset_180 = pvrtmp_22359 - pvrtmp_22361;
            uintptr_t ran_15530 = GIB_STORE_TAG(pvrtmp_22361, offset_180);
            GibCursor after_tag_19045 = loc_15690 + 1;

            *(uintptr_t *) after_tag_19045 = ran_15528;

            GibCursor writecur_19049 = after_tag_19045 + 8;

            *(uintptr_t *) writecur_19049 = ran_15529;

            GibCursor writecur_19050 = writecur_19049 + 8;

            *(uintptr_t *) writecur_19050 = ran_15530;

            GibCursor writecur_19051 = writecur_19050 + 8;

            *(GibFloat *) writecur_19051 = pvrtmp_22302;

            GibCursor writecur_19052 = writecur_19051 + sizeof(GibFloat);

            *(GibFloat *) writecur_19052 = pvrtmp_22303;

            GibCursor writecur_19053 = writecur_19052 + sizeof(GibFloat);

            *(GibFloat *) writecur_19053 = pvrtmp_22304;

            GibCursor writecur_19054 = writecur_19053 + sizeof(GibFloat);

            *(GibInt *) writecur_19054 = total_points_611_7811_12422;

            GibCursor writecur_19055 = writecur_19054 + sizeof(GibInt);

            *(GibFloat *) writecur_19055 = width_612_7812_12431;

            GibCursor writecur_19056 = writecur_19055 + sizeof(GibFloat);

            return (GibCursorGibCursorGibCursorProd) {pvrtmp_22385, loc_15690,
                                                      pvrtmp_22376};
        }
    }
}
GibFloat maxFloat(GibFloat a_622_7817_12436, GibFloat b_623_7818_12437)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_11856_12438 = a_622_7817_12436 > b_623_7818_12437;

    if (fltIf_11856_12438) {
        return a_622_7817_12436;
    } else {
        return b_623_7818_12437;
    }
}
GibFloat minFloat(GibFloat a_624_7819_12439, GibFloat b_625_7820_12440)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_11857_12441 = a_624_7819_12439 < b_625_7820_12440;

    if (fltIf_11857_12441) {
        return a_624_7819_12439;
    } else {
        return b_625_7820_12440;
    }
}
GibCursorGibVectorProd oneStep_seq(GibCursor end_r_15693,
                                   GibCursor bht_665_7855_12442,
                                   GibVector *mpts_666_7856_12443,
                                   GibVector *ps_667_7857_12444)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibCursor pvrtmp_22395;
    GibVector *pvrtmp_22396;
    GibVector *times_191 = gib_vector_alloc(gib_get_iters_param(),
                                            sizeof(double));
    struct timespec begin_pvrtmp_22395;
    struct timespec end_pvrtmp_22395;

    for (long long iters_pvrtmp_22395 = 0; iters_pvrtmp_22395 <
         gib_get_iters_param(); iters_pvrtmp_22395++) {
        if (iters_pvrtmp_22395 != gib_get_iters_param() - 1)
            gib_list_bumpalloc_save_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_22395);

        GibInt n_1291_9087_10689_12446 = gib_vector_length(ps_667_7857_12444);

        // gib_shadowstack_push(rstack, bht_665_7855_12442, end_r_15693, Stk,
        //                      BH_Tree_T);

        GibInt n__1294_9091_10693_12450 =  maxInt(n_1291_9087_10689_12446, 0);

        // frame = gib_shadowstack_pop(rstack);
        // bht_665_7855_12442 = frame->ptr;
        // end_r_15693 = frame->endptr;

        GibInt tmp_187 = sizeof(GibFloatGibFloatGibFloatGibFloatGibFloatProd);
        GibVector *vec_1295_9092_10694_12451 =
                  gib_vector_alloc(n__1294_9091_10693_12450, tmp_187);
        GibCursorGibVectorProd tmp_struct_186 =
                                generate_loop_3496_5968(end_r_15693, vec_1295_9092_10694_12451, 0, n__1294_9091_10693_12450, bht_665_7855_12442, mpts_666_7856_12443, ps_667_7857_12444);
        GibCursor pvrtmp_22393 = tmp_struct_186.field0;
        GibVector *pvrtmp_22394 = tmp_struct_186.field1;

        pvrtmp_22395 = pvrtmp_22393;
        pvrtmp_22396 = pvrtmp_22394;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_22395);
        if (iters_pvrtmp_22395 != gib_get_iters_param() - 1)
            gib_list_bumpalloc_restore_state();

        double itertime_188 = gib_difftimespecs(&begin_pvrtmp_22395,
                                                &end_pvrtmp_22395);

        printf("itertime: %lf\n", itertime_188);
        gib_vector_inplace_update(times_191, iters_pvrtmp_22395, &itertime_188);
    }
    gib_vector_inplace_sort(times_191, gib_compare_doubles);

    double *tmp_192 = (double *) gib_vector_nth(times_191,
                                                gib_get_iters_param() / 2);
    double selftimed_190 = *tmp_192;
    double batchtime_189 = gib_sum_timing_array(times_191);

    gib_print_timing_array(times_191);
    gib_vector_free(times_191);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_189);
    printf("SELFTIMED: %e\n", selftimed_190);
    return (GibCursorGibVectorProd) {end_r_15693, pvrtmp_22396};
}
GibCursorGibCursorProd check_coins(GibCursor end_r_15695,
                                   GibInt amt_682_7864_12454,
                                   GibCursor tr_683_7865_12455)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibCursorGibCursorGibIntProd tmp_struct_193 =
                                  lenA(end_r_15695, tr_683_7865_12455);
    GibCursor pvrtmp_22399 = tmp_struct_193.field0;
    GibCursor pvrtmp_22400 = tmp_struct_193.field1;
    GibInt pvrtmp_22401 = tmp_struct_193.field2;
    GibBool fltIf_11858_12457 = amt_682_7864_12454 == 777;

    if (fltIf_11858_12457) {
        GibBool fltAppE_11859_12458 = pvrtmp_22401 == 140899;
        unsigned char tailapp_17316 =  print_check(fltAppE_11859_12458);

        return (GibCursorGibCursorProd) {pvrtmp_22399, pvrtmp_22400};
    } else {
        GibBool fltIf_11860_12459 = amt_682_7864_12454 == 999;

        if (fltIf_11860_12459) {
            GibBool fltAppE_11861_12460 = pvrtmp_22401 == 329565;
            unsigned char tailapp_17317 =  print_check(fltAppE_11861_12460);

            return (GibCursorGibCursorProd) {pvrtmp_22399, pvrtmp_22400};
        } else {
            unsigned char wildcard__94_685_7867_12461 = printf("%ld",
                                                               pvrtmp_22401);
            unsigned char wildcard__92_686_7868_12462 = gib_print_symbol(21877);
            unsigned char tailapp_17318 =  print_check(true);

            return (GibCursorGibCursorProd) {pvrtmp_22399, pvrtmp_22400};
        }
    }
}
GibCursorGibCursorGibCursorProd payA_seq(GibCursor end_r_15697,
                                         GibCursor loc_15696,
                                         GibInt amt_687_7869_12464,
                                         GibList *coins_688_7870_12465)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_15696 + 18 > end_r_15697) {
        gib_grow_region(&loc_15696, &end_r_15697);
    }

    GibBool fltIf_11863_12466 = amt_687_7869_12464 == 0;

    if (fltIf_11863_12466) {
        *(GibPackedTag *) loc_15696 = 1;

        GibCursor writetag_19071 = loc_15696 + 1;
        GibCursor after_tag_19072 = loc_15696 + 1;

        *(GibInt *) after_tag_19072 = 1;

        GibCursor writecur_19076 = after_tag_19072 + sizeof(GibInt);

        return (GibCursorGibCursorGibCursorProd) {end_r_15697, loc_15696,
                                                  writecur_19076};
    } else {
        GibBool fltIf_11864_12467 = gib_list_is_empty(coins_688_7870_12465);

        if (fltIf_11864_12467) {
            *(GibPackedTag *) loc_15696 = 0;

            GibCursor writetag_19079 = loc_15696 + 1;
            GibCursor after_tag_19080 = loc_15696 + 1;

            *(GibInt *) after_tag_19080 = 0;

            GibCursor writecur_19084 = after_tag_19080 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorProd) {end_r_15697, loc_15696,
                                                      writecur_19084};
        } else {
            GibIntGibIntProd *tmp_197;

            tmp_197 = (GibIntGibIntProd *) gib_list_head(coins_688_7870_12465);

            GibIntGibIntProd tup_40_689_7871_12468 = *tmp_197;
            GibList *coins_rst_692_7874_12471 =
                    gib_list_tail(coins_688_7870_12465);
            GibBool fltIf_11865_12472 = tup_40_689_7871_12468.field0 >
                    amt_687_7869_12464;

            if (fltIf_11865_12472) {
                GibCursorGibCursorGibCursorProd tmp_struct_194 =
                                                 payA_seq(end_r_15697, loc_15696, amt_687_7869_12464, coins_rst_692_7874_12471);
                GibCursor pvrtmp_22410 = tmp_struct_194.field0;
                GibCursor pvrtmp_22411 = tmp_struct_194.field1;
                GibCursor pvrtmp_22412 = tmp_struct_194.field2;

                return (GibCursorGibCursorGibCursorProd) {pvrtmp_22410,
                                                          pvrtmp_22411,
                                                          pvrtmp_22412};
            } else {
                GibBool fltIf_11866_12476 = tup_40_689_7871_12468.field1 == 1;
                GibList *coins1_693_7875_12479;

                if (fltIf_11866_12476) {
                    GibList *flt_22419 =
                            gib_list_copy(coins_rst_692_7874_12471);

                    coins1_693_7875_12479 = flt_22419;
                } else {
                    GibInt fltPrd_11868_12477 = tup_40_689_7871_12468.field1 -
                           1;
                    GibList *flt_22422 =
                            gib_list_cons(&(GibIntGibIntProd) {tup_40_689_7871_12468.field0,
                                                               fltPrd_11868_12477},
                                          coins_rst_692_7874_12471);

                    coins1_693_7875_12479 = flt_22422;
                }

                GibInt fltAppE_11869_12480 = amt_687_7869_12464 -
                       tup_40_689_7871_12468.field0;
                GibCursor loc_16037 = loc_15696 + 1;

                *(GibPackedTag *) loc_15696 = 2;

                GibCursor writetag_19093 = loc_15696 + 1;

                gib_shadowstack_push(rstack, loc_15696, end_r_15697, Stk,
                                     AList_T);

                GibCursorGibCursorGibCursorProd tmp_struct_195 =
                                                 payA_seq(end_r_15697, loc_16037, fltAppE_11869_12480, coins1_693_7875_12479);
                GibCursor pvrtmp_22423 = tmp_struct_195.field0;
                GibCursor pvrtmp_22424 = tmp_struct_195.field1;
                GibCursor pvrtmp_22425 = tmp_struct_195.field2;

                frame = gib_shadowstack_pop(rstack);
                loc_15696 = frame->ptr;
                end_r_15697 = frame->endptr;
                gib_shadowstack_push(rstack, loc_15696, pvrtmp_22423, Stk,
                                     AList_T);

                GibCursorGibCursorGibCursorProd tmp_struct_196 =
                                                 payA_seq(pvrtmp_22423, pvrtmp_22425, amt_687_7869_12464, coins_rst_692_7874_12471);
                GibCursor pvrtmp_22430 = tmp_struct_196.field0;
                GibCursor pvrtmp_22431 = tmp_struct_196.field1;
                GibCursor pvrtmp_22432 = tmp_struct_196.field2;

                frame = gib_shadowstack_pop(rstack);
                loc_15696 = frame->ptr;
                pvrtmp_22423 = frame->endptr;
                gib_list_free(coins1_693_7875_12479);

                GibCursor after_tag_19094 = loc_15696 + 1;

                return (GibCursorGibCursorGibCursorProd) {pvrtmp_22430,
                                                          loc_15696,
                                                          pvrtmp_22432};
            }
        }
    }
}
GibCursorGibCursorGibIntProd sumExp(GibCursor end_r_15699,
                                    GibCursor exp_710_7892_12484)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_22441 = *(GibPackedTag *) exp_710_7892_12484;
    GibCursor tmpcur_22442 = exp_710_7892_12484 + 1;


  switch_22463:
    ;
    switch (tmpval_22441) {

      case 0:
        {
            GibInt tmpval_22443 = *(GibInt *) tmpcur_22442;
            GibCursor tmpcur_22444 = tmpcur_22442 + sizeof(GibInt);
            GibCursor jump_17323 = tmpcur_22442 + 8;

            return (GibCursorGibCursorGibIntProd) {end_r_15699, jump_17323,
                                                   tmpval_22443};
            break;
        }

      case 3:
        {
            GibCursorGibCursorGibIntProd tmp_struct_201 =
                                          sumExp(end_r_15699, tmpcur_22442);
            GibCursor pvrtmp_22445 = tmp_struct_201.field0;
            GibCursor pvrtmp_22446 = tmp_struct_201.field1;
            GibInt pvrtmp_22447 = tmp_struct_201.field2;
            GibCursorGibCursorGibIntProd tmp_struct_202 =
                                          sumExp(pvrtmp_22445, pvrtmp_22446);
            GibCursor pvrtmp_22448 = tmp_struct_202.field0;
            GibCursor pvrtmp_22449 = tmp_struct_202.field1;
            GibInt pvrtmp_22450 = tmp_struct_202.field2;
            GibInt tailprim_17326 = pvrtmp_22447 + pvrtmp_22450;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_22448, pvrtmp_22449,
                                                   tailprim_17326};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_204 = *(uintptr_t *) tmpcur_22442;
            GibCursor tmpcur_22451 = GIB_UNTAG(tagged_tmpcur_204);
            GibCursor tmpaftercur_22452 = tmpcur_22442 + 8;
            uint16_t tmptag_22453 = GIB_GET_TAG(tagged_tmpcur_204);
            GibCursor end_from_tagged_indr_17982 = tmpcur_22451 + tmptag_22453;
            GibCursor jump_17984 = tmpcur_22442 + 8;
            GibCursorGibCursorGibIntProd tmp_struct_203 =
                                          sumExp(end_from_tagged_indr_17982, tmpcur_22451);
            GibCursor pvrtmp_22454 = tmp_struct_203.field0;
            GibCursor pvrtmp_22455 = tmp_struct_203.field1;
            GibInt pvrtmp_22456 = tmp_struct_203.field2;

            return (GibCursorGibCursorGibIntProd) {end_r_15699, jump_17984,
                                                   pvrtmp_22456};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_206 = *(uintptr_t *) tmpcur_22442;
            GibCursor tmpcur_22457 = GIB_UNTAG(tagged_tmpcur_206);
            GibCursor tmpaftercur_22458 = tmpcur_22442 + 8;
            uint16_t tmptag_22459 = GIB_GET_TAG(tagged_tmpcur_206);
            GibCursor end_from_tagged_indr_17982 = tmpcur_22457 + tmptag_22459;
            GibCursorGibCursorGibIntProd tmp_struct_205 =
                                          sumExp(end_from_tagged_indr_17982, tmpcur_22457);
            GibCursor pvrtmp_22460 = tmp_struct_205.field0;
            GibCursor pvrtmp_22461 = tmp_struct_205.field1;
            GibInt pvrtmp_22462 = tmp_struct_205.field2;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_22460, pvrtmp_22461,
                                                   pvrtmp_22462};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_22441");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd foldConstants2(GibCursor end_r_15702,
                                                                 GibCursor end_r_15703,
                                                                 GibCursor loc_15701,
                                                                 GibCursor exp_714_7896_12490)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_15701 + 18 > end_r_15703) {
        gib_grow_region(&loc_15701, &end_r_15703);
    }

    GibPackedTag tmpval_22464 = *(GibPackedTag *) exp_714_7896_12490;
    GibCursor tmpcur_22465 = exp_714_7896_12490 + 1;


  switch_22561:
    ;
    switch (tmpval_22464) {

      case 0:
        {
            GibInt tmpval_22466 = *(GibInt *) tmpcur_22465;
            GibCursor tmpcur_22467 = tmpcur_22465 + sizeof(GibInt);
            GibCursor jump_17327 = tmpcur_22465 + 8;

            *(GibPackedTag *) loc_15701 = 0;

            GibCursor writetag_19120 = loc_15701 + 1;
            GibCursor after_tag_19121 = loc_15701 + 1;

            *(GibInt *) after_tag_19121 = tmpval_22466;

            GibCursor writecur_19125 = after_tag_19121 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15702,
                                                                        end_r_15703,
                                                                        jump_17327,
                                                                        loc_15701,
                                                                        writecur_19125};
            break;
        }

      case 1:
        {
            GibCursor jump_17329 = exp_714_7896_12490 + 1;

            *(GibPackedTag *) loc_15701 = 1;

            GibCursor writetag_19129 = loc_15701 + 1;
            GibCursor after_tag_19130 = loc_15701 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15702,
                                                                        end_r_15703,
                                                                        jump_17329,
                                                                        loc_15701,
                                                                        after_tag_19130};
            break;
        }

      case 2:
        {
            GibCursor jump_17331 = exp_714_7896_12490 + 1;

            *(GibPackedTag *) loc_15701 = 2;

            GibCursor writetag_19137 = loc_15701 + 1;
            GibCursor after_tag_19138 = loc_15701 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15702,
                                                                        end_r_15703,
                                                                        jump_17331,
                                                                        loc_15701,
                                                                        after_tag_19138};
            break;
        }

      case 3:
        {
            // gib_shadowstack_push(rstack, tmpcur_22465, end_r_15702, Stk, Exp_T);
            // gib_shadowstack_push(wstack, loc_15701, end_r_15703, Stk, Exp_T);

            GibCursorGibFloatProd tmp_struct_207 =
                                   maybeLit(end_r_15702, tmpcur_22465);
            GibCursor pvrtmp_22480 = tmp_struct_207.field0;
            GibFloat pvrtmp_22481 = tmp_struct_207.field1;

            // frame = gib_shadowstack_pop(wstack);
            // loc_15701 = frame->ptr;
            // end_r_15703 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // tmpcur_22465 = frame->ptr;
            // end_r_15702 = frame->endptr;

            GibFloat fltPrm_11875_12496 = 0.0 - 3.14;
            GibFloat fltPrm_11874_12497 = pvrtmp_22481 - fltPrm_11875_12496;
            GibBool fltIf_11873_12498 = fltPrm_11874_12497 < 1.0e-2;
            GibBool fltIf_11872_12499;

            if (fltIf_11873_12498) {
                fltIf_11872_12499 = false;
            } else {
                fltIf_11872_12499 = true;
            }
            if (fltIf_11872_12499) {
                // gib_shadowstack_push(wstack, loc_15701, end_r_15703, Stk,
                //                      Exp_T);

                GibCursorGibCursorProd tmp_struct_208 =
                                        trav_exp(end_r_15702, tmpcur_22465);
                GibCursor pvrtmp_22484 = tmp_struct_208.field0;
                GibCursor pvrtmp_22485 = tmp_struct_208.field1;

                // frame = gib_shadowstack_pop(wstack);
                // loc_15701 = frame->ptr;
                // end_r_15703 = frame->endptr;
                // gib_shadowstack_push(rstack, pvrtmp_22485, pvrtmp_22484, Stk,
                //                      Exp_T);
                // gib_shadowstack_push(wstack, loc_15701, end_r_15703, Stk,
                //                      Exp_T);

                GibCursorGibFloatProd tmp_struct_209 =
                                       maybeLit(pvrtmp_22484, pvrtmp_22485);
                GibCursor pvrtmp_22486 = tmp_struct_209.field0;
                GibFloat pvrtmp_22487 = tmp_struct_209.field1;

                // frame = gib_shadowstack_pop(wstack);
                // loc_15701 = frame->ptr;
                // end_r_15703 = frame->endptr;
                // frame = gib_shadowstack_pop(rstack);
                // pvrtmp_22485 = frame->ptr;
                // pvrtmp_22484 = frame->endptr;

                GibFloat fltPrm_11879_12503 = 0.0 - 3.14;
                GibFloat fltPrm_11878_12504 = pvrtmp_22487 - fltPrm_11879_12503;
                GibBool fltIf_11877_12505 = fltPrm_11878_12504 < 1.0e-2;
                GibBool fltIf_11876_12506;

                if (fltIf_11877_12505) {
                    fltIf_11876_12506 = false;
                } else {
                    fltIf_11876_12506 = true;
                }
                if (fltIf_11876_12506) {
                    // gib_shadowstack_push(wstack, loc_15701, end_r_15703, Stk,
                    //                      Exp_T);

                    GibCursorGibCursorProd tmp_struct_210 =
                                            trav_exp(pvrtmp_22484, pvrtmp_22485);
                    GibCursor pvrtmp_22490 = tmp_struct_210.field0;
                    GibCursor pvrtmp_22491 = tmp_struct_210.field1;

                    // frame = gib_shadowstack_pop(wstack);
                    // loc_15701 = frame->ptr;
                    // end_r_15703 = frame->endptr;

                    GibInt fltPrm_11881_12508 = (GibInt) pvrtmp_22481;
                    GibInt fltPrm_11882_12509 = (GibInt) pvrtmp_22487;
                    GibInt fltPkd_11880_12510 = fltPrm_11881_12508 +
                           fltPrm_11882_12509;

                    *(GibPackedTag *) loc_15701 = 0;

                    GibCursor writetag_19153 = loc_15701 + 1;
                    GibCursor after_tag_19154 = loc_15701 + 1;

                    *(GibInt *) after_tag_19154 = fltPkd_11880_12510;

                    GibCursor writecur_19158 = after_tag_19154 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_22490,
                                                                                end_r_15703,
                                                                                pvrtmp_22491,
                                                                                loc_15701,
                                                                                writecur_19158};
                } else {
                    GibInt fltPkd_11883_12511 = (GibInt) pvrtmp_22481;
                    GibCursor loc_16078 = loc_15701 + 1;

                    *(GibPackedTag *) loc_15701 = 3;

                    GibCursor writetag_19172 = loc_15701 + 1;

                    *(GibPackedTag *) loc_16078 = 0;

                    GibCursor writetag_19161 = loc_16078 + 1;
                    GibCursor after_tag_19162 = loc_16078 + 1;

                    *(GibInt *) after_tag_19162 = fltPkd_11883_12511;

                    GibCursor writecur_19166 = after_tag_19162 + sizeof(GibInt);

                    // gib_shadowstack_push(rstack, loc_15701, end_r_15703, Stk,
                    //                      Exp_T);

                    GibCursorGibCursorGibCursorGibCursorGibCursorProd
                    tmp_struct_211 =
                     foldConstants2(pvrtmp_22484, end_r_15703, writecur_19166, pvrtmp_22485);
                    GibCursor pvrtmp_22498 = tmp_struct_211.field0;
                    GibCursor pvrtmp_22499 = tmp_struct_211.field1;
                    GibCursor pvrtmp_22500 = tmp_struct_211.field2;
                    GibCursor pvrtmp_22501 = tmp_struct_211.field3;
                    GibCursor pvrtmp_22502 = tmp_struct_211.field4;

                    // frame = gib_shadowstack_pop(rstack);
                    // loc_15701 = frame->ptr;
                    // end_r_15703 = frame->endptr;

                    GibCursor after_tag_19173 = loc_15701 + 1;

                    return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_22498,
                                                                                pvrtmp_22499,
                                                                                pvrtmp_22500,
                                                                                loc_15701,
                                                                                pvrtmp_22502};
                }
            } else {
                GibCursor loc_16088 = loc_15701 + 1;

                *(GibPackedTag *) loc_15701 = 3;

                GibCursor writetag_19188 = loc_15701 + 1;

                // gib_shadowstack_push(rstack, loc_15701, end_r_15703, Stk,
                //                      Exp_T);

                GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_212
                                                                  =
                                                                   foldConstants2(end_r_15702, end_r_15703, loc_16088, tmpcur_22465);
                GibCursor pvrtmp_22511 = tmp_struct_212.field0;
                GibCursor pvrtmp_22512 = tmp_struct_212.field1;
                GibCursor pvrtmp_22513 = tmp_struct_212.field2;
                GibCursor pvrtmp_22514 = tmp_struct_212.field3;
                GibCursor pvrtmp_22515 = tmp_struct_212.field4;

                // frame = gib_shadowstack_pop(rstack);
                // loc_15701 = frame->ptr;
                // end_r_15703 = frame->endptr;
                // gib_shadowstack_push(rstack, loc_15701, pvrtmp_22512, Stk,
                //                      Exp_T);

                GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_213
                                                                  =
                                                                   foldConstants2(pvrtmp_22511, pvrtmp_22512, pvrtmp_22515, pvrtmp_22513);
                GibCursor pvrtmp_22520 = tmp_struct_213.field0;
                GibCursor pvrtmp_22521 = tmp_struct_213.field1;
                GibCursor pvrtmp_22522 = tmp_struct_213.field2;
                GibCursor pvrtmp_22523 = tmp_struct_213.field3;
                GibCursor pvrtmp_22524 = tmp_struct_213.field4;

                // frame = gib_shadowstack_pop(rstack);
                // loc_15701 = frame->ptr;
                // pvrtmp_22512 = frame->endptr;

                GibCursor after_tag_19189 = loc_15701 + 1;

                return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_22520,
                                                                            pvrtmp_22521,
                                                                            pvrtmp_22522,
                                                                            loc_15701,
                                                                            pvrtmp_22524};
            }
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_215 = *(uintptr_t *) tmpcur_22465;
            GibCursor tmpcur_22533 = GIB_UNTAG(tagged_tmpcur_215);
            GibCursor tmpaftercur_22534 = tmpcur_22465 + 8;
            uint16_t tmptag_22535 = GIB_GET_TAG(tagged_tmpcur_215);
            GibCursor end_from_tagged_indr_17988 = tmpcur_22533 + tmptag_22535;
            GibCursor jump_17990 = tmpcur_22465 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_214 =
                                                               foldConstants2(end_from_tagged_indr_17988, end_r_15703, loc_15701, tmpcur_22533);
            GibCursor pvrtmp_22536 = tmp_struct_214.field0;
            GibCursor pvrtmp_22537 = tmp_struct_214.field1;
            GibCursor pvrtmp_22538 = tmp_struct_214.field2;
            GibCursor pvrtmp_22539 = tmp_struct_214.field3;
            GibCursor pvrtmp_22540 = tmp_struct_214.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15702,
                                                                        pvrtmp_22537,
                                                                        jump_17990,
                                                                        pvrtmp_22539,
                                                                        pvrtmp_22540};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_217 = *(uintptr_t *) tmpcur_22465;
            GibCursor tmpcur_22547 = GIB_UNTAG(tagged_tmpcur_217);
            GibCursor tmpaftercur_22548 = tmpcur_22465 + 8;
            uint16_t tmptag_22549 = GIB_GET_TAG(tagged_tmpcur_217);
            GibCursor end_from_tagged_indr_17988 = tmpcur_22547 + tmptag_22549;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_216 =
                                                               foldConstants2(end_from_tagged_indr_17988, end_r_15703, loc_15701, tmpcur_22547);
            GibCursor pvrtmp_22550 = tmp_struct_216.field0;
            GibCursor pvrtmp_22551 = tmp_struct_216.field1;
            GibCursor pvrtmp_22552 = tmp_struct_216.field2;
            GibCursor pvrtmp_22553 = tmp_struct_216.field3;
            GibCursor pvrtmp_22554 = tmp_struct_216.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_22550,
                                                                        pvrtmp_22551,
                                                                        pvrtmp_22552,
                                                                        pvrtmp_22553,
                                                                        pvrtmp_22554};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_22464");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorProd buildExp(GibCursor end_r_15705,
                                         GibCursor loc_15704,
                                         GibInt n_726_7908_12516)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_15704 + 18 > end_r_15705) {
        gib_grow_region(&loc_15704, &end_r_15705);
    }

    GibBool fltIf_11884_12517 = n_726_7908_12516 == 0;

    if (fltIf_11884_12517) {
        GibCursor loc_16096 = loc_15704 + 1;

        *(GibPackedTag *) loc_15704 = 3;

        GibCursor writetag_19224 = loc_15704 + 1;

        *(GibPackedTag *) loc_16096 = 0;

        GibCursor writetag_19208 = loc_16096 + 1;
        GibCursor after_tag_19209 = loc_16096 + 1;

        *(GibInt *) after_tag_19209 = 0;

        GibCursor writecur_19213 = after_tag_19209 + sizeof(GibInt);

        *(GibPackedTag *) writecur_19213 = 0;

        GibCursor writetag_19216 = writecur_19213 + 1;
        GibCursor after_tag_19217 = writecur_19213 + 1;

        *(GibInt *) after_tag_19217 = 1;

        GibCursor writecur_19221 = after_tag_19217 + sizeof(GibInt);
        GibCursor after_tag_19225 = loc_15704 + 1;

        return (GibCursorGibCursorGibCursorProd) {end_r_15705, loc_15704,
                                                  writecur_19221};
    } else {
        GibInt fltAppE_11888_12520 = n_726_7908_12516 - 1;
        GibCursor loc_16102 = loc_15704 + 1;

        *(GibPackedTag *) loc_15704 = 3;

        GibCursor writetag_19238 = loc_15704 + 1;

        gib_shadowstack_push(rstack, loc_15704, end_r_15705, Stk, Exp_T);

        GibCursorGibCursorGibCursorProd tmp_struct_221 =
                                         buildExp(end_r_15705, loc_16102, fltAppE_11888_12520);
        GibCursor pvrtmp_22570 = tmp_struct_221.field0;
        GibCursor pvrtmp_22571 = tmp_struct_221.field1;
        GibCursor pvrtmp_22572 = tmp_struct_221.field2;

        frame = gib_shadowstack_pop(rstack);
        loc_15704 = frame->ptr;
        end_r_15705 = frame->endptr;

        GibInt fltAppE_11890_12522 = n_726_7908_12516 - 1;

        gib_shadowstack_push(rstack, loc_15704, pvrtmp_22570, Stk, Exp_T);

        GibCursorGibCursorGibCursorProd tmp_struct_222 =
                                         buildExp(pvrtmp_22570, pvrtmp_22572, fltAppE_11890_12522);
        GibCursor pvrtmp_22577 = tmp_struct_222.field0;
        GibCursor pvrtmp_22578 = tmp_struct_222.field1;
        GibCursor pvrtmp_22579 = tmp_struct_222.field2;

        frame = gib_shadowstack_pop(rstack);
        loc_15704 = frame->ptr;
        pvrtmp_22570 = frame->endptr;

        GibCursor after_tag_19239 = loc_15704 + 1;

        return (GibCursorGibCursorGibCursorProd) {pvrtmp_22577, loc_15704,
                                                  pvrtmp_22579};
    }
}
unsigned char print_check(GibBool b_745_7915_12524)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (b_745_7915_12524) {
        unsigned char wildcard__14_746_7916_12525 = gib_print_symbol(21853);

        return 0;
    } else {
        unsigned char wildcard__16_747_7917_12526 = gib_print_symbol(21854);

        return 0;
    }
}
GibFloat sumList(GibVector *ls_793_7961_12527)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibInt fltAppE_11891_12530 = gib_vector_length(ls_793_7961_12527);
    GibFloat tailapp_17345 =
              foldl_loop_3487_6016(0, fltAppE_11891_12530, 0.0, ls_793_7961_12527);

    return tailapp_17345;
}
GibCursorGibCursorGibFloatProd sumKdTree(GibCursor end_r_15707,
                                         GibCursor tr_820_7982_12531)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_22588 = *(GibPackedTag *) tr_820_7982_12531;
    GibCursor tmpcur_22589 = tr_820_7982_12531 + 1;


  switch_22641:
    ;
    switch (tmpval_22588) {

      case 2:
        {
            GibCursor jump_17347 = tr_820_7982_12531 + 1;

            return (GibCursorGibCursorGibFloatProd) {end_r_15707, jump_17347,
                                                     0.0};
            break;
        }

      case 0:
        {
            GibFloat tmpval_22590 = *(GibFloat *) tmpcur_22589;
            GibCursor tmpcur_22591 = tmpcur_22589 + sizeof(GibFloat);
            GibFloat tmpval_22592 = *(GibFloat *) tmpcur_22591;
            GibCursor tmpcur_22593 = tmpcur_22591 + sizeof(GibFloat);
            GibFloat tmpval_22594 = *(GibFloat *) tmpcur_22593;
            GibCursor tmpcur_22595 = tmpcur_22593 + sizeof(GibFloat);
            GibCursor jump_17350 = tmpcur_22593 + 4;
            GibFloat fltPrm_11892_12535 = tmpval_22590 + tmpval_22592;
            GibFloat tailprim_17351 = fltPrm_11892_12535 + tmpval_22594;

            return (GibCursorGibCursorGibFloatProd) {end_r_15707, jump_17350,
                                                     tailprim_17351};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_228 = *(uintptr_t *) tmpcur_22589;
            GibCursor tmpcur_22596 = GIB_UNTAG(tagged_tmpcur_228);
            GibCursor tmpaftercur_22597 = tmpcur_22589 + 8;
            uint16_t tmptag_22598 = GIB_GET_TAG(tagged_tmpcur_228);
            GibCursor end_from_tagged_absran_15531 = tmpcur_22596 +
                      tmptag_22598;
            GibFloat tmpval_22599 = *(GibFloat *) tmpaftercur_22597;
            GibCursor tmpcur_22600 = tmpaftercur_22597 + sizeof(GibFloat);
            GibFloat tmpval_22601 = *(GibFloat *) tmpcur_22600;
            GibCursor tmpcur_22602 = tmpcur_22600 + sizeof(GibFloat);
            GibFloat tmpval_22603 = *(GibFloat *) tmpcur_22602;
            GibCursor tmpcur_22604 = tmpcur_22602 + sizeof(GibFloat);
            GibInt tmpval_22605 = *(GibInt *) tmpcur_22604;
            GibCursor tmpcur_22606 = tmpcur_22604 + sizeof(GibInt);
            GibInt tmpval_22607 = *(GibInt *) tmpcur_22606;
            GibCursor tmpcur_22608 = tmpcur_22606 + sizeof(GibInt);
            GibFloat tmpval_22609 = *(GibFloat *) tmpcur_22608;
            GibCursor tmpcur_22610 = tmpcur_22608 + sizeof(GibFloat);
            GibFloat tmpval_22611 = *(GibFloat *) tmpcur_22610;
            GibCursor tmpcur_22612 = tmpcur_22610 + sizeof(GibFloat);
            GibFloat tmpval_22613 = *(GibFloat *) tmpcur_22612;
            GibCursor tmpcur_22614 = tmpcur_22612 + sizeof(GibFloat);
            GibFloat tmpval_22615 = *(GibFloat *) tmpcur_22614;
            GibCursor tmpcur_22616 = tmpcur_22614 + sizeof(GibFloat);
            GibFloat tmpval_22617 = *(GibFloat *) tmpcur_22616;
            GibCursor tmpcur_22618 = tmpcur_22616 + sizeof(GibFloat);
            GibFloat tmpval_22619 = *(GibFloat *) tmpcur_22618;
            GibCursor tmpcur_22620 = tmpcur_22618 + sizeof(GibFloat);
            GibFloat tmpval_22621 = *(GibFloat *) tmpcur_22620;
            GibCursor tmpcur_22622 = tmpcur_22620 + sizeof(GibFloat);

            gib_shadowstack_push(rstack, tmpcur_22596, end_r_15707, Stk,
                                 KdTree_T);

            GibCursorGibCursorGibFloatProd tmp_struct_226 =
                                            sumKdTree(end_r_15707, tmpcur_22622);
            GibCursor pvrtmp_22623 = tmp_struct_226.field0;
            GibCursor pvrtmp_22624 = tmp_struct_226.field1;
            GibFloat pvrtmp_22625 = tmp_struct_226.field2;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_22596 = frame->ptr;
            end_r_15707 = frame->endptr;

            GibCursorGibCursorGibFloatProd tmp_struct_227 =
                                            sumKdTree(end_from_tagged_absran_15531, tmpcur_22596);
            GibCursor pvrtmp_22626 = tmp_struct_227.field0;
            GibCursor pvrtmp_22627 = tmp_struct_227.field1;
            GibFloat pvrtmp_22628 = tmp_struct_227.field2;
            GibFloat fltPrm_11895_12552 = tmpval_22599 + tmpval_22601;
            GibFloat fltPrm_11894_12553 = fltPrm_11895_12552 + tmpval_22603;
            GibFloat fltPrm_11893_12554 = fltPrm_11894_12553 + pvrtmp_22625;
            GibFloat tailprim_17367 = fltPrm_11893_12554 + pvrtmp_22628;

            return (GibCursorGibCursorGibFloatProd) {pvrtmp_22626, pvrtmp_22627,
                                                     tailprim_17367};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_230 = *(uintptr_t *) tmpcur_22589;
            GibCursor tmpcur_22629 = GIB_UNTAG(tagged_tmpcur_230);
            GibCursor tmpaftercur_22630 = tmpcur_22589 + 8;
            uint16_t tmptag_22631 = GIB_GET_TAG(tagged_tmpcur_230);
            GibCursor end_from_tagged_indr_17994 = tmpcur_22629 + tmptag_22631;
            GibCursor jump_17996 = tmpcur_22589 + 8;
            GibCursorGibCursorGibFloatProd tmp_struct_229 =
                                            sumKdTree(end_from_tagged_indr_17994, tmpcur_22629);
            GibCursor pvrtmp_22632 = tmp_struct_229.field0;
            GibCursor pvrtmp_22633 = tmp_struct_229.field1;
            GibFloat pvrtmp_22634 = tmp_struct_229.field2;

            return (GibCursorGibCursorGibFloatProd) {end_r_15707, jump_17996,
                                                     pvrtmp_22634};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_232 = *(uintptr_t *) tmpcur_22589;
            GibCursor tmpcur_22635 = GIB_UNTAG(tagged_tmpcur_232);
            GibCursor tmpaftercur_22636 = tmpcur_22589 + 8;
            uint16_t tmptag_22637 = GIB_GET_TAG(tagged_tmpcur_232);
            GibCursor end_from_tagged_indr_17994 = tmpcur_22635 + tmptag_22637;
            GibCursorGibCursorGibFloatProd tmp_struct_231 =
                                            sumKdTree(end_from_tagged_indr_17994, tmpcur_22635);
            GibCursor pvrtmp_22638 = tmp_struct_231.field0;
            GibCursor pvrtmp_22639 = tmp_struct_231.field1;
            GibFloat pvrtmp_22640 = tmp_struct_231.field2;

            return (GibCursorGibCursorGibFloatProd) {pvrtmp_22638, pvrtmp_22639,
                                                     pvrtmp_22640};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_22588");
            exit(1);
        }
    }
}
GibCursorGibIntProd countCorr_seq(GibCursor end_r_15709,
                                  GibFloatGibFloatGibFloatProd probe_906_8068_12555,
                                  GibFloat radius_907_8069_12556,
                                  GibCursor tr_908_8070_12557)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_22642 = *(GibPackedTag *) tr_908_8070_12557;
    GibCursor tmpcur_22643 = tr_908_8070_12557 + 1;


  switch_22730:
    ;
    switch (tmpval_22642) {

      case 2:
        {
            return (GibCursorGibIntProd) {end_r_15709, 0};
            break;
        }

      case 0:
        {
            GibFloat tmpval_22644 = *(GibFloat *) tmpcur_22643;
            GibCursor tmpcur_22645 = tmpcur_22643 + sizeof(GibFloat);
            GibFloat tmpval_22646 = *(GibFloat *) tmpcur_22645;
            GibCursor tmpcur_22647 = tmpcur_22645 + sizeof(GibFloat);
            GibFloat tmpval_22648 = *(GibFloat *) tmpcur_22647;
            GibCursor tmpcur_22649 = tmpcur_22647 + sizeof(GibFloat);
            GibFloat fltPrm_11897_12562 =
                      dist_point3d((GibFloatGibFloatGibFloatProd) {probe_906_8068_12555.field0, probe_906_8068_12555.field1, probe_906_8068_12555.field2}, (GibFloatGibFloatGibFloatProd) {tmpval_22644, tmpval_22646, tmpval_22648});
            GibFloat fltPrm_11899_12563 = radius_907_8069_12556 *
                     radius_907_8069_12556;
            GibBool fltIf_11896_12564 = fltPrm_11897_12562 < fltPrm_11899_12563;

            if (fltIf_11896_12564) {
                return (GibCursorGibIntProd) {end_r_15709, 1};
            } else {
                return (GibCursorGibIntProd) {end_r_15709, 0};
            }
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_235 = *(uintptr_t *) tmpcur_22643;
            GibCursor tmpcur_22659 = GIB_UNTAG(tagged_tmpcur_235);
            GibCursor tmpaftercur_22660 = tmpcur_22643 + 8;
            uint16_t tmptag_22661 = GIB_GET_TAG(tagged_tmpcur_235);
            GibCursor end_from_tagged_absran_15534 = tmpcur_22659 +
                      tmptag_22661;
            GibFloat tmpval_22662 = *(GibFloat *) tmpaftercur_22660;
            GibCursor tmpcur_22663 = tmpaftercur_22660 + sizeof(GibFloat);
            GibFloat tmpval_22664 = *(GibFloat *) tmpcur_22663;
            GibCursor tmpcur_22665 = tmpcur_22663 + sizeof(GibFloat);
            GibFloat tmpval_22666 = *(GibFloat *) tmpcur_22665;
            GibCursor tmpcur_22667 = tmpcur_22665 + sizeof(GibFloat);
            GibInt tmpval_22668 = *(GibInt *) tmpcur_22667;
            GibCursor tmpcur_22669 = tmpcur_22667 + sizeof(GibInt);
            GibInt tmpval_22670 = *(GibInt *) tmpcur_22669;
            GibCursor tmpcur_22671 = tmpcur_22669 + sizeof(GibInt);
            GibFloat tmpval_22672 = *(GibFloat *) tmpcur_22671;
            GibCursor tmpcur_22673 = tmpcur_22671 + sizeof(GibFloat);
            GibFloat tmpval_22674 = *(GibFloat *) tmpcur_22673;
            GibCursor tmpcur_22675 = tmpcur_22673 + sizeof(GibFloat);
            GibFloat tmpval_22676 = *(GibFloat *) tmpcur_22675;
            GibCursor tmpcur_22677 = tmpcur_22675 + sizeof(GibFloat);
            GibFloat tmpval_22678 = *(GibFloat *) tmpcur_22677;
            GibCursor tmpcur_22679 = tmpcur_22677 + sizeof(GibFloat);
            GibFloat tmpval_22680 = *(GibFloat *) tmpcur_22679;
            GibCursor tmpcur_22681 = tmpcur_22679 + sizeof(GibFloat);
            GibFloat tmpval_22682 = *(GibFloat *) tmpcur_22681;
            GibCursor tmpcur_22683 = tmpcur_22681 + sizeof(GibFloat);
            GibFloat tmpval_22684 = *(GibFloat *) tmpcur_22683;
            GibCursor tmpcur_22685 = tmpcur_22683 + sizeof(GibFloat);
            GibFloat fltPrm_11900_12579 = tmpval_22674 + tmpval_22676;
            GibFloat center_x_926_8088_12580 = fltPrm_11900_12579 / 2.0;
            GibFloat fltPrm_11901_12581 = tmpval_22678 + tmpval_22680;
            GibFloat center_y_927_8089_12582 = fltPrm_11901_12581 / 2.0;
            GibFloat fltPrm_11902_12583 = tmpval_22682 + tmpval_22684;
            GibFloat center_z_928_8090_12584 = fltPrm_11902_12583 / 2.0;
            GibFloat d_x_933_8095_12589 = probe_906_8068_12555.field0 -
                     center_x_926_8088_12580;
            GibFloat d_y_934_8096_12590 = probe_906_8068_12555.field1 -
                     center_y_927_8089_12582;
            GibFloat d_z_935_8097_12591 = probe_906_8068_12555.field2 -
                     center_z_928_8090_12584;
            GibFloat fltPrm_11903_12592 = tmpval_22676 - tmpval_22674;
            GibFloat boxdist_x_936_8098_12593 = fltPrm_11903_12592 / 2.0;
            GibFloat fltPrm_11904_12594 = tmpval_22680 - tmpval_22678;
            GibFloat boxdist_y_937_8099_12595 = fltPrm_11904_12594 / 2.0;
            GibFloat fltPrm_11905_12596 = tmpval_22684 - tmpval_22682;
            GibFloat boxdist_z_938_8100_12597 = fltPrm_11905_12596 / 2.0;
            GibFloat fltPrm_11907_12598 = d_x_933_8095_12589 *
                     d_x_933_8095_12589;
            GibFloat fltPrm_11908_12599 = d_y_934_8096_12590 *
                     d_y_934_8096_12590;
            GibFloat fltPrm_11906_12600 = fltPrm_11907_12598 +
                     fltPrm_11908_12599;
            GibFloat fltPrm_11909_12601 = d_z_935_8097_12591 *
                     d_z_935_8097_12591;
            GibFloat sum_939_8101_12602 = fltPrm_11906_12600 +
                     fltPrm_11909_12601;
            GibFloat fltPrm_11911_12603 = boxdist_x_936_8098_12593 *
                     boxdist_x_936_8098_12593;
            GibFloat fltPrm_11912_12604 = boxdist_y_937_8099_12595 *
                     boxdist_y_937_8099_12595;
            GibFloat fltPrm_11910_12605 = fltPrm_11911_12603 +
                     fltPrm_11912_12604;
            GibFloat fltPrm_11913_12606 = boxdist_z_938_8100_12597 *
                     boxdist_z_938_8100_12597;
            GibFloat boxsum_940_8102_12607 = fltPrm_11910_12605 +
                     fltPrm_11913_12606;
            GibFloat fltPrm_11915_12608 = sum_939_8101_12602 -
                     boxsum_940_8102_12607;
            GibFloat fltPrm_11916_12609 = radius_907_8069_12556 *
                     radius_907_8069_12556;
            GibBool fltIf_11914_12610 = fltPrm_11915_12608 < fltPrm_11916_12609;

            if (fltIf_11914_12610) {
                gib_shadowstack_push(rstack, tmpcur_22659, end_r_15709, Stk,
                                     KdTree_T);

                GibCursorGibIntProd tmp_struct_233 =
                                     countCorr_seq(end_r_15709, (GibFloatGibFloatGibFloatProd) {probe_906_8068_12555.field0, probe_906_8068_12555.field1, probe_906_8068_12555.field2}, radius_907_8069_12556, tmpcur_22685);
                GibCursor pvrtmp_22689 = tmp_struct_233.field0;
                GibInt pvrtmp_22690 = tmp_struct_233.field1;

                frame = gib_shadowstack_pop(rstack);
                tmpcur_22659 = frame->ptr;
                end_r_15709 = frame->endptr;

                GibCursorGibIntProd tmp_struct_234 =
                                     countCorr_seq(end_from_tagged_absran_15534, (GibFloatGibFloatGibFloatProd) {probe_906_8068_12555.field0, probe_906_8068_12555.field1, probe_906_8068_12555.field2}, radius_907_8069_12556, tmpcur_22659);
                GibCursor pvrtmp_22694 = tmp_struct_234.field0;
                GibInt pvrtmp_22695 = tmp_struct_234.field1;
                GibFloat fltPrm_11918_12614 =
                          dist_point3d((GibFloatGibFloatGibFloatProd) {probe_906_8068_12555.field0, probe_906_8068_12555.field1, probe_906_8068_12555.field2}, (GibFloatGibFloatGibFloatProd) {tmpval_22662, tmpval_22664, tmpval_22666});
                GibFloat fltPrm_11920_12615 = radius_907_8069_12556 *
                         radius_907_8069_12556;
                GibBool fltIf_11917_12616 = fltPrm_11918_12614 <
                        fltPrm_11920_12615;

                if (fltIf_11917_12616) {
                    GibInt fltPrm_11921_12617 = pvrtmp_22690 + pvrtmp_22695;
                    GibInt tailprim_17390 = fltPrm_11921_12617 + 1;

                    return (GibCursorGibIntProd) {pvrtmp_22694, tailprim_17390};
                } else {
                    GibInt tailprim_17391 = pvrtmp_22690 + pvrtmp_22695;

                    return (GibCursorGibIntProd) {pvrtmp_22694, tailprim_17391};
                }
            } else {
                GibFloat fltPrm_11923_12619 =
                          dist_point3d((GibFloatGibFloatGibFloatProd) {probe_906_8068_12555.field0, probe_906_8068_12555.field1, probe_906_8068_12555.field2}, (GibFloatGibFloatGibFloatProd) {tmpval_22662, tmpval_22664, tmpval_22666});
                GibFloat fltPrm_11925_12620 = radius_907_8069_12556 *
                         radius_907_8069_12556;
                GibBool fltIf_11922_12621 = fltPrm_11923_12619 <
                        fltPrm_11925_12620;

                if (fltIf_11922_12621) {
                    return (GibCursorGibIntProd) {end_r_15709, 1};
                } else {
                    return (GibCursorGibIntProd) {end_r_15709, 0};
                }
            }
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_237 = *(uintptr_t *) tmpcur_22643;
            GibCursor tmpcur_22714 = GIB_UNTAG(tagged_tmpcur_237);
            GibCursor tmpaftercur_22715 = tmpcur_22643 + 8;
            uint16_t tmptag_22716 = GIB_GET_TAG(tagged_tmpcur_237);
            GibCursor end_from_tagged_indr_18000 = tmpcur_22714 + tmptag_22716;
            GibCursor jump_18002 = tmpcur_22643 + 8;
            GibCursorGibIntProd tmp_struct_236 =
                                 countCorr_seq(end_from_tagged_indr_18000, (GibFloatGibFloatGibFloatProd) {probe_906_8068_12555.field0, probe_906_8068_12555.field1, probe_906_8068_12555.field2}, radius_907_8069_12556, tmpcur_22714);
            GibCursor pvrtmp_22720 = tmp_struct_236.field0;
            GibInt pvrtmp_22721 = tmp_struct_236.field1;

            return (GibCursorGibIntProd) {end_r_15709, pvrtmp_22721};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_239 = *(uintptr_t *) tmpcur_22643;
            GibCursor tmpcur_22722 = GIB_UNTAG(tagged_tmpcur_239);
            GibCursor tmpaftercur_22723 = tmpcur_22643 + 8;
            uint16_t tmptag_22724 = GIB_GET_TAG(tagged_tmpcur_239);
            GibCursor end_from_tagged_indr_18000 = tmpcur_22722 + tmptag_22724;
            GibCursorGibIntProd tmp_struct_238 =
                                 countCorr_seq(end_from_tagged_indr_18000, (GibFloatGibFloatGibFloatProd) {probe_906_8068_12555.field0, probe_906_8068_12555.field1, probe_906_8068_12555.field2}, radius_907_8069_12556, tmpcur_22722);
            GibCursor pvrtmp_22728 = tmp_struct_238.field0;
            GibInt pvrtmp_22729 = tmp_struct_238.field1;

            return (GibCursorGibIntProd) {pvrtmp_22728, pvrtmp_22729};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_22642");
            exit(1);
        }
    }
}
GibFloatGibFloatGibFloatProd least_dist_point3d(GibFloatGibFloatGibFloatProd a_943_8105_12622,
                                                GibFloatGibFloatGibFloatProd b_944_8106_12623,
                                                GibFloatGibFloatGibFloatProd c_945_8107_12624)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibFloat d1_946_8108_12625 =
              dist_point3d((GibFloatGibFloatGibFloatProd) {a_943_8105_12622.field0, a_943_8105_12622.field1, a_943_8105_12622.field2}, (GibFloatGibFloatGibFloatProd) {b_944_8106_12623.field0, b_944_8106_12623.field1, b_944_8106_12623.field2});
    GibFloat d2_947_8109_12626 =
              dist_point3d((GibFloatGibFloatGibFloatProd) {a_943_8105_12622.field0, a_943_8105_12622.field1, a_943_8105_12622.field2}, (GibFloatGibFloatGibFloatProd) {c_945_8107_12624.field0, c_945_8107_12624.field1, c_945_8107_12624.field2});
    GibBool fltIf_11926_12627 = d1_946_8108_12625 < d2_947_8109_12626;

    if (fltIf_11926_12627) {
        return b_944_8106_12623;
    } else {
        return c_945_8107_12624;
    }
}
GibCursorGibCursorGibFloatGibFloatGibFloatProd find_nearest(GibCursor end_r_15712,
                                                            GibCursor end_r_15713,
                                                            GibFloatGibFloatGibFloatProd pivot_948_8110_12628,
                                                            GibFloatGibFloatGibFloatProd query_949_8111_12629,
                                                            GibFloat tst_pivot_950_8112_12630,
                                                            GibFloat tst_query_951_8113_12631,
                                                            GibCursor good_side_952_8114_12632,
                                                            GibCursor other_side_953_8115_12633)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    // gib_shadowstack_push(rstack, other_side_953_8115_12633, end_r_15713, Stk,
    //                      KdTree_T);

    GibCursorGibFloatGibFloatGibFloatProd tmp_struct_240 =
                                           nearest(end_r_15712, good_side_952_8114_12632, (GibFloatGibFloatGibFloatProd) {query_949_8111_12629.field0, query_949_8111_12629.field1, query_949_8111_12629.field2});
    GibCursor pvrtmp_22746 = tmp_struct_240.field0;
    GibFloat pvrtmp_22747 = tmp_struct_240.field1;
    GibFloat pvrtmp_22748 = tmp_struct_240.field2;
    GibFloat pvrtmp_22749 = tmp_struct_240.field3;

    // frame = gib_shadowstack_pop(rstack);
    // other_side_953_8115_12633 = frame->ptr;
    // end_r_15713 = frame->endptr;
    // gib_shadowstack_push(rstack, other_side_953_8115_12633, end_r_15713, Stk,
    //                      KdTree_T);

    GibFloatGibFloatGibFloatProd tmp_struct_241 =
                                  least_dist_point3d((GibFloatGibFloatGibFloatProd) {query_949_8111_12629.field0, query_949_8111_12629.field1, query_949_8111_12629.field2}, (GibFloatGibFloatGibFloatProd) {pvrtmp_22747, pvrtmp_22748, pvrtmp_22749}, (GibFloatGibFloatGibFloatProd) {pivot_948_8110_12628.field0, pivot_948_8110_12628.field1, pivot_948_8110_12628.field2});
    GibFloat pvrtmp_22762 = tmp_struct_241.field0;
    GibFloat pvrtmp_22763 = tmp_struct_241.field1;
    GibFloat pvrtmp_22764 = tmp_struct_241.field2;

    // frame = gib_shadowstack_pop(rstack);
    // other_side_953_8115_12633 = frame->ptr;
    // end_r_15713 = frame->endptr;

    GibFloat nearest_other_side_956_8118_12636 = tst_query_951_8113_12631 -
             tst_pivot_950_8112_12630;
    GibFloat fltPrm_11928_12637 = nearest_other_side_956_8118_12636 *
             nearest_other_side_956_8118_12636;

    // gib_shadowstack_push(rstack, other_side_953_8115_12633, end_r_15713, Stk,
    //                      KdTree_T);

    GibFloat fltPrm_11929_12638 =
              dist_point3d((GibFloatGibFloatGibFloatProd) {query_949_8111_12629.field0, query_949_8111_12629.field1, query_949_8111_12629.field2}, (GibFloatGibFloatGibFloatProd) {pvrtmp_22762, pvrtmp_22763, pvrtmp_22764});

    // frame = gib_shadowstack_pop(rstack);
    // other_side_953_8115_12633 = frame->ptr;
    // end_r_15713 = frame->endptr;

    GibBool fltIf_11927_12639 = fltPrm_11928_12637 <= fltPrm_11929_12638;

    if (fltIf_11927_12639) {
        GibCursorGibFloatGibFloatGibFloatProd tmp_struct_242 =
                                               nearest(end_r_15713, other_side_953_8115_12633, (GibFloatGibFloatGibFloatProd) {query_949_8111_12629.field0, query_949_8111_12629.field1, query_949_8111_12629.field2});
        GibCursor pvrtmp_22774 = tmp_struct_242.field0;
        GibFloat pvrtmp_22775 = tmp_struct_242.field1;
        GibFloat pvrtmp_22776 = tmp_struct_242.field2;
        GibFloat pvrtmp_22777 = tmp_struct_242.field3;
        GibFloatGibFloatGibFloatProd tmp_struct_243 =
                                      least_dist_point3d((GibFloatGibFloatGibFloatProd) {query_949_8111_12629.field0, query_949_8111_12629.field1, query_949_8111_12629.field2}, (GibFloatGibFloatGibFloatProd) {pvrtmp_22762, pvrtmp_22763, pvrtmp_22764}, (GibFloatGibFloatGibFloatProd) {pvrtmp_22775, pvrtmp_22776, pvrtmp_22777});
        GibFloat pvrtmp_22790 = tmp_struct_243.field0;
        GibFloat pvrtmp_22791 = tmp_struct_243.field1;
        GibFloat pvrtmp_22792 = tmp_struct_243.field2;

        return (GibCursorGibCursorGibFloatGibFloatGibFloatProd) {pvrtmp_22746,
                                                                 pvrtmp_22774,
                                                                 pvrtmp_22790,
                                                                 pvrtmp_22791,
                                                                 pvrtmp_22792};
    } else {
        return (GibCursorGibCursorGibFloatGibFloatGibFloatProd) {pvrtmp_22746,
                                                                 end_r_15713,
                                                                 pvrtmp_22762,
                                                                 pvrtmp_22763,
                                                                 pvrtmp_22764};
    }
}
GibCursorGibFloatGibFloatGibFloatProd nearest(GibCursor end_r_15715,
                                              GibCursor tr_959_8121_12642,
                                              GibFloatGibFloatGibFloatProd query_960_8122_12643)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_22793 = *(GibPackedTag *) tr_959_8121_12642;
    GibCursor tmpcur_22794 = tr_959_8121_12642 + 1;


  switch_22897:
    ;
    switch (tmpval_22793) {

      case 2:
        {
            return (GibCursorGibFloatGibFloatGibFloatProd) {end_r_15715, 0.0,
                                                            0.0, 0.0};
            break;
        }

      case 0:
        {
            GibFloat tmpval_22798 = *(GibFloat *) tmpcur_22794;
            GibCursor tmpcur_22799 = tmpcur_22794 + sizeof(GibFloat);
            GibFloat tmpval_22800 = *(GibFloat *) tmpcur_22799;
            GibCursor tmpcur_22801 = tmpcur_22799 + sizeof(GibFloat);
            GibFloat tmpval_22802 = *(GibFloat *) tmpcur_22801;
            GibCursor tmpcur_22803 = tmpcur_22801 + sizeof(GibFloat);

            return (GibCursorGibFloatGibFloatGibFloatProd) {end_r_15715,
                                                            tmpval_22798,
                                                            tmpval_22800,
                                                            tmpval_22802};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_246 = *(uintptr_t *) tmpcur_22794;
            GibCursor tmpcur_22807 = GIB_UNTAG(tagged_tmpcur_246);
            GibCursor tmpaftercur_22808 = tmpcur_22794 + 8;
            uint16_t tmptag_22809 = GIB_GET_TAG(tagged_tmpcur_246);
            GibCursor end_from_tagged_absran_15537 = tmpcur_22807 +
                      tmptag_22809;
            GibFloat tmpval_22810 = *(GibFloat *) tmpaftercur_22808;
            GibCursor tmpcur_22811 = tmpaftercur_22808 + sizeof(GibFloat);
            GibFloat tmpval_22812 = *(GibFloat *) tmpcur_22811;
            GibCursor tmpcur_22813 = tmpcur_22811 + sizeof(GibFloat);
            GibFloat tmpval_22814 = *(GibFloat *) tmpcur_22813;
            GibCursor tmpcur_22815 = tmpcur_22813 + sizeof(GibFloat);
            GibInt tmpval_22816 = *(GibInt *) tmpcur_22815;
            GibCursor tmpcur_22817 = tmpcur_22815 + sizeof(GibInt);
            GibInt tmpval_22818 = *(GibInt *) tmpcur_22817;
            GibCursor tmpcur_22819 = tmpcur_22817 + sizeof(GibInt);
            GibFloat tmpval_22820 = *(GibFloat *) tmpcur_22819;
            GibCursor tmpcur_22821 = tmpcur_22819 + sizeof(GibFloat);
            GibFloat tmpval_22822 = *(GibFloat *) tmpcur_22821;
            GibCursor tmpcur_22823 = tmpcur_22821 + sizeof(GibFloat);
            GibFloat tmpval_22824 = *(GibFloat *) tmpcur_22823;
            GibCursor tmpcur_22825 = tmpcur_22823 + sizeof(GibFloat);
            GibFloat tmpval_22826 = *(GibFloat *) tmpcur_22825;
            GibCursor tmpcur_22827 = tmpcur_22825 + sizeof(GibFloat);
            GibFloat tmpval_22828 = *(GibFloat *) tmpcur_22827;
            GibCursor tmpcur_22829 = tmpcur_22827 + sizeof(GibFloat);
            GibFloat tmpval_22830 = *(GibFloat *) tmpcur_22829;
            GibCursor tmpcur_22831 = tmpcur_22829 + sizeof(GibFloat);
            GibFloat tmpval_22832 = *(GibFloat *) tmpcur_22831;
            GibCursor tmpcur_22833 = tmpcur_22831 + sizeof(GibFloat);

            // gib_shadowstack_push(rstack, tmpcur_22807, end_r_15715, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, tmpcur_22833, end_r_15715, Stk,
            //                      KdTree_T);

            GibFloat tst_query_979_8141_12662 =
                      get_coord_point3d(tmpval_22818, (GibFloatGibFloatGibFloatProd) {query_960_8122_12643.field0, query_960_8122_12643.field1, query_960_8122_12643.field2});

            // frame = gib_shadowstack_pop(rstack);
            // tmpcur_22833 = frame->ptr;
            // end_r_15715 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // tmpcur_22807 = frame->ptr;
            // end_r_15715 = frame->endptr;
            // gib_shadowstack_push(rstack, tmpcur_22807, end_r_15715, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, tmpcur_22833, end_r_15715, Stk,
            //                      KdTree_T);

            GibFloat tst_pivot_980_8142_12663 =
                      get_coord_point3d(tmpval_22818, (GibFloatGibFloatGibFloatProd) {tmpval_22810, tmpval_22812, tmpval_22814});

            // frame = gib_shadowstack_pop(rstack);
            // tmpcur_22833 = frame->ptr;
            // end_r_15715 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // tmpcur_22807 = frame->ptr;
            // end_r_15715 = frame->endptr;

            GibBool fltIf_11930_12664 = tst_query_979_8141_12662 <
                    tst_pivot_980_8142_12663;

            if (fltIf_11930_12664) {
                GibCursorGibCursorGibFloatGibFloatGibFloatProd tmp_struct_244 =
                                                                find_nearest(end_r_15715, end_from_tagged_absran_15537, (GibFloatGibFloatGibFloatProd) {tmpval_22810, tmpval_22812, tmpval_22814}, (GibFloatGibFloatGibFloatProd) {query_960_8122_12643.field0, query_960_8122_12643.field1, query_960_8122_12643.field2}, tst_pivot_980_8142_12663, tst_query_979_8141_12662, tmpcur_22833, tmpcur_22807);
                GibCursor pvrtmp_22849 = tmp_struct_244.field0;
                GibCursor pvrtmp_22850 = tmp_struct_244.field1;
                GibFloat pvrtmp_22851 = tmp_struct_244.field2;
                GibFloat pvrtmp_22852 = tmp_struct_244.field3;
                GibFloat pvrtmp_22853 = tmp_struct_244.field4;

                return (GibCursorGibFloatGibFloatGibFloatProd) {pvrtmp_22850,
                                                                pvrtmp_22851,
                                                                pvrtmp_22852,
                                                                pvrtmp_22853};
            } else {
                GibCursorGibCursorGibFloatGibFloatGibFloatProd tmp_struct_245 =
                                                                find_nearest(end_from_tagged_absran_15537, end_r_15715, (GibFloatGibFloatGibFloatProd) {tmpval_22810, tmpval_22812, tmpval_22814}, (GibFloatGibFloatGibFloatProd) {query_960_8122_12643.field0, query_960_8122_12643.field1, query_960_8122_12643.field2}, tst_pivot_980_8142_12663, tst_query_979_8141_12662, tmpcur_22807, tmpcur_22833);
                GibCursor pvrtmp_22863 = tmp_struct_245.field0;
                GibCursor pvrtmp_22864 = tmp_struct_245.field1;
                GibFloat pvrtmp_22865 = tmp_struct_245.field2;
                GibFloat pvrtmp_22866 = tmp_struct_245.field3;
                GibFloat pvrtmp_22867 = tmp_struct_245.field4;

                return (GibCursorGibFloatGibFloatGibFloatProd) {pvrtmp_22863,
                                                                pvrtmp_22865,
                                                                pvrtmp_22866,
                                                                pvrtmp_22867};
            }
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_248 = *(uintptr_t *) tmpcur_22794;
            GibCursor tmpcur_22871 = GIB_UNTAG(tagged_tmpcur_248);
            GibCursor tmpaftercur_22872 = tmpcur_22794 + 8;
            uint16_t tmptag_22873 = GIB_GET_TAG(tagged_tmpcur_248);
            GibCursor end_from_tagged_indr_18005 = tmpcur_22871 + tmptag_22873;
            GibCursor jump_18007 = tmpcur_22794 + 8;
            GibCursorGibFloatGibFloatGibFloatProd tmp_struct_247 =
                                                   nearest(end_from_tagged_indr_18005, tmpcur_22871, (GibFloatGibFloatGibFloatProd) {query_960_8122_12643.field0, query_960_8122_12643.field1, query_960_8122_12643.field2});
            GibCursor pvrtmp_22877 = tmp_struct_247.field0;
            GibFloat pvrtmp_22878 = tmp_struct_247.field1;
            GibFloat pvrtmp_22879 = tmp_struct_247.field2;
            GibFloat pvrtmp_22880 = tmp_struct_247.field3;

            return (GibCursorGibFloatGibFloatGibFloatProd) {end_r_15715,
                                                            pvrtmp_22878,
                                                            pvrtmp_22879,
                                                            pvrtmp_22880};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_250 = *(uintptr_t *) tmpcur_22794;
            GibCursor tmpcur_22884 = GIB_UNTAG(tagged_tmpcur_250);
            GibCursor tmpaftercur_22885 = tmpcur_22794 + 8;
            uint16_t tmptag_22886 = GIB_GET_TAG(tagged_tmpcur_250);
            GibCursor end_from_tagged_indr_18005 = tmpcur_22884 + tmptag_22886;
            GibCursorGibFloatGibFloatGibFloatProd tmp_struct_249 =
                                                   nearest(end_from_tagged_indr_18005, tmpcur_22884, (GibFloatGibFloatGibFloatProd) {query_960_8122_12643.field0, query_960_8122_12643.field1, query_960_8122_12643.field2});
            GibCursor pvrtmp_22890 = tmp_struct_249.field0;
            GibFloat pvrtmp_22891 = tmp_struct_249.field1;
            GibFloat pvrtmp_22892 = tmp_struct_249.field2;
            GibFloat pvrtmp_22893 = tmp_struct_249.field3;

            return (GibCursorGibFloatGibFloatGibFloatProd) {pvrtmp_22890,
                                                            pvrtmp_22891,
                                                            pvrtmp_22892,
                                                            pvrtmp_22893};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_22793");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorProd mkKdTreeWithAxis_seq(GibCursor end_r_15717,
                                                     GibCursor loc_15716,
                                                     GibInt axis_1029_8191_12665,
                                                     GibVector *pts_1030_8192_12666)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_15716 + 74 > end_r_15717) {
        gib_grow_region(&loc_15716, &end_r_15717);
    }

    GibInt len_1031_8193_12667 = gib_vector_length(pts_1030_8192_12666);
    GibBool fltIf_11931_12668 = len_1031_8193_12667 == 0;

    if (fltIf_11931_12668) {
        *(GibPackedTag *) loc_15716 = 2;

        GibCursor writetag_19347 = loc_15716 + 1;
        GibCursor after_tag_19348 = loc_15716 + 1;

        return (GibCursorGibCursorGibCursorProd) {end_r_15717, loc_15716,
                                                  after_tag_19348};
    } else {
        GibBool fltIf_11932_12669 = len_1031_8193_12667 == 1;

        if (fltIf_11932_12669) {
            GibFloatGibFloatGibFloatProd *tmp_251;

            tmp_251 =
                (GibFloatGibFloatGibFloatProd *) gib_vector_nth(pts_1030_8192_12666,
                                                                0);

            GibFloatGibFloatGibFloatProd tup_386_1032_8194_12672 = *tmp_251;

            *(GibPackedTag *) loc_15716 = 0;

            GibCursor writetag_19354 = loc_15716 + 1;
            GibCursor after_tag_19355 = loc_15716 + 1;

            *(GibFloat *) after_tag_19355 = tup_386_1032_8194_12672.field0;

            GibCursor writecur_19359 = after_tag_19355 + sizeof(GibFloat);

            *(GibFloat *) writecur_19359 = tup_386_1032_8194_12672.field1;

            GibCursor writecur_19360 = writecur_19359 + sizeof(GibFloat);

            *(GibFloat *) writecur_19360 = tup_386_1032_8194_12672.field2;

            GibCursor writecur_19361 = writecur_19360 + sizeof(GibFloat);

            return (GibCursorGibCursorGibCursorProd) {end_r_15717, loc_15716,
                                                      writecur_19361};
        } else {
            // gib_shadowstack_push(wstack, loc_15716, end_r_15717, Stk, KdTree_T);

            GibVector *sorted_pts_1036_8198_12676 =
                       sort_point3d(axis_1029_8191_12665, pts_1030_8192_12666);

            // frame = gib_shadowstack_pop(wstack);
            // loc_15716 = frame->ptr;
            // end_r_15717 = frame->endptr;

            GibInt pivot_idx_1037_8199_12677 = len_1031_8193_12667 / 2;
            GibFloatGibFloatGibFloatProd *tmp_269;

            tmp_269 =
                (GibFloatGibFloatGibFloatProd *) gib_vector_nth(sorted_pts_1036_8198_12676,
                                                                pivot_idx_1037_8199_12677);

            GibFloatGibFloatGibFloatProd pivot_1038_8200_12680 = *tmp_269;
            GibVector *left_pts_1043_8205_12688 = gib_vector_slice(0,
                                                                   pivot_idx_1037_8199_12677,
                                                                   sorted_pts_1036_8198_12676);
            GibInt i_536_8969_10748_12689 = pivot_idx_1037_8199_12677 + 1;
            GibInt fltPrm_11933_12690 = len_1031_8193_12667 -
                   pivot_idx_1037_8199_12677;
            GibInt n_537_8970_10749_12691 = fltPrm_11933_12690 - 1;
            GibVector *right_pts_1044_8206_12693 =
                      gib_vector_slice(i_536_8969_10748_12689,
                                       n_537_8970_10749_12691,
                                       sorted_pts_1036_8198_12676);

            // gib_shadowstack_push(wstack, loc_15716, end_r_15717, Stk, KdTree_T);

            GibInt next_axis_1045_8207_12694 =
                    getNextAxis_3d(axis_1029_8191_12665);

            // frame = gib_shadowstack_pop(wstack);
            // loc_15716 = frame->ptr;
            // end_r_15717 = frame->endptr;

            GibCursor loc_16241 = loc_15716 + 65;

            *(GibPackedTag *) loc_15716 = 3;

            GibCursor writetag_19396 = loc_15716 + 1;

            // gib_shadowstack_push(rstack, loc_15716, end_r_15717, Stk, KdTree_T);

            GibCursorGibCursorGibCursorProd tmp_struct_252 =
                                             mkKdTreeWithAxis_seq(end_r_15717, loc_16241, next_axis_1045_8207_12694, left_pts_1043_8205_12688);
            GibCursor pvrtmp_22906 = tmp_struct_252.field0;
            GibCursor pvrtmp_22907 = tmp_struct_252.field1;
            GibCursor pvrtmp_22908 = tmp_struct_252.field2;

            // frame = gib_shadowstack_pop(rstack);
            // loc_15716 = frame->ptr;
            // end_r_15717 = frame->endptr;
            // gib_shadowstack_push(rstack, loc_15716, pvrtmp_22906, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, loc_16241, pvrtmp_22906, Stk,
            //                      KdTree_T);

            GibCursorGibCursorGibCursorProd tmp_struct_253 =
                                             mkKdTreeWithAxis_seq(pvrtmp_22906, pvrtmp_22908, next_axis_1045_8207_12694, right_pts_1044_8206_12693);
            GibCursor pvrtmp_22913 = tmp_struct_253.field0;
            GibCursor pvrtmp_22914 = tmp_struct_253.field1;
            GibCursor pvrtmp_22915 = tmp_struct_253.field2;

            // frame = gib_shadowstack_pop(rstack);
            // loc_16241 = frame->ptr;
            // pvrtmp_22906 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // loc_15716 = frame->ptr;
            // pvrtmp_22906 = frame->endptr;
            // gib_shadowstack_push(rstack, loc_15716, pvrtmp_22913, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, pvrtmp_22908, pvrtmp_22913, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, loc_16241, pvrtmp_22913, Stk,
            //                      KdTree_T);

            GibCursorGibFloatProd tmp_struct_254 =
                                   get_minx_kdtree(pvrtmp_22913, pvrtmp_22907);
            GibCursor pvrtmp_22920 = tmp_struct_254.field0;
            GibFloat pvrtmp_22921 = tmp_struct_254.field1;

            // frame = gib_shadowstack_pop(rstack);
            // loc_16241 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // pvrtmp_22908 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // loc_15716 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // gib_shadowstack_push(rstack, loc_15716, pvrtmp_22913, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, pvrtmp_22908, pvrtmp_22920, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, loc_16241, pvrtmp_22913, Stk,
            //                      KdTree_T);

            GibCursorGibFloatProd tmp_struct_255 =
                                   get_minx_kdtree(pvrtmp_22920, pvrtmp_22914);
            GibCursor pvrtmp_22922 = tmp_struct_255.field0;
            GibFloat pvrtmp_22923 = tmp_struct_255.field1;

            // frame = gib_shadowstack_pop(rstack);
            // loc_16241 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // pvrtmp_22908 = frame->ptr;
            // pvrtmp_22920 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // loc_15716 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // gib_shadowstack_push(rstack, loc_15716, pvrtmp_22913, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, pvrtmp_22908, pvrtmp_22920, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, loc_16241, pvrtmp_22913, Stk,
            //                      KdTree_T);

            GibFloat fltAppE_11934_12699 =
                      minFloat(pvrtmp_22921, pvrtmp_22923);

            // frame = gib_shadowstack_pop(rstack);
            // loc_16241 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // pvrtmp_22908 = frame->ptr;
            // pvrtmp_22920 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // loc_15716 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // gib_shadowstack_push(rstack, loc_15716, pvrtmp_22913, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, pvrtmp_22908, pvrtmp_22920, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, loc_16241, pvrtmp_22913, Stk,
            //                      KdTree_T);

            GibFloat min_x_1048_8210_12700 =
                      minFloat(pivot_1038_8200_12680.field0, fltAppE_11934_12699);

            // frame = gib_shadowstack_pop(rstack);
            // loc_16241 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // pvrtmp_22908 = frame->ptr;
            // pvrtmp_22920 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // loc_15716 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // gib_shadowstack_push(rstack, loc_15716, pvrtmp_22913, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, pvrtmp_22908, pvrtmp_22920, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, loc_16241, pvrtmp_22913, Stk,
            //                      KdTree_T);

            GibCursorGibFloatProd tmp_struct_256 =
                                   get_maxx_kdtree(pvrtmp_22913, pvrtmp_22907);
            GibCursor pvrtmp_22924 = tmp_struct_256.field0;
            GibFloat pvrtmp_22925 = tmp_struct_256.field1;

            // frame = gib_shadowstack_pop(rstack);
            // loc_16241 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // pvrtmp_22908 = frame->ptr;
            // pvrtmp_22920 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // loc_15716 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // gib_shadowstack_push(rstack, loc_15716, pvrtmp_22913, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, pvrtmp_22908, pvrtmp_22924, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, loc_16241, pvrtmp_22913, Stk,
            //                      KdTree_T);

            GibCursorGibFloatProd tmp_struct_257 =
                                   get_maxx_kdtree(pvrtmp_22924, pvrtmp_22914);
            GibCursor pvrtmp_22926 = tmp_struct_257.field0;
            GibFloat pvrtmp_22927 = tmp_struct_257.field1;

            // frame = gib_shadowstack_pop(rstack);
            // loc_16241 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // pvrtmp_22908 = frame->ptr;
            // pvrtmp_22924 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // loc_15716 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // gib_shadowstack_push(rstack, loc_15716, pvrtmp_22913, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, pvrtmp_22908, pvrtmp_22924, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, loc_16241, pvrtmp_22913, Stk,
            //                      KdTree_T);

            GibFloat fltAppE_11937_12703 =
                      maxFloat(pvrtmp_22925, pvrtmp_22927);

            // frame = gib_shadowstack_pop(rstack);
            // loc_16241 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // pvrtmp_22908 = frame->ptr;
            // pvrtmp_22924 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // loc_15716 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // gib_shadowstack_push(rstack, loc_15716, pvrtmp_22913, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, pvrtmp_22908, pvrtmp_22924, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, loc_16241, pvrtmp_22913, Stk,
            //                      KdTree_T);

            GibFloat max_x_1049_8211_12704 =
                      maxFloat(pivot_1038_8200_12680.field0, fltAppE_11937_12703);

            // frame = gib_shadowstack_pop(rstack);
            // loc_16241 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // pvrtmp_22908 = frame->ptr;
            // pvrtmp_22924 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // loc_15716 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // gib_shadowstack_push(rstack, loc_15716, pvrtmp_22913, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, pvrtmp_22908, pvrtmp_22924, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, loc_16241, pvrtmp_22913, Stk,
            //                      KdTree_T);

            GibCursorGibFloatProd tmp_struct_258 =
                                   get_miny_kdtree(pvrtmp_22913, pvrtmp_22907);
            GibCursor pvrtmp_22928 = tmp_struct_258.field0;
            GibFloat pvrtmp_22929 = tmp_struct_258.field1;

            // frame = gib_shadowstack_pop(rstack);
            // loc_16241 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // pvrtmp_22908 = frame->ptr;
            // pvrtmp_22924 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // loc_15716 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // gib_shadowstack_push(rstack, loc_15716, pvrtmp_22913, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, pvrtmp_22908, pvrtmp_22928, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, loc_16241, pvrtmp_22913, Stk,
            //                      KdTree_T);

            GibCursorGibFloatProd tmp_struct_259 =
                                   get_miny_kdtree(pvrtmp_22928, pvrtmp_22914);
            GibCursor pvrtmp_22930 = tmp_struct_259.field0;
            GibFloat pvrtmp_22931 = tmp_struct_259.field1;

            // frame = gib_shadowstack_pop(rstack);
            // loc_16241 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // pvrtmp_22908 = frame->ptr;
            // pvrtmp_22928 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // loc_15716 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // gib_shadowstack_push(rstack, loc_15716, pvrtmp_22913, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, pvrtmp_22908, pvrtmp_22928, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, loc_16241, pvrtmp_22913, Stk,
            //                      KdTree_T);

            GibFloat fltAppE_11940_12707 =
                      minFloat(pvrtmp_22929, pvrtmp_22931);

            // frame = gib_shadowstack_pop(rstack);
            // loc_16241 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // pvrtmp_22908 = frame->ptr;
            // pvrtmp_22928 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // loc_15716 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // gib_shadowstack_push(rstack, loc_15716, pvrtmp_22913, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, pvrtmp_22908, pvrtmp_22928, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, loc_16241, pvrtmp_22913, Stk,
            //                      KdTree_T);

            GibFloat min_y_1050_8212_12708 =
                      minFloat(pivot_1038_8200_12680.field1, fltAppE_11940_12707);

            // frame = gib_shadowstack_pop(rstack);
            // loc_16241 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // pvrtmp_22908 = frame->ptr;
            // pvrtmp_22928 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // loc_15716 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // gib_shadowstack_push(rstack, loc_15716, pvrtmp_22913, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, pvrtmp_22908, pvrtmp_22928, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, loc_16241, pvrtmp_22913, Stk,
            //                      KdTree_T);

            GibCursorGibFloatProd tmp_struct_260 =
                                   get_maxy_kdtree(pvrtmp_22913, pvrtmp_22907);
            GibCursor pvrtmp_22932 = tmp_struct_260.field0;
            GibFloat pvrtmp_22933 = tmp_struct_260.field1;

            // frame = gib_shadowstack_pop(rstack);
            // loc_16241 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // pvrtmp_22908 = frame->ptr;
            // pvrtmp_22928 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // loc_15716 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // gib_shadowstack_push(rstack, loc_15716, pvrtmp_22913, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, pvrtmp_22908, pvrtmp_22932, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, loc_16241, pvrtmp_22913, Stk,
            //                      KdTree_T);

            GibCursorGibFloatProd tmp_struct_261 =
                                   get_maxy_kdtree(pvrtmp_22932, pvrtmp_22914);
            GibCursor pvrtmp_22934 = tmp_struct_261.field0;
            GibFloat pvrtmp_22935 = tmp_struct_261.field1;

            // frame = gib_shadowstack_pop(rstack);
            // loc_16241 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // pvrtmp_22908 = frame->ptr;
            // pvrtmp_22932 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // loc_15716 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // gib_shadowstack_push(rstack, loc_15716, pvrtmp_22913, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, pvrtmp_22908, pvrtmp_22932, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, loc_16241, pvrtmp_22913, Stk,
            //                      KdTree_T);

            GibFloat fltAppE_11943_12711 =
                      maxFloat(pvrtmp_22933, pvrtmp_22935);

            // frame = gib_shadowstack_pop(rstack);
            // loc_16241 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // pvrtmp_22908 = frame->ptr;
            // pvrtmp_22932 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // loc_15716 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // gib_shadowstack_push(rstack, loc_15716, pvrtmp_22913, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, pvrtmp_22908, pvrtmp_22932, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, loc_16241, pvrtmp_22913, Stk,
            //                      KdTree_T);

            GibFloat max_y_1051_8213_12712 =
                      maxFloat(pivot_1038_8200_12680.field1, fltAppE_11943_12711);

            // frame = gib_shadowstack_pop(rstack);
            // loc_16241 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // pvrtmp_22908 = frame->ptr;
            // pvrtmp_22932 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // loc_15716 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // gib_shadowstack_push(rstack, loc_15716, pvrtmp_22913, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, pvrtmp_22908, pvrtmp_22932, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, loc_16241, pvrtmp_22913, Stk,
            //                      KdTree_T);

            GibCursorGibFloatProd tmp_struct_262 =
                                   get_minz_kdtree(pvrtmp_22913, pvrtmp_22907);
            GibCursor pvrtmp_22936 = tmp_struct_262.field0;
            GibFloat pvrtmp_22937 = tmp_struct_262.field1;

            // frame = gib_shadowstack_pop(rstack);
            // loc_16241 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // pvrtmp_22908 = frame->ptr;
            // pvrtmp_22932 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // loc_15716 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // gib_shadowstack_push(rstack, loc_15716, pvrtmp_22913, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, pvrtmp_22908, pvrtmp_22936, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, loc_16241, pvrtmp_22913, Stk,
            //                      KdTree_T);

            GibCursorGibFloatProd tmp_struct_263 =
                                   get_minz_kdtree(pvrtmp_22936, pvrtmp_22914);
            GibCursor pvrtmp_22938 = tmp_struct_263.field0;
            GibFloat pvrtmp_22939 = tmp_struct_263.field1;

            // frame = gib_shadowstack_pop(rstack);
            // loc_16241 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // pvrtmp_22908 = frame->ptr;
            // pvrtmp_22936 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // loc_15716 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // gib_shadowstack_push(rstack, loc_15716, pvrtmp_22913, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, pvrtmp_22908, pvrtmp_22936, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, loc_16241, pvrtmp_22913, Stk,
            //                      KdTree_T);

            GibFloat fltAppE_11946_12715 =
                      minFloat(pvrtmp_22937, pvrtmp_22939);

            // frame = gib_shadowstack_pop(rstack);
            // loc_16241 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // pvrtmp_22908 = frame->ptr;
            // pvrtmp_22936 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // loc_15716 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // gib_shadowstack_push(rstack, loc_15716, pvrtmp_22913, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, pvrtmp_22908, pvrtmp_22936, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, loc_16241, pvrtmp_22913, Stk,
            //                      KdTree_T);

            GibFloat min_z_1052_8214_12716 =
                      minFloat(pivot_1038_8200_12680.field2, fltAppE_11946_12715);

            // frame = gib_shadowstack_pop(rstack);
            // loc_16241 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // pvrtmp_22908 = frame->ptr;
            // pvrtmp_22936 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // loc_15716 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // gib_shadowstack_push(rstack, loc_15716, pvrtmp_22913, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, pvrtmp_22908, pvrtmp_22936, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, loc_16241, pvrtmp_22913, Stk,
            //                      KdTree_T);

            GibCursorGibFloatProd tmp_struct_264 =
                                   get_maxz_kdtree(pvrtmp_22913, pvrtmp_22907);
            GibCursor pvrtmp_22940 = tmp_struct_264.field0;
            GibFloat pvrtmp_22941 = tmp_struct_264.field1;

            // frame = gib_shadowstack_pop(rstack);
            // loc_16241 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // pvrtmp_22908 = frame->ptr;
            // pvrtmp_22936 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // loc_15716 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // gib_shadowstack_push(rstack, loc_15716, pvrtmp_22913, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, pvrtmp_22908, pvrtmp_22940, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, loc_16241, pvrtmp_22913, Stk,
            //                      KdTree_T);

            GibCursorGibFloatProd tmp_struct_265 =
                                   get_maxz_kdtree(pvrtmp_22940, pvrtmp_22914);
            GibCursor pvrtmp_22942 = tmp_struct_265.field0;
            GibFloat pvrtmp_22943 = tmp_struct_265.field1;

            // frame = gib_shadowstack_pop(rstack);
            // loc_16241 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // pvrtmp_22908 = frame->ptr;
            // pvrtmp_22940 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // loc_15716 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // gib_shadowstack_push(rstack, loc_15716, pvrtmp_22913, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, pvrtmp_22908, pvrtmp_22940, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, loc_16241, pvrtmp_22913, Stk,
            //                      KdTree_T);

            GibFloat fltAppE_11949_12719 =
                      maxFloat(pvrtmp_22941, pvrtmp_22943);

            // frame = gib_shadowstack_pop(rstack);
            // loc_16241 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // pvrtmp_22908 = frame->ptr;
            // pvrtmp_22940 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // loc_15716 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // gib_shadowstack_push(rstack, loc_15716, pvrtmp_22913, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, pvrtmp_22908, pvrtmp_22940, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, loc_16241, pvrtmp_22913, Stk,
            //                      KdTree_T);

            GibFloat max_z_1053_8215_12720 =
                      maxFloat(pivot_1038_8200_12680.field2, fltAppE_11949_12719);

            // frame = gib_shadowstack_pop(rstack);
            // loc_16241 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // pvrtmp_22908 = frame->ptr;
            // pvrtmp_22940 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // loc_15716 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // gib_shadowstack_push(rstack, loc_15716, pvrtmp_22913, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, pvrtmp_22908, pvrtmp_22940, Stk,
                                 // KdTree_T);

            GibCursorGibIntProd tmp_struct_266 =
                                 get_total_points_kdtree(pvrtmp_22913, pvrtmp_22907);
            GibCursor pvrtmp_22944 = tmp_struct_266.field0;
            GibInt pvrtmp_22945 = tmp_struct_266.field1;

            // frame = gib_shadowstack_pop(rstack);
            // pvrtmp_22908 = frame->ptr;
            // pvrtmp_22940 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // loc_15716 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;
            // gib_shadowstack_push(rstack, loc_15716, pvrtmp_22913, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, pvrtmp_22908, pvrtmp_22944, Stk,
            //                      KdTree_T);

            GibCursorGibIntProd tmp_struct_267 =
                                 get_total_points_kdtree(pvrtmp_22944, pvrtmp_22914);
            GibCursor pvrtmp_22946 = tmp_struct_267.field0;
            GibInt pvrtmp_22947 = tmp_struct_267.field1;

            // frame = gib_shadowstack_pop(rstack);
            // pvrtmp_22908 = frame->ptr;
            // pvrtmp_22944 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // loc_15716 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;

            GibInt fltPrm_11952_12723 = pvrtmp_22945 + pvrtmp_22947;
            GibInt total_points_1054_8216_12724 = fltPrm_11952_12723 + 1;

            // gib_shadowstack_push(rstack, loc_15716, pvrtmp_22913, Stk,
            //                      KdTree_T);
            // gib_shadowstack_push(rstack, pvrtmp_22908, pvrtmp_22944, Stk,
            //                      KdTree_T);

            GibFloat fltPkd_11955_12725 =
                      get_coord_point3d(axis_1029_8191_12665, (GibFloatGibFloatGibFloatProd) {pivot_1038_8200_12680.field0, pivot_1038_8200_12680.field1, pivot_1038_8200_12680.field2});

            // frame = gib_shadowstack_pop(rstack);
            // pvrtmp_22908 = frame->ptr;
            // pvrtmp_22944 = frame->endptr;
            // frame = gib_shadowstack_pop(rstack);
            // loc_15716 = frame->ptr;
            // pvrtmp_22913 = frame->endptr;

            uint16_t offset_268 = pvrtmp_22906 - pvrtmp_22908;
            uintptr_t ran_15540 = GIB_STORE_TAG(pvrtmp_22908, offset_268);
            GibCursor after_tag_19397 = loc_15716 + 1;

            *(uintptr_t *) after_tag_19397 = ran_15540;

            GibCursor writecur_19401 = after_tag_19397 + 8;

            *(GibFloat *) writecur_19401 = pivot_1038_8200_12680.field0;

            GibCursor writecur_19402 = writecur_19401 + sizeof(GibFloat);

            *(GibFloat *) writecur_19402 = pivot_1038_8200_12680.field1;

            GibCursor writecur_19403 = writecur_19402 + sizeof(GibFloat);

            *(GibFloat *) writecur_19403 = pivot_1038_8200_12680.field2;

            GibCursor writecur_19404 = writecur_19403 + sizeof(GibFloat);

            *(GibInt *) writecur_19404 = total_points_1054_8216_12724;

            GibCursor writecur_19405 = writecur_19404 + sizeof(GibInt);

            *(GibInt *) writecur_19405 = axis_1029_8191_12665;

            GibCursor writecur_19406 = writecur_19405 + sizeof(GibInt);

            *(GibFloat *) writecur_19406 = fltPkd_11955_12725;

            GibCursor writecur_19407 = writecur_19406 + sizeof(GibFloat);

            *(GibFloat *) writecur_19407 = min_x_1048_8210_12700;

            GibCursor writecur_19408 = writecur_19407 + sizeof(GibFloat);

            *(GibFloat *) writecur_19408 = max_x_1049_8211_12704;

            GibCursor writecur_19409 = writecur_19408 + sizeof(GibFloat);

            *(GibFloat *) writecur_19409 = min_y_1050_8212_12708;

            GibCursor writecur_19410 = writecur_19409 + sizeof(GibFloat);

            *(GibFloat *) writecur_19410 = max_y_1051_8213_12712;

            GibCursor writecur_19411 = writecur_19410 + sizeof(GibFloat);

            *(GibFloat *) writecur_19411 = min_z_1052_8214_12716;

            GibCursor writecur_19412 = writecur_19411 + sizeof(GibFloat);

            *(GibFloat *) writecur_19412 = max_z_1053_8215_12720;

            GibCursor writecur_19413 = writecur_19412 + sizeof(GibFloat);

            return (GibCursorGibCursorGibCursorProd) {pvrtmp_22944, loc_15716,
                                                      pvrtmp_22915};
        }
    }
}
GibCursorGibIntProd get_total_points_kdtree(GibCursor end_r_15719,
                                            GibCursor tr_1109_8271_12726)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_22955 = *(GibPackedTag *) tr_1109_8271_12726;
    GibCursor tmpcur_22956 = tr_1109_8271_12726 + 1;


  switch_23000:
    ;
    switch (tmpval_22955) {

      case 2:
        {
            return (GibCursorGibIntProd) {end_r_15719, 0};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_273 = *(uintptr_t *) tmpcur_22956;
            GibCursor tmpcur_22957 = GIB_UNTAG(tagged_tmpcur_273);
            GibCursor tmpaftercur_22958 = tmpcur_22956 + 8;
            uint16_t tmptag_22959 = GIB_GET_TAG(tagged_tmpcur_273);
            GibCursor end_from_tagged_absran_15541 = tmpcur_22957 +
                      tmptag_22959;
            GibFloat tmpval_22960 = *(GibFloat *) tmpaftercur_22958;
            GibCursor tmpcur_22961 = tmpaftercur_22958 + sizeof(GibFloat);
            GibFloat tmpval_22962 = *(GibFloat *) tmpcur_22961;
            GibCursor tmpcur_22963 = tmpcur_22961 + sizeof(GibFloat);
            GibFloat tmpval_22964 = *(GibFloat *) tmpcur_22963;
            GibCursor tmpcur_22965 = tmpcur_22963 + sizeof(GibFloat);
            GibInt tmpval_22966 = *(GibInt *) tmpcur_22965;
            GibCursor tmpcur_22967 = tmpcur_22965 + sizeof(GibInt);
            GibInt tmpval_22968 = *(GibInt *) tmpcur_22967;
            GibCursor tmpcur_22969 = tmpcur_22967 + sizeof(GibInt);
            GibFloat tmpval_22970 = *(GibFloat *) tmpcur_22969;
            GibCursor tmpcur_22971 = tmpcur_22969 + sizeof(GibFloat);
            GibFloat tmpval_22972 = *(GibFloat *) tmpcur_22971;
            GibCursor tmpcur_22973 = tmpcur_22971 + sizeof(GibFloat);
            GibFloat tmpval_22974 = *(GibFloat *) tmpcur_22973;
            GibCursor tmpcur_22975 = tmpcur_22973 + sizeof(GibFloat);
            GibFloat tmpval_22976 = *(GibFloat *) tmpcur_22975;
            GibCursor tmpcur_22977 = tmpcur_22975 + sizeof(GibFloat);
            GibFloat tmpval_22978 = *(GibFloat *) tmpcur_22977;
            GibCursor tmpcur_22979 = tmpcur_22977 + sizeof(GibFloat);
            GibFloat tmpval_22980 = *(GibFloat *) tmpcur_22979;
            GibCursor tmpcur_22981 = tmpcur_22979 + sizeof(GibFloat);
            GibFloat tmpval_22982 = *(GibFloat *) tmpcur_22981;
            GibCursor tmpcur_22983 = tmpcur_22981 + sizeof(GibFloat);

            return (GibCursorGibIntProd) {end_r_15719, tmpval_22966};
            break;
        }

      case 0:
        {
            GibFloat tmpval_22984 = *(GibFloat *) tmpcur_22956;
            GibCursor tmpcur_22985 = tmpcur_22956 + sizeof(GibFloat);
            GibFloat tmpval_22986 = *(GibFloat *) tmpcur_22985;
            GibCursor tmpcur_22987 = tmpcur_22985 + sizeof(GibFloat);
            GibFloat tmpval_22988 = *(GibFloat *) tmpcur_22987;
            GibCursor tmpcur_22989 = tmpcur_22987 + sizeof(GibFloat);

            return (GibCursorGibIntProd) {end_r_15719, 1};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_275 = *(uintptr_t *) tmpcur_22956;
            GibCursor tmpcur_22990 = GIB_UNTAG(tagged_tmpcur_275);
            GibCursor tmpaftercur_22991 = tmpcur_22956 + 8;
            uint16_t tmptag_22992 = GIB_GET_TAG(tagged_tmpcur_275);
            GibCursor end_from_tagged_indr_18010 = tmpcur_22990 + tmptag_22992;
            GibCursor jump_18012 = tmpcur_22956 + 8;
            GibCursorGibIntProd tmp_struct_274 =
                                 get_total_points_kdtree(end_from_tagged_indr_18010, tmpcur_22990);
            GibCursor pvrtmp_22993 = tmp_struct_274.field0;
            GibInt pvrtmp_22994 = tmp_struct_274.field1;

            return (GibCursorGibIntProd) {end_r_15719, pvrtmp_22994};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_277 = *(uintptr_t *) tmpcur_22956;
            GibCursor tmpcur_22995 = GIB_UNTAG(tagged_tmpcur_277);
            GibCursor tmpaftercur_22996 = tmpcur_22956 + 8;
            uint16_t tmptag_22997 = GIB_GET_TAG(tagged_tmpcur_277);
            GibCursor end_from_tagged_indr_18010 = tmpcur_22995 + tmptag_22997;
            GibCursorGibIntProd tmp_struct_276 =
                                 get_total_points_kdtree(end_from_tagged_indr_18010, tmpcur_22995);
            GibCursor pvrtmp_22998 = tmp_struct_276.field0;
            GibInt pvrtmp_22999 = tmp_struct_276.field1;

            return (GibCursorGibIntProd) {pvrtmp_22998, pvrtmp_22999};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_22955");
            exit(1);
        }
    }
}
GibCursorGibFloatProd get_maxz_kdtree(GibCursor end_r_15721,
                                      GibCursor tr_1127_8289_12744)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_23001 = *(GibPackedTag *) tr_1127_8289_12744;
    GibCursor tmpcur_23002 = tr_1127_8289_12744 + 1;


  switch_23046:
    ;
    switch (tmpval_23001) {

      case 2:
        {
            return (GibCursorGibFloatProd) {end_r_15721, 0.0};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_278 = *(uintptr_t *) tmpcur_23002;
            GibCursor tmpcur_23003 = GIB_UNTAG(tagged_tmpcur_278);
            GibCursor tmpaftercur_23004 = tmpcur_23002 + 8;
            uint16_t tmptag_23005 = GIB_GET_TAG(tagged_tmpcur_278);
            GibCursor end_from_tagged_absran_15544 = tmpcur_23003 +
                      tmptag_23005;
            GibFloat tmpval_23006 = *(GibFloat *) tmpaftercur_23004;
            GibCursor tmpcur_23007 = tmpaftercur_23004 + sizeof(GibFloat);
            GibFloat tmpval_23008 = *(GibFloat *) tmpcur_23007;
            GibCursor tmpcur_23009 = tmpcur_23007 + sizeof(GibFloat);
            GibFloat tmpval_23010 = *(GibFloat *) tmpcur_23009;
            GibCursor tmpcur_23011 = tmpcur_23009 + sizeof(GibFloat);
            GibInt tmpval_23012 = *(GibInt *) tmpcur_23011;
            GibCursor tmpcur_23013 = tmpcur_23011 + sizeof(GibInt);
            GibInt tmpval_23014 = *(GibInt *) tmpcur_23013;
            GibCursor tmpcur_23015 = tmpcur_23013 + sizeof(GibInt);
            GibFloat tmpval_23016 = *(GibFloat *) tmpcur_23015;
            GibCursor tmpcur_23017 = tmpcur_23015 + sizeof(GibFloat);
            GibFloat tmpval_23018 = *(GibFloat *) tmpcur_23017;
            GibCursor tmpcur_23019 = tmpcur_23017 + sizeof(GibFloat);
            GibFloat tmpval_23020 = *(GibFloat *) tmpcur_23019;
            GibCursor tmpcur_23021 = tmpcur_23019 + sizeof(GibFloat);
            GibFloat tmpval_23022 = *(GibFloat *) tmpcur_23021;
            GibCursor tmpcur_23023 = tmpcur_23021 + sizeof(GibFloat);
            GibFloat tmpval_23024 = *(GibFloat *) tmpcur_23023;
            GibCursor tmpcur_23025 = tmpcur_23023 + sizeof(GibFloat);
            GibFloat tmpval_23026 = *(GibFloat *) tmpcur_23025;
            GibCursor tmpcur_23027 = tmpcur_23025 + sizeof(GibFloat);
            GibFloat tmpval_23028 = *(GibFloat *) tmpcur_23027;
            GibCursor tmpcur_23029 = tmpcur_23027 + sizeof(GibFloat);

            return (GibCursorGibFloatProd) {end_r_15721, tmpval_23028};
            break;
        }

      case 0:
        {
            GibFloat tmpval_23030 = *(GibFloat *) tmpcur_23002;
            GibCursor tmpcur_23031 = tmpcur_23002 + sizeof(GibFloat);
            GibFloat tmpval_23032 = *(GibFloat *) tmpcur_23031;
            GibCursor tmpcur_23033 = tmpcur_23031 + sizeof(GibFloat);
            GibFloat tmpval_23034 = *(GibFloat *) tmpcur_23033;
            GibCursor tmpcur_23035 = tmpcur_23033 + sizeof(GibFloat);

            return (GibCursorGibFloatProd) {end_r_15721, tmpval_23034};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_280 = *(uintptr_t *) tmpcur_23002;
            GibCursor tmpcur_23036 = GIB_UNTAG(tagged_tmpcur_280);
            GibCursor tmpaftercur_23037 = tmpcur_23002 + 8;
            uint16_t tmptag_23038 = GIB_GET_TAG(tagged_tmpcur_280);
            GibCursor end_from_tagged_indr_18015 = tmpcur_23036 + tmptag_23038;
            GibCursor jump_18017 = tmpcur_23002 + 8;
            GibCursorGibFloatProd tmp_struct_279 =
                                   get_maxz_kdtree(end_from_tagged_indr_18015, tmpcur_23036);
            GibCursor pvrtmp_23039 = tmp_struct_279.field0;
            GibFloat pvrtmp_23040 = tmp_struct_279.field1;

            return (GibCursorGibFloatProd) {end_r_15721, pvrtmp_23040};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_282 = *(uintptr_t *) tmpcur_23002;
            GibCursor tmpcur_23041 = GIB_UNTAG(tagged_tmpcur_282);
            GibCursor tmpaftercur_23042 = tmpcur_23002 + 8;
            uint16_t tmptag_23043 = GIB_GET_TAG(tagged_tmpcur_282);
            GibCursor end_from_tagged_indr_18015 = tmpcur_23041 + tmptag_23043;
            GibCursorGibFloatProd tmp_struct_281 =
                                   get_maxz_kdtree(end_from_tagged_indr_18015, tmpcur_23041);
            GibCursor pvrtmp_23044 = tmp_struct_281.field0;
            GibFloat pvrtmp_23045 = tmp_struct_281.field1;

            return (GibCursorGibFloatProd) {pvrtmp_23044, pvrtmp_23045};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_23001");
            exit(1);
        }
    }
}
GibCursorGibFloatProd get_minz_kdtree(GibCursor end_r_15723,
                                      GibCursor tr_1145_8307_12762)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_23047 = *(GibPackedTag *) tr_1145_8307_12762;
    GibCursor tmpcur_23048 = tr_1145_8307_12762 + 1;


  switch_23092:
    ;
    switch (tmpval_23047) {

      case 2:
        {
            return (GibCursorGibFloatProd) {end_r_15723, 0.0};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_283 = *(uintptr_t *) tmpcur_23048;
            GibCursor tmpcur_23049 = GIB_UNTAG(tagged_tmpcur_283);
            GibCursor tmpaftercur_23050 = tmpcur_23048 + 8;
            uint16_t tmptag_23051 = GIB_GET_TAG(tagged_tmpcur_283);
            GibCursor end_from_tagged_absran_15547 = tmpcur_23049 +
                      tmptag_23051;
            GibFloat tmpval_23052 = *(GibFloat *) tmpaftercur_23050;
            GibCursor tmpcur_23053 = tmpaftercur_23050 + sizeof(GibFloat);
            GibFloat tmpval_23054 = *(GibFloat *) tmpcur_23053;
            GibCursor tmpcur_23055 = tmpcur_23053 + sizeof(GibFloat);
            GibFloat tmpval_23056 = *(GibFloat *) tmpcur_23055;
            GibCursor tmpcur_23057 = tmpcur_23055 + sizeof(GibFloat);
            GibInt tmpval_23058 = *(GibInt *) tmpcur_23057;
            GibCursor tmpcur_23059 = tmpcur_23057 + sizeof(GibInt);
            GibInt tmpval_23060 = *(GibInt *) tmpcur_23059;
            GibCursor tmpcur_23061 = tmpcur_23059 + sizeof(GibInt);
            GibFloat tmpval_23062 = *(GibFloat *) tmpcur_23061;
            GibCursor tmpcur_23063 = tmpcur_23061 + sizeof(GibFloat);
            GibFloat tmpval_23064 = *(GibFloat *) tmpcur_23063;
            GibCursor tmpcur_23065 = tmpcur_23063 + sizeof(GibFloat);
            GibFloat tmpval_23066 = *(GibFloat *) tmpcur_23065;
            GibCursor tmpcur_23067 = tmpcur_23065 + sizeof(GibFloat);
            GibFloat tmpval_23068 = *(GibFloat *) tmpcur_23067;
            GibCursor tmpcur_23069 = tmpcur_23067 + sizeof(GibFloat);
            GibFloat tmpval_23070 = *(GibFloat *) tmpcur_23069;
            GibCursor tmpcur_23071 = tmpcur_23069 + sizeof(GibFloat);
            GibFloat tmpval_23072 = *(GibFloat *) tmpcur_23071;
            GibCursor tmpcur_23073 = tmpcur_23071 + sizeof(GibFloat);
            GibFloat tmpval_23074 = *(GibFloat *) tmpcur_23073;
            GibCursor tmpcur_23075 = tmpcur_23073 + sizeof(GibFloat);

            return (GibCursorGibFloatProd) {end_r_15723, tmpval_23072};
            break;
        }

      case 0:
        {
            GibFloat tmpval_23076 = *(GibFloat *) tmpcur_23048;
            GibCursor tmpcur_23077 = tmpcur_23048 + sizeof(GibFloat);
            GibFloat tmpval_23078 = *(GibFloat *) tmpcur_23077;
            GibCursor tmpcur_23079 = tmpcur_23077 + sizeof(GibFloat);
            GibFloat tmpval_23080 = *(GibFloat *) tmpcur_23079;
            GibCursor tmpcur_23081 = tmpcur_23079 + sizeof(GibFloat);

            return (GibCursorGibFloatProd) {end_r_15723, tmpval_23080};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_285 = *(uintptr_t *) tmpcur_23048;
            GibCursor tmpcur_23082 = GIB_UNTAG(tagged_tmpcur_285);
            GibCursor tmpaftercur_23083 = tmpcur_23048 + 8;
            uint16_t tmptag_23084 = GIB_GET_TAG(tagged_tmpcur_285);
            GibCursor end_from_tagged_indr_18020 = tmpcur_23082 + tmptag_23084;
            GibCursor jump_18022 = tmpcur_23048 + 8;
            GibCursorGibFloatProd tmp_struct_284 =
                                   get_minz_kdtree(end_from_tagged_indr_18020, tmpcur_23082);
            GibCursor pvrtmp_23085 = tmp_struct_284.field0;
            GibFloat pvrtmp_23086 = tmp_struct_284.field1;

            return (GibCursorGibFloatProd) {end_r_15723, pvrtmp_23086};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_287 = *(uintptr_t *) tmpcur_23048;
            GibCursor tmpcur_23087 = GIB_UNTAG(tagged_tmpcur_287);
            GibCursor tmpaftercur_23088 = tmpcur_23048 + 8;
            uint16_t tmptag_23089 = GIB_GET_TAG(tagged_tmpcur_287);
            GibCursor end_from_tagged_indr_18020 = tmpcur_23087 + tmptag_23089;
            GibCursorGibFloatProd tmp_struct_286 =
                                   get_minz_kdtree(end_from_tagged_indr_18020, tmpcur_23087);
            GibCursor pvrtmp_23090 = tmp_struct_286.field0;
            GibFloat pvrtmp_23091 = tmp_struct_286.field1;

            return (GibCursorGibFloatProd) {pvrtmp_23090, pvrtmp_23091};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_23047");
            exit(1);
        }
    }
}
GibCursorGibFloatProd get_maxy_kdtree(GibCursor end_r_15725,
                                      GibCursor tr_1163_8325_12780)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_23093 = *(GibPackedTag *) tr_1163_8325_12780;
    GibCursor tmpcur_23094 = tr_1163_8325_12780 + 1;


  switch_23138:
    ;
    switch (tmpval_23093) {

      case 2:
        {
            return (GibCursorGibFloatProd) {end_r_15725, 0.0};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_288 = *(uintptr_t *) tmpcur_23094;
            GibCursor tmpcur_23095 = GIB_UNTAG(tagged_tmpcur_288);
            GibCursor tmpaftercur_23096 = tmpcur_23094 + 8;
            uint16_t tmptag_23097 = GIB_GET_TAG(tagged_tmpcur_288);
            GibCursor end_from_tagged_absran_15550 = tmpcur_23095 +
                      tmptag_23097;
            GibFloat tmpval_23098 = *(GibFloat *) tmpaftercur_23096;
            GibCursor tmpcur_23099 = tmpaftercur_23096 + sizeof(GibFloat);
            GibFloat tmpval_23100 = *(GibFloat *) tmpcur_23099;
            GibCursor tmpcur_23101 = tmpcur_23099 + sizeof(GibFloat);
            GibFloat tmpval_23102 = *(GibFloat *) tmpcur_23101;
            GibCursor tmpcur_23103 = tmpcur_23101 + sizeof(GibFloat);
            GibInt tmpval_23104 = *(GibInt *) tmpcur_23103;
            GibCursor tmpcur_23105 = tmpcur_23103 + sizeof(GibInt);
            GibInt tmpval_23106 = *(GibInt *) tmpcur_23105;
            GibCursor tmpcur_23107 = tmpcur_23105 + sizeof(GibInt);
            GibFloat tmpval_23108 = *(GibFloat *) tmpcur_23107;
            GibCursor tmpcur_23109 = tmpcur_23107 + sizeof(GibFloat);
            GibFloat tmpval_23110 = *(GibFloat *) tmpcur_23109;
            GibCursor tmpcur_23111 = tmpcur_23109 + sizeof(GibFloat);
            GibFloat tmpval_23112 = *(GibFloat *) tmpcur_23111;
            GibCursor tmpcur_23113 = tmpcur_23111 + sizeof(GibFloat);
            GibFloat tmpval_23114 = *(GibFloat *) tmpcur_23113;
            GibCursor tmpcur_23115 = tmpcur_23113 + sizeof(GibFloat);
            GibFloat tmpval_23116 = *(GibFloat *) tmpcur_23115;
            GibCursor tmpcur_23117 = tmpcur_23115 + sizeof(GibFloat);
            GibFloat tmpval_23118 = *(GibFloat *) tmpcur_23117;
            GibCursor tmpcur_23119 = tmpcur_23117 + sizeof(GibFloat);
            GibFloat tmpval_23120 = *(GibFloat *) tmpcur_23119;
            GibCursor tmpcur_23121 = tmpcur_23119 + sizeof(GibFloat);

            return (GibCursorGibFloatProd) {end_r_15725, tmpval_23116};
            break;
        }

      case 0:
        {
            GibFloat tmpval_23122 = *(GibFloat *) tmpcur_23094;
            GibCursor tmpcur_23123 = tmpcur_23094 + sizeof(GibFloat);
            GibFloat tmpval_23124 = *(GibFloat *) tmpcur_23123;
            GibCursor tmpcur_23125 = tmpcur_23123 + sizeof(GibFloat);
            GibFloat tmpval_23126 = *(GibFloat *) tmpcur_23125;
            GibCursor tmpcur_23127 = tmpcur_23125 + sizeof(GibFloat);

            return (GibCursorGibFloatProd) {end_r_15725, tmpval_23124};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_290 = *(uintptr_t *) tmpcur_23094;
            GibCursor tmpcur_23128 = GIB_UNTAG(tagged_tmpcur_290);
            GibCursor tmpaftercur_23129 = tmpcur_23094 + 8;
            uint16_t tmptag_23130 = GIB_GET_TAG(tagged_tmpcur_290);
            GibCursor end_from_tagged_indr_18025 = tmpcur_23128 + tmptag_23130;
            GibCursor jump_18027 = tmpcur_23094 + 8;
            GibCursorGibFloatProd tmp_struct_289 =
                                   get_maxy_kdtree(end_from_tagged_indr_18025, tmpcur_23128);
            GibCursor pvrtmp_23131 = tmp_struct_289.field0;
            GibFloat pvrtmp_23132 = tmp_struct_289.field1;

            return (GibCursorGibFloatProd) {end_r_15725, pvrtmp_23132};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_292 = *(uintptr_t *) tmpcur_23094;
            GibCursor tmpcur_23133 = GIB_UNTAG(tagged_tmpcur_292);
            GibCursor tmpaftercur_23134 = tmpcur_23094 + 8;
            uint16_t tmptag_23135 = GIB_GET_TAG(tagged_tmpcur_292);
            GibCursor end_from_tagged_indr_18025 = tmpcur_23133 + tmptag_23135;
            GibCursorGibFloatProd tmp_struct_291 =
                                   get_maxy_kdtree(end_from_tagged_indr_18025, tmpcur_23133);
            GibCursor pvrtmp_23136 = tmp_struct_291.field0;
            GibFloat pvrtmp_23137 = tmp_struct_291.field1;

            return (GibCursorGibFloatProd) {pvrtmp_23136, pvrtmp_23137};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_23093");
            exit(1);
        }
    }
}
GibCursorGibFloatProd get_miny_kdtree(GibCursor end_r_15727,
                                      GibCursor tr_1181_8343_12798)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_23139 = *(GibPackedTag *) tr_1181_8343_12798;
    GibCursor tmpcur_23140 = tr_1181_8343_12798 + 1;


  switch_23184:
    ;
    switch (tmpval_23139) {

      case 2:
        {
            return (GibCursorGibFloatProd) {end_r_15727, 0.0};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_293 = *(uintptr_t *) tmpcur_23140;
            GibCursor tmpcur_23141 = GIB_UNTAG(tagged_tmpcur_293);
            GibCursor tmpaftercur_23142 = tmpcur_23140 + 8;
            uint16_t tmptag_23143 = GIB_GET_TAG(tagged_tmpcur_293);
            GibCursor end_from_tagged_absran_15553 = tmpcur_23141 +
                      tmptag_23143;
            GibFloat tmpval_23144 = *(GibFloat *) tmpaftercur_23142;
            GibCursor tmpcur_23145 = tmpaftercur_23142 + sizeof(GibFloat);
            GibFloat tmpval_23146 = *(GibFloat *) tmpcur_23145;
            GibCursor tmpcur_23147 = tmpcur_23145 + sizeof(GibFloat);
            GibFloat tmpval_23148 = *(GibFloat *) tmpcur_23147;
            GibCursor tmpcur_23149 = tmpcur_23147 + sizeof(GibFloat);
            GibInt tmpval_23150 = *(GibInt *) tmpcur_23149;
            GibCursor tmpcur_23151 = tmpcur_23149 + sizeof(GibInt);
            GibInt tmpval_23152 = *(GibInt *) tmpcur_23151;
            GibCursor tmpcur_23153 = tmpcur_23151 + sizeof(GibInt);
            GibFloat tmpval_23154 = *(GibFloat *) tmpcur_23153;
            GibCursor tmpcur_23155 = tmpcur_23153 + sizeof(GibFloat);
            GibFloat tmpval_23156 = *(GibFloat *) tmpcur_23155;
            GibCursor tmpcur_23157 = tmpcur_23155 + sizeof(GibFloat);
            GibFloat tmpval_23158 = *(GibFloat *) tmpcur_23157;
            GibCursor tmpcur_23159 = tmpcur_23157 + sizeof(GibFloat);
            GibFloat tmpval_23160 = *(GibFloat *) tmpcur_23159;
            GibCursor tmpcur_23161 = tmpcur_23159 + sizeof(GibFloat);
            GibFloat tmpval_23162 = *(GibFloat *) tmpcur_23161;
            GibCursor tmpcur_23163 = tmpcur_23161 + sizeof(GibFloat);
            GibFloat tmpval_23164 = *(GibFloat *) tmpcur_23163;
            GibCursor tmpcur_23165 = tmpcur_23163 + sizeof(GibFloat);
            GibFloat tmpval_23166 = *(GibFloat *) tmpcur_23165;
            GibCursor tmpcur_23167 = tmpcur_23165 + sizeof(GibFloat);

            return (GibCursorGibFloatProd) {end_r_15727, tmpval_23160};
            break;
        }

      case 0:
        {
            GibFloat tmpval_23168 = *(GibFloat *) tmpcur_23140;
            GibCursor tmpcur_23169 = tmpcur_23140 + sizeof(GibFloat);
            GibFloat tmpval_23170 = *(GibFloat *) tmpcur_23169;
            GibCursor tmpcur_23171 = tmpcur_23169 + sizeof(GibFloat);
            GibFloat tmpval_23172 = *(GibFloat *) tmpcur_23171;
            GibCursor tmpcur_23173 = tmpcur_23171 + sizeof(GibFloat);

            return (GibCursorGibFloatProd) {end_r_15727, tmpval_23170};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_295 = *(uintptr_t *) tmpcur_23140;
            GibCursor tmpcur_23174 = GIB_UNTAG(tagged_tmpcur_295);
            GibCursor tmpaftercur_23175 = tmpcur_23140 + 8;
            uint16_t tmptag_23176 = GIB_GET_TAG(tagged_tmpcur_295);
            GibCursor end_from_tagged_indr_18030 = tmpcur_23174 + tmptag_23176;
            GibCursor jump_18032 = tmpcur_23140 + 8;
            GibCursorGibFloatProd tmp_struct_294 =
                                   get_miny_kdtree(end_from_tagged_indr_18030, tmpcur_23174);
            GibCursor pvrtmp_23177 = tmp_struct_294.field0;
            GibFloat pvrtmp_23178 = tmp_struct_294.field1;

            return (GibCursorGibFloatProd) {end_r_15727, pvrtmp_23178};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_297 = *(uintptr_t *) tmpcur_23140;
            GibCursor tmpcur_23179 = GIB_UNTAG(tagged_tmpcur_297);
            GibCursor tmpaftercur_23180 = tmpcur_23140 + 8;
            uint16_t tmptag_23181 = GIB_GET_TAG(tagged_tmpcur_297);
            GibCursor end_from_tagged_indr_18030 = tmpcur_23179 + tmptag_23181;
            GibCursorGibFloatProd tmp_struct_296 =
                                   get_miny_kdtree(end_from_tagged_indr_18030, tmpcur_23179);
            GibCursor pvrtmp_23182 = tmp_struct_296.field0;
            GibFloat pvrtmp_23183 = tmp_struct_296.field1;

            return (GibCursorGibFloatProd) {pvrtmp_23182, pvrtmp_23183};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_23139");
            exit(1);
        }
    }
}
GibCursorGibFloatProd get_maxx_kdtree(GibCursor end_r_15729,
                                      GibCursor tr_1199_8361_12816)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_23185 = *(GibPackedTag *) tr_1199_8361_12816;
    GibCursor tmpcur_23186 = tr_1199_8361_12816 + 1;


  switch_23230:
    ;
    switch (tmpval_23185) {

      case 2:
        {
            return (GibCursorGibFloatProd) {end_r_15729, 0.0};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_298 = *(uintptr_t *) tmpcur_23186;
            GibCursor tmpcur_23187 = GIB_UNTAG(tagged_tmpcur_298);
            GibCursor tmpaftercur_23188 = tmpcur_23186 + 8;
            uint16_t tmptag_23189 = GIB_GET_TAG(tagged_tmpcur_298);
            GibCursor end_from_tagged_absran_15556 = tmpcur_23187 +
                      tmptag_23189;
            GibFloat tmpval_23190 = *(GibFloat *) tmpaftercur_23188;
            GibCursor tmpcur_23191 = tmpaftercur_23188 + sizeof(GibFloat);
            GibFloat tmpval_23192 = *(GibFloat *) tmpcur_23191;
            GibCursor tmpcur_23193 = tmpcur_23191 + sizeof(GibFloat);
            GibFloat tmpval_23194 = *(GibFloat *) tmpcur_23193;
            GibCursor tmpcur_23195 = tmpcur_23193 + sizeof(GibFloat);
            GibInt tmpval_23196 = *(GibInt *) tmpcur_23195;
            GibCursor tmpcur_23197 = tmpcur_23195 + sizeof(GibInt);
            GibInt tmpval_23198 = *(GibInt *) tmpcur_23197;
            GibCursor tmpcur_23199 = tmpcur_23197 + sizeof(GibInt);
            GibFloat tmpval_23200 = *(GibFloat *) tmpcur_23199;
            GibCursor tmpcur_23201 = tmpcur_23199 + sizeof(GibFloat);
            GibFloat tmpval_23202 = *(GibFloat *) tmpcur_23201;
            GibCursor tmpcur_23203 = tmpcur_23201 + sizeof(GibFloat);
            GibFloat tmpval_23204 = *(GibFloat *) tmpcur_23203;
            GibCursor tmpcur_23205 = tmpcur_23203 + sizeof(GibFloat);
            GibFloat tmpval_23206 = *(GibFloat *) tmpcur_23205;
            GibCursor tmpcur_23207 = tmpcur_23205 + sizeof(GibFloat);
            GibFloat tmpval_23208 = *(GibFloat *) tmpcur_23207;
            GibCursor tmpcur_23209 = tmpcur_23207 + sizeof(GibFloat);
            GibFloat tmpval_23210 = *(GibFloat *) tmpcur_23209;
            GibCursor tmpcur_23211 = tmpcur_23209 + sizeof(GibFloat);
            GibFloat tmpval_23212 = *(GibFloat *) tmpcur_23211;
            GibCursor tmpcur_23213 = tmpcur_23211 + sizeof(GibFloat);

            return (GibCursorGibFloatProd) {end_r_15729, tmpval_23204};
            break;
        }

      case 0:
        {
            GibFloat tmpval_23214 = *(GibFloat *) tmpcur_23186;
            GibCursor tmpcur_23215 = tmpcur_23186 + sizeof(GibFloat);
            GibFloat tmpval_23216 = *(GibFloat *) tmpcur_23215;
            GibCursor tmpcur_23217 = tmpcur_23215 + sizeof(GibFloat);
            GibFloat tmpval_23218 = *(GibFloat *) tmpcur_23217;
            GibCursor tmpcur_23219 = tmpcur_23217 + sizeof(GibFloat);

            return (GibCursorGibFloatProd) {end_r_15729, tmpval_23214};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_300 = *(uintptr_t *) tmpcur_23186;
            GibCursor tmpcur_23220 = GIB_UNTAG(tagged_tmpcur_300);
            GibCursor tmpaftercur_23221 = tmpcur_23186 + 8;
            uint16_t tmptag_23222 = GIB_GET_TAG(tagged_tmpcur_300);
            GibCursor end_from_tagged_indr_18035 = tmpcur_23220 + tmptag_23222;
            GibCursor jump_18037 = tmpcur_23186 + 8;
            GibCursorGibFloatProd tmp_struct_299 =
                                   get_maxx_kdtree(end_from_tagged_indr_18035, tmpcur_23220);
            GibCursor pvrtmp_23223 = tmp_struct_299.field0;
            GibFloat pvrtmp_23224 = tmp_struct_299.field1;

            return (GibCursorGibFloatProd) {end_r_15729, pvrtmp_23224};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_302 = *(uintptr_t *) tmpcur_23186;
            GibCursor tmpcur_23225 = GIB_UNTAG(tagged_tmpcur_302);
            GibCursor tmpaftercur_23226 = tmpcur_23186 + 8;
            uint16_t tmptag_23227 = GIB_GET_TAG(tagged_tmpcur_302);
            GibCursor end_from_tagged_indr_18035 = tmpcur_23225 + tmptag_23227;
            GibCursorGibFloatProd tmp_struct_301 =
                                   get_maxx_kdtree(end_from_tagged_indr_18035, tmpcur_23225);
            GibCursor pvrtmp_23228 = tmp_struct_301.field0;
            GibFloat pvrtmp_23229 = tmp_struct_301.field1;

            return (GibCursorGibFloatProd) {pvrtmp_23228, pvrtmp_23229};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_23185");
            exit(1);
        }
    }
}
GibCursorGibFloatProd get_minx_kdtree(GibCursor end_r_15731,
                                      GibCursor tr_1217_8379_12834)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_23231 = *(GibPackedTag *) tr_1217_8379_12834;
    GibCursor tmpcur_23232 = tr_1217_8379_12834 + 1;


  switch_23276:
    ;
    switch (tmpval_23231) {

      case 2:
        {
            return (GibCursorGibFloatProd) {end_r_15731, 0.0};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_303 = *(uintptr_t *) tmpcur_23232;
            GibCursor tmpcur_23233 = GIB_UNTAG(tagged_tmpcur_303);
            GibCursor tmpaftercur_23234 = tmpcur_23232 + 8;
            uint16_t tmptag_23235 = GIB_GET_TAG(tagged_tmpcur_303);
            GibCursor end_from_tagged_absran_15559 = tmpcur_23233 +
                      tmptag_23235;
            GibFloat tmpval_23236 = *(GibFloat *) tmpaftercur_23234;
            GibCursor tmpcur_23237 = tmpaftercur_23234 + sizeof(GibFloat);
            GibFloat tmpval_23238 = *(GibFloat *) tmpcur_23237;
            GibCursor tmpcur_23239 = tmpcur_23237 + sizeof(GibFloat);
            GibFloat tmpval_23240 = *(GibFloat *) tmpcur_23239;
            GibCursor tmpcur_23241 = tmpcur_23239 + sizeof(GibFloat);
            GibInt tmpval_23242 = *(GibInt *) tmpcur_23241;
            GibCursor tmpcur_23243 = tmpcur_23241 + sizeof(GibInt);
            GibInt tmpval_23244 = *(GibInt *) tmpcur_23243;
            GibCursor tmpcur_23245 = tmpcur_23243 + sizeof(GibInt);
            GibFloat tmpval_23246 = *(GibFloat *) tmpcur_23245;
            GibCursor tmpcur_23247 = tmpcur_23245 + sizeof(GibFloat);
            GibFloat tmpval_23248 = *(GibFloat *) tmpcur_23247;
            GibCursor tmpcur_23249 = tmpcur_23247 + sizeof(GibFloat);
            GibFloat tmpval_23250 = *(GibFloat *) tmpcur_23249;
            GibCursor tmpcur_23251 = tmpcur_23249 + sizeof(GibFloat);
            GibFloat tmpval_23252 = *(GibFloat *) tmpcur_23251;
            GibCursor tmpcur_23253 = tmpcur_23251 + sizeof(GibFloat);
            GibFloat tmpval_23254 = *(GibFloat *) tmpcur_23253;
            GibCursor tmpcur_23255 = tmpcur_23253 + sizeof(GibFloat);
            GibFloat tmpval_23256 = *(GibFloat *) tmpcur_23255;
            GibCursor tmpcur_23257 = tmpcur_23255 + sizeof(GibFloat);
            GibFloat tmpval_23258 = *(GibFloat *) tmpcur_23257;
            GibCursor tmpcur_23259 = tmpcur_23257 + sizeof(GibFloat);

            return (GibCursorGibFloatProd) {end_r_15731, tmpval_23248};
            break;
        }

      case 0:
        {
            GibFloat tmpval_23260 = *(GibFloat *) tmpcur_23232;
            GibCursor tmpcur_23261 = tmpcur_23232 + sizeof(GibFloat);
            GibFloat tmpval_23262 = *(GibFloat *) tmpcur_23261;
            GibCursor tmpcur_23263 = tmpcur_23261 + sizeof(GibFloat);
            GibFloat tmpval_23264 = *(GibFloat *) tmpcur_23263;
            GibCursor tmpcur_23265 = tmpcur_23263 + sizeof(GibFloat);

            return (GibCursorGibFloatProd) {end_r_15731, tmpval_23260};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_305 = *(uintptr_t *) tmpcur_23232;
            GibCursor tmpcur_23266 = GIB_UNTAG(tagged_tmpcur_305);
            GibCursor tmpaftercur_23267 = tmpcur_23232 + 8;
            uint16_t tmptag_23268 = GIB_GET_TAG(tagged_tmpcur_305);
            GibCursor end_from_tagged_indr_18040 = tmpcur_23266 + tmptag_23268;
            GibCursor jump_18042 = tmpcur_23232 + 8;
            GibCursorGibFloatProd tmp_struct_304 =
                                   get_minx_kdtree(end_from_tagged_indr_18040, tmpcur_23266);
            GibCursor pvrtmp_23269 = tmp_struct_304.field0;
            GibFloat pvrtmp_23270 = tmp_struct_304.field1;

            return (GibCursorGibFloatProd) {end_r_15731, pvrtmp_23270};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_307 = *(uintptr_t *) tmpcur_23232;
            GibCursor tmpcur_23271 = GIB_UNTAG(tagged_tmpcur_307);
            GibCursor tmpaftercur_23272 = tmpcur_23232 + 8;
            uint16_t tmptag_23273 = GIB_GET_TAG(tagged_tmpcur_307);
            GibCursor end_from_tagged_indr_18040 = tmpcur_23271 + tmptag_23273;
            GibCursorGibFloatProd tmp_struct_306 =
                                   get_minx_kdtree(end_from_tagged_indr_18040, tmpcur_23271);
            GibCursor pvrtmp_23274 = tmp_struct_306.field0;
            GibFloat pvrtmp_23275 = tmp_struct_306.field1;

            return (GibCursorGibFloatProd) {pvrtmp_23274, pvrtmp_23275};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_23231");
            exit(1);
        }
    }
}
GibFloat get_coord_point3d(GibInt axis_1247_8409_12852,
                           GibFloatGibFloatGibFloatProd pt_1248_8410_12853)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_11956_12858 = axis_1247_8409_12852 == 0;

    if (fltIf_11956_12858) {
        return pt_1248_8410_12853.field0;
    } else {
        GibBool fltIf_11957_12859 = axis_1247_8409_12852 == 1;

        if (fltIf_11957_12859) {
            return pt_1248_8410_12853.field1;
        } else {
            return pt_1248_8410_12853.field2;
        }
    }
}
GibInt getNextAxis_3d(GibInt i_1253_8415_12860)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibInt fltPrm_11958_12861 = i_1253_8415_12860 + 1;
    GibInt tailprim_17543 = fltPrm_11958_12861 % 3;

    return tailprim_17543;
}
GibVector *sort_point3d(GibInt axis_1254_8416_12862,
                        GibVector *ls_1255_8417_12863)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibInt fltAppE_11959_12865 = gib_vector_length(ls_1255_8417_12863);
    GibInt n__1294_9222_13216_13961 =  maxInt(fltAppE_11959_12865, 0);
    GibInt tmp_308 = sizeof(GibFloatGibFloatGibFloatProd);
    GibVector *vec_1295_9223_13217_13962 =
              gib_vector_alloc(n__1294_9222_13216_13961, tmp_308);
    GibVector *vec1_1296_9224_13218_13963 =
               generate_loop_3495_5969(vec_1295_9223_13217_13962, 0, n__1294_9222_13216_13961, ls_1255_8417_12863);
    GibBool fltIf_11960_12867 = axis_1254_8416_12862 == 0;

    if (fltIf_11960_12867) {
        GibVector *tailprim_17544 =
                  gib_vector_inplace_sort(vec1_1296_9224_13218_13963,
                                          cmpx_point3d);

        return tailprim_17544;
    } else {
        GibBool fltIf_11961_12869 = axis_1254_8416_12862 == 1;

        if (fltIf_11961_12869) {
            GibVector *tailprim_17545 =
                      gib_vector_inplace_sort(vec1_1296_9224_13218_13963,
                                              cmpy_point3d);

            return tailprim_17545;
        } else {
            GibVector *tailprim_17546 =
                      gib_vector_inplace_sort(vec1_1296_9224_13218_13963,
                                              cmpz_point3d);

            return tailprim_17546;
        }
    }
}
GibFloat dist_point3d(GibFloatGibFloatGibFloatProd a_1265_8421_12872,
                      GibFloatGibFloatGibFloatProd b_1266_8422_12873)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibFloat d1_1275_8431_12882 = a_1265_8421_12872.field0 -
             b_1266_8422_12873.field0;
    GibFloat d2_1276_8432_12883 = a_1265_8421_12872.field1 -
             b_1266_8422_12873.field1;
    GibFloat d3_1277_8433_12884 = a_1265_8421_12872.field2 -
             b_1266_8422_12873.field2;
    GibFloat fltPrm_11963_12885 = d1_1275_8431_12882 * d1_1275_8431_12882;
    GibFloat fltPrm_11964_12886 = d2_1276_8432_12883 * d2_1276_8432_12883;
    GibFloat fltPrm_11962_12887 = fltPrm_11963_12885 + fltPrm_11964_12886;
    GibFloat fltPrm_11965_12888 = d3_1277_8433_12884 * d3_1277_8433_12884;
    GibFloat tailprim_17547 = fltPrm_11962_12887 + fltPrm_11965_12888;

    return tailprim_17547;
}
GibFloat float_abs(GibFloat f_1280_8434_12889)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_11966_12890 = f_1280_8434_12889 < 0.0;

    if (fltIf_11966_12890) {
        GibFloat fltPrm_11967_12891 = 0.0 - 1.0;
        GibFloat tailprim_17548 = f_1280_8434_12889 * fltPrm_11967_12891;

        return tailprim_17548;
    } else {
        return f_1280_8434_12889;
    }
}
GibBool eq_point3d(GibFloatGibFloatGibFloatProd a_1281_8435_12892,
                   GibFloatGibFloatGibFloatProd b_1282_8436_12893)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltPrm_11968_12902 = a_1281_8435_12892.field0 ==
            b_1282_8436_12893.field0;
    GibBool fltPrm_11970_12903 = a_1281_8435_12892.field1 ==
            b_1282_8436_12893.field1;
    GibBool fltPrm_11971_12904 = a_1281_8435_12892.field2 ==
            b_1282_8436_12893.field2;
    GibBool fltPrm_11969_12905 = fltPrm_11970_12903 && fltPrm_11971_12904;
    GibBool tailprim_17549 = fltPrm_11968_12902 && fltPrm_11969_12905;

    return tailprim_17549;
}
GibVector *masspointsInBox_seq(GibFloatGibFloatGibFloatGibFloatProd box_1343_8471_12906,
                               GibVector *mpts_1344_8472_12907)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibInt fltAppE_11972_12910 = gib_vector_length(mpts_1344_8472_12907);
    GibInt n__1294_9794_13222_13967 =  maxInt(fltAppE_11972_12910, 0);
    GibInt tmp_310 = sizeof(GibInt);
    GibVector *vec_1295_9795_13223_13968 =
              gib_vector_alloc(n__1294_9794_13222_13967, tmp_310);
    GibVector *vec1_1296_9796_13224_13969 =
               generate_loop_3493_5975(vec_1295_9795_13223_13968, 0, n__1294_9794_13222_13967, mpts_1344_8472_12907, (GibFloatGibFloatGibFloatGibFloatProd) {box_1343_8471_12906.field0, box_1343_8471_12906.field1, box_1343_8471_12906.field2, box_1343_8471_12906.field3});
    GibInt fltAppE_12046_13227_13972 =
           gib_vector_length(vec1_1296_9796_13224_13969);
    GibInt num_ones_1585_9165_10770_12912 =
            foldl_loop_3499_5967(0, fltAppE_12046_13227_13972, 0, vec1_1296_9796_13224_13969);
    GibInt tmp_309 = sizeof(GibFloatGibFloatGibFloatProd);
    GibVector *to_1586_9166_10771_12913 =
              gib_vector_alloc(num_ones_1585_9165_10770_12912, tmp_309);
    GibInt len_idxs_1587_9167_10772_12914 =
           gib_vector_length(vec1_1296_9796_13224_13969);
    GibVector *tailapp_17550 =
               filter_loop_3498(vec1_1296_9796_13224_13969, 0, 0, len_idxs_1587_9167_10772_12914, mpts_1344_8472_12907, to_1586_9166_10771_12913);

    return tailapp_17550;
}
GibFloatGibFloatGibFloatProd calcCentroid_seq(GibVector *mpts_1359_8483_12915)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibInt fltAppE_11973_12918 = gib_vector_length(mpts_1359_8483_12915);
    GibFloatGibFloatGibFloatProd tmp_struct_311 =
                                  foldl_loop_3488_6015(0, fltAppE_11973_12918, (GibFloatGibFloatGibFloatProd) {0.0, 0.0, 0.0}, mpts_1359_8483_12915);
    GibFloat pvrtmp_23287 = tmp_struct_311.field0;
    GibFloat pvrtmp_23288 = tmp_struct_311.field1;
    GibFloat pvrtmp_23289 = tmp_struct_311.field2;
    GibFloat fltPrd_11974_12924 = pvrtmp_23287 / pvrtmp_23289;
    GibFloat fltPrd_11975_12925 = pvrtmp_23288 / pvrtmp_23289;

    return (GibFloatGibFloatGibFloatProd) {fltPrd_11974_12924,
                                           fltPrd_11975_12925, pvrtmp_23289};
}
GibCursorGibFloatGibFloatProd calcAccel_seq(GibCursor end_r_15733,
                                            GibFloatGibFloatGibFloatProd mpt_1376_8489_12926,
                                            GibCursor tr_1377_8490_12927)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_23293 = *(GibPackedTag *) tr_1377_8490_12927;
    GibCursor tmpcur_23294 = tr_1377_8490_12927 + 1;


  switch_23390:
    ;
    switch (tmpval_23293) {

      case 0:
        {
            return (GibCursorGibFloatGibFloatProd) {end_r_15733, 0.0, 0.0};
            break;
        }

      case 1:
        {
            GibFloat tmpval_23297 = *(GibFloat *) tmpcur_23294;
            GibCursor tmpcur_23298 = tmpcur_23294 + sizeof(GibFloat);
            GibFloat tmpval_23299 = *(GibFloat *) tmpcur_23298;
            GibCursor tmpcur_23300 = tmpcur_23298 + sizeof(GibFloat);
            GibFloat tmpval_23301 = *(GibFloat *) tmpcur_23300;
            GibCursor tmpcur_23302 = tmpcur_23300 + sizeof(GibFloat);
            GibBool fltPrm_11977_12939 = mpt_1376_8489_12926.field0 ==
                    tmpval_23297;
            GibBool fltPrm_11979_12940 = mpt_1376_8489_12926.field1 ==
                    tmpval_23299;
            GibBool fltPrm_11980_12941 = mpt_1376_8489_12926.field2 ==
                    tmpval_23301;
            GibBool fltPrm_11978_12942 = fltPrm_11979_12940 &&
                    fltPrm_11980_12941;
            GibBool fltIf_11976_12943 = fltPrm_11977_12939 &&
                    fltPrm_11978_12942;

            if (fltIf_11976_12943) {
                return (GibCursorGibFloatGibFloatProd) {end_r_15733, 0.0, 0.0};
            } else {
                GibFloat dx_1413_8526_10783_12944 = mpt_1376_8489_12926.field0 -
                         tmpval_23297;
                GibFloat dy_1414_8527_10784_12945 = mpt_1376_8489_12926.field1 -
                         tmpval_23299;
                GibFloat fltPrm_11981_12946 = dx_1413_8526_10783_12944 *
                         dx_1413_8526_10783_12944;
                GibFloat fltPrm_11982_12947 = dy_1414_8527_10784_12945 *
                         dy_1414_8527_10784_12945;
                GibFloat rsqr_1415_8528_10785_12948 = fltPrm_11981_12946 +
                         fltPrm_11982_12947;
                GibFloat r_1416_8529_10786_12949 =
                         sqrt(rsqr_1415_8528_10785_12948);
                GibFloat fltPrm_11983_12950 = mpt_1376_8489_12926.field2 *
                         tmpval_23301;
                GibFloat fltPrm_11984_12951 = rsqr_1415_8528_10785_12948 *
                         r_1416_8529_10786_12949;
                GibFloat s_1417_8530_10787_12952 = fltPrm_11983_12950 /
                         fltPrm_11984_12951;
                GibFloat fltPrd_11985_12953 = dx_1413_8526_10783_12944 *
                         s_1417_8530_10787_12952;
                GibFloat fltPrd_11986_12954 = dy_1414_8527_10784_12945 *
                         s_1417_8530_10787_12952;

                return (GibCursorGibFloatGibFloatProd) {end_r_15733,
                                                        fltPrd_11985_12953,
                                                        fltPrd_11986_12954};
            }
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_318 = *(uintptr_t *) tmpcur_23294;
            GibCursor tmpcur_23307 = GIB_UNTAG(tagged_tmpcur_318);
            GibCursor tmpaftercur_23308 = tmpcur_23294 + 8;
            uint16_t tmptag_23309 = GIB_GET_TAG(tagged_tmpcur_318);
            GibCursor end_from_tagged_absran_15562 = tmpcur_23307 +
                      tmptag_23309;
            uintptr_t tagged_tmpcur_317 = *(uintptr_t *) tmpaftercur_23308;
            GibCursor tmpcur_23310 = GIB_UNTAG(tagged_tmpcur_317);
            GibCursor tmpaftercur_23311 = tmpaftercur_23308 + 8;
            uint16_t tmptag_23312 = GIB_GET_TAG(tagged_tmpcur_317);
            GibCursor end_from_tagged_absran_15563 = tmpcur_23310 +
                      tmptag_23312;
            uintptr_t tagged_tmpcur_316 = *(uintptr_t *) tmpaftercur_23311;
            GibCursor tmpcur_23313 = GIB_UNTAG(tagged_tmpcur_316);
            GibCursor tmpaftercur_23314 = tmpaftercur_23311 + 8;
            uint16_t tmptag_23315 = GIB_GET_TAG(tagged_tmpcur_316);
            GibCursor end_from_tagged_absran_15564 = tmpcur_23313 +
                      tmptag_23315;
            GibFloat tmpval_23316 = *(GibFloat *) tmpaftercur_23314;
            GibCursor tmpcur_23317 = tmpaftercur_23314 + sizeof(GibFloat);
            GibFloat tmpval_23318 = *(GibFloat *) tmpcur_23317;
            GibCursor tmpcur_23319 = tmpcur_23317 + sizeof(GibFloat);
            GibFloat tmpval_23320 = *(GibFloat *) tmpcur_23319;
            GibCursor tmpcur_23321 = tmpcur_23319 + sizeof(GibFloat);
            GibInt tmpval_23322 = *(GibInt *) tmpcur_23321;
            GibCursor tmpcur_23323 = tmpcur_23321 + sizeof(GibInt);
            GibFloat tmpval_23324 = *(GibFloat *) tmpcur_23323;
            GibCursor tmpcur_23325 = tmpcur_23323 + sizeof(GibFloat);
            GibFloat d1_1576_8683_13095_13981 = mpt_1376_8489_12926.field0 -
                     tmpval_23316;
            GibFloat d2_1577_8684_13096_13982 = mpt_1376_8489_12926.field1 -
                     tmpval_23318;
            GibFloat fltPrm_12023_13097_13983 = d1_1576_8683_13095_13981 *
                     d1_1576_8683_13095_13981;
            GibFloat fltPrm_12024_13098_13984 = d2_1577_8684_13096_13982 *
                     d2_1577_8684_13096_13982;
            GibFloat r2_1421_8534_10791_12970 = fltPrm_12023_13097_13983 +
                     fltPrm_12024_13098_13984;
            GibFloat widthsq_1422_8535_10792_12971 = tmpval_23324 *
                     tmpval_23324;
            GibBool fltIf_11987_12972 = r2_1421_8534_10791_12970 <
                    widthsq_1422_8535_10792_12971;

            if (fltIf_11987_12972) {
                // gib_shadowstack_push(rstack, tmpcur_23313, end_r_15733, Stk,
                //                      BH_Tree_T);
                // gib_shadowstack_push(rstack, tmpcur_23310, end_r_15733, Stk,
                //                      BH_Tree_T);
                // gib_shadowstack_push(rstack, tmpcur_23307, end_r_15733, Stk,
                //                      BH_Tree_T);

                GibCursorGibFloatGibFloatProd tmp_struct_312 =
                                               calcAccel_seq(end_r_15733, (GibFloatGibFloatGibFloatProd) {mpt_1376_8489_12926.field0, mpt_1376_8489_12926.field1, mpt_1376_8489_12926.field2}, tmpcur_23325);
                GibCursor pvrtmp_23333 = tmp_struct_312.field0;
                GibFloat pvrtmp_23334 = tmp_struct_312.field1;
                GibFloat pvrtmp_23335 = tmp_struct_312.field2;

                // frame = gib_shadowstack_pop(rstack);
                // tmpcur_23307 = frame->ptr;
                // end_r_15733 = frame->endptr;
                // frame = gib_shadowstack_pop(rstack);
                // tmpcur_23310 = frame->ptr;
                // end_r_15733 = frame->endptr;
                // frame = gib_shadowstack_pop(rstack);
                // tmpcur_23313 = frame->ptr;
                // end_r_15733 = frame->endptr;
                // gib_shadowstack_push(rstack, tmpcur_23313, pvrtmp_23333, Stk,
                //                      BH_Tree_T);
                // gib_shadowstack_push(rstack, tmpcur_23310, pvrtmp_23333, Stk,
                //                      BH_Tree_T);

                GibCursorGibFloatGibFloatProd tmp_struct_313 =
                                               calcAccel_seq(end_from_tagged_absran_15562, (GibFloatGibFloatGibFloatProd) {mpt_1376_8489_12926.field0, mpt_1376_8489_12926.field1, mpt_1376_8489_12926.field2}, tmpcur_23307);
                GibCursor pvrtmp_23341 = tmp_struct_313.field0;
                GibFloat pvrtmp_23342 = tmp_struct_313.field1;
                GibFloat pvrtmp_23343 = tmp_struct_313.field2;

                // frame = gib_shadowstack_pop(rstack);
                // tmpcur_23310 = frame->ptr;
                // pvrtmp_23333 = frame->endptr;
                // frame = gib_shadowstack_pop(rstack);
                // tmpcur_23313 = frame->ptr;
                // pvrtmp_23333 = frame->endptr;
                // gib_shadowstack_push(rstack, tmpcur_23313, pvrtmp_23341, Stk,
                //                      BH_Tree_T);

                GibCursorGibFloatGibFloatProd tmp_struct_314 =
                                               calcAccel_seq(end_from_tagged_absran_15563, (GibFloatGibFloatGibFloatProd) {mpt_1376_8489_12926.field0, mpt_1376_8489_12926.field1, mpt_1376_8489_12926.field2}, tmpcur_23310);
                GibCursor pvrtmp_23349 = tmp_struct_314.field0;
                GibFloat pvrtmp_23350 = tmp_struct_314.field1;
                GibFloat pvrtmp_23351 = tmp_struct_314.field2;

                // frame = gib_shadowstack_pop(rstack);
                // tmpcur_23313 = frame->ptr;
                // pvrtmp_23341 = frame->endptr;

                GibCursorGibFloatGibFloatProd tmp_struct_315 =
                                               calcAccel_seq(end_from_tagged_absran_15564, (GibFloatGibFloatGibFloatProd) {mpt_1376_8489_12926.field0, mpt_1376_8489_12926.field1, mpt_1376_8489_12926.field2}, tmpcur_23313);
                GibCursor pvrtmp_23357 = tmp_struct_315.field0;
                GibFloat pvrtmp_23358 = tmp_struct_315.field1;
                GibFloat pvrtmp_23359 = tmp_struct_315.field2;
                GibFloat fltPrm_11990_12985 = pvrtmp_23334 + pvrtmp_23342;
                GibFloat fltPrm_11989_12986 = fltPrm_11990_12985 + pvrtmp_23350;
                GibFloat fltPrd_11988_12987 = fltPrm_11989_12986 + pvrtmp_23358;
                GibFloat fltPrm_11993_12988 = pvrtmp_23335 + pvrtmp_23343;
                GibFloat fltPrm_11992_12989 = fltPrm_11993_12988 + pvrtmp_23351;
                GibFloat fltPrd_11991_12990 = fltPrm_11992_12989 + pvrtmp_23359;

                return (GibCursorGibFloatGibFloatProd) {pvrtmp_23357,
                                                        fltPrd_11988_12987,
                                                        fltPrd_11991_12990};
            } else {
                GibBool fltPrm_11995_12999 = mpt_1376_8489_12926.field0 ==
                        tmpval_23316;
                GibBool fltPrm_11997_13000 = mpt_1376_8489_12926.field1 ==
                        tmpval_23318;
                GibBool fltPrm_11998_13001 = mpt_1376_8489_12926.field2 ==
                        tmpval_23320;
                GibBool fltPrm_11996_13002 = fltPrm_11997_13000 &&
                        fltPrm_11998_13001;
                GibBool fltIf_11994_13003 = fltPrm_11995_12999 &&
                        fltPrm_11996_13002;

                if (fltIf_11994_13003) {
                    return (GibCursorGibFloatGibFloatProd) {end_r_15733, 0.0,
                                                            0.0};
                } else {
                    GibFloat dx_1413_8526_10801_13004 =
                             mpt_1376_8489_12926.field0 - tmpval_23316;
                    GibFloat dy_1414_8527_10802_13005 =
                             mpt_1376_8489_12926.field1 - tmpval_23318;
                    GibFloat fltPrm_11999_13006 = dx_1413_8526_10801_13004 *
                             dx_1413_8526_10801_13004;
                    GibFloat fltPrm_12000_13007 = dy_1414_8527_10802_13005 *
                             dy_1414_8527_10802_13005;
                    GibFloat rsqr_1415_8528_10803_13008 = fltPrm_11999_13006 +
                             fltPrm_12000_13007;
                    GibFloat r_1416_8529_10804_13009 =
                             sqrt(rsqr_1415_8528_10803_13008);
                    GibFloat fltPrm_12001_13010 = mpt_1376_8489_12926.field2 *
                             tmpval_23320;
                    GibFloat fltPrm_12002_13011 = rsqr_1415_8528_10803_13008 *
                             r_1416_8529_10804_13009;
                    GibFloat s_1417_8530_10805_13012 = fltPrm_12001_13010 /
                             fltPrm_12002_13011;
                    GibFloat fltPrd_12003_13013 = dx_1413_8526_10801_13004 *
                             s_1417_8530_10805_13012;
                    GibFloat fltPrd_12004_13014 = dy_1414_8527_10802_13005 *
                             s_1417_8530_10805_13012;

                    return (GibCursorGibFloatGibFloatProd) {end_r_15733,
                                                            fltPrd_12003_13013,
                                                            fltPrd_12004_13014};
                }
            }
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_320 = *(uintptr_t *) tmpcur_23294;
            GibCursor tmpcur_23368 = GIB_UNTAG(tagged_tmpcur_320);
            GibCursor tmpaftercur_23369 = tmpcur_23294 + 8;
            uint16_t tmptag_23370 = GIB_GET_TAG(tagged_tmpcur_320);
            GibCursor end_from_tagged_indr_18045 = tmpcur_23368 + tmptag_23370;
            GibCursor jump_18047 = tmpcur_23294 + 8;
            GibCursorGibFloatGibFloatProd tmp_struct_319 =
                                           calcAccel_seq(end_from_tagged_indr_18045, (GibFloatGibFloatGibFloatProd) {mpt_1376_8489_12926.field0, mpt_1376_8489_12926.field1, mpt_1376_8489_12926.field2}, tmpcur_23368);
            GibCursor pvrtmp_23374 = tmp_struct_319.field0;
            GibFloat pvrtmp_23375 = tmp_struct_319.field1;
            GibFloat pvrtmp_23376 = tmp_struct_319.field2;

            return (GibCursorGibFloatGibFloatProd) {end_r_15733, pvrtmp_23375,
                                                    pvrtmp_23376};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_322 = *(uintptr_t *) tmpcur_23294;
            GibCursor tmpcur_23379 = GIB_UNTAG(tagged_tmpcur_322);
            GibCursor tmpaftercur_23380 = tmpcur_23294 + 8;
            uint16_t tmptag_23381 = GIB_GET_TAG(tagged_tmpcur_322);
            GibCursor end_from_tagged_indr_18045 = tmpcur_23379 + tmptag_23381;
            GibCursorGibFloatGibFloatProd tmp_struct_321 =
                                           calcAccel_seq(end_from_tagged_indr_18045, (GibFloatGibFloatGibFloatProd) {mpt_1376_8489_12926.field0, mpt_1376_8489_12926.field1, mpt_1376_8489_12926.field2}, tmpcur_23379);
            GibCursor pvrtmp_23385 = tmp_struct_321.field0;
            GibFloat pvrtmp_23386 = tmp_struct_321.field1;
            GibFloat pvrtmp_23387 = tmp_struct_321.field2;

            return (GibCursorGibFloatGibFloatProd) {pvrtmp_23385, pvrtmp_23386,
                                                    pvrtmp_23387};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_23293");
            exit(1);
        }
    }
}
GibCursorGibIntProd getTotalPoints_qtree(GibCursor end_r_15735,
                                         GibCursor tr_1435_8548_13031)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_23391 = *(GibPackedTag *) tr_1435_8548_13031;
    GibCursor tmpcur_23392 = tr_1435_8548_13031 + 1;


  switch_23428:
    ;
    switch (tmpval_23391) {

      case 0:
        {
            return (GibCursorGibIntProd) {end_r_15735, 0};
            break;
        }

      case 1:
        {
            GibFloat tmpval_23393 = *(GibFloat *) tmpcur_23392;
            GibCursor tmpcur_23394 = tmpcur_23392 + sizeof(GibFloat);
            GibFloat tmpval_23395 = *(GibFloat *) tmpcur_23394;
            GibCursor tmpcur_23396 = tmpcur_23394 + sizeof(GibFloat);
            GibFloat tmpval_23397 = *(GibFloat *) tmpcur_23396;
            GibCursor tmpcur_23398 = tmpcur_23396 + sizeof(GibFloat);

            return (GibCursorGibIntProd) {end_r_15735, 1};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_325 = *(uintptr_t *) tmpcur_23392;
            GibCursor tmpcur_23399 = GIB_UNTAG(tagged_tmpcur_325);
            GibCursor tmpaftercur_23400 = tmpcur_23392 + 8;
            uint16_t tmptag_23401 = GIB_GET_TAG(tagged_tmpcur_325);
            GibCursor end_from_tagged_absran_15569 = tmpcur_23399 +
                      tmptag_23401;
            uintptr_t tagged_tmpcur_324 = *(uintptr_t *) tmpaftercur_23400;
            GibCursor tmpcur_23402 = GIB_UNTAG(tagged_tmpcur_324);
            GibCursor tmpaftercur_23403 = tmpaftercur_23400 + 8;
            uint16_t tmptag_23404 = GIB_GET_TAG(tagged_tmpcur_324);
            GibCursor end_from_tagged_absran_15570 = tmpcur_23402 +
                      tmptag_23404;
            uintptr_t tagged_tmpcur_323 = *(uintptr_t *) tmpaftercur_23403;
            GibCursor tmpcur_23405 = GIB_UNTAG(tagged_tmpcur_323);
            GibCursor tmpaftercur_23406 = tmpaftercur_23403 + 8;
            uint16_t tmptag_23407 = GIB_GET_TAG(tagged_tmpcur_323);
            GibCursor end_from_tagged_absran_15571 = tmpcur_23405 +
                      tmptag_23407;
            GibFloat tmpval_23408 = *(GibFloat *) tmpaftercur_23406;
            GibCursor tmpcur_23409 = tmpaftercur_23406 + sizeof(GibFloat);
            GibFloat tmpval_23410 = *(GibFloat *) tmpcur_23409;
            GibCursor tmpcur_23411 = tmpcur_23409 + sizeof(GibFloat);
            GibFloat tmpval_23412 = *(GibFloat *) tmpcur_23411;
            GibCursor tmpcur_23413 = tmpcur_23411 + sizeof(GibFloat);
            GibInt tmpval_23414 = *(GibInt *) tmpcur_23413;
            GibCursor tmpcur_23415 = tmpcur_23413 + sizeof(GibInt);
            GibFloat tmpval_23416 = *(GibFloat *) tmpcur_23415;
            GibCursor tmpcur_23417 = tmpcur_23415 + sizeof(GibFloat);

            return (GibCursorGibIntProd) {end_r_15735, tmpval_23414};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_327 = *(uintptr_t *) tmpcur_23392;
            GibCursor tmpcur_23418 = GIB_UNTAG(tagged_tmpcur_327);
            GibCursor tmpaftercur_23419 = tmpcur_23392 + 8;
            uint16_t tmptag_23420 = GIB_GET_TAG(tagged_tmpcur_327);
            GibCursor end_from_tagged_indr_18050 = tmpcur_23418 + tmptag_23420;
            GibCursor jump_18052 = tmpcur_23392 + 8;
            GibCursorGibIntProd tmp_struct_326 =
                                 getTotalPoints_qtree(end_from_tagged_indr_18050, tmpcur_23418);
            GibCursor pvrtmp_23421 = tmp_struct_326.field0;
            GibInt pvrtmp_23422 = tmp_struct_326.field1;

            return (GibCursorGibIntProd) {end_r_15735, pvrtmp_23422};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_329 = *(uintptr_t *) tmpcur_23392;
            GibCursor tmpcur_23423 = GIB_UNTAG(tagged_tmpcur_329);
            GibCursor tmpaftercur_23424 = tmpcur_23392 + 8;
            uint16_t tmptag_23425 = GIB_GET_TAG(tagged_tmpcur_329);
            GibCursor end_from_tagged_indr_18050 = tmpcur_23423 + tmptag_23425;
            GibCursorGibIntProd tmp_struct_328 =
                                 getTotalPoints_qtree(end_from_tagged_indr_18050, tmpcur_23423);
            GibCursor pvrtmp_23426 = tmp_struct_328.field0;
            GibInt pvrtmp_23427 = tmp_struct_328.field1;

            return (GibCursorGibIntProd) {pvrtmp_23426, pvrtmp_23427};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_23391");
            exit(1);
        }
    }
}
GibFloat sum_mass_points(GibVector *mpts_1502_8615_13044)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibInt fltAppE_12009_13047 = gib_vector_length(mpts_1502_8615_13044);
    GibFloat tailapp_17584 =
              foldl_loop_3487_6017(0, fltAppE_12009_13047, 0.0, mpts_1502_8615_13044);

    return tailapp_17584;
}
GibCursorGibCursorGibIntProd countLeavesQtree(GibCursor end_r_15737,
                                              GibCursor tr_1509_8616_13048)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_23429 = *(GibPackedTag *) tr_1509_8616_13048;
    GibCursor tmpcur_23430 = tr_1509_8616_13048 + 1;


  switch_23480:
    ;
    switch (tmpval_23429) {

      case 0:
        {
            GibCursor jump_17587 = tr_1509_8616_13048 + 1;

            return (GibCursorGibCursorGibIntProd) {end_r_15737, jump_17587, 0};
            break;
        }

      case 1:
        {
            GibFloat tmpval_23431 = *(GibFloat *) tmpcur_23430;
            GibCursor tmpcur_23432 = tmpcur_23430 + sizeof(GibFloat);
            GibFloat tmpval_23433 = *(GibFloat *) tmpcur_23432;
            GibCursor tmpcur_23434 = tmpcur_23432 + sizeof(GibFloat);
            GibFloat tmpval_23435 = *(GibFloat *) tmpcur_23434;
            GibCursor tmpcur_23436 = tmpcur_23434 + sizeof(GibFloat);
            GibCursor jump_17590 = tmpcur_23434 + 4;

            return (GibCursorGibCursorGibIntProd) {end_r_15737, jump_17590, 1};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_336 = *(uintptr_t *) tmpcur_23430;
            GibCursor tmpcur_23437 = GIB_UNTAG(tagged_tmpcur_336);
            GibCursor tmpaftercur_23438 = tmpcur_23430 + 8;
            uint16_t tmptag_23439 = GIB_GET_TAG(tagged_tmpcur_336);
            GibCursor end_from_tagged_absran_15576 = tmpcur_23437 +
                      tmptag_23439;
            uintptr_t tagged_tmpcur_335 = *(uintptr_t *) tmpaftercur_23438;
            GibCursor tmpcur_23440 = GIB_UNTAG(tagged_tmpcur_335);
            GibCursor tmpaftercur_23441 = tmpaftercur_23438 + 8;
            uint16_t tmptag_23442 = GIB_GET_TAG(tagged_tmpcur_335);
            GibCursor end_from_tagged_absran_15577 = tmpcur_23440 +
                      tmptag_23442;
            uintptr_t tagged_tmpcur_334 = *(uintptr_t *) tmpaftercur_23441;
            GibCursor tmpcur_23443 = GIB_UNTAG(tagged_tmpcur_334);
            GibCursor tmpaftercur_23444 = tmpaftercur_23441 + 8;
            uint16_t tmptag_23445 = GIB_GET_TAG(tagged_tmpcur_334);
            GibCursor end_from_tagged_absran_15578 = tmpcur_23443 +
                      tmptag_23445;
            GibFloat tmpval_23446 = *(GibFloat *) tmpaftercur_23444;
            GibCursor tmpcur_23447 = tmpaftercur_23444 + sizeof(GibFloat);
            GibFloat tmpval_23448 = *(GibFloat *) tmpcur_23447;
            GibCursor tmpcur_23449 = tmpcur_23447 + sizeof(GibFloat);
            GibFloat tmpval_23450 = *(GibFloat *) tmpcur_23449;
            GibCursor tmpcur_23451 = tmpcur_23449 + sizeof(GibFloat);
            GibInt tmpval_23452 = *(GibInt *) tmpcur_23451;
            GibCursor tmpcur_23453 = tmpcur_23451 + sizeof(GibInt);
            GibFloat tmpval_23454 = *(GibFloat *) tmpcur_23453;
            GibCursor tmpcur_23455 = tmpcur_23453 + sizeof(GibFloat);

            gib_shadowstack_push(rstack, tmpcur_23443, end_r_15737, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, tmpcur_23440, end_r_15737, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, tmpcur_23437, end_r_15737, Stk,
                                 BH_Tree_T);

            GibCursorGibCursorGibIntProd tmp_struct_330 =
                                          countLeavesQtree(end_r_15737, tmpcur_23455);
            GibCursor pvrtmp_23456 = tmp_struct_330.field0;
            GibCursor pvrtmp_23457 = tmp_struct_330.field1;
            GibInt pvrtmp_23458 = tmp_struct_330.field2;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_23437 = frame->ptr;
            end_r_15737 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tmpcur_23440 = frame->ptr;
            end_r_15737 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tmpcur_23443 = frame->ptr;
            end_r_15737 = frame->endptr;
            gib_shadowstack_push(rstack, tmpcur_23443, pvrtmp_23456, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, tmpcur_23440, pvrtmp_23456, Stk,
                                 BH_Tree_T);

            GibCursorGibCursorGibIntProd tmp_struct_331 =
                                          countLeavesQtree(end_from_tagged_absran_15576, tmpcur_23437);
            GibCursor pvrtmp_23459 = tmp_struct_331.field0;
            GibCursor pvrtmp_23460 = tmp_struct_331.field1;
            GibInt pvrtmp_23461 = tmp_struct_331.field2;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_23440 = frame->ptr;
            pvrtmp_23456 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tmpcur_23443 = frame->ptr;
            pvrtmp_23456 = frame->endptr;

            GibInt fltPrm_12011_13063 = pvrtmp_23458 + pvrtmp_23461;

            gib_shadowstack_push(rstack, tmpcur_23443, pvrtmp_23459, Stk,
                                 BH_Tree_T);

            GibCursorGibCursorGibIntProd tmp_struct_332 =
                                          countLeavesQtree(end_from_tagged_absran_15577, tmpcur_23440);
            GibCursor pvrtmp_23462 = tmp_struct_332.field0;
            GibCursor pvrtmp_23463 = tmp_struct_332.field1;
            GibInt pvrtmp_23464 = tmp_struct_332.field2;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_23443 = frame->ptr;
            pvrtmp_23459 = frame->endptr;

            GibInt fltPrm_12010_13065 = fltPrm_12011_13063 + pvrtmp_23464;
            GibCursorGibCursorGibIntProd tmp_struct_333 =
                                          countLeavesQtree(end_from_tagged_absran_15578, tmpcur_23443);
            GibCursor pvrtmp_23465 = tmp_struct_333.field0;
            GibCursor pvrtmp_23466 = tmp_struct_333.field1;
            GibInt pvrtmp_23467 = tmp_struct_333.field2;
            GibInt tailprim_17603 = fltPrm_12010_13065 + pvrtmp_23467;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_23465, pvrtmp_23466,
                                                   tailprim_17603};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_338 = *(uintptr_t *) tmpcur_23430;
            GibCursor tmpcur_23468 = GIB_UNTAG(tagged_tmpcur_338);
            GibCursor tmpaftercur_23469 = tmpcur_23430 + 8;
            uint16_t tmptag_23470 = GIB_GET_TAG(tagged_tmpcur_338);
            GibCursor end_from_tagged_indr_18055 = tmpcur_23468 + tmptag_23470;
            GibCursor jump_18057 = tmpcur_23430 + 8;
            GibCursorGibCursorGibIntProd tmp_struct_337 =
                                          countLeavesQtree(end_from_tagged_indr_18055, tmpcur_23468);
            GibCursor pvrtmp_23471 = tmp_struct_337.field0;
            GibCursor pvrtmp_23472 = tmp_struct_337.field1;
            GibInt pvrtmp_23473 = tmp_struct_337.field2;

            return (GibCursorGibCursorGibIntProd) {end_r_15737, jump_18057,
                                                   pvrtmp_23473};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_340 = *(uintptr_t *) tmpcur_23430;
            GibCursor tmpcur_23474 = GIB_UNTAG(tagged_tmpcur_340);
            GibCursor tmpaftercur_23475 = tmpcur_23430 + 8;
            uint16_t tmptag_23476 = GIB_GET_TAG(tagged_tmpcur_340);
            GibCursor end_from_tagged_indr_18055 = tmpcur_23474 + tmptag_23476;
            GibCursorGibCursorGibIntProd tmp_struct_339 =
                                          countLeavesQtree(end_from_tagged_indr_18055, tmpcur_23474);
            GibCursor pvrtmp_23477 = tmp_struct_339.field0;
            GibCursor pvrtmp_23478 = tmp_struct_339.field1;
            GibInt pvrtmp_23479 = tmp_struct_339.field2;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_23477, pvrtmp_23478,
                                                   pvrtmp_23479};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_23429");
            exit(1);
        }
    }
}
GibCursorGibCursorGibFloatProd sumQtree(GibCursor end_r_15739,
                                        GibCursor tr_1522_8629_13067)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_23481 = *(GibPackedTag *) tr_1522_8629_13067;
    GibCursor tmpcur_23482 = tr_1522_8629_13067 + 1;


  switch_23532:
    ;
    switch (tmpval_23481) {

      case 0:
        {
            GibCursor jump_17605 = tr_1522_8629_13067 + 1;

            return (GibCursorGibCursorGibFloatProd) {end_r_15739, jump_17605,
                                                     0.0};
            break;
        }

      case 1:
        {
            GibFloat tmpval_23483 = *(GibFloat *) tmpcur_23482;
            GibCursor tmpcur_23484 = tmpcur_23482 + sizeof(GibFloat);
            GibFloat tmpval_23485 = *(GibFloat *) tmpcur_23484;
            GibCursor tmpcur_23486 = tmpcur_23484 + sizeof(GibFloat);
            GibFloat tmpval_23487 = *(GibFloat *) tmpcur_23486;
            GibCursor tmpcur_23488 = tmpcur_23486 + sizeof(GibFloat);
            GibCursor jump_17608 = tmpcur_23486 + 4;
            GibFloat fltPrm_12016_13071 = tmpval_23483 + tmpval_23485;
            GibFloat tailprim_17609 = fltPrm_12016_13071 + tmpval_23487;

            return (GibCursorGibCursorGibFloatProd) {end_r_15739, jump_17608,
                                                     tailprim_17609};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_347 = *(uintptr_t *) tmpcur_23482;
            GibCursor tmpcur_23489 = GIB_UNTAG(tagged_tmpcur_347);
            GibCursor tmpaftercur_23490 = tmpcur_23482 + 8;
            uint16_t tmptag_23491 = GIB_GET_TAG(tagged_tmpcur_347);
            GibCursor end_from_tagged_absran_15583 = tmpcur_23489 +
                      tmptag_23491;
            uintptr_t tagged_tmpcur_346 = *(uintptr_t *) tmpaftercur_23490;
            GibCursor tmpcur_23492 = GIB_UNTAG(tagged_tmpcur_346);
            GibCursor tmpaftercur_23493 = tmpaftercur_23490 + 8;
            uint16_t tmptag_23494 = GIB_GET_TAG(tagged_tmpcur_346);
            GibCursor end_from_tagged_absran_15584 = tmpcur_23492 +
                      tmptag_23494;
            uintptr_t tagged_tmpcur_345 = *(uintptr_t *) tmpaftercur_23493;
            GibCursor tmpcur_23495 = GIB_UNTAG(tagged_tmpcur_345);
            GibCursor tmpaftercur_23496 = tmpaftercur_23493 + 8;
            uint16_t tmptag_23497 = GIB_GET_TAG(tagged_tmpcur_345);
            GibCursor end_from_tagged_absran_15585 = tmpcur_23495 +
                      tmptag_23497;
            GibFloat tmpval_23498 = *(GibFloat *) tmpaftercur_23496;
            GibCursor tmpcur_23499 = tmpaftercur_23496 + sizeof(GibFloat);
            GibFloat tmpval_23500 = *(GibFloat *) tmpcur_23499;
            GibCursor tmpcur_23501 = tmpcur_23499 + sizeof(GibFloat);
            GibFloat tmpval_23502 = *(GibFloat *) tmpcur_23501;
            GibCursor tmpcur_23503 = tmpcur_23501 + sizeof(GibFloat);
            GibInt tmpval_23504 = *(GibInt *) tmpcur_23503;
            GibCursor tmpcur_23505 = tmpcur_23503 + sizeof(GibInt);
            GibFloat tmpval_23506 = *(GibFloat *) tmpcur_23505;
            GibCursor tmpcur_23507 = tmpcur_23505 + sizeof(GibFloat);

            gib_shadowstack_push(rstack, tmpcur_23495, end_r_15739, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, tmpcur_23492, end_r_15739, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, tmpcur_23489, end_r_15739, Stk,
                                 BH_Tree_T);

            GibCursorGibCursorGibFloatProd tmp_struct_341 =
                                            sumQtree(end_r_15739, tmpcur_23507);
            GibCursor pvrtmp_23508 = tmp_struct_341.field0;
            GibCursor pvrtmp_23509 = tmp_struct_341.field1;
            GibFloat pvrtmp_23510 = tmp_struct_341.field2;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_23489 = frame->ptr;
            end_r_15739 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tmpcur_23492 = frame->ptr;
            end_r_15739 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tmpcur_23495 = frame->ptr;
            end_r_15739 = frame->endptr;
            gib_shadowstack_push(rstack, tmpcur_23495, pvrtmp_23508, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, tmpcur_23492, pvrtmp_23508, Stk,
                                 BH_Tree_T);

            GibCursorGibCursorGibFloatProd tmp_struct_342 =
                                            sumQtree(end_from_tagged_absran_15583, tmpcur_23489);
            GibCursor pvrtmp_23511 = tmp_struct_342.field0;
            GibCursor pvrtmp_23512 = tmp_struct_342.field1;
            GibFloat pvrtmp_23513 = tmp_struct_342.field2;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_23492 = frame->ptr;
            pvrtmp_23508 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tmpcur_23495 = frame->ptr;
            pvrtmp_23508 = frame->endptr;

            GibFloat fltPrm_12018_13083 = pvrtmp_23510 + pvrtmp_23513;

            gib_shadowstack_push(rstack, tmpcur_23495, pvrtmp_23511, Stk,
                                 BH_Tree_T);

            GibCursorGibCursorGibFloatProd tmp_struct_343 =
                                            sumQtree(end_from_tagged_absran_15584, tmpcur_23492);
            GibCursor pvrtmp_23514 = tmp_struct_343.field0;
            GibCursor pvrtmp_23515 = tmp_struct_343.field1;
            GibFloat pvrtmp_23516 = tmp_struct_343.field2;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_23495 = frame->ptr;
            pvrtmp_23511 = frame->endptr;

            GibFloat fltPrm_12017_13085 = fltPrm_12018_13083 + pvrtmp_23516;
            GibCursorGibCursorGibFloatProd tmp_struct_344 =
                                            sumQtree(end_from_tagged_absran_15585, tmpcur_23495);
            GibCursor pvrtmp_23517 = tmp_struct_344.field0;
            GibCursor pvrtmp_23518 = tmp_struct_344.field1;
            GibFloat pvrtmp_23519 = tmp_struct_344.field2;
            GibFloat tailprim_17622 = fltPrm_12017_13085 + pvrtmp_23519;

            return (GibCursorGibCursorGibFloatProd) {pvrtmp_23517, pvrtmp_23518,
                                                     tailprim_17622};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_349 = *(uintptr_t *) tmpcur_23482;
            GibCursor tmpcur_23520 = GIB_UNTAG(tagged_tmpcur_349);
            GibCursor tmpaftercur_23521 = tmpcur_23482 + 8;
            uint16_t tmptag_23522 = GIB_GET_TAG(tagged_tmpcur_349);
            GibCursor end_from_tagged_indr_18061 = tmpcur_23520 + tmptag_23522;
            GibCursor jump_18063 = tmpcur_23482 + 8;
            GibCursorGibCursorGibFloatProd tmp_struct_348 =
                                            sumQtree(end_from_tagged_indr_18061, tmpcur_23520);
            GibCursor pvrtmp_23523 = tmp_struct_348.field0;
            GibCursor pvrtmp_23524 = tmp_struct_348.field1;
            GibFloat pvrtmp_23525 = tmp_struct_348.field2;

            return (GibCursorGibCursorGibFloatProd) {end_r_15739, jump_18063,
                                                     pvrtmp_23525};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_351 = *(uintptr_t *) tmpcur_23482;
            GibCursor tmpcur_23526 = GIB_UNTAG(tagged_tmpcur_351);
            GibCursor tmpaftercur_23527 = tmpcur_23482 + 8;
            uint16_t tmptag_23528 = GIB_GET_TAG(tagged_tmpcur_351);
            GibCursor end_from_tagged_indr_18061 = tmpcur_23526 + tmptag_23528;
            GibCursorGibCursorGibFloatProd tmp_struct_350 =
                                            sumQtree(end_from_tagged_indr_18061, tmpcur_23526);
            GibCursor pvrtmp_23529 = tmp_struct_350.field0;
            GibCursor pvrtmp_23530 = tmp_struct_350.field1;
            GibFloat pvrtmp_23531 = tmp_struct_350.field2;

            return (GibCursorGibCursorGibFloatProd) {pvrtmp_23529, pvrtmp_23530,
                                                     pvrtmp_23531};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_23481");
            exit(1);
        }
    }
}
GibCursorGibCursorGibIntProd lenA(GibCursor end_r_15741,
                                  GibCursor ls_1601_8685_13099)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_23533 = *(GibPackedTag *) ls_1601_8685_13099;
    GibCursor tmpcur_23534 = ls_1601_8685_13099 + 1;


  switch_23557:
    ;
    switch (tmpval_23533) {

      case 0:
        {
            GibInt tmpval_23535 = *(GibInt *) tmpcur_23534;
            GibCursor tmpcur_23536 = tmpcur_23534 + sizeof(GibInt);
            GibCursor jump_17625 = tmpcur_23534 + 8;

            return (GibCursorGibCursorGibIntProd) {end_r_15741, jump_17625, 0};
            break;
        }

      case 1:
        {
            GibInt tmpval_23537 = *(GibInt *) tmpcur_23534;
            GibCursor tmpcur_23538 = tmpcur_23534 + sizeof(GibInt);
            GibCursor jump_17626 = tmpcur_23534 + 8;

            return (GibCursorGibCursorGibIntProd) {end_r_15741, jump_17626, 1};
            break;
        }

      case 2:
        {
            GibCursorGibCursorGibIntProd tmp_struct_352 =
                                          lenA(end_r_15741, tmpcur_23534);
            GibCursor pvrtmp_23539 = tmp_struct_352.field0;
            GibCursor pvrtmp_23540 = tmp_struct_352.field1;
            GibInt pvrtmp_23541 = tmp_struct_352.field2;
            GibCursorGibCursorGibIntProd tmp_struct_353 =
                                          lenA(pvrtmp_23539, pvrtmp_23540);
            GibCursor pvrtmp_23542 = tmp_struct_353.field0;
            GibCursor pvrtmp_23543 = tmp_struct_353.field1;
            GibInt pvrtmp_23544 = tmp_struct_353.field2;
            GibInt tailprim_17629 = pvrtmp_23541 + pvrtmp_23544;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_23542, pvrtmp_23543,
                                                   tailprim_17629};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_355 = *(uintptr_t *) tmpcur_23534;
            GibCursor tmpcur_23545 = GIB_UNTAG(tagged_tmpcur_355);
            GibCursor tmpaftercur_23546 = tmpcur_23534 + 8;
            uint16_t tmptag_23547 = GIB_GET_TAG(tagged_tmpcur_355);
            GibCursor end_from_tagged_indr_18067 = tmpcur_23545 + tmptag_23547;
            GibCursor jump_18069 = tmpcur_23534 + 8;
            GibCursorGibCursorGibIntProd tmp_struct_354 =
                                          lenA(end_from_tagged_indr_18067, tmpcur_23545);
            GibCursor pvrtmp_23548 = tmp_struct_354.field0;
            GibCursor pvrtmp_23549 = tmp_struct_354.field1;
            GibInt pvrtmp_23550 = tmp_struct_354.field2;

            return (GibCursorGibCursorGibIntProd) {end_r_15741, jump_18069,
                                                   pvrtmp_23550};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_357 = *(uintptr_t *) tmpcur_23534;
            GibCursor tmpcur_23551 = GIB_UNTAG(tagged_tmpcur_357);
            GibCursor tmpaftercur_23552 = tmpcur_23534 + 8;
            uint16_t tmptag_23553 = GIB_GET_TAG(tagged_tmpcur_357);
            GibCursor end_from_tagged_indr_18067 = tmpcur_23551 + tmptag_23553;
            GibCursorGibCursorGibIntProd tmp_struct_356 =
                                          lenA(end_from_tagged_indr_18067, tmpcur_23551);
            GibCursor pvrtmp_23554 = tmp_struct_356.field0;
            GibCursor pvrtmp_23555 = tmp_struct_356.field1;
            GibInt pvrtmp_23556 = tmp_struct_356.field2;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_23554, pvrtmp_23555,
                                                   pvrtmp_23556};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_23533");
            exit(1);
        }
    }
}
GibCursorGibCursorProd trav_exp(GibCursor end_r_15743,
                                GibCursor exp_1631_8715_13106)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_23558 = *(GibPackedTag *) exp_1631_8715_13106;
    GibCursor tmpcur_23559 = exp_1631_8715_13106 + 1;


  switch_23576:
    ;
    switch (tmpval_23558) {

      case 0:
        {
            GibInt tmpval_23560 = *(GibInt *) tmpcur_23559;
            GibCursor tmpcur_23561 = tmpcur_23559 + sizeof(GibInt);
            GibCursor jump_17630 = tmpcur_23559 + 8;

            return (GibCursorGibCursorProd) {end_r_15743, jump_17630};
            break;
        }

      case 1:
        {
            GibCursor jump_17632 = exp_1631_8715_13106 + 1;

            return (GibCursorGibCursorProd) {end_r_15743, jump_17632};
            break;
        }

      case 2:
        {
            GibCursor jump_17634 = exp_1631_8715_13106 + 1;

            return (GibCursorGibCursorProd) {end_r_15743, jump_17634};
            break;
        }

      case 3:
        {
            GibCursorGibCursorProd tmp_struct_358 =
                                    trav_exp(end_r_15743, tmpcur_23559);
            GibCursor pvrtmp_23562 = tmp_struct_358.field0;
            GibCursor pvrtmp_23563 = tmp_struct_358.field1;
            GibCursorGibCursorProd tmp_struct_359 =
                                    trav_exp(pvrtmp_23562, pvrtmp_23563);
            GibCursor pvrtmp_23564 = tmp_struct_359.field0;
            GibCursor pvrtmp_23565 = tmp_struct_359.field1;

            return (GibCursorGibCursorProd) {pvrtmp_23564, pvrtmp_23565};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_361 = *(uintptr_t *) tmpcur_23559;
            GibCursor tmpcur_23566 = GIB_UNTAG(tagged_tmpcur_361);
            GibCursor tmpaftercur_23567 = tmpcur_23559 + 8;
            uint16_t tmptag_23568 = GIB_GET_TAG(tagged_tmpcur_361);
            GibCursor end_from_tagged_indr_18073 = tmpcur_23566 + tmptag_23568;
            GibCursor jump_18075 = tmpcur_23559 + 8;
            GibCursorGibCursorProd tmp_struct_360 =
                                    trav_exp(end_from_tagged_indr_18073, tmpcur_23566);
            GibCursor pvrtmp_23569 = tmp_struct_360.field0;
            GibCursor pvrtmp_23570 = tmp_struct_360.field1;

            return (GibCursorGibCursorProd) {end_r_15743, jump_18075};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_363 = *(uintptr_t *) tmpcur_23559;
            GibCursor tmpcur_23571 = GIB_UNTAG(tagged_tmpcur_363);
            GibCursor tmpaftercur_23572 = tmpcur_23559 + 8;
            uint16_t tmptag_23573 = GIB_GET_TAG(tagged_tmpcur_363);
            GibCursor end_from_tagged_indr_18073 = tmpcur_23571 + tmptag_23573;
            GibCursorGibCursorProd tmp_struct_362 =
                                    trav_exp(end_from_tagged_indr_18073, tmpcur_23571);
            GibCursor pvrtmp_23574 = tmp_struct_362.field0;
            GibCursor pvrtmp_23575 = tmp_struct_362.field1;

            return (GibCursorGibCursorProd) {pvrtmp_23574, pvrtmp_23575};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_23558");
            exit(1);
        }
    }
}
GibCursorGibFloatProd maybeLit(GibCursor end_r_15745,
                               GibCursor exp_1651_8735_13112)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_23577 = *(GibPackedTag *) exp_1651_8735_13112;
    GibCursor tmpcur_23578 = exp_1651_8735_13112 + 1;


  switch_23591:
    ;
    switch (tmpval_23577) {

      case 0:
        {
            GibInt tmpval_23579 = *(GibInt *) tmpcur_23578;
            GibCursor tmpcur_23580 = tmpcur_23578 + sizeof(GibInt);
            GibFloat tailprim_17640 = (GibFloat) tmpval_23579;

            return (GibCursorGibFloatProd) {end_r_15745, tailprim_17640};
            break;
        }

      case 3:
        {
            GibFloat tailprim_17641 = 0.0 - 3.14;

            return (GibCursorGibFloatProd) {end_r_15745, tailprim_17641};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_365 = *(uintptr_t *) tmpcur_23578;
            GibCursor tmpcur_23581 = GIB_UNTAG(tagged_tmpcur_365);
            GibCursor tmpaftercur_23582 = tmpcur_23578 + 8;
            uint16_t tmptag_23583 = GIB_GET_TAG(tagged_tmpcur_365);
            GibCursor end_from_tagged_indr_18079 = tmpcur_23581 + tmptag_23583;
            GibCursor jump_18081 = tmpcur_23578 + 8;
            GibCursorGibFloatProd tmp_struct_364 =
                                   maybeLit(end_from_tagged_indr_18079, tmpcur_23581);
            GibCursor pvrtmp_23584 = tmp_struct_364.field0;
            GibFloat pvrtmp_23585 = tmp_struct_364.field1;

            return (GibCursorGibFloatProd) {end_r_15745, pvrtmp_23585};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_367 = *(uintptr_t *) tmpcur_23578;
            GibCursor tmpcur_23586 = GIB_UNTAG(tagged_tmpcur_367);
            GibCursor tmpaftercur_23587 = tmpcur_23578 + 8;
            uint16_t tmptag_23588 = GIB_GET_TAG(tagged_tmpcur_367);
            GibCursor end_from_tagged_indr_18079 = tmpcur_23586 + tmptag_23588;
            GibCursorGibFloatProd tmp_struct_366 =
                                   maybeLit(end_from_tagged_indr_18079, tmpcur_23586);
            GibCursor pvrtmp_23589 = tmp_struct_366.field0;
            GibFloat pvrtmp_23590 = tmp_struct_366.field1;

            return (GibCursorGibFloatProd) {pvrtmp_23589, pvrtmp_23590};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_23577");
            exit(1);
        }
    }
}
GibInt maxInt(GibInt a_1664_8748_13116, GibInt b_1665_8749_13117)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_12027_13118 = a_1664_8748_13116 > b_1665_8749_13117;

    if (fltIf_12027_13118) {
        return a_1664_8748_13116;
    } else {
        return b_1665_8749_13117;
    }
}
GibInt cmpz_point3d_original(GibFloatGibFloatGibFloatProd a_2053_8837_13119,
                             GibFloatGibFloatGibFloatProd b_2054_8838_13120)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_12028_13127 = a_2053_8837_13119.field2 <
            b_2054_8838_13120.field2;

    if (fltIf_12028_13127) {
        GibInt tailprim_17644 = 0 - 1;

        return tailprim_17644;
    } else {
        GibBool fltIf_12029_13128 = a_2053_8837_13119.field2 >
                b_2054_8838_13120.field2;

        if (fltIf_12029_13128) {
            return 1;
        } else {
            return 0;
        }
    }
}
int cmpz_point3d(const void *a_2053_8837_13119, const void *b_2054_8838_13120)
{
    GibFloatGibFloatGibFloatProd fst_368 =
                                 *(GibFloatGibFloatGibFloatProd *) a_2053_8837_13119;
    GibFloatGibFloatGibFloatProd snd_369 =
                                 *(GibFloatGibFloatGibFloatProd *) b_2054_8838_13120;

    return cmpz_point3d_original(fst_368, snd_369);
}
GibInt cmpy_point3d_original(GibFloatGibFloatGibFloatProd a_2059_8843_13129,
                             GibFloatGibFloatGibFloatProd b_2060_8844_13130)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_12030_13137 = a_2059_8843_13129.field1 <
            b_2060_8844_13130.field1;

    if (fltIf_12030_13137) {
        GibInt tailprim_17647 = 0 - 1;

        return tailprim_17647;
    } else {
        GibBool fltIf_12031_13138 = a_2059_8843_13129.field1 >
                b_2060_8844_13130.field1;

        if (fltIf_12031_13138) {
            return 1;
        } else {
            return 0;
        }
    }
}
int cmpy_point3d(const void *a_2059_8843_13129, const void *b_2060_8844_13130)
{
    GibFloatGibFloatGibFloatProd fst_370 =
                                 *(GibFloatGibFloatGibFloatProd *) a_2059_8843_13129;
    GibFloatGibFloatGibFloatProd snd_371 =
                                 *(GibFloatGibFloatGibFloatProd *) b_2060_8844_13130;

    return cmpy_point3d_original(fst_370, snd_371);
}
GibInt cmpx_point3d_original(GibFloatGibFloatGibFloatProd a_2065_8849_13139,
                             GibFloatGibFloatGibFloatProd b_2066_8850_13140)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_12032_13147 = a_2065_8849_13139.field0 <
            b_2066_8850_13140.field0;

    if (fltIf_12032_13147) {
        GibInt tailprim_17650 = 0 - 1;

        return tailprim_17650;
    } else {
        GibBool fltIf_12033_13148 = a_2065_8849_13139.field0 >
                b_2066_8850_13140.field0;

        if (fltIf_12033_13148) {
            return 1;
        } else {
            return 0;
        }
    }
}
int cmpx_point3d(const void *a_2065_8849_13139, const void *b_2066_8850_13140)
{
    GibFloatGibFloatGibFloatProd fst_372 =
                                 *(GibFloatGibFloatGibFloatProd *) a_2065_8849_13139;
    GibFloatGibFloatGibFloatProd snd_373 =
                                 *(GibFloatGibFloatGibFloatProd *) b_2066_8850_13140;

    return cmpx_point3d_original(fst_372, snd_373);
}
GibVector *filter_loop_3498(GibVector *idxs_1676_8958_13149,
                            GibInt write_at_1677_8959_13150,
                            GibInt start_1678_8960_13151,
                            GibInt end_1679_8961_13152,
                            GibVector *from_1680_8962_13153,
                            GibVector *to_1681_8963_13154)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_12034_13155 = start_1678_8960_13151 == end_1679_8961_13152;

    if (fltIf_12034_13155) {
        return to_1681_8963_13154;
    } else {
        GibInt *tmp_375;

        tmp_375 = (GibInt *) gib_vector_nth(idxs_1676_8958_13149,
                                            start_1678_8960_13151);

        GibInt idx_1683_8964_13158 = *tmp_375;
        GibInt fltPrm_12036_13159 = 0 - 1;
        GibBool fltIf_12035_13160 = idx_1683_8964_13158 == fltPrm_12036_13159;

        if (fltIf_12035_13160) {
            GibInt fltAppE_12037_13161 = start_1678_8960_13151 + 1;
            GibVector *tailapp_17651 =
                       filter_loop_3498(idxs_1676_8958_13149, write_at_1677_8959_13150, fltAppE_12037_13161, end_1679_8961_13152, from_1680_8962_13153, to_1681_8963_13154);

            return tailapp_17651;
        } else {
            GibFloatGibFloatGibFloatProd *tmp_374;

            tmp_374 =
                (GibFloatGibFloatGibFloatProd *) gib_vector_nth(from_1680_8962_13153,
                                                                idx_1683_8964_13158);

            GibFloatGibFloatGibFloatProd elt_1684_8965_13164 = *tmp_374;
            GibVector *to1_1685_8966_13165 =
                      gib_vector_inplace_update(to_1681_8963_13154,
                                                write_at_1677_8959_13150,
                                                &elt_1684_8965_13164);
            GibInt fltAppE_12038_13166 = write_at_1677_8959_13150 + 1;
            GibInt fltAppE_12039_13167 = start_1678_8960_13151 + 1;
            GibVector *tailapp_17652 =
                       filter_loop_3498(idxs_1676_8958_13149, fltAppE_12038_13166, fltAppE_12039_13167, end_1679_8961_13152, from_1680_8962_13153, to1_1685_8966_13165);

            return tailapp_17652;
        }
    }
}
GibInt foldl_loop_3499_5967(GibInt idx_1765_9799_13228,
                            GibInt end_1766_9800_13229,
                            GibInt acc_1768_9801_13230,
                            GibVector *vec_1769_9802_13231)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_12047_13232 = idx_1765_9799_13228 == end_1766_9800_13229;

    if (fltIf_12047_13232) {
        return acc_1768_9801_13230;
    } else {
        GibInt *tmp_376;

        tmp_376 = (GibInt *) gib_vector_nth(vec_1769_9802_13231,
                                            idx_1765_9799_13228);

        GibInt x_1583_9790_11561_13234 = *tmp_376;
        GibInt fltPrm_12049_13235 = 0 - 1;
        GibBool fltIf_12048_13236 = x_1583_9790_11561_13234 ==
                fltPrm_12049_13235;
        GibInt acc1_1772_9803_13237;

        if (fltIf_12048_13236) {
            acc1_1772_9803_13237 = acc_1768_9801_13230;
        } else {
            GibInt flt_23592 = acc_1768_9801_13230 + 1;

            acc1_1772_9803_13237 = flt_23592;
        }

        GibInt fltAppE_12050_13238 = idx_1765_9799_13228 + 1;
        GibInt tailapp_17653 =
                foldl_loop_3499_5967(fltAppE_12050_13238, end_1766_9800_13229, acc1_1772_9803_13237, vec_1769_9802_13231);

        return tailapp_17653;
    }
}
GibCursorGibVectorProd generate_loop_3496_5968(GibCursor end_r_15747,
                                               GibVector *vec_1797_9804_13239,
                                               GibInt idx_1798_9805_13240,
                                               GibInt end_1799_9806_13241,
                                               GibCursor bht_665_9807_13242,
                                               GibVector *mpts_666_9808_13243,
                                               GibVector *ps_667_9809_13244)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_12051_13245 = idx_1798_9805_13240 == end_1799_9806_13241;

    if (fltIf_12051_13245) {
        return (GibCursorGibVectorProd) {end_r_15747, vec_1797_9804_13239};
    } else {
        GibFloatGibFloatGibFloatGibFloatGibFloatProd *tmp_380;

        tmp_380 =
            (GibFloatGibFloatGibFloatGibFloatGibFloatProd *) gib_vector_nth(ps_667_9809_13244,
                                                                            idx_1798_9805_13240);

        GibFloatGibFloatGibFloatGibFloatGibFloatProd p_669_9084_11566_13250 =
                                                     *tmp_380;
        GibFloatGibFloatGibFloatProd *tmp_379;

        tmp_379 =
            (GibFloatGibFloatGibFloatProd *) gib_vector_nth(mpts_666_9808_13243,
                                                            idx_1798_9805_13240);

        GibFloatGibFloatGibFloatProd mpt_670_9085_11567_13251 = *tmp_379;

        // gib_shadowstack_push(rstack, bht_665_9807_13242, end_r_15747, Stk,
        //                      BH_Tree_T);

        GibCursorGibFloatGibFloatProd tmp_struct_377 =
                                       calcAccel_seq(end_r_15747, (GibFloatGibFloatGibFloatProd) {mpt_670_9085_11567_13251.field0, mpt_670_9085_11567_13251.field1, mpt_670_9085_11567_13251.field2}, bht_665_9807_13242);
        GibCursor pvrtmp_23596 = tmp_struct_377.field0;
        GibFloat pvrtmp_23597 = tmp_struct_377.field1;
        GibFloat pvrtmp_23598 = tmp_struct_377.field2;

        // frame = gib_shadowstack_pop(rstack);
        // bht_665_9807_13242 = frame->ptr;
        // end_r_15747 = frame->endptr;

        GibFloat fltPrm_12006_13027_14001 = pvrtmp_23597 * 2.0;
        GibFloat fltPrd_12005_13028_14002 = p_669_9084_11566_13250.field3 +
                 fltPrm_12006_13027_14001;
        GibFloat fltPrm_12008_13029_14003 = pvrtmp_23598 * 2.0;
        GibFloat fltPrd_12007_13030_14004 = p_669_9084_11566_13250.field4 +
                 fltPrm_12008_13029_14003;
        GibVector *vec1_1802_9810_13254 =
                  gib_vector_inplace_update(vec_1797_9804_13239,
                                            idx_1798_9805_13240,
                                            &(GibFloatGibFloatGibFloatGibFloatGibFloatProd) {p_669_9084_11566_13250.field0,
                                                                                             p_669_9084_11566_13250.field1,
                                                                                             p_669_9084_11566_13250.field2,
                                                                                             fltPrd_12005_13028_14002,
                                                                                             fltPrd_12007_13030_14004});
        GibInt fltAppE_12053_13255 = idx_1798_9805_13240 + 1;
        GibCursorGibVectorProd tmp_struct_378 =
                                generate_loop_3496_5968(end_r_15747, vec1_1802_9810_13254, fltAppE_12053_13255, end_1799_9806_13241, bht_665_9807_13242, mpts_666_9808_13243, ps_667_9809_13244);
        GibCursor pvrtmp_23606 = tmp_struct_378.field0;
        GibVector *pvrtmp_23607 = tmp_struct_378.field1;

        return (GibCursorGibVectorProd) {pvrtmp_23606, pvrtmp_23607};
    }
}
GibVector *generate_loop_3495_5969(GibVector *vec_1797_9811_13256,
                                   GibInt idx_1798_9812_13257,
                                   GibInt end_1799_9813_13258,
                                   GibVector *vec_1794_9814_13259)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_12054_13260 = idx_1798_9812_13257 == end_1799_9813_13258;

    if (fltIf_12054_13260) {
        return vec_1797_9811_13256;
    } else {
        GibFloatGibFloatGibFloatProd *tmp_381;

        tmp_381 =
            (GibFloatGibFloatGibFloatProd *) gib_vector_nth(vec_1794_9814_13259,
                                                            idx_1798_9812_13257);

        GibFloatGibFloatGibFloatProd fltPrm_12055_13263 = *tmp_381;
        GibVector *vec1_1802_9815_13264 =
                  gib_vector_inplace_update(vec_1797_9811_13256,
                                            idx_1798_9812_13257,
                                            &fltPrm_12055_13263);
        GibInt fltAppE_12056_13265 = idx_1798_9812_13257 + 1;
        GibVector *tailapp_17655 =
                   generate_loop_3495_5969(vec1_1802_9815_13264, fltAppE_12056_13265, end_1799_9813_13258, vec_1794_9814_13259);

        return tailapp_17655;
    }
}
GibVector *generate_loop_3493_5973(GibVector *vec_1797_9841_13266,
                                   GibInt idx_1798_9842_13267,
                                   GibInt end_1799_9843_13268)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_12057_13269 = idx_1798_9842_13267 == end_1799_9843_13268;

    if (fltIf_12057_13269) {
        return vec_1797_9841_13266;
    } else {
        GibVector *vec1_1802_9844_13272 =
                  gib_vector_inplace_update(vec_1797_9841_13266,
                                            idx_1798_9842_13267,
                                            &idx_1798_9842_13267);
        GibInt fltAppE_12059_13273 = idx_1798_9842_13267 + 1;
        GibVector *tailapp_17656 =
                   generate_loop_3493_5973(vec1_1802_9844_13272, fltAppE_12059_13273, end_1799_9843_13268);

        return tailapp_17656;
    }
}
GibVector *generate_loop_3493_5975(GibVector *vec_1797_9850_13274,
                                   GibInt idx_1798_9851_13275,
                                   GibInt end_1799_9852_13276,
                                   GibVector *vec_1579_9853_13277,
                                   GibFloatGibFloatGibFloatGibFloatProd box_1343_9854_13278)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_12060_13279 = idx_1798_9851_13275 == end_1799_9852_13276;

    if (fltIf_12060_13279) {
        return vec_1797_9850_13274;
    } else {
        GibFloatGibFloatGibFloatProd *tmp_382;

        tmp_382 =
            (GibFloatGibFloatGibFloatProd *) gib_vector_nth(vec_1579_9853_13277,
                                                            idx_1798_9851_13275);

        GibFloatGibFloatGibFloatProd fltAppE_12063_13283 = *tmp_382;
        GibBool fltPrm_12040_13208_14024 = fltAppE_12063_13283.field0 >=
                box_1343_9854_13278.field0;
        GibBool fltPrm_12042_13209_14025 = fltAppE_12063_13283.field0 <=
                box_1343_9854_13278.field2;
        GibBool fltPrm_12044_13210_14026 = fltAppE_12063_13283.field1 >=
                box_1343_9854_13278.field1;
        GibBool fltPrm_12045_13211_14027 = fltAppE_12063_13283.field1 <=
                box_1343_9854_13278.field3;
        GibBool fltPrm_12043_13212_14028 = fltPrm_12044_13210_14026 &&
                fltPrm_12045_13211_14027;
        GibBool fltPrm_12041_13213_14029 = fltPrm_12042_13209_14025 &&
                fltPrm_12043_13212_14028;
        GibBool fltIf_12062_13284 = fltPrm_12040_13208_14024 &&
                fltPrm_12041_13213_14029;
        GibInt fltPrm_12061_13285;

        if (fltIf_12062_13284) {
            fltPrm_12061_13285 = idx_1798_9851_13275;
        } else {
            GibInt flt_23610 = 0 - 1;

            fltPrm_12061_13285 = flt_23610;
        }

        GibVector *vec1_1802_9855_13286 =
                  gib_vector_inplace_update(vec_1797_9850_13274,
                                            idx_1798_9851_13275,
                                            &fltPrm_12061_13285);
        GibInt fltAppE_12064_13287 = idx_1798_9851_13275 + 1;
        GibVector *tailapp_17657 =
                   generate_loop_3493_5975(vec1_1802_9855_13286, fltAppE_12064_13287, end_1799_9852_13276, vec_1579_9853_13277, (GibFloatGibFloatGibFloatGibFloatProd) {box_1343_9854_13278.field0, box_1343_9854_13278.field1, box_1343_9854_13278.field2, box_1343_9854_13278.field3});

        return tailapp_17657;
    }
}
GibCursorGibVectorProd generate_loop_3495_5986(GibCursor end_r_15749,
                                               GibVector *vec_1797_9925_13294,
                                               GibInt idx_1798_9926_13295,
                                               GibInt end_1799_9927_13296,
                                               GibVector *vec_627_9928_13297,
                                               GibCursor tr_561_9929_13298)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_12065_13299 = idx_1798_9926_13295 == end_1799_9927_13296;

    if (fltIf_12065_13299) {
        return (GibCursorGibVectorProd) {end_r_15749, vec_1797_9925_13294};
    } else {
        GibFloatGibFloatGibFloatProd *tmp_385;

        tmp_385 =
            (GibFloatGibFloatGibFloatProd *) gib_vector_nth(vec_627_9928_13297,
                                                            idx_1798_9926_13295);

        GibFloatGibFloatGibFloatProd fltAppE_12067_13303 = *tmp_385;

        // gib_shadowstack_push(rstack, tr_561_9929_13298, end_r_15749, Stk,
        //                      KdTree_T);

        GibCursorGibFloatGibFloatGibFloatProd tmp_struct_383 =
                                               nearest(end_r_15749, tr_561_9929_13298, (GibFloatGibFloatGibFloatProd) {fltAppE_12067_13303.field0, fltAppE_12067_13303.field1, fltAppE_12067_13303.field2});
        GibCursor pvrtmp_23618 = tmp_struct_383.field0;
        GibFloat pvrtmp_23619 = tmp_struct_383.field1;
        GibFloat pvrtmp_23620 = tmp_struct_383.field2;
        GibFloat pvrtmp_23621 = tmp_struct_383.field3;

        // frame = gib_shadowstack_pop(rstack);
        // tr_561_9929_13298 = frame->ptr;
        // end_r_15749 = frame->endptr;

        GibVector *vec1_1802_9930_13305 =
                  gib_vector_inplace_update(vec_1797_9925_13294,
                                            idx_1798_9926_13295,
                                            &(GibFloatGibFloatGibFloatProd) {pvrtmp_23619,
                                                                             pvrtmp_23620,
                                                                             pvrtmp_23621});
        GibInt fltAppE_12068_13306 = idx_1798_9926_13295 + 1;
        GibCursorGibVectorProd tmp_struct_384 =
                                generate_loop_3495_5986(end_r_15749, vec1_1802_9930_13305, fltAppE_12068_13306, end_1799_9927_13296, vec_627_9928_13297, tr_561_9929_13298);
        GibCursor pvrtmp_23625 = tmp_struct_384.field0;
        GibVector *pvrtmp_23626 = tmp_struct_384.field1;

        return (GibCursorGibVectorProd) {pvrtmp_23625, pvrtmp_23626};
    }
}
GibCursorGibVectorProd generate_loop_3493_5989(GibCursor end_r_15751,
                                               GibVector *vec_1797_9942_13314,
                                               GibInt idx_1798_9943_13315,
                                               GibInt end_1799_9944_13316,
                                               GibVector *vec_627_9945_13317,
                                               GibFloat radius_532_9946_13318,
                                               GibCursor tr_533_9947_13319)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_12069_13320 = idx_1798_9943_13315 == end_1799_9944_13316;

    if (fltIf_12069_13320) {
        return (GibCursorGibVectorProd) {end_r_15751, vec_1797_9942_13314};
    } else {
        GibFloatGibFloatGibFloatProd *tmp_388;

        tmp_388 =
            (GibFloatGibFloatGibFloatProd *) gib_vector_nth(vec_627_9945_13317,
                                                            idx_1798_9943_13315);

        GibFloatGibFloatGibFloatProd fltAppE_12071_13325 = *tmp_388;

        gib_shadowstack_push(rstack, tr_533_9947_13319, end_r_15751, Stk,
                             KdTree_T);

        GibCursorGibIntProd tmp_struct_386 =
                             countCorr_seq(end_r_15751, (GibFloatGibFloatGibFloatProd) {fltAppE_12071_13325.field0, fltAppE_12071_13325.field1, fltAppE_12071_13325.field2}, radius_532_9946_13318, tr_533_9947_13319);
        GibCursor pvrtmp_23630 = tmp_struct_386.field0;
        GibInt pvrtmp_23631 = tmp_struct_386.field1;

        frame = gib_shadowstack_pop(rstack);
        tr_533_9947_13319 = frame->ptr;
        end_r_15751 = frame->endptr;

        GibVector *vec1_1802_9948_13327 =
                  gib_vector_inplace_update(vec_1797_9942_13314,
                                            idx_1798_9943_13315, &pvrtmp_23631);
        GibInt fltAppE_12072_13328 = idx_1798_9943_13315 + 1;
        GibCursorGibVectorProd tmp_struct_387 =
                                generate_loop_3493_5989(end_r_15751, vec1_1802_9948_13327, fltAppE_12072_13328, end_1799_9944_13316, vec_627_9945_13317, radius_532_9946_13318, tr_533_9947_13319);
        GibCursor pvrtmp_23632 = tmp_struct_387.field0;
        GibVector *pvrtmp_23633 = tmp_struct_387.field1;

        return (GibCursorGibVectorProd) {pvrtmp_23632, pvrtmp_23633};
    }
}
GibVector *generate_loop_3496_5995(GibVector *vec_1797_9970_13334,
                                   GibInt idx_1798_9971_13335,
                                   GibInt end_1799_9972_13336,
                                   GibVector *vec_627_9973_13337)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_12073_13338 = idx_1798_9971_13335 == end_1799_9972_13336;

    if (fltIf_12073_13338) {
        return vec_1797_9970_13334;
    } else {
        GibFloatGibFloatProd *tmp_389;

        tmp_389 = (GibFloatGibFloatProd *) gib_vector_nth(vec_627_9973_13337,
                                                          idx_1798_9971_13335);

        GibFloatGibFloatProd fltAppE_12075_13341 = *tmp_389;
        GibVector *vec1_1802_9974_13343 =
                  gib_vector_inplace_update(vec_1797_9970_13334,
                                            idx_1798_9971_13335,
                                            &(GibFloatGibFloatGibFloatGibFloatGibFloatProd) {fltAppE_12075_13341.field0,
                                                                                             fltAppE_12075_13341.field1,
                                                                                             1.0,
                                                                                             0.0,
                                                                                             0.0});
        GibInt fltAppE_12076_13344 = idx_1798_9971_13335 + 1;
        GibVector *tailapp_17660 =
                   generate_loop_3496_5995(vec1_1802_9974_13343, fltAppE_12076_13344, end_1799_9972_13336, vec_627_9973_13337);

        return tailapp_17660;
    }
}
GibVector *generate_loop_3496_6001(GibVector *vec_1797_9996_13350,
                                   GibInt idx_1798_9997_13351,
                                   GibInt end_1799_9998_13352,
                                   GibVector *vec_627_9999_13353)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_12077_13354 = idx_1798_9997_13351 == end_1799_9998_13352;

    if (fltIf_12077_13354) {
        return vec_1797_9996_13350;
    } else {
        GibFloatGibFloatProd *tmp_390;

        tmp_390 = (GibFloatGibFloatProd *) gib_vector_nth(vec_627_9999_13353,
                                                          idx_1798_9997_13351);

        GibFloatGibFloatProd fltAppE_12079_13357 = *tmp_390;
        GibVector *vec1_1802_10000_13359 =
                  gib_vector_inplace_update(vec_1797_9996_13350,
                                            idx_1798_9997_13351,
                                            &(GibFloatGibFloatGibFloatGibFloatGibFloatProd) {fltAppE_12079_13357.field0,
                                                                                             fltAppE_12079_13357.field1,
                                                                                             1.0,
                                                                                             0.0,
                                                                                             0.0});
        GibInt fltAppE_12080_13360 = idx_1798_9997_13351 + 1;
        GibVector *tailapp_17661 =
                   generate_loop_3496_6001(vec1_1802_10000_13359, fltAppE_12080_13360, end_1799_9998_13352, vec_627_9999_13353);

        return tailapp_17661;
    }
}
GibVector *generate_loop_3495_6007(GibVector *vec_1797_10022_13366,
                                   GibInt idx_1798_10023_13367,
                                   GibInt end_1799_10024_13368,
                                   GibVector *vec_627_10025_13369)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_12081_13370 = idx_1798_10023_13367 == end_1799_10024_13368;

    if (fltIf_12081_13370) {
        return vec_1797_10022_13366;
    } else {
        GibFloatGibFloatProd *tmp_391;

        tmp_391 = (GibFloatGibFloatProd *) gib_vector_nth(vec_627_10025_13369,
                                                          idx_1798_10023_13367);

        GibFloatGibFloatProd fltAppE_12083_13373 = *tmp_391;
        GibVector *vec1_1802_10026_13375 =
                  gib_vector_inplace_update(vec_1797_10022_13366,
                                            idx_1798_10023_13367,
                                            &(GibFloatGibFloatGibFloatProd) {fltAppE_12083_13373.field0,
                                                                             fltAppE_12083_13373.field1,
                                                                             1.0});
        GibInt fltAppE_12084_13376 = idx_1798_10023_13367 + 1;
        GibVector *tailapp_17662 =
                   generate_loop_3495_6007(vec1_1802_10026_13375, fltAppE_12084_13376, end_1799_10024_13368, vec_627_10025_13369);

        return tailapp_17662;
    }
}
GibVector *generate_loop_3495_6013(GibVector *vec_1797_10048_13382,
                                   GibInt idx_1798_10049_13383,
                                   GibInt end_1799_10050_13384,
                                   GibVector *vec_627_10051_13385)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_12085_13386 = idx_1798_10049_13383 == end_1799_10050_13384;

    if (fltIf_12085_13386) {
        return vec_1797_10048_13382;
    } else {
        GibFloatGibFloatProd *tmp_392;

        tmp_392 = (GibFloatGibFloatProd *) gib_vector_nth(vec_627_10051_13385,
                                                          idx_1798_10049_13383);

        GibFloatGibFloatProd fltAppE_12087_13389 = *tmp_392;
        GibVector *vec1_1802_10052_13391 =
                  gib_vector_inplace_update(vec_1797_10048_13382,
                                            idx_1798_10049_13383,
                                            &(GibFloatGibFloatGibFloatProd) {fltAppE_12087_13389.field0,
                                                                             fltAppE_12087_13389.field1,
                                                                             1.0});
        GibInt fltAppE_12088_13392 = idx_1798_10049_13383 + 1;
        GibVector *tailapp_17663 =
                   generate_loop_3495_6013(vec1_1802_10052_13391, fltAppE_12088_13392, end_1799_10050_13384, vec_627_10051_13385);

        return tailapp_17663;
    }
}
GibFloatGibFloatGibFloatProd foldl_loop_3488_6015(GibInt idx_1765_10061_13393,
                                                  GibInt end_1766_10062_13394,
                                                  GibFloatGibFloatGibFloatProd acc_1768_10063_13395,
                                                  GibVector *vec_1769_10064_13396)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_12089_13397 = idx_1765_10061_13393 == end_1766_10062_13394;

    if (fltIf_12089_13397) {
        return acc_1768_10063_13395;
    } else {
        GibFloatGibFloatGibFloatProd *tmp_394;

        tmp_394 =
            (GibFloatGibFloatGibFloatProd *) gib_vector_nth(vec_1769_10064_13396,
                                                            idx_1765_10061_13393);

        GibFloatGibFloatGibFloatProd mpt_1360_9153_11714_13399 = *tmp_394;
        GibFloat fltPrm_12091_13408 = mpt_1360_9153_11714_13399.field0 *
                 mpt_1360_9153_11714_13399.field2;
        GibFloat fltPrd_12090_13409 = acc_1768_10063_13395.field0 +
                 fltPrm_12091_13408;
        GibFloat fltPrm_12093_13410 = mpt_1360_9153_11714_13399.field1 *
                 mpt_1360_9153_11714_13399.field2;
        GibFloat fltPrd_12092_13411 = acc_1768_10063_13395.field1 +
                 fltPrm_12093_13410;
        GibFloat fltPrd_12094_13412 = acc_1768_10063_13395.field2 +
                 mpt_1360_9153_11714_13399.field2;
        GibInt fltAppE_12095_13414 = idx_1765_10061_13393 + 1;
        GibFloatGibFloatGibFloatProd tmp_struct_393 =
                                      foldl_loop_3488_6015(fltAppE_12095_13414, end_1766_10062_13394, (GibFloatGibFloatGibFloatProd) {fltPrd_12090_13409, fltPrd_12092_13411, fltPrd_12094_13412}, vec_1769_10064_13396);
        GibFloat pvrtmp_23656 = tmp_struct_393.field0;
        GibFloat pvrtmp_23657 = tmp_struct_393.field1;
        GibFloat pvrtmp_23658 = tmp_struct_393.field2;

        return (GibFloatGibFloatGibFloatProd) {pvrtmp_23656, pvrtmp_23657,
                                               pvrtmp_23658};
    }
}
GibFloat foldl_loop_3487_6016(GibInt idx_1765_10068_13415,
                              GibInt end_1766_10069_13416,
                              GibFloat acc_1768_10070_13417,
                              GibVector *vec_1769_10071_13418)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_12096_13419 = idx_1765_10068_13415 == end_1766_10069_13416;

    if (fltIf_12096_13419) {
        return acc_1768_10070_13417;
    } else {
        GibFloatGibFloatGibFloatProd *tmp_395;

        tmp_395 =
            (GibFloatGibFloatGibFloatProd *) gib_vector_nth(vec_1769_10071_13418,
                                                            idx_1765_10068_13415);

        GibFloatGibFloatGibFloatProd pt_794_9118_11724_13421 = *tmp_395;
        GibFloat fltPrm_12098_13426 = acc_1768_10070_13417 +
                 pt_794_9118_11724_13421.field0;
        GibFloat fltPrm_12097_13427 = fltPrm_12098_13426 +
                 pt_794_9118_11724_13421.field1;
        GibFloat acc1_1772_10072_13428 = fltPrm_12097_13427 +
                 pt_794_9118_11724_13421.field2;
        GibInt fltAppE_12099_13429 = idx_1765_10068_13415 + 1;
        GibFloat tailapp_17665 =
                  foldl_loop_3487_6016(fltAppE_12099_13429, end_1766_10069_13416, acc1_1772_10072_13428, vec_1769_10071_13418);

        return tailapp_17665;
    }
}
GibFloat foldl_loop_3487_6017(GibInt idx_1765_10075_13430,
                              GibInt end_1766_10076_13431,
                              GibFloat acc_1768_10077_13432,
                              GibVector *vec_1769_10078_13433)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_12100_13434 = idx_1765_10075_13430 == end_1766_10076_13431;

    if (fltIf_12100_13434) {
        return acc_1768_10077_13432;
    } else {
        GibFloatGibFloatGibFloatProd *tmp_396;

        tmp_396 =
            (GibFloatGibFloatGibFloatProd *) gib_vector_nth(vec_1769_10078_13433,
                                                            idx_1765_10075_13430);

        GibFloatGibFloatGibFloatProd pt_1503_9169_11730_13436 = *tmp_396;
        GibFloat fltPrm_12102_13441 = acc_1768_10077_13432 +
                 pt_1503_9169_11730_13436.field0;
        GibFloat fltPrm_12101_13442 = fltPrm_12102_13441 +
                 pt_1503_9169_11730_13436.field1;
        GibFloat acc1_1772_10079_13443 = fltPrm_12101_13442 +
                 pt_1503_9169_11730_13436.field2;
        GibInt fltAppE_12103_13444 = idx_1765_10075_13430 + 1;
        GibFloat tailapp_17666 =
                  foldl_loop_3487_6017(fltAppE_12103_13444, end_1766_10076_13431, acc1_1772_10079_13443, vec_1769_10078_13433);

        return tailapp_17666;
    }
}
GibFloat foldl_loop_3485_6023(GibInt idx_1765_10117_13445,
                              GibInt end_1766_10118_13446,
                              GibFloat acc_1768_10119_13447,
                              GibVector *vec_1769_10120_13448)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_12104_13449 = idx_1765_10117_13445 == end_1766_10118_13446;

    if (fltIf_12104_13449) {
        return acc_1768_10119_13447;
    } else {
        GibFloatGibFloatProd *tmp_397;

        tmp_397 = (GibFloatGibFloatProd *) gib_vector_nth(vec_1769_10120_13448,
                                                          idx_1765_10117_13445);

        GibFloatGibFloatProd pt_312_9003_11748_13451 = *tmp_397;
        GibFloat acc1_1772_10121_13453 =
                  minFloat(pt_312_9003_11748_13451.field0, acc_1768_10119_13447);
        GibInt fltAppE_12106_13454 = idx_1765_10117_13445 + 1;
        GibFloat tailapp_17667 =
                  foldl_loop_3485_6023(fltAppE_12106_13454, end_1766_10118_13446, acc1_1772_10121_13453, vec_1769_10120_13448);

        return tailapp_17667;
    }
}
GibFloat foldl_loop_3485_6024(GibInt idx_1765_10124_13455,
                              GibInt end_1766_10125_13456,
                              GibFloat acc_1768_10126_13457,
                              GibVector *vec_1769_10127_13458)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_12107_13459 = idx_1765_10124_13455 == end_1766_10125_13456;

    if (fltIf_12107_13459) {
        return acc_1768_10126_13457;
    } else {
        GibFloatGibFloatProd *tmp_398;

        tmp_398 = (GibFloatGibFloatProd *) gib_vector_nth(vec_1769_10127_13458,
                                                          idx_1765_10124_13455);

        GibFloatGibFloatProd pt_315_9005_11750_13461 = *tmp_398;
        GibFloat acc1_1772_10128_13463 =
                  minFloat(pt_315_9005_11750_13461.field1, acc_1768_10126_13457);
        GibInt fltAppE_12109_13464 = idx_1765_10124_13455 + 1;
        GibFloat tailapp_17668 =
                  foldl_loop_3485_6024(fltAppE_12109_13464, end_1766_10125_13456, acc1_1772_10128_13463, vec_1769_10127_13458);

        return tailapp_17668;
    }
}
GibFloat foldl_loop_3485_6025(GibInt idx_1765_10131_13465,
                              GibInt end_1766_10132_13466,
                              GibFloat acc_1768_10133_13467,
                              GibVector *vec_1769_10134_13468)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_12110_13469 = idx_1765_10131_13465 == end_1766_10132_13466;

    if (fltIf_12110_13469) {
        return acc_1768_10133_13467;
    } else {
        GibFloatGibFloatProd *tmp_399;

        tmp_399 = (GibFloatGibFloatProd *) gib_vector_nth(vec_1769_10134_13468,
                                                          idx_1765_10131_13465);

        GibFloatGibFloatProd pt_318_9007_11752_13471 = *tmp_399;
        GibFloat acc1_1772_10135_13473 =
                  maxFloat(pt_318_9007_11752_13471.field0, acc_1768_10133_13467);
        GibInt fltAppE_12112_13474 = idx_1765_10131_13465 + 1;
        GibFloat tailapp_17669 =
                  foldl_loop_3485_6025(fltAppE_12112_13474, end_1766_10132_13466, acc1_1772_10135_13473, vec_1769_10134_13468);

        return tailapp_17669;
    }
}
GibFloat foldl_loop_3485_6026(GibInt idx_1765_10138_13475,
                              GibInt end_1766_10139_13476,
                              GibFloat acc_1768_10140_13477,
                              GibVector *vec_1769_10141_13478)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_12113_13479 = idx_1765_10138_13475 == end_1766_10139_13476;

    if (fltIf_12113_13479) {
        return acc_1768_10140_13477;
    } else {
        GibFloatGibFloatProd *tmp_400;

        tmp_400 = (GibFloatGibFloatProd *) gib_vector_nth(vec_1769_10141_13478,
                                                          idx_1765_10138_13475);

        GibFloatGibFloatProd pt_321_9009_11754_13481 = *tmp_400;
        GibFloat acc1_1772_10142_13483 =
                  maxFloat(pt_321_9009_11754_13481.field1, acc_1768_10140_13477);
        GibInt fltAppE_12115_13484 = idx_1765_10138_13475 + 1;
        GibFloat tailapp_17670 =
                  foldl_loop_3485_6026(fltAppE_12115_13484, end_1766_10139_13476, acc1_1772_10142_13483, vec_1769_10141_13478);

        return tailapp_17670;
    }
}
GibFloat foldl_loop_3485_6031(GibInt idx_1765_10173_13485,
                              GibInt end_1766_10174_13486,
                              GibFloat acc_1768_10175_13487,
                              GibVector *vec_1769_10176_13488)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_12116_13489 = idx_1765_10173_13485 == end_1766_10174_13486;

    if (fltIf_12116_13489) {
        return acc_1768_10175_13487;
    } else {
        GibFloatGibFloatProd *tmp_401;

        tmp_401 = (GibFloatGibFloatProd *) gib_vector_nth(vec_1769_10176_13488,
                                                          idx_1765_10173_13485);

        GibFloatGibFloatProd pt_364_9035_11764_13491 = *tmp_401;
        GibFloat acc1_1772_10177_13493 =
                  minFloat(pt_364_9035_11764_13491.field0, acc_1768_10175_13487);
        GibInt fltAppE_12118_13494 = idx_1765_10173_13485 + 1;
        GibFloat tailapp_17671 =
                  foldl_loop_3485_6031(fltAppE_12118_13494, end_1766_10174_13486, acc1_1772_10177_13493, vec_1769_10176_13488);

        return tailapp_17671;
    }
}
GibFloat foldl_loop_3485_6032(GibInt idx_1765_10180_13495,
                              GibInt end_1766_10181_13496,
                              GibFloat acc_1768_10182_13497,
                              GibVector *vec_1769_10183_13498)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_12119_13499 = idx_1765_10180_13495 == end_1766_10181_13496;

    if (fltIf_12119_13499) {
        return acc_1768_10182_13497;
    } else {
        GibFloatGibFloatProd *tmp_402;

        tmp_402 = (GibFloatGibFloatProd *) gib_vector_nth(vec_1769_10183_13498,
                                                          idx_1765_10180_13495);

        GibFloatGibFloatProd pt_367_9037_11766_13501 = *tmp_402;
        GibFloat acc1_1772_10184_13503 =
                  minFloat(pt_367_9037_11766_13501.field1, acc_1768_10182_13497);
        GibInt fltAppE_12121_13504 = idx_1765_10180_13495 + 1;
        GibFloat tailapp_17672 =
                  foldl_loop_3485_6032(fltAppE_12121_13504, end_1766_10181_13496, acc1_1772_10184_13503, vec_1769_10183_13498);

        return tailapp_17672;
    }
}
GibFloat foldl_loop_3485_6033(GibInt idx_1765_10187_13505,
                              GibInt end_1766_10188_13506,
                              GibFloat acc_1768_10189_13507,
                              GibVector *vec_1769_10190_13508)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_12122_13509 = idx_1765_10187_13505 == end_1766_10188_13506;

    if (fltIf_12122_13509) {
        return acc_1768_10189_13507;
    } else {
        GibFloatGibFloatProd *tmp_403;

        tmp_403 = (GibFloatGibFloatProd *) gib_vector_nth(vec_1769_10190_13508,
                                                          idx_1765_10187_13505);

        GibFloatGibFloatProd pt_370_9039_11768_13511 = *tmp_403;
        GibFloat acc1_1772_10191_13513 =
                  maxFloat(pt_370_9039_11768_13511.field0, acc_1768_10189_13507);
        GibInt fltAppE_12124_13514 = idx_1765_10187_13505 + 1;
        GibFloat tailapp_17673 =
                  foldl_loop_3485_6033(fltAppE_12124_13514, end_1766_10188_13506, acc1_1772_10191_13513, vec_1769_10190_13508);

        return tailapp_17673;
    }
}
GibFloat foldl_loop_3485_6034(GibInt idx_1765_10194_13515,
                              GibInt end_1766_10195_13516,
                              GibFloat acc_1768_10196_13517,
                              GibVector *vec_1769_10197_13518)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_12125_13519 = idx_1765_10194_13515 == end_1766_10195_13516;

    if (fltIf_12125_13519) {
        return acc_1768_10196_13517;
    } else {
        GibFloatGibFloatProd *tmp_404;

        tmp_404 = (GibFloatGibFloatProd *) gib_vector_nth(vec_1769_10197_13518,
                                                          idx_1765_10194_13515);

        GibFloatGibFloatProd pt_373_9041_11770_13521 = *tmp_404;
        GibFloat acc1_1772_10198_13523 =
                  maxFloat(pt_373_9041_11770_13521.field1, acc_1768_10196_13517);
        GibInt fltAppE_12127_13524 = idx_1765_10194_13515 + 1;
        GibFloat tailapp_17674 =
                  foldl_loop_3485_6034(fltAppE_12127_13524, end_1766_10195_13516, acc1_1772_10198_13523, vec_1769_10197_13518);

        return tailapp_17674;
    }
}
GibBoolGibIntProd foldl_loop_3484_6035(GibInt idx_1765_10199_13525,
                                       GibInt end_1766_10200_13526,
                                       GibBoolGibIntProd acc_1768_10201_13527,
                                       GibVector *vec_1769_10202_13528,
                                       GibVector *pts_545_10203_13529,
                                       GibVector *actual_546_10204_13530)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_12128_13531 = idx_1765_10199_13525 == end_1766_10200_13526;

    if (fltIf_12128_13531) {
        return acc_1768_10201_13527;
    } else {
        GibInt *tmp_408;

        tmp_408 = (GibInt *) gib_vector_nth(vec_1769_10202_13528,
                                            idx_1765_10199_13525);

        GibInt i_550_9059_11772_13533 = *tmp_408;
        GibFloatGibFloatGibFloatProd *tmp_407;

        tmp_407 =
            (GibFloatGibFloatGibFloatProd *) gib_vector_nth(pts_545_10203_13529,
                                                            i_550_9059_11772_13533);

        GibFloatGibFloatGibFloatProd pt_552_9062_11775_13536 = *tmp_407;
        GibFloatGibFloatGibFloatProd *tmp_406;

        tmp_406 =
            (GibFloatGibFloatGibFloatProd *) gib_vector_nth(actual_546_10204_13530,
                                                            i_550_9059_11772_13533);

        GibFloatGibFloatGibFloatProd nn_553_9063_11776_13537 = *tmp_406;
        GibBool fltIf_12129_13541 =
                 eq_point3d((GibFloatGibFloatGibFloatProd) {pt_552_9062_11775_13536.field0, pt_552_9062_11775_13536.field1, pt_552_9062_11775_13536.field2}, (GibFloatGibFloatGibFloatProd) {nn_553_9063_11776_13537.field0, nn_553_9063_11776_13537.field1, nn_553_9063_11776_13537.field2});
        GibBool pvrtmp_23665;
        GibInt pvrtmp_23666;

        if (fltIf_12129_13541) {
            GibBool fltPrd_12130_13543 = acc_1768_10201_13527.field0 && true;

            pvrtmp_23665 = fltPrd_12130_13543;
            pvrtmp_23666 = acc_1768_10201_13527.field1;
        } else {
            GibInt fltPrd_12133_13545 = acc_1768_10201_13527.field1 + 1;

            pvrtmp_23665 = false;
            pvrtmp_23666 = fltPrd_12133_13545;
        }

        GibInt fltAppE_12134_13547 = idx_1765_10199_13525 + 1;
        GibBoolGibIntProd tmp_struct_405 =
                           foldl_loop_3484_6035(fltAppE_12134_13547, end_1766_10200_13526, (GibBoolGibIntProd) {pvrtmp_23665, pvrtmp_23666}, vec_1769_10202_13528, pts_545_10203_13529, actual_546_10204_13530);
        GibBool pvrtmp_23669 = tmp_struct_405.field0;
        GibInt pvrtmp_23670 = tmp_struct_405.field1;

        return (GibBoolGibIntProd) {pvrtmp_23669, pvrtmp_23670};
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_Tree(GibCursor end_r_15754,
                                                             GibCursor end_r_15755,
                                                             GibCursor loc_15753,
                                                             GibCursor arg_7118_10206_13548)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_15753 + 18 > end_r_15755) {
        gib_grow_region(&loc_15753, &end_r_15755);
    }

    GibPackedTag tmpval_23671 = *(GibPackedTag *) arg_7118_10206_13548;
    GibCursor tmpcur_23672 = arg_7118_10206_13548 + 1;


  switch_23731:
    ;
    switch (tmpval_23671) {

      case 0:
        {
            GibInt tmpval_23673 = *(GibInt *) tmpcur_23672;
            GibCursor tmpcur_23674 = tmpcur_23672 + sizeof(GibInt);
            GibCursor jump_17676 = tmpcur_23672 + 8;

            *(GibPackedTag *) loc_15753 = 0;

            GibCursor writetag_19779 = loc_15753 + 1;
            GibCursor after_tag_19780 = loc_15753 + 1;

            *(GibInt *) after_tag_19780 = tmpval_23673;

            GibCursor writecur_19784 = after_tag_19780 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15754,
                                                                        end_r_15755,
                                                                        jump_17676,
                                                                        loc_15753,
                                                                        writecur_19784};
            break;
        }

      case 1:
        {
            GibInt tmpval_23679 = *(GibInt *) tmpcur_23672;
            GibCursor tmpcur_23680 = tmpcur_23672 + sizeof(GibInt);
            GibCursor loc_16554 = loc_15753 + 9;

            *(GibPackedTag *) loc_15753 = 1;

            GibCursor writetag_19795 = loc_15753 + 1;
            GibCursor after_tag_19796 = loc_15753 + 1;

            *(GibInt *) after_tag_19796 = tmpval_23679;

            GibCursor writecur_19800 = after_tag_19796 + sizeof(GibInt);

            gib_shadowstack_push(rstack, loc_15753, end_r_15755, Stk, Tree_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_409 =
                                                               _copy_Tree(end_r_15754, end_r_15755, loc_16554, tmpcur_23680);
            GibCursor pvrtmp_23681 = tmp_struct_409.field0;
            GibCursor pvrtmp_23682 = tmp_struct_409.field1;
            GibCursor pvrtmp_23683 = tmp_struct_409.field2;
            GibCursor pvrtmp_23684 = tmp_struct_409.field3;
            GibCursor pvrtmp_23685 = tmp_struct_409.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_15753 = frame->ptr;
            end_r_15755 = frame->endptr;
            gib_shadowstack_push(rstack, loc_15753, pvrtmp_23682, Stk, Tree_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_410 =
                                                               _copy_Tree(pvrtmp_23681, pvrtmp_23682, pvrtmp_23685, pvrtmp_23683);
            GibCursor pvrtmp_23690 = tmp_struct_410.field0;
            GibCursor pvrtmp_23691 = tmp_struct_410.field1;
            GibCursor pvrtmp_23692 = tmp_struct_410.field2;
            GibCursor pvrtmp_23693 = tmp_struct_410.field3;
            GibCursor pvrtmp_23694 = tmp_struct_410.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_15753 = frame->ptr;
            pvrtmp_23682 = frame->endptr;
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_23690,
                                                                        pvrtmp_23691,
                                                                        pvrtmp_23692,
                                                                        loc_15753,
                                                                        pvrtmp_23694};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_412 = *(uintptr_t *) tmpcur_23672;
            GibCursor tmpcur_23703 = GIB_UNTAG(tagged_tmpcur_412);
            GibCursor tmpaftercur_23704 = tmpcur_23672 + 8;
            uint16_t tmptag_23705 = GIB_GET_TAG(tagged_tmpcur_412);
            GibCursor end_from_tagged_indr_18084 = tmpcur_23703 + tmptag_23705;
            GibCursor jump_18086 = tmpcur_23672 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_411 =
                                                               _copy_Tree(end_from_tagged_indr_18084, end_r_15755, loc_15753, tmpcur_23703);
            GibCursor pvrtmp_23706 = tmp_struct_411.field0;
            GibCursor pvrtmp_23707 = tmp_struct_411.field1;
            GibCursor pvrtmp_23708 = tmp_struct_411.field2;
            GibCursor pvrtmp_23709 = tmp_struct_411.field3;
            GibCursor pvrtmp_23710 = tmp_struct_411.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15754,
                                                                        pvrtmp_23707,
                                                                        jump_18086,
                                                                        pvrtmp_23709,
                                                                        pvrtmp_23710};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_414 = *(uintptr_t *) tmpcur_23672;
            GibCursor tmpcur_23717 = GIB_UNTAG(tagged_tmpcur_414);
            GibCursor tmpaftercur_23718 = tmpcur_23672 + 8;
            uint16_t tmptag_23719 = GIB_GET_TAG(tagged_tmpcur_414);
            GibCursor end_from_tagged_indr_18084 = tmpcur_23717 + tmptag_23719;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_413 =
                                                               _copy_Tree(end_from_tagged_indr_18084, end_r_15755, loc_15753, tmpcur_23717);
            GibCursor pvrtmp_23720 = tmp_struct_413.field0;
            GibCursor pvrtmp_23721 = tmp_struct_413.field1;
            GibCursor pvrtmp_23722 = tmp_struct_413.field2;
            GibCursor pvrtmp_23723 = tmp_struct_413.field3;
            GibCursor pvrtmp_23724 = tmp_struct_413.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_23720,
                                                                        pvrtmp_23721,
                                                                        pvrtmp_23722,
                                                                        pvrtmp_23723,
                                                                        pvrtmp_23724};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_23671");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_Tree(GibCursor end_r_15758,
                                                                          GibCursor end_r_15759,
                                                                          GibCursor loc_15757,
                                                                          GibCursor arg_7127_10215_13557)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_23732 = *(GibPackedTag *) arg_7127_10215_13557;
    GibCursor tmpcur_23733 = arg_7127_10215_13557 + 1;


  switch_23792:
    ;
    switch (tmpval_23732) {

      case 0:
        {
            GibInt tmpval_23734 = *(GibInt *) tmpcur_23733;
            GibCursor tmpcur_23735 = tmpcur_23733 + sizeof(GibInt);
            GibCursor jump_17682 = tmpcur_23733 + 8;

            *(GibPackedTag *) loc_15757 = 0;

            GibCursor writetag_19818 = loc_15757 + 1;
            GibCursor after_tag_19819 = loc_15757 + 1;

            *(GibInt *) after_tag_19819 = tmpval_23734;

            GibCursor writecur_19823 = after_tag_19819 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15758,
                                                                        end_r_15759,
                                                                        jump_17682,
                                                                        loc_15757,
                                                                        writecur_19823};
            break;
        }

      case 1:
        {
            GibInt tmpval_23740 = *(GibInt *) tmpcur_23733;
            GibCursor tmpcur_23741 = tmpcur_23733 + sizeof(GibInt);
            GibCursor loc_16576 = loc_15757 + 9;

            *(GibPackedTag *) loc_15757 = 1;

            GibCursor writetag_19834 = loc_15757 + 1;
            GibCursor after_tag_19835 = loc_15757 + 1;

            *(GibInt *) after_tag_19835 = tmpval_23740;

            GibCursor writecur_19839 = after_tag_19835 + sizeof(GibInt);

            gib_shadowstack_push(rstack, loc_15757, end_r_15759, Stk, Tree_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_418 =
                                                               _copy_without_ptrs_Tree(end_r_15758, end_r_15759, loc_16576, tmpcur_23741);
            GibCursor pvrtmp_23742 = tmp_struct_418.field0;
            GibCursor pvrtmp_23743 = tmp_struct_418.field1;
            GibCursor pvrtmp_23744 = tmp_struct_418.field2;
            GibCursor pvrtmp_23745 = tmp_struct_418.field3;
            GibCursor pvrtmp_23746 = tmp_struct_418.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_15757 = frame->ptr;
            end_r_15759 = frame->endptr;
            gib_shadowstack_push(rstack, loc_15757, pvrtmp_23743, Stk, Tree_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_419 =
                                                               _copy_without_ptrs_Tree(pvrtmp_23742, pvrtmp_23743, pvrtmp_23746, pvrtmp_23744);
            GibCursor pvrtmp_23751 = tmp_struct_419.field0;
            GibCursor pvrtmp_23752 = tmp_struct_419.field1;
            GibCursor pvrtmp_23753 = tmp_struct_419.field2;
            GibCursor pvrtmp_23754 = tmp_struct_419.field3;
            GibCursor pvrtmp_23755 = tmp_struct_419.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_15757 = frame->ptr;
            pvrtmp_23743 = frame->endptr;
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_23751,
                                                                        pvrtmp_23752,
                                                                        pvrtmp_23753,
                                                                        loc_15757,
                                                                        pvrtmp_23755};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_421 = *(uintptr_t *) tmpcur_23733;
            GibCursor tmpcur_23764 = GIB_UNTAG(tagged_tmpcur_421);
            GibCursor tmpaftercur_23765 = tmpcur_23733 + 8;
            uint16_t tmptag_23766 = GIB_GET_TAG(tagged_tmpcur_421);
            GibCursor end_from_tagged_indr_18090 = tmpcur_23764 + tmptag_23766;
            GibCursor jump_18092 = tmpcur_23733 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_420 =
                                                               _copy_without_ptrs_Tree(end_from_tagged_indr_18090, end_r_15759, loc_15757, tmpcur_23764);
            GibCursor pvrtmp_23767 = tmp_struct_420.field0;
            GibCursor pvrtmp_23768 = tmp_struct_420.field1;
            GibCursor pvrtmp_23769 = tmp_struct_420.field2;
            GibCursor pvrtmp_23770 = tmp_struct_420.field3;
            GibCursor pvrtmp_23771 = tmp_struct_420.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15758,
                                                                        pvrtmp_23768,
                                                                        jump_18092,
                                                                        pvrtmp_23770,
                                                                        pvrtmp_23771};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_423 = *(uintptr_t *) tmpcur_23733;
            GibCursor tmpcur_23778 = GIB_UNTAG(tagged_tmpcur_423);
            GibCursor tmpaftercur_23779 = tmpcur_23733 + 8;
            uint16_t tmptag_23780 = GIB_GET_TAG(tagged_tmpcur_423);
            GibCursor end_from_tagged_indr_18090 = tmpcur_23778 + tmptag_23780;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_422 =
                                                               _copy_without_ptrs_Tree(end_from_tagged_indr_18090, end_r_15759, loc_15757, tmpcur_23778);
            GibCursor pvrtmp_23781 = tmp_struct_422.field0;
            GibCursor pvrtmp_23782 = tmp_struct_422.field1;
            GibCursor pvrtmp_23783 = tmp_struct_422.field2;
            GibCursor pvrtmp_23784 = tmp_struct_422.field3;
            GibCursor pvrtmp_23785 = tmp_struct_422.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_23781,
                                                                        pvrtmp_23782,
                                                                        pvrtmp_23783,
                                                                        pvrtmp_23784,
                                                                        pvrtmp_23785};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_23732");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_Tree(GibCursor end_r_15761,
                                      GibCursor arg_7136_10224_13566)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_23793 = *(GibPackedTag *) arg_7136_10224_13566;
    GibCursor tmpcur_23794 = arg_7136_10224_13566 + 1;


  switch_23813:
    ;
    switch (tmpval_23793) {

      case 0:
        {
            GibInt tmpval_23795 = *(GibInt *) tmpcur_23794;
            GibCursor tmpcur_23796 = tmpcur_23794 + sizeof(GibInt);
            GibCursor jump_17688 = tmpcur_23794 + 8;

            return (GibCursorGibCursorProd) {end_r_15761, jump_17688};
            break;
        }

      case 1:
        {
            GibInt tmpval_23797 = *(GibInt *) tmpcur_23794;
            GibCursor tmpcur_23798 = tmpcur_23794 + sizeof(GibInt);
            GibCursorGibCursorProd tmp_struct_424 =
                                    _traverse_Tree(end_r_15761, tmpcur_23798);
            GibCursor pvrtmp_23799 = tmp_struct_424.field0;
            GibCursor pvrtmp_23800 = tmp_struct_424.field1;
            GibCursorGibCursorProd tmp_struct_425 =
                                    _traverse_Tree(pvrtmp_23799, pvrtmp_23800);
            GibCursor pvrtmp_23801 = tmp_struct_425.field0;
            GibCursor pvrtmp_23802 = tmp_struct_425.field1;

            return (GibCursorGibCursorProd) {pvrtmp_23801, pvrtmp_23802};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_427 = *(uintptr_t *) tmpcur_23794;
            GibCursor tmpcur_23803 = GIB_UNTAG(tagged_tmpcur_427);
            GibCursor tmpaftercur_23804 = tmpcur_23794 + 8;
            uint16_t tmptag_23805 = GIB_GET_TAG(tagged_tmpcur_427);
            GibCursor end_from_tagged_indr_18096 = tmpcur_23803 + tmptag_23805;
            GibCursor jump_18098 = tmpcur_23794 + 8;
            GibCursorGibCursorProd tmp_struct_426 =
                                    _traverse_Tree(end_from_tagged_indr_18096, tmpcur_23803);
            GibCursor pvrtmp_23806 = tmp_struct_426.field0;
            GibCursor pvrtmp_23807 = tmp_struct_426.field1;

            return (GibCursorGibCursorProd) {end_r_15761, jump_18098};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_429 = *(uintptr_t *) tmpcur_23794;
            GibCursor tmpcur_23808 = GIB_UNTAG(tagged_tmpcur_429);
            GibCursor tmpaftercur_23809 = tmpcur_23794 + 8;
            uint16_t tmptag_23810 = GIB_GET_TAG(tagged_tmpcur_429);
            GibCursor end_from_tagged_indr_18096 = tmpcur_23808 + tmptag_23810;
            GibCursorGibCursorProd tmp_struct_428 =
                                    _traverse_Tree(end_from_tagged_indr_18096, tmpcur_23808);
            GibCursor pvrtmp_23811 = tmp_struct_428.field0;
            GibCursor pvrtmp_23812 = tmp_struct_428.field1;

            return (GibCursorGibCursorProd) {pvrtmp_23811, pvrtmp_23812};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_23793");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_Tree(GibCursor end_r_15763,
                                   GibCursor arg_7145_10231_13573)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_23814 = *(GibPackedTag *) arg_7145_10231_13573;
    GibCursor tmpcur_23815 = arg_7145_10231_13573 + 1;


  switch_23834:
    ;
    switch (tmpval_23814) {

      case 0:
        {
            GibInt tmpval_23816 = *(GibInt *) tmpcur_23815;
            GibCursor tmpcur_23817 = tmpcur_23815 + sizeof(GibInt);
            GibCursor jump_17694 = tmpcur_23815 + 8;
            unsigned char wildcard_7148_10233_13575 = gib_print_symbol(21864);
            unsigned char y_7147_10234_13576 = printf("%ld", tmpval_23816);
            unsigned char wildcard_7149_10235_13577 = gib_print_symbol(21857);

            return (GibCursorGibCursorProd) {end_r_15763, jump_17694};
            break;
        }

      case 1:
        {
            GibInt tmpval_23818 = *(GibInt *) tmpcur_23815;
            GibCursor tmpcur_23819 = tmpcur_23815 + sizeof(GibInt);
            unsigned char wildcard_7156_10239_13581 = gib_print_symbol(21860);
            unsigned char y_7153_10240_13582 = printf("%ld", tmpval_23818);
            GibCursorGibCursorProd tmp_struct_430 =
                                    _print_Tree(end_r_15763, tmpcur_23819);
            GibCursor pvrtmp_23820 = tmp_struct_430.field0;
            GibCursor pvrtmp_23821 = tmp_struct_430.field1;
            GibCursorGibCursorProd tmp_struct_431 =
                                    _print_Tree(pvrtmp_23820, pvrtmp_23821);
            GibCursor pvrtmp_23822 = tmp_struct_431.field0;
            GibCursor pvrtmp_23823 = tmp_struct_431.field1;
            unsigned char wildcard_7157_10243_13585 = gib_print_symbol(21857);

            return (GibCursorGibCursorProd) {pvrtmp_23822, pvrtmp_23823};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_433 = *(uintptr_t *) tmpcur_23815;
            GibCursor tmpcur_23824 = GIB_UNTAG(tagged_tmpcur_433);
            GibCursor tmpaftercur_23825 = tmpcur_23815 + 8;
            uint16_t tmptag_23826 = GIB_GET_TAG(tagged_tmpcur_433);
            GibCursor end_from_tagged_indr_18102 = tmpcur_23824 + tmptag_23826;
            GibCursor jump_18104 = tmpcur_23815 + 8;
            unsigned char wildcard_18107 = gib_print_symbol(21876);
            GibCursorGibCursorProd tmp_struct_432 =
                                    _print_Tree(end_from_tagged_indr_18102, tmpcur_23824);
            GibCursor pvrtmp_23827 = tmp_struct_432.field0;
            GibCursor pvrtmp_23828 = tmp_struct_432.field1;

            return (GibCursorGibCursorProd) {end_r_15763, jump_18104};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_435 = *(uintptr_t *) tmpcur_23815;
            GibCursor tmpcur_23829 = GIB_UNTAG(tagged_tmpcur_435);
            GibCursor tmpaftercur_23830 = tmpcur_23815 + 8;
            uint16_t tmptag_23831 = GIB_GET_TAG(tagged_tmpcur_435);
            GibCursor end_from_tagged_indr_18102 = tmpcur_23829 + tmptag_23831;
            unsigned char wildcard_18107 = gib_print_symbol(21875);
            GibCursorGibCursorProd tmp_struct_434 =
                                    _print_Tree(end_from_tagged_indr_18102, tmpcur_23829);
            GibCursor pvrtmp_23832 = tmp_struct_434.field0;
            GibCursor pvrtmp_23833 = tmp_struct_434.field1;

            return (GibCursorGibCursorProd) {pvrtmp_23832, pvrtmp_23833};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_23814");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_KdTree(GibCursor end_r_15766,
                                                               GibCursor end_r_15767,
                                                               GibCursor loc_15765,
                                                               GibCursor arg_7158_10244_13586)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_15765 + 74 > end_r_15767) {
        gib_grow_region(&loc_15765, &end_r_15767);
    }

    GibPackedTag tmpval_23835 = *(GibPackedTag *) arg_7158_10244_13586;
    GibCursor tmpcur_23836 = arg_7158_10244_13586 + 1;


  switch_23928:
    ;
    switch (tmpval_23835) {

      case 0:
        {
            GibFloat tmpval_23837 = *(GibFloat *) tmpcur_23836;
            GibCursor tmpcur_23838 = tmpcur_23836 + sizeof(GibFloat);
            GibFloat tmpval_23839 = *(GibFloat *) tmpcur_23838;
            GibCursor tmpcur_23840 = tmpcur_23838 + sizeof(GibFloat);
            GibFloat tmpval_23841 = *(GibFloat *) tmpcur_23840;
            GibCursor tmpcur_23842 = tmpcur_23840 + sizeof(GibFloat);
            GibCursor jump_17702 = tmpcur_23840 + 4;

            *(GibPackedTag *) loc_15765 = 0;

            GibCursor writetag_19891 = loc_15765 + 1;
            GibCursor after_tag_19892 = loc_15765 + 1;

            *(GibFloat *) after_tag_19892 = tmpval_23837;

            GibCursor writecur_19896 = after_tag_19892 + sizeof(GibFloat);

            *(GibFloat *) writecur_19896 = tmpval_23839;

            GibCursor writecur_19897 = writecur_19896 + sizeof(GibFloat);

            *(GibFloat *) writecur_19897 = tmpval_23841;

            GibCursor writecur_19898 = writecur_19897 + sizeof(GibFloat);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15766,
                                                                        end_r_15767,
                                                                        jump_17702,
                                                                        loc_15765,
                                                                        writecur_19898};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_439 = *(uintptr_t *) tmpcur_23836;
            GibCursor tmpcur_23847 = GIB_UNTAG(tagged_tmpcur_439);
            GibCursor tmpaftercur_23848 = tmpcur_23836 + 8;
            uint16_t tmptag_23849 = GIB_GET_TAG(tagged_tmpcur_439);
            GibCursor end_from_tagged_absran_15591 = tmpcur_23847 +
                      tmptag_23849;
            GibFloat tmpval_23850 = *(GibFloat *) tmpaftercur_23848;
            GibCursor tmpcur_23851 = tmpaftercur_23848 + sizeof(GibFloat);
            GibFloat tmpval_23852 = *(GibFloat *) tmpcur_23851;
            GibCursor tmpcur_23853 = tmpcur_23851 + sizeof(GibFloat);
            GibFloat tmpval_23854 = *(GibFloat *) tmpcur_23853;
            GibCursor tmpcur_23855 = tmpcur_23853 + sizeof(GibFloat);
            GibInt tmpval_23856 = *(GibInt *) tmpcur_23855;
            GibCursor tmpcur_23857 = tmpcur_23855 + sizeof(GibInt);
            GibInt tmpval_23858 = *(GibInt *) tmpcur_23857;
            GibCursor tmpcur_23859 = tmpcur_23857 + sizeof(GibInt);
            GibFloat tmpval_23860 = *(GibFloat *) tmpcur_23859;
            GibCursor tmpcur_23861 = tmpcur_23859 + sizeof(GibFloat);
            GibFloat tmpval_23862 = *(GibFloat *) tmpcur_23861;
            GibCursor tmpcur_23863 = tmpcur_23861 + sizeof(GibFloat);
            GibFloat tmpval_23864 = *(GibFloat *) tmpcur_23863;
            GibCursor tmpcur_23865 = tmpcur_23863 + sizeof(GibFloat);
            GibFloat tmpval_23866 = *(GibFloat *) tmpcur_23865;
            GibCursor tmpcur_23867 = tmpcur_23865 + sizeof(GibFloat);
            GibFloat tmpval_23868 = *(GibFloat *) tmpcur_23867;
            GibCursor tmpcur_23869 = tmpcur_23867 + sizeof(GibFloat);
            GibFloat tmpval_23870 = *(GibFloat *) tmpcur_23869;
            GibCursor tmpcur_23871 = tmpcur_23869 + sizeof(GibFloat);
            GibFloat tmpval_23872 = *(GibFloat *) tmpcur_23871;
            GibCursor tmpcur_23873 = tmpcur_23871 + sizeof(GibFloat);
            GibCursor loc_16650 = loc_15765 + 65;

            *(GibPackedTag *) loc_15765 = 3;

            GibCursor writetag_19921 = loc_15765 + 1;

            gib_shadowstack_push(rstack, loc_15765, end_r_15767, Stk, KdTree_T);
            gib_shadowstack_push(rstack, tmpcur_23847, end_r_15766, Stk,
                                 KdTree_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_436 =
                                                               _copy_KdTree(end_r_15766, end_r_15767, loc_16650, tmpcur_23873);
            GibCursor pvrtmp_23874 = tmp_struct_436.field0;
            GibCursor pvrtmp_23875 = tmp_struct_436.field1;
            GibCursor pvrtmp_23876 = tmp_struct_436.field2;
            GibCursor pvrtmp_23877 = tmp_struct_436.field3;
            GibCursor pvrtmp_23878 = tmp_struct_436.field4;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_23847 = frame->ptr;
            end_r_15766 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_15765 = frame->ptr;
            end_r_15767 = frame->endptr;
            gib_shadowstack_push(rstack, loc_15765, pvrtmp_23875, Stk,
                                 KdTree_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_437 =
                                                               _copy_KdTree(end_from_tagged_absran_15591, pvrtmp_23875, pvrtmp_23878, tmpcur_23847);
            GibCursor pvrtmp_23883 = tmp_struct_437.field0;
            GibCursor pvrtmp_23884 = tmp_struct_437.field1;
            GibCursor pvrtmp_23885 = tmp_struct_437.field2;
            GibCursor pvrtmp_23886 = tmp_struct_437.field3;
            GibCursor pvrtmp_23887 = tmp_struct_437.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_15765 = frame->ptr;
            pvrtmp_23875 = frame->endptr;

            uint16_t offset_438 = pvrtmp_23875 - pvrtmp_23878;
            uintptr_t ran_15594 = GIB_STORE_TAG(pvrtmp_23878, offset_438);
            GibCursor after_tag_19922 = loc_15765 + 1;

            *(uintptr_t *) after_tag_19922 = ran_15594;

            GibCursor writecur_19926 = after_tag_19922 + 8;

            *(GibFloat *) writecur_19926 = tmpval_23850;

            GibCursor writecur_19927 = writecur_19926 + sizeof(GibFloat);

            *(GibFloat *) writecur_19927 = tmpval_23852;

            GibCursor writecur_19928 = writecur_19927 + sizeof(GibFloat);

            *(GibFloat *) writecur_19928 = tmpval_23854;

            GibCursor writecur_19929 = writecur_19928 + sizeof(GibFloat);

            *(GibInt *) writecur_19929 = tmpval_23856;

            GibCursor writecur_19930 = writecur_19929 + sizeof(GibInt);

            *(GibInt *) writecur_19930 = tmpval_23858;

            GibCursor writecur_19931 = writecur_19930 + sizeof(GibInt);

            *(GibFloat *) writecur_19931 = tmpval_23860;

            GibCursor writecur_19932 = writecur_19931 + sizeof(GibFloat);

            *(GibFloat *) writecur_19932 = tmpval_23862;

            GibCursor writecur_19933 = writecur_19932 + sizeof(GibFloat);

            *(GibFloat *) writecur_19933 = tmpval_23864;

            GibCursor writecur_19934 = writecur_19933 + sizeof(GibFloat);

            *(GibFloat *) writecur_19934 = tmpval_23866;

            GibCursor writecur_19935 = writecur_19934 + sizeof(GibFloat);

            *(GibFloat *) writecur_19935 = tmpval_23868;

            GibCursor writecur_19936 = writecur_19935 + sizeof(GibFloat);

            *(GibFloat *) writecur_19936 = tmpval_23870;

            GibCursor writecur_19937 = writecur_19936 + sizeof(GibFloat);

            *(GibFloat *) writecur_19937 = tmpval_23872;

            GibCursor writecur_19938 = writecur_19937 + sizeof(GibFloat);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_23883,
                                                                        pvrtmp_23884,
                                                                        pvrtmp_23885,
                                                                        loc_15765,
                                                                        pvrtmp_23887};
            break;
        }

      case 2:
        {
            GibCursor jump_17720 = arg_7158_10244_13586 + 1;

            *(GibPackedTag *) loc_15765 = 2;

            GibCursor writetag_19945 = loc_15765 + 1;
            GibCursor after_tag_19946 = loc_15765 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15766,
                                                                        end_r_15767,
                                                                        jump_17720,
                                                                        loc_15765,
                                                                        after_tag_19946};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_441 = *(uintptr_t *) tmpcur_23836;
            GibCursor tmpcur_23900 = GIB_UNTAG(tagged_tmpcur_441);
            GibCursor tmpaftercur_23901 = tmpcur_23836 + 8;
            uint16_t tmptag_23902 = GIB_GET_TAG(tagged_tmpcur_441);
            GibCursor end_from_tagged_indr_18108 = tmpcur_23900 + tmptag_23902;
            GibCursor jump_18110 = tmpcur_23836 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_440 =
                                                               _copy_KdTree(end_from_tagged_indr_18108, end_r_15767, loc_15765, tmpcur_23900);
            GibCursor pvrtmp_23903 = tmp_struct_440.field0;
            GibCursor pvrtmp_23904 = tmp_struct_440.field1;
            GibCursor pvrtmp_23905 = tmp_struct_440.field2;
            GibCursor pvrtmp_23906 = tmp_struct_440.field3;
            GibCursor pvrtmp_23907 = tmp_struct_440.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15766,
                                                                        pvrtmp_23904,
                                                                        jump_18110,
                                                                        pvrtmp_23906,
                                                                        pvrtmp_23907};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_443 = *(uintptr_t *) tmpcur_23836;
            GibCursor tmpcur_23914 = GIB_UNTAG(tagged_tmpcur_443);
            GibCursor tmpaftercur_23915 = tmpcur_23836 + 8;
            uint16_t tmptag_23916 = GIB_GET_TAG(tagged_tmpcur_443);
            GibCursor end_from_tagged_indr_18108 = tmpcur_23914 + tmptag_23916;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_442 =
                                                               _copy_KdTree(end_from_tagged_indr_18108, end_r_15767, loc_15765, tmpcur_23914);
            GibCursor pvrtmp_23917 = tmp_struct_442.field0;
            GibCursor pvrtmp_23918 = tmp_struct_442.field1;
            GibCursor pvrtmp_23919 = tmp_struct_442.field2;
            GibCursor pvrtmp_23920 = tmp_struct_442.field3;
            GibCursor pvrtmp_23921 = tmp_struct_442.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_23917,
                                                                        pvrtmp_23918,
                                                                        pvrtmp_23919,
                                                                        pvrtmp_23920,
                                                                        pvrtmp_23921};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_23835");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_KdTree(GibCursor end_r_15770,
                                                                            GibCursor end_r_15771,
                                                                            GibCursor loc_15769,
                                                                            GibCursor arg_7193_10279_13621)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_23929 = *(GibPackedTag *) arg_7193_10279_13621;
    GibCursor tmpcur_23930 = arg_7193_10279_13621 + 1;


  switch_24022:
    ;
    switch (tmpval_23929) {

      case 0:
        {
            GibFloat tmpval_23931 = *(GibFloat *) tmpcur_23930;
            GibCursor tmpcur_23932 = tmpcur_23930 + sizeof(GibFloat);
            GibFloat tmpval_23933 = *(GibFloat *) tmpcur_23932;
            GibCursor tmpcur_23934 = tmpcur_23932 + sizeof(GibFloat);
            GibFloat tmpval_23935 = *(GibFloat *) tmpcur_23934;
            GibCursor tmpcur_23936 = tmpcur_23934 + sizeof(GibFloat);
            GibCursor jump_17724 = tmpcur_23934 + 4;

            *(GibPackedTag *) loc_15769 = 0;

            GibCursor writetag_19966 = loc_15769 + 1;
            GibCursor after_tag_19967 = loc_15769 + 1;

            *(GibFloat *) after_tag_19967 = tmpval_23931;

            GibCursor writecur_19971 = after_tag_19967 + sizeof(GibFloat);

            *(GibFloat *) writecur_19971 = tmpval_23933;

            GibCursor writecur_19972 = writecur_19971 + sizeof(GibFloat);

            *(GibFloat *) writecur_19972 = tmpval_23935;

            GibCursor writecur_19973 = writecur_19972 + sizeof(GibFloat);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15770,
                                                                        end_r_15771,
                                                                        jump_17724,
                                                                        loc_15769,
                                                                        writecur_19973};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_449 = *(uintptr_t *) tmpcur_23930;
            GibCursor tmpcur_23941 = GIB_UNTAG(tagged_tmpcur_449);
            GibCursor tmpaftercur_23942 = tmpcur_23930 + 8;
            uint16_t tmptag_23943 = GIB_GET_TAG(tagged_tmpcur_449);
            GibCursor end_from_tagged_absran_15596 = tmpcur_23941 +
                      tmptag_23943;
            GibFloat tmpval_23944 = *(GibFloat *) tmpaftercur_23942;
            GibCursor tmpcur_23945 = tmpaftercur_23942 + sizeof(GibFloat);
            GibFloat tmpval_23946 = *(GibFloat *) tmpcur_23945;
            GibCursor tmpcur_23947 = tmpcur_23945 + sizeof(GibFloat);
            GibFloat tmpval_23948 = *(GibFloat *) tmpcur_23947;
            GibCursor tmpcur_23949 = tmpcur_23947 + sizeof(GibFloat);
            GibInt tmpval_23950 = *(GibInt *) tmpcur_23949;
            GibCursor tmpcur_23951 = tmpcur_23949 + sizeof(GibInt);
            GibInt tmpval_23952 = *(GibInt *) tmpcur_23951;
            GibCursor tmpcur_23953 = tmpcur_23951 + sizeof(GibInt);
            GibFloat tmpval_23954 = *(GibFloat *) tmpcur_23953;
            GibCursor tmpcur_23955 = tmpcur_23953 + sizeof(GibFloat);
            GibFloat tmpval_23956 = *(GibFloat *) tmpcur_23955;
            GibCursor tmpcur_23957 = tmpcur_23955 + sizeof(GibFloat);
            GibFloat tmpval_23958 = *(GibFloat *) tmpcur_23957;
            GibCursor tmpcur_23959 = tmpcur_23957 + sizeof(GibFloat);
            GibFloat tmpval_23960 = *(GibFloat *) tmpcur_23959;
            GibCursor tmpcur_23961 = tmpcur_23959 + sizeof(GibFloat);
            GibFloat tmpval_23962 = *(GibFloat *) tmpcur_23961;
            GibCursor tmpcur_23963 = tmpcur_23961 + sizeof(GibFloat);
            GibFloat tmpval_23964 = *(GibFloat *) tmpcur_23963;
            GibCursor tmpcur_23965 = tmpcur_23963 + sizeof(GibFloat);
            GibFloat tmpval_23966 = *(GibFloat *) tmpcur_23965;
            GibCursor tmpcur_23967 = tmpcur_23965 + sizeof(GibFloat);
            GibCursor loc_16729 = loc_15769 + 57;

            *(GibPackedTag *) loc_15769 = 1;

            GibCursor writetag_19996 = loc_15769 + 1;
            GibCursor after_tag_19997 = loc_15769 + 1;

            *(GibFloat *) after_tag_19997 = tmpval_23944;

            GibCursor writecur_20001 = after_tag_19997 + sizeof(GibFloat);

            *(GibFloat *) writecur_20001 = tmpval_23946;

            GibCursor writecur_20002 = writecur_20001 + sizeof(GibFloat);

            *(GibFloat *) writecur_20002 = tmpval_23948;

            GibCursor writecur_20003 = writecur_20002 + sizeof(GibFloat);

            *(GibInt *) writecur_20003 = tmpval_23950;

            GibCursor writecur_20004 = writecur_20003 + sizeof(GibInt);

            *(GibInt *) writecur_20004 = tmpval_23952;

            GibCursor writecur_20005 = writecur_20004 + sizeof(GibInt);

            *(GibFloat *) writecur_20005 = tmpval_23954;

            GibCursor writecur_20006 = writecur_20005 + sizeof(GibFloat);

            *(GibFloat *) writecur_20006 = tmpval_23956;

            GibCursor writecur_20007 = writecur_20006 + sizeof(GibFloat);

            *(GibFloat *) writecur_20007 = tmpval_23958;

            GibCursor writecur_20008 = writecur_20007 + sizeof(GibFloat);

            *(GibFloat *) writecur_20008 = tmpval_23960;

            GibCursor writecur_20009 = writecur_20008 + sizeof(GibFloat);

            *(GibFloat *) writecur_20009 = tmpval_23962;

            GibCursor writecur_20010 = writecur_20009 + sizeof(GibFloat);

            *(GibFloat *) writecur_20010 = tmpval_23964;

            GibCursor writecur_20011 = writecur_20010 + sizeof(GibFloat);

            *(GibFloat *) writecur_20011 = tmpval_23966;

            GibCursor writecur_20012 = writecur_20011 + sizeof(GibFloat);

            gib_shadowstack_push(rstack, loc_15769, end_r_15771, Stk, KdTree_T);
            gib_shadowstack_push(rstack, tmpcur_23941, end_r_15770, Stk,
                                 KdTree_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_447 =
                                                               _copy_without_ptrs_KdTree(end_r_15770, end_r_15771, loc_16729, tmpcur_23967);
            GibCursor pvrtmp_23968 = tmp_struct_447.field0;
            GibCursor pvrtmp_23969 = tmp_struct_447.field1;
            GibCursor pvrtmp_23970 = tmp_struct_447.field2;
            GibCursor pvrtmp_23971 = tmp_struct_447.field3;
            GibCursor pvrtmp_23972 = tmp_struct_447.field4;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_23941 = frame->ptr;
            end_r_15770 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_15769 = frame->ptr;
            end_r_15771 = frame->endptr;
            gib_shadowstack_push(rstack, loc_15769, pvrtmp_23969, Stk,
                                 KdTree_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_448 =
                                                               _copy_without_ptrs_KdTree(end_from_tagged_absran_15596, pvrtmp_23969, pvrtmp_23972, tmpcur_23941);
            GibCursor pvrtmp_23977 = tmp_struct_448.field0;
            GibCursor pvrtmp_23978 = tmp_struct_448.field1;
            GibCursor pvrtmp_23979 = tmp_struct_448.field2;
            GibCursor pvrtmp_23980 = tmp_struct_448.field3;
            GibCursor pvrtmp_23981 = tmp_struct_448.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_15769 = frame->ptr;
            pvrtmp_23969 = frame->endptr;
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_23977,
                                                                        pvrtmp_23978,
                                                                        pvrtmp_23979,
                                                                        loc_15769,
                                                                        pvrtmp_23981};
            break;
        }

      case 2:
        {
            GibCursor jump_17742 = arg_7193_10279_13621 + 1;

            *(GibPackedTag *) loc_15769 = 2;

            GibCursor writetag_20019 = loc_15769 + 1;
            GibCursor after_tag_20020 = loc_15769 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15770,
                                                                        end_r_15771,
                                                                        jump_17742,
                                                                        loc_15769,
                                                                        after_tag_20020};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_451 = *(uintptr_t *) tmpcur_23930;
            GibCursor tmpcur_23994 = GIB_UNTAG(tagged_tmpcur_451);
            GibCursor tmpaftercur_23995 = tmpcur_23930 + 8;
            uint16_t tmptag_23996 = GIB_GET_TAG(tagged_tmpcur_451);
            GibCursor end_from_tagged_indr_18114 = tmpcur_23994 + tmptag_23996;
            GibCursor jump_18116 = tmpcur_23930 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_450 =
                                                               _copy_without_ptrs_KdTree(end_from_tagged_indr_18114, end_r_15771, loc_15769, tmpcur_23994);
            GibCursor pvrtmp_23997 = tmp_struct_450.field0;
            GibCursor pvrtmp_23998 = tmp_struct_450.field1;
            GibCursor pvrtmp_23999 = tmp_struct_450.field2;
            GibCursor pvrtmp_24000 = tmp_struct_450.field3;
            GibCursor pvrtmp_24001 = tmp_struct_450.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15770,
                                                                        pvrtmp_23998,
                                                                        jump_18116,
                                                                        pvrtmp_24000,
                                                                        pvrtmp_24001};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_453 = *(uintptr_t *) tmpcur_23930;
            GibCursor tmpcur_24008 = GIB_UNTAG(tagged_tmpcur_453);
            GibCursor tmpaftercur_24009 = tmpcur_23930 + 8;
            uint16_t tmptag_24010 = GIB_GET_TAG(tagged_tmpcur_453);
            GibCursor end_from_tagged_indr_18114 = tmpcur_24008 + tmptag_24010;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_452 =
                                                               _copy_without_ptrs_KdTree(end_from_tagged_indr_18114, end_r_15771, loc_15769, tmpcur_24008);
            GibCursor pvrtmp_24011 = tmp_struct_452.field0;
            GibCursor pvrtmp_24012 = tmp_struct_452.field1;
            GibCursor pvrtmp_24013 = tmp_struct_452.field2;
            GibCursor pvrtmp_24014 = tmp_struct_452.field3;
            GibCursor pvrtmp_24015 = tmp_struct_452.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_24011,
                                                                        pvrtmp_24012,
                                                                        pvrtmp_24013,
                                                                        pvrtmp_24014,
                                                                        pvrtmp_24015};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_23929");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_KdTree(GibCursor end_r_15773,
                                        GibCursor arg_7228_10314_13656)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_24023 = *(GibPackedTag *) arg_7228_10314_13656;
    GibCursor tmpcur_24024 = arg_7228_10314_13656 + 1;


  switch_24072:
    ;
    switch (tmpval_24023) {

      case 0:
        {
            GibFloat tmpval_24025 = *(GibFloat *) tmpcur_24024;
            GibCursor tmpcur_24026 = tmpcur_24024 + sizeof(GibFloat);
            GibFloat tmpval_24027 = *(GibFloat *) tmpcur_24026;
            GibCursor tmpcur_24028 = tmpcur_24026 + sizeof(GibFloat);
            GibFloat tmpval_24029 = *(GibFloat *) tmpcur_24028;
            GibCursor tmpcur_24030 = tmpcur_24028 + sizeof(GibFloat);
            GibCursor jump_17746 = tmpcur_24028 + 4;

            return (GibCursorGibCursorProd) {end_r_15773, jump_17746};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_456 = *(uintptr_t *) tmpcur_24024;
            GibCursor tmpcur_24031 = GIB_UNTAG(tagged_tmpcur_456);
            GibCursor tmpaftercur_24032 = tmpcur_24024 + 8;
            uint16_t tmptag_24033 = GIB_GET_TAG(tagged_tmpcur_456);
            GibCursor end_from_tagged_absran_15599 = tmpcur_24031 +
                      tmptag_24033;
            GibFloat tmpval_24034 = *(GibFloat *) tmpaftercur_24032;
            GibCursor tmpcur_24035 = tmpaftercur_24032 + sizeof(GibFloat);
            GibFloat tmpval_24036 = *(GibFloat *) tmpcur_24035;
            GibCursor tmpcur_24037 = tmpcur_24035 + sizeof(GibFloat);
            GibFloat tmpval_24038 = *(GibFloat *) tmpcur_24037;
            GibCursor tmpcur_24039 = tmpcur_24037 + sizeof(GibFloat);
            GibInt tmpval_24040 = *(GibInt *) tmpcur_24039;
            GibCursor tmpcur_24041 = tmpcur_24039 + sizeof(GibInt);
            GibInt tmpval_24042 = *(GibInt *) tmpcur_24041;
            GibCursor tmpcur_24043 = tmpcur_24041 + sizeof(GibInt);
            GibFloat tmpval_24044 = *(GibFloat *) tmpcur_24043;
            GibCursor tmpcur_24045 = tmpcur_24043 + sizeof(GibFloat);
            GibFloat tmpval_24046 = *(GibFloat *) tmpcur_24045;
            GibCursor tmpcur_24047 = tmpcur_24045 + sizeof(GibFloat);
            GibFloat tmpval_24048 = *(GibFloat *) tmpcur_24047;
            GibCursor tmpcur_24049 = tmpcur_24047 + sizeof(GibFloat);
            GibFloat tmpval_24050 = *(GibFloat *) tmpcur_24049;
            GibCursor tmpcur_24051 = tmpcur_24049 + sizeof(GibFloat);
            GibFloat tmpval_24052 = *(GibFloat *) tmpcur_24051;
            GibCursor tmpcur_24053 = tmpcur_24051 + sizeof(GibFloat);
            GibFloat tmpval_24054 = *(GibFloat *) tmpcur_24053;
            GibCursor tmpcur_24055 = tmpcur_24053 + sizeof(GibFloat);
            GibFloat tmpval_24056 = *(GibFloat *) tmpcur_24055;
            GibCursor tmpcur_24057 = tmpcur_24055 + sizeof(GibFloat);

            gib_shadowstack_push(rstack, tmpcur_24031, end_r_15773, Stk,
                                 KdTree_T);

            GibCursorGibCursorProd tmp_struct_454 =
                                    _traverse_KdTree(end_r_15773, tmpcur_24057);
            GibCursor pvrtmp_24058 = tmp_struct_454.field0;
            GibCursor pvrtmp_24059 = tmp_struct_454.field1;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_24031 = frame->ptr;
            end_r_15773 = frame->endptr;

            GibCursorGibCursorProd tmp_struct_455 =
                                    _traverse_KdTree(end_from_tagged_absran_15599, tmpcur_24031);
            GibCursor pvrtmp_24060 = tmp_struct_455.field0;
            GibCursor pvrtmp_24061 = tmp_struct_455.field1;

            return (GibCursorGibCursorProd) {pvrtmp_24060, pvrtmp_24061};
            break;
        }

      case 2:
        {
            GibCursor jump_17764 = arg_7228_10314_13656 + 1;

            return (GibCursorGibCursorProd) {end_r_15773, jump_17764};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_458 = *(uintptr_t *) tmpcur_24024;
            GibCursor tmpcur_24062 = GIB_UNTAG(tagged_tmpcur_458);
            GibCursor tmpaftercur_24063 = tmpcur_24024 + 8;
            uint16_t tmptag_24064 = GIB_GET_TAG(tagged_tmpcur_458);
            GibCursor end_from_tagged_indr_18120 = tmpcur_24062 + tmptag_24064;
            GibCursor jump_18122 = tmpcur_24024 + 8;
            GibCursorGibCursorProd tmp_struct_457 =
                                    _traverse_KdTree(end_from_tagged_indr_18120, tmpcur_24062);
            GibCursor pvrtmp_24065 = tmp_struct_457.field0;
            GibCursor pvrtmp_24066 = tmp_struct_457.field1;

            return (GibCursorGibCursorProd) {end_r_15773, jump_18122};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_460 = *(uintptr_t *) tmpcur_24024;
            GibCursor tmpcur_24067 = GIB_UNTAG(tagged_tmpcur_460);
            GibCursor tmpaftercur_24068 = tmpcur_24024 + 8;
            uint16_t tmptag_24069 = GIB_GET_TAG(tagged_tmpcur_460);
            GibCursor end_from_tagged_indr_18120 = tmpcur_24067 + tmptag_24069;
            GibCursorGibCursorProd tmp_struct_459 =
                                    _traverse_KdTree(end_from_tagged_indr_18120, tmpcur_24067);
            GibCursor pvrtmp_24070 = tmp_struct_459.field0;
            GibCursor pvrtmp_24071 = tmp_struct_459.field1;

            return (GibCursorGibCursorProd) {pvrtmp_24070, pvrtmp_24071};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_24023");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_KdTree(GibCursor end_r_15775,
                                     GibCursor arg_7263_10334_13676)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_24073 = *(GibPackedTag *) arg_7263_10334_13676;
    GibCursor tmpcur_24074 = arg_7263_10334_13676 + 1;


  switch_24122:
    ;
    switch (tmpval_24073) {

      case 0:
        {
            GibFloat tmpval_24075 = *(GibFloat *) tmpcur_24074;
            GibCursor tmpcur_24076 = tmpcur_24074 + sizeof(GibFloat);
            GibFloat tmpval_24077 = *(GibFloat *) tmpcur_24076;
            GibCursor tmpcur_24078 = tmpcur_24076 + sizeof(GibFloat);
            GibFloat tmpval_24079 = *(GibFloat *) tmpcur_24078;
            GibCursor tmpcur_24080 = tmpcur_24078 + sizeof(GibFloat);
            GibCursor jump_17768 = tmpcur_24078 + 4;
            unsigned char wildcard_7270_10338_13680 = gib_print_symbol(21866);
            unsigned char y_7267_10339_13681 = printf("%.2f", tmpval_24075);
            unsigned char y_7268_10340_13682 = printf("%.2f", tmpval_24077);
            unsigned char y_7269_10341_13683 = printf("%.2f", tmpval_24079);
            unsigned char wildcard_7271_10342_13684 = gib_print_symbol(21857);

            return (GibCursorGibCursorProd) {end_r_15775, jump_17768};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_463 = *(uintptr_t *) tmpcur_24074;
            GibCursor tmpcur_24081 = GIB_UNTAG(tagged_tmpcur_463);
            GibCursor tmpaftercur_24082 = tmpcur_24074 + 8;
            uint16_t tmptag_24083 = GIB_GET_TAG(tagged_tmpcur_463);
            GibCursor end_from_tagged_absran_15602 = tmpcur_24081 +
                      tmptag_24083;
            GibFloat tmpval_24084 = *(GibFloat *) tmpaftercur_24082;
            GibCursor tmpcur_24085 = tmpaftercur_24082 + sizeof(GibFloat);
            GibFloat tmpval_24086 = *(GibFloat *) tmpcur_24085;
            GibCursor tmpcur_24087 = tmpcur_24085 + sizeof(GibFloat);
            GibFloat tmpval_24088 = *(GibFloat *) tmpcur_24087;
            GibCursor tmpcur_24089 = tmpcur_24087 + sizeof(GibFloat);
            GibInt tmpval_24090 = *(GibInt *) tmpcur_24089;
            GibCursor tmpcur_24091 = tmpcur_24089 + sizeof(GibInt);
            GibInt tmpval_24092 = *(GibInt *) tmpcur_24091;
            GibCursor tmpcur_24093 = tmpcur_24091 + sizeof(GibInt);
            GibFloat tmpval_24094 = *(GibFloat *) tmpcur_24093;
            GibCursor tmpcur_24095 = tmpcur_24093 + sizeof(GibFloat);
            GibFloat tmpval_24096 = *(GibFloat *) tmpcur_24095;
            GibCursor tmpcur_24097 = tmpcur_24095 + sizeof(GibFloat);
            GibFloat tmpval_24098 = *(GibFloat *) tmpcur_24097;
            GibCursor tmpcur_24099 = tmpcur_24097 + sizeof(GibFloat);
            GibFloat tmpval_24100 = *(GibFloat *) tmpcur_24099;
            GibCursor tmpcur_24101 = tmpcur_24099 + sizeof(GibFloat);
            GibFloat tmpval_24102 = *(GibFloat *) tmpcur_24101;
            GibCursor tmpcur_24103 = tmpcur_24101 + sizeof(GibFloat);
            GibFloat tmpval_24104 = *(GibFloat *) tmpcur_24103;
            GibCursor tmpcur_24105 = tmpcur_24103 + sizeof(GibFloat);
            GibFloat tmpval_24106 = *(GibFloat *) tmpcur_24105;
            GibCursor tmpcur_24107 = tmpcur_24105 + sizeof(GibFloat);
            unsigned char wildcard_7300_10357_13699 = gib_print_symbol(21865);
            unsigned char y_7286_10358_13700 = printf("%.2f", tmpval_24084);
            unsigned char y_7287_10359_13701 = printf("%.2f", tmpval_24086);
            unsigned char y_7288_10360_13702 = printf("%.2f", tmpval_24088);
            unsigned char y_7289_10361_13703 = printf("%ld", tmpval_24090);
            unsigned char y_7290_10362_13704 = printf("%ld", tmpval_24092);
            unsigned char y_7291_10363_13705 = printf("%.2f", tmpval_24094);
            unsigned char y_7292_10364_13706 = printf("%.2f", tmpval_24096);
            unsigned char y_7293_10365_13707 = printf("%.2f", tmpval_24098);
            unsigned char y_7294_10366_13708 = printf("%.2f", tmpval_24100);
            unsigned char y_7295_10367_13709 = printf("%.2f", tmpval_24102);
            unsigned char y_7296_10368_13710 = printf("%.2f", tmpval_24104);
            unsigned char y_7297_10369_13711 = printf("%.2f", tmpval_24106);

            gib_shadowstack_push(rstack, tmpcur_24081, end_r_15775, Stk,
                                 KdTree_T);

            GibCursorGibCursorProd tmp_struct_461 =
                                    _print_KdTree(end_r_15775, tmpcur_24107);
            GibCursor pvrtmp_24108 = tmp_struct_461.field0;
            GibCursor pvrtmp_24109 = tmp_struct_461.field1;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_24081 = frame->ptr;
            end_r_15775 = frame->endptr;

            GibCursorGibCursorProd tmp_struct_462 =
                                    _print_KdTree(end_from_tagged_absran_15602, tmpcur_24081);
            GibCursor pvrtmp_24110 = tmp_struct_462.field0;
            GibCursor pvrtmp_24111 = tmp_struct_462.field1;
            unsigned char wildcard_7301_10372_13714 = gib_print_symbol(21857);

            return (GibCursorGibCursorProd) {pvrtmp_24110, pvrtmp_24111};
            break;
        }

      case 2:
        {
            GibCursor jump_17786 = arg_7263_10334_13676 + 1;
            unsigned char wildcard_7302_10373_13715 = gib_print_symbol(21867);
            unsigned char wildcard_7303_10374_13716 = gib_print_symbol(21857);

            return (GibCursorGibCursorProd) {end_r_15775, jump_17786};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_465 = *(uintptr_t *) tmpcur_24074;
            GibCursor tmpcur_24112 = GIB_UNTAG(tagged_tmpcur_465);
            GibCursor tmpaftercur_24113 = tmpcur_24074 + 8;
            uint16_t tmptag_24114 = GIB_GET_TAG(tagged_tmpcur_465);
            GibCursor end_from_tagged_indr_18126 = tmpcur_24112 + tmptag_24114;
            GibCursor jump_18128 = tmpcur_24074 + 8;
            unsigned char wildcard_18131 = gib_print_symbol(21876);
            GibCursorGibCursorProd tmp_struct_464 =
                                    _print_KdTree(end_from_tagged_indr_18126, tmpcur_24112);
            GibCursor pvrtmp_24115 = tmp_struct_464.field0;
            GibCursor pvrtmp_24116 = tmp_struct_464.field1;

            return (GibCursorGibCursorProd) {end_r_15775, jump_18128};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_467 = *(uintptr_t *) tmpcur_24074;
            GibCursor tmpcur_24117 = GIB_UNTAG(tagged_tmpcur_467);
            GibCursor tmpaftercur_24118 = tmpcur_24074 + 8;
            uint16_t tmptag_24119 = GIB_GET_TAG(tagged_tmpcur_467);
            GibCursor end_from_tagged_indr_18126 = tmpcur_24117 + tmptag_24119;
            unsigned char wildcard_18131 = gib_print_symbol(21875);
            GibCursorGibCursorProd tmp_struct_466 =
                                    _print_KdTree(end_from_tagged_indr_18126, tmpcur_24117);
            GibCursor pvrtmp_24120 = tmp_struct_466.field0;
            GibCursor pvrtmp_24121 = tmp_struct_466.field1;

            return (GibCursorGibCursorProd) {pvrtmp_24120, pvrtmp_24121};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_24073");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_BH_Tree(GibCursor end_r_15778,
                                                                GibCursor end_r_15779,
                                                                GibCursor loc_15777,
                                                                GibCursor arg_7304_10375_13717)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_15777 + 58 > end_r_15779) {
        gib_grow_region(&loc_15777, &end_r_15779);
    }

    GibPackedTag tmpval_24123 = *(GibPackedTag *) arg_7304_10375_13717;
    GibCursor tmpcur_24124 = arg_7304_10375_13717 + 1;


  switch_24226:
    ;
    switch (tmpval_24123) {

      case 0:
        {
            GibCursor jump_17788 = arg_7304_10375_13717 + 1;

            *(GibPackedTag *) loc_15777 = 0;

            GibCursor writetag_20099 = loc_15777 + 1;
            GibCursor after_tag_20100 = loc_15777 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15778,
                                                                        end_r_15779,
                                                                        jump_17788,
                                                                        loc_15777,
                                                                        after_tag_20100};
            break;
        }

      case 1:
        {
            GibFloat tmpval_24129 = *(GibFloat *) tmpcur_24124;
            GibCursor tmpcur_24130 = tmpcur_24124 + sizeof(GibFloat);
            GibFloat tmpval_24131 = *(GibFloat *) tmpcur_24130;
            GibCursor tmpcur_24132 = tmpcur_24130 + sizeof(GibFloat);
            GibFloat tmpval_24133 = *(GibFloat *) tmpcur_24132;
            GibCursor tmpcur_24134 = tmpcur_24132 + sizeof(GibFloat);
            GibCursor jump_17792 = tmpcur_24132 + 4;

            *(GibPackedTag *) loc_15777 = 1;

            GibCursor writetag_20110 = loc_15777 + 1;
            GibCursor after_tag_20111 = loc_15777 + 1;

            *(GibFloat *) after_tag_20111 = tmpval_24129;

            GibCursor writecur_20115 = after_tag_20111 + sizeof(GibFloat);

            *(GibFloat *) writecur_20115 = tmpval_24131;

            GibCursor writecur_20116 = writecur_20115 + sizeof(GibFloat);

            *(GibFloat *) writecur_20116 = tmpval_24133;

            GibCursor writecur_20117 = writecur_20116 + sizeof(GibFloat);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15778,
                                                                        end_r_15779,
                                                                        jump_17792,
                                                                        loc_15777,
                                                                        writecur_20117};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_477 = *(uintptr_t *) tmpcur_24124;
            GibCursor tmpcur_24139 = GIB_UNTAG(tagged_tmpcur_477);
            GibCursor tmpaftercur_24140 = tmpcur_24124 + 8;
            uint16_t tmptag_24141 = GIB_GET_TAG(tagged_tmpcur_477);
            GibCursor end_from_tagged_absran_15608 = tmpcur_24139 +
                      tmptag_24141;
            uintptr_t tagged_tmpcur_476 = *(uintptr_t *) tmpaftercur_24140;
            GibCursor tmpcur_24142 = GIB_UNTAG(tagged_tmpcur_476);
            GibCursor tmpaftercur_24143 = tmpaftercur_24140 + 8;
            uint16_t tmptag_24144 = GIB_GET_TAG(tagged_tmpcur_476);
            GibCursor end_from_tagged_absran_15609 = tmpcur_24142 +
                      tmptag_24144;
            uintptr_t tagged_tmpcur_475 = *(uintptr_t *) tmpaftercur_24143;
            GibCursor tmpcur_24145 = GIB_UNTAG(tagged_tmpcur_475);
            GibCursor tmpaftercur_24146 = tmpaftercur_24143 + 8;
            uint16_t tmptag_24147 = GIB_GET_TAG(tagged_tmpcur_475);
            GibCursor end_from_tagged_absran_15610 = tmpcur_24145 +
                      tmptag_24147;
            GibFloat tmpval_24148 = *(GibFloat *) tmpaftercur_24146;
            GibCursor tmpcur_24149 = tmpaftercur_24146 + sizeof(GibFloat);
            GibFloat tmpval_24150 = *(GibFloat *) tmpcur_24149;
            GibCursor tmpcur_24151 = tmpcur_24149 + sizeof(GibFloat);
            GibFloat tmpval_24152 = *(GibFloat *) tmpcur_24151;
            GibCursor tmpcur_24153 = tmpcur_24151 + sizeof(GibFloat);
            GibInt tmpval_24154 = *(GibInt *) tmpcur_24153;
            GibCursor tmpcur_24155 = tmpcur_24153 + sizeof(GibInt);
            GibFloat tmpval_24156 = *(GibFloat *) tmpcur_24155;
            GibCursor tmpcur_24157 = tmpcur_24155 + sizeof(GibFloat);
            GibCursor loc_16853 = loc_15777 + 49;

            *(GibPackedTag *) loc_15777 = 3;

            GibCursor writetag_20141 = loc_15777 + 1;

            gib_shadowstack_push(rstack, loc_15777, end_r_15779, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, tmpcur_24145, end_r_15778, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, tmpcur_24142, end_r_15778, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, tmpcur_24139, end_r_15778, Stk,
                                 BH_Tree_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_468 =
                                                               _copy_BH_Tree(end_r_15778, end_r_15779, loc_16853, tmpcur_24157);
            GibCursor pvrtmp_24158 = tmp_struct_468.field0;
            GibCursor pvrtmp_24159 = tmp_struct_468.field1;
            GibCursor pvrtmp_24160 = tmp_struct_468.field2;
            GibCursor pvrtmp_24161 = tmp_struct_468.field3;
            GibCursor pvrtmp_24162 = tmp_struct_468.field4;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_24139 = frame->ptr;
            end_r_15778 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tmpcur_24142 = frame->ptr;
            end_r_15778 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tmpcur_24145 = frame->ptr;
            end_r_15778 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_15777 = frame->ptr;
            end_r_15779 = frame->endptr;
            gib_shadowstack_push(rstack, loc_15777, pvrtmp_24159, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, tmpcur_24145, pvrtmp_24158, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, tmpcur_24142, pvrtmp_24158, Stk,
                                 BH_Tree_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_469 =
                                                               _copy_BH_Tree(end_from_tagged_absran_15608, pvrtmp_24159, pvrtmp_24162, tmpcur_24139);
            GibCursor pvrtmp_24167 = tmp_struct_469.field0;
            GibCursor pvrtmp_24168 = tmp_struct_469.field1;
            GibCursor pvrtmp_24169 = tmp_struct_469.field2;
            GibCursor pvrtmp_24170 = tmp_struct_469.field3;
            GibCursor pvrtmp_24171 = tmp_struct_469.field4;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_24142 = frame->ptr;
            pvrtmp_24158 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tmpcur_24145 = frame->ptr;
            pvrtmp_24158 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_15777 = frame->ptr;
            pvrtmp_24159 = frame->endptr;
            gib_shadowstack_push(rstack, loc_15777, pvrtmp_24168, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, tmpcur_24145, pvrtmp_24167, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, pvrtmp_24162, pvrtmp_24168, Stk,
                                 BH_Tree_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_470 =
                                                               _copy_BH_Tree(end_from_tagged_absran_15609, pvrtmp_24168, pvrtmp_24171, tmpcur_24142);
            GibCursor pvrtmp_24176 = tmp_struct_470.field0;
            GibCursor pvrtmp_24177 = tmp_struct_470.field1;
            GibCursor pvrtmp_24178 = tmp_struct_470.field2;
            GibCursor pvrtmp_24179 = tmp_struct_470.field3;
            GibCursor pvrtmp_24180 = tmp_struct_470.field4;

            frame = gib_shadowstack_pop(rstack);
            pvrtmp_24162 = frame->ptr;
            pvrtmp_24168 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tmpcur_24145 = frame->ptr;
            pvrtmp_24167 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_15777 = frame->ptr;
            pvrtmp_24168 = frame->endptr;
            gib_shadowstack_push(rstack, loc_15777, pvrtmp_24177, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, pvrtmp_24171, pvrtmp_24177, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, pvrtmp_24162, pvrtmp_24177, Stk,
                                 BH_Tree_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_471 =
                                                               _copy_BH_Tree(end_from_tagged_absran_15610, pvrtmp_24177, pvrtmp_24180, tmpcur_24145);
            GibCursor pvrtmp_24185 = tmp_struct_471.field0;
            GibCursor pvrtmp_24186 = tmp_struct_471.field1;
            GibCursor pvrtmp_24187 = tmp_struct_471.field2;
            GibCursor pvrtmp_24188 = tmp_struct_471.field3;
            GibCursor pvrtmp_24189 = tmp_struct_471.field4;

            frame = gib_shadowstack_pop(rstack);
            pvrtmp_24162 = frame->ptr;
            pvrtmp_24177 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_24171 = frame->ptr;
            pvrtmp_24177 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_15777 = frame->ptr;
            pvrtmp_24177 = frame->endptr;

            uint16_t offset_474 = pvrtmp_24159 - pvrtmp_24162;
            uintptr_t ran_15615 = GIB_STORE_TAG(pvrtmp_24162, offset_474);
            uint16_t offset_473 = pvrtmp_24168 - pvrtmp_24171;
            uintptr_t ran_15616 = GIB_STORE_TAG(pvrtmp_24171, offset_473);
            uint16_t offset_472 = pvrtmp_24177 - pvrtmp_24180;
            uintptr_t ran_15617 = GIB_STORE_TAG(pvrtmp_24180, offset_472);
            GibCursor after_tag_20142 = loc_15777 + 1;

            *(uintptr_t *) after_tag_20142 = ran_15615;

            GibCursor writecur_20146 = after_tag_20142 + 8;

            *(uintptr_t *) writecur_20146 = ran_15616;

            GibCursor writecur_20147 = writecur_20146 + 8;

            *(uintptr_t *) writecur_20147 = ran_15617;

            GibCursor writecur_20148 = writecur_20147 + 8;

            *(GibFloat *) writecur_20148 = tmpval_24148;

            GibCursor writecur_20149 = writecur_20148 + sizeof(GibFloat);

            *(GibFloat *) writecur_20149 = tmpval_24150;

            GibCursor writecur_20150 = writecur_20149 + sizeof(GibFloat);

            *(GibFloat *) writecur_20150 = tmpval_24152;

            GibCursor writecur_20151 = writecur_20150 + sizeof(GibFloat);

            *(GibInt *) writecur_20151 = tmpval_24154;

            GibCursor writecur_20152 = writecur_20151 + sizeof(GibInt);

            *(GibFloat *) writecur_20152 = tmpval_24156;

            GibCursor writecur_20153 = writecur_20152 + sizeof(GibFloat);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_24185,
                                                                        pvrtmp_24186,
                                                                        pvrtmp_24187,
                                                                        loc_15777,
                                                                        pvrtmp_24189};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_479 = *(uintptr_t *) tmpcur_24124;
            GibCursor tmpcur_24198 = GIB_UNTAG(tagged_tmpcur_479);
            GibCursor tmpaftercur_24199 = tmpcur_24124 + 8;
            uint16_t tmptag_24200 = GIB_GET_TAG(tagged_tmpcur_479);
            GibCursor end_from_tagged_indr_18132 = tmpcur_24198 + tmptag_24200;
            GibCursor jump_18134 = tmpcur_24124 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_478 =
                                                               _copy_BH_Tree(end_from_tagged_indr_18132, end_r_15779, loc_15777, tmpcur_24198);
            GibCursor pvrtmp_24201 = tmp_struct_478.field0;
            GibCursor pvrtmp_24202 = tmp_struct_478.field1;
            GibCursor pvrtmp_24203 = tmp_struct_478.field2;
            GibCursor pvrtmp_24204 = tmp_struct_478.field3;
            GibCursor pvrtmp_24205 = tmp_struct_478.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15778,
                                                                        pvrtmp_24202,
                                                                        jump_18134,
                                                                        pvrtmp_24204,
                                                                        pvrtmp_24205};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_481 = *(uintptr_t *) tmpcur_24124;
            GibCursor tmpcur_24212 = GIB_UNTAG(tagged_tmpcur_481);
            GibCursor tmpaftercur_24213 = tmpcur_24124 + 8;
            uint16_t tmptag_24214 = GIB_GET_TAG(tagged_tmpcur_481);
            GibCursor end_from_tagged_indr_18132 = tmpcur_24212 + tmptag_24214;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_480 =
                                                               _copy_BH_Tree(end_from_tagged_indr_18132, end_r_15779, loc_15777, tmpcur_24212);
            GibCursor pvrtmp_24215 = tmp_struct_480.field0;
            GibCursor pvrtmp_24216 = tmp_struct_480.field1;
            GibCursor pvrtmp_24217 = tmp_struct_480.field2;
            GibCursor pvrtmp_24218 = tmp_struct_480.field3;
            GibCursor pvrtmp_24219 = tmp_struct_480.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_24215,
                                                                        pvrtmp_24216,
                                                                        pvrtmp_24217,
                                                                        pvrtmp_24218,
                                                                        pvrtmp_24219};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_24123");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_BH_Tree(GibCursor end_r_15782,
                                                                             GibCursor end_r_15783,
                                                                             GibCursor loc_15781,
                                                                             GibCursor arg_7329_10400_13742)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_24227 = *(GibPackedTag *) arg_7329_10400_13742;
    GibCursor tmpcur_24228 = arg_7329_10400_13742 + 1;


  switch_24330:
    ;
    switch (tmpval_24227) {

      case 0:
        {
            GibCursor jump_17807 = arg_7329_10400_13742 + 1;

            *(GibPackedTag *) loc_15781 = 0;

            GibCursor writetag_20174 = loc_15781 + 1;
            GibCursor after_tag_20175 = loc_15781 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15782,
                                                                        end_r_15783,
                                                                        jump_17807,
                                                                        loc_15781,
                                                                        after_tag_20175};
            break;
        }

      case 1:
        {
            GibFloat tmpval_24233 = *(GibFloat *) tmpcur_24228;
            GibCursor tmpcur_24234 = tmpcur_24228 + sizeof(GibFloat);
            GibFloat tmpval_24235 = *(GibFloat *) tmpcur_24234;
            GibCursor tmpcur_24236 = tmpcur_24234 + sizeof(GibFloat);
            GibFloat tmpval_24237 = *(GibFloat *) tmpcur_24236;
            GibCursor tmpcur_24238 = tmpcur_24236 + sizeof(GibFloat);
            GibCursor jump_17811 = tmpcur_24236 + 4;

            *(GibPackedTag *) loc_15781 = 1;

            GibCursor writetag_20185 = loc_15781 + 1;
            GibCursor after_tag_20186 = loc_15781 + 1;

            *(GibFloat *) after_tag_20186 = tmpval_24233;

            GibCursor writecur_20190 = after_tag_20186 + sizeof(GibFloat);

            *(GibFloat *) writecur_20190 = tmpval_24235;

            GibCursor writecur_20191 = writecur_20190 + sizeof(GibFloat);

            *(GibFloat *) writecur_20191 = tmpval_24237;

            GibCursor writecur_20192 = writecur_20191 + sizeof(GibFloat);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15782,
                                                                        end_r_15783,
                                                                        jump_17811,
                                                                        loc_15781,
                                                                        writecur_20192};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_491 = *(uintptr_t *) tmpcur_24228;
            GibCursor tmpcur_24243 = GIB_UNTAG(tagged_tmpcur_491);
            GibCursor tmpaftercur_24244 = tmpcur_24228 + 8;
            uint16_t tmptag_24245 = GIB_GET_TAG(tagged_tmpcur_491);
            GibCursor end_from_tagged_absran_15621 = tmpcur_24243 +
                      tmptag_24245;
            uintptr_t tagged_tmpcur_490 = *(uintptr_t *) tmpaftercur_24244;
            GibCursor tmpcur_24246 = GIB_UNTAG(tagged_tmpcur_490);
            GibCursor tmpaftercur_24247 = tmpaftercur_24244 + 8;
            uint16_t tmptag_24248 = GIB_GET_TAG(tagged_tmpcur_490);
            GibCursor end_from_tagged_absran_15622 = tmpcur_24246 +
                      tmptag_24248;
            uintptr_t tagged_tmpcur_489 = *(uintptr_t *) tmpaftercur_24247;
            GibCursor tmpcur_24249 = GIB_UNTAG(tagged_tmpcur_489);
            GibCursor tmpaftercur_24250 = tmpaftercur_24247 + 8;
            uint16_t tmptag_24251 = GIB_GET_TAG(tagged_tmpcur_489);
            GibCursor end_from_tagged_absran_15623 = tmpcur_24249 +
                      tmptag_24251;
            GibFloat tmpval_24252 = *(GibFloat *) tmpaftercur_24250;
            GibCursor tmpcur_24253 = tmpaftercur_24250 + sizeof(GibFloat);
            GibFloat tmpval_24254 = *(GibFloat *) tmpcur_24253;
            GibCursor tmpcur_24255 = tmpcur_24253 + sizeof(GibFloat);
            GibFloat tmpval_24256 = *(GibFloat *) tmpcur_24255;
            GibCursor tmpcur_24257 = tmpcur_24255 + sizeof(GibFloat);
            GibInt tmpval_24258 = *(GibInt *) tmpcur_24257;
            GibCursor tmpcur_24259 = tmpcur_24257 + sizeof(GibInt);
            GibFloat tmpval_24260 = *(GibFloat *) tmpcur_24259;
            GibCursor tmpcur_24261 = tmpcur_24259 + sizeof(GibFloat);
            GibCursor loc_16924 = loc_15781 + 25;

            *(GibPackedTag *) loc_15781 = 2;

            GibCursor writetag_20216 = loc_15781 + 1;
            GibCursor after_tag_20217 = loc_15781 + 1;

            *(GibFloat *) after_tag_20217 = tmpval_24252;

            GibCursor writecur_20221 = after_tag_20217 + sizeof(GibFloat);

            *(GibFloat *) writecur_20221 = tmpval_24254;

            GibCursor writecur_20222 = writecur_20221 + sizeof(GibFloat);

            *(GibFloat *) writecur_20222 = tmpval_24256;

            GibCursor writecur_20223 = writecur_20222 + sizeof(GibFloat);

            *(GibInt *) writecur_20223 = tmpval_24258;

            GibCursor writecur_20224 = writecur_20223 + sizeof(GibInt);

            *(GibFloat *) writecur_20224 = tmpval_24260;

            GibCursor writecur_20225 = writecur_20224 + sizeof(GibFloat);

            gib_shadowstack_push(rstack, loc_15781, end_r_15783, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, tmpcur_24249, end_r_15782, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, tmpcur_24246, end_r_15782, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, tmpcur_24243, end_r_15782, Stk,
                                 BH_Tree_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_485 =
                                                               _copy_without_ptrs_BH_Tree(end_r_15782, end_r_15783, loc_16924, tmpcur_24261);
            GibCursor pvrtmp_24262 = tmp_struct_485.field0;
            GibCursor pvrtmp_24263 = tmp_struct_485.field1;
            GibCursor pvrtmp_24264 = tmp_struct_485.field2;
            GibCursor pvrtmp_24265 = tmp_struct_485.field3;
            GibCursor pvrtmp_24266 = tmp_struct_485.field4;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_24243 = frame->ptr;
            end_r_15782 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tmpcur_24246 = frame->ptr;
            end_r_15782 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tmpcur_24249 = frame->ptr;
            end_r_15782 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_15781 = frame->ptr;
            end_r_15783 = frame->endptr;
            gib_shadowstack_push(rstack, loc_15781, pvrtmp_24263, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, tmpcur_24249, pvrtmp_24262, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, tmpcur_24246, pvrtmp_24262, Stk,
                                 BH_Tree_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_486 =
                                                               _copy_without_ptrs_BH_Tree(end_from_tagged_absran_15621, pvrtmp_24263, pvrtmp_24266, tmpcur_24243);
            GibCursor pvrtmp_24271 = tmp_struct_486.field0;
            GibCursor pvrtmp_24272 = tmp_struct_486.field1;
            GibCursor pvrtmp_24273 = tmp_struct_486.field2;
            GibCursor pvrtmp_24274 = tmp_struct_486.field3;
            GibCursor pvrtmp_24275 = tmp_struct_486.field4;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_24246 = frame->ptr;
            pvrtmp_24262 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tmpcur_24249 = frame->ptr;
            pvrtmp_24262 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_15781 = frame->ptr;
            pvrtmp_24263 = frame->endptr;
            gib_shadowstack_push(rstack, loc_15781, pvrtmp_24272, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, tmpcur_24249, pvrtmp_24271, Stk,
                                 BH_Tree_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_487 =
                                                               _copy_without_ptrs_BH_Tree(end_from_tagged_absran_15622, pvrtmp_24272, pvrtmp_24275, tmpcur_24246);
            GibCursor pvrtmp_24280 = tmp_struct_487.field0;
            GibCursor pvrtmp_24281 = tmp_struct_487.field1;
            GibCursor pvrtmp_24282 = tmp_struct_487.field2;
            GibCursor pvrtmp_24283 = tmp_struct_487.field3;
            GibCursor pvrtmp_24284 = tmp_struct_487.field4;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_24249 = frame->ptr;
            pvrtmp_24271 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_15781 = frame->ptr;
            pvrtmp_24272 = frame->endptr;
            gib_shadowstack_push(rstack, loc_15781, pvrtmp_24281, Stk,
                                 BH_Tree_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_488 =
                                                               _copy_without_ptrs_BH_Tree(end_from_tagged_absran_15623, pvrtmp_24281, pvrtmp_24284, tmpcur_24249);
            GibCursor pvrtmp_24289 = tmp_struct_488.field0;
            GibCursor pvrtmp_24290 = tmp_struct_488.field1;
            GibCursor pvrtmp_24291 = tmp_struct_488.field2;
            GibCursor pvrtmp_24292 = tmp_struct_488.field3;
            GibCursor pvrtmp_24293 = tmp_struct_488.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_15781 = frame->ptr;
            pvrtmp_24281 = frame->endptr;
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_24289,
                                                                        pvrtmp_24290,
                                                                        pvrtmp_24291,
                                                                        loc_15781,
                                                                        pvrtmp_24293};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_493 = *(uintptr_t *) tmpcur_24228;
            GibCursor tmpcur_24302 = GIB_UNTAG(tagged_tmpcur_493);
            GibCursor tmpaftercur_24303 = tmpcur_24228 + 8;
            uint16_t tmptag_24304 = GIB_GET_TAG(tagged_tmpcur_493);
            GibCursor end_from_tagged_indr_18138 = tmpcur_24302 + tmptag_24304;
            GibCursor jump_18140 = tmpcur_24228 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_492 =
                                                               _copy_without_ptrs_BH_Tree(end_from_tagged_indr_18138, end_r_15783, loc_15781, tmpcur_24302);
            GibCursor pvrtmp_24305 = tmp_struct_492.field0;
            GibCursor pvrtmp_24306 = tmp_struct_492.field1;
            GibCursor pvrtmp_24307 = tmp_struct_492.field2;
            GibCursor pvrtmp_24308 = tmp_struct_492.field3;
            GibCursor pvrtmp_24309 = tmp_struct_492.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15782,
                                                                        pvrtmp_24306,
                                                                        jump_18140,
                                                                        pvrtmp_24308,
                                                                        pvrtmp_24309};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_495 = *(uintptr_t *) tmpcur_24228;
            GibCursor tmpcur_24316 = GIB_UNTAG(tagged_tmpcur_495);
            GibCursor tmpaftercur_24317 = tmpcur_24228 + 8;
            uint16_t tmptag_24318 = GIB_GET_TAG(tagged_tmpcur_495);
            GibCursor end_from_tagged_indr_18138 = tmpcur_24316 + tmptag_24318;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_494 =
                                                               _copy_without_ptrs_BH_Tree(end_from_tagged_indr_18138, end_r_15783, loc_15781, tmpcur_24316);
            GibCursor pvrtmp_24319 = tmp_struct_494.field0;
            GibCursor pvrtmp_24320 = tmp_struct_494.field1;
            GibCursor pvrtmp_24321 = tmp_struct_494.field2;
            GibCursor pvrtmp_24322 = tmp_struct_494.field3;
            GibCursor pvrtmp_24323 = tmp_struct_494.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_24319,
                                                                        pvrtmp_24320,
                                                                        pvrtmp_24321,
                                                                        pvrtmp_24322,
                                                                        pvrtmp_24323};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_24227");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_BH_Tree(GibCursor end_r_15785,
                                         GibCursor arg_7354_10425_13767)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_24331 = *(GibPackedTag *) arg_7354_10425_13767;
    GibCursor tmpcur_24332 = arg_7354_10425_13767 + 1;


  switch_24376:
    ;
    switch (tmpval_24331) {

      case 0:
        {
            GibCursor jump_17826 = arg_7354_10425_13767 + 1;

            return (GibCursorGibCursorProd) {end_r_15785, jump_17826};
            break;
        }

      case 1:
        {
            GibFloat tmpval_24333 = *(GibFloat *) tmpcur_24332;
            GibCursor tmpcur_24334 = tmpcur_24332 + sizeof(GibFloat);
            GibFloat tmpval_24335 = *(GibFloat *) tmpcur_24334;
            GibCursor tmpcur_24336 = tmpcur_24334 + sizeof(GibFloat);
            GibFloat tmpval_24337 = *(GibFloat *) tmpcur_24336;
            GibCursor tmpcur_24338 = tmpcur_24336 + sizeof(GibFloat);
            GibCursor jump_17830 = tmpcur_24336 + 4;

            return (GibCursorGibCursorProd) {end_r_15785, jump_17830};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_502 = *(uintptr_t *) tmpcur_24332;
            GibCursor tmpcur_24339 = GIB_UNTAG(tagged_tmpcur_502);
            GibCursor tmpaftercur_24340 = tmpcur_24332 + 8;
            uint16_t tmptag_24341 = GIB_GET_TAG(tagged_tmpcur_502);
            GibCursor end_from_tagged_absran_15628 = tmpcur_24339 +
                      tmptag_24341;
            uintptr_t tagged_tmpcur_501 = *(uintptr_t *) tmpaftercur_24340;
            GibCursor tmpcur_24342 = GIB_UNTAG(tagged_tmpcur_501);
            GibCursor tmpaftercur_24343 = tmpaftercur_24340 + 8;
            uint16_t tmptag_24344 = GIB_GET_TAG(tagged_tmpcur_501);
            GibCursor end_from_tagged_absran_15629 = tmpcur_24342 +
                      tmptag_24344;
            uintptr_t tagged_tmpcur_500 = *(uintptr_t *) tmpaftercur_24343;
            GibCursor tmpcur_24345 = GIB_UNTAG(tagged_tmpcur_500);
            GibCursor tmpaftercur_24346 = tmpaftercur_24343 + 8;
            uint16_t tmptag_24347 = GIB_GET_TAG(tagged_tmpcur_500);
            GibCursor end_from_tagged_absran_15630 = tmpcur_24345 +
                      tmptag_24347;
            GibFloat tmpval_24348 = *(GibFloat *) tmpaftercur_24346;
            GibCursor tmpcur_24349 = tmpaftercur_24346 + sizeof(GibFloat);
            GibFloat tmpval_24350 = *(GibFloat *) tmpcur_24349;
            GibCursor tmpcur_24351 = tmpcur_24349 + sizeof(GibFloat);
            GibFloat tmpval_24352 = *(GibFloat *) tmpcur_24351;
            GibCursor tmpcur_24353 = tmpcur_24351 + sizeof(GibFloat);
            GibInt tmpval_24354 = *(GibInt *) tmpcur_24353;
            GibCursor tmpcur_24355 = tmpcur_24353 + sizeof(GibInt);
            GibFloat tmpval_24356 = *(GibFloat *) tmpcur_24355;
            GibCursor tmpcur_24357 = tmpcur_24355 + sizeof(GibFloat);

            gib_shadowstack_push(rstack, tmpcur_24345, end_r_15785, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, tmpcur_24342, end_r_15785, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, tmpcur_24339, end_r_15785, Stk,
                                 BH_Tree_T);

            GibCursorGibCursorProd tmp_struct_496 =
                                    _traverse_BH_Tree(end_r_15785, tmpcur_24357);
            GibCursor pvrtmp_24358 = tmp_struct_496.field0;
            GibCursor pvrtmp_24359 = tmp_struct_496.field1;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_24339 = frame->ptr;
            end_r_15785 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tmpcur_24342 = frame->ptr;
            end_r_15785 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tmpcur_24345 = frame->ptr;
            end_r_15785 = frame->endptr;
            gib_shadowstack_push(rstack, tmpcur_24345, pvrtmp_24358, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, tmpcur_24342, pvrtmp_24358, Stk,
                                 BH_Tree_T);

            GibCursorGibCursorProd tmp_struct_497 =
                                    _traverse_BH_Tree(end_from_tagged_absran_15628, tmpcur_24339);
            GibCursor pvrtmp_24360 = tmp_struct_497.field0;
            GibCursor pvrtmp_24361 = tmp_struct_497.field1;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_24342 = frame->ptr;
            pvrtmp_24358 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tmpcur_24345 = frame->ptr;
            pvrtmp_24358 = frame->endptr;
            gib_shadowstack_push(rstack, tmpcur_24345, pvrtmp_24360, Stk,
                                 BH_Tree_T);

            GibCursorGibCursorProd tmp_struct_498 =
                                    _traverse_BH_Tree(end_from_tagged_absran_15629, tmpcur_24342);
            GibCursor pvrtmp_24362 = tmp_struct_498.field0;
            GibCursor pvrtmp_24363 = tmp_struct_498.field1;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_24345 = frame->ptr;
            pvrtmp_24360 = frame->endptr;

            GibCursorGibCursorProd tmp_struct_499 =
                                    _traverse_BH_Tree(end_from_tagged_absran_15630, tmpcur_24345);
            GibCursor pvrtmp_24364 = tmp_struct_499.field0;
            GibCursor pvrtmp_24365 = tmp_struct_499.field1;

            return (GibCursorGibCursorProd) {pvrtmp_24364, pvrtmp_24365};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_504 = *(uintptr_t *) tmpcur_24332;
            GibCursor tmpcur_24366 = GIB_UNTAG(tagged_tmpcur_504);
            GibCursor tmpaftercur_24367 = tmpcur_24332 + 8;
            uint16_t tmptag_24368 = GIB_GET_TAG(tagged_tmpcur_504);
            GibCursor end_from_tagged_indr_18144 = tmpcur_24366 + tmptag_24368;
            GibCursor jump_18146 = tmpcur_24332 + 8;
            GibCursorGibCursorProd tmp_struct_503 =
                                    _traverse_BH_Tree(end_from_tagged_indr_18144, tmpcur_24366);
            GibCursor pvrtmp_24369 = tmp_struct_503.field0;
            GibCursor pvrtmp_24370 = tmp_struct_503.field1;

            return (GibCursorGibCursorProd) {end_r_15785, jump_18146};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_506 = *(uintptr_t *) tmpcur_24332;
            GibCursor tmpcur_24371 = GIB_UNTAG(tagged_tmpcur_506);
            GibCursor tmpaftercur_24372 = tmpcur_24332 + 8;
            uint16_t tmptag_24373 = GIB_GET_TAG(tagged_tmpcur_506);
            GibCursor end_from_tagged_indr_18144 = tmpcur_24371 + tmptag_24373;
            GibCursorGibCursorProd tmp_struct_505 =
                                    _traverse_BH_Tree(end_from_tagged_indr_18144, tmpcur_24371);
            GibCursor pvrtmp_24374 = tmp_struct_505.field0;
            GibCursor pvrtmp_24375 = tmp_struct_505.field1;

            return (GibCursorGibCursorProd) {pvrtmp_24374, pvrtmp_24375};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_24331");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_BH_Tree(GibCursor end_r_15787,
                                      GibCursor arg_7379_10442_13784)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_24377 = *(GibPackedTag *) arg_7379_10442_13784;
    GibCursor tmpcur_24378 = arg_7379_10442_13784 + 1;


  switch_24422:
    ;
    switch (tmpval_24377) {

      case 0:
        {
            GibCursor jump_17845 = arg_7379_10442_13784 + 1;
            unsigned char wildcard_7380_10443_13785 = gib_print_symbol(21870);
            unsigned char wildcard_7381_10444_13786 = gib_print_symbol(21857);

            return (GibCursorGibCursorProd) {end_r_15787, jump_17845};
            break;
        }

      case 1:
        {
            GibFloat tmpval_24379 = *(GibFloat *) tmpcur_24378;
            GibCursor tmpcur_24380 = tmpcur_24378 + sizeof(GibFloat);
            GibFloat tmpval_24381 = *(GibFloat *) tmpcur_24380;
            GibCursor tmpcur_24382 = tmpcur_24380 + sizeof(GibFloat);
            GibFloat tmpval_24383 = *(GibFloat *) tmpcur_24382;
            GibCursor tmpcur_24384 = tmpcur_24382 + sizeof(GibFloat);
            GibCursor jump_17849 = tmpcur_24382 + 4;
            unsigned char wildcard_7388_10448_13790 = gib_print_symbol(21869);
            unsigned char y_7385_10449_13791 = printf("%.2f", tmpval_24379);
            unsigned char y_7386_10450_13792 = printf("%.2f", tmpval_24381);
            unsigned char y_7387_10451_13793 = printf("%.2f", tmpval_24383);
            unsigned char wildcard_7389_10452_13794 = gib_print_symbol(21857);

            return (GibCursorGibCursorProd) {end_r_15787, jump_17849};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_513 = *(uintptr_t *) tmpcur_24378;
            GibCursor tmpcur_24385 = GIB_UNTAG(tagged_tmpcur_513);
            GibCursor tmpaftercur_24386 = tmpcur_24378 + 8;
            uint16_t tmptag_24387 = GIB_GET_TAG(tagged_tmpcur_513);
            GibCursor end_from_tagged_absran_15635 = tmpcur_24385 +
                      tmptag_24387;
            uintptr_t tagged_tmpcur_512 = *(uintptr_t *) tmpaftercur_24386;
            GibCursor tmpcur_24388 = GIB_UNTAG(tagged_tmpcur_512);
            GibCursor tmpaftercur_24389 = tmpaftercur_24386 + 8;
            uint16_t tmptag_24390 = GIB_GET_TAG(tagged_tmpcur_512);
            GibCursor end_from_tagged_absran_15636 = tmpcur_24388 +
                      tmptag_24390;
            uintptr_t tagged_tmpcur_511 = *(uintptr_t *) tmpaftercur_24389;
            GibCursor tmpcur_24391 = GIB_UNTAG(tagged_tmpcur_511);
            GibCursor tmpaftercur_24392 = tmpaftercur_24389 + 8;
            uint16_t tmptag_24393 = GIB_GET_TAG(tagged_tmpcur_511);
            GibCursor end_from_tagged_absran_15637 = tmpcur_24391 +
                      tmptag_24393;
            GibFloat tmpval_24394 = *(GibFloat *) tmpaftercur_24392;
            GibCursor tmpcur_24395 = tmpaftercur_24392 + sizeof(GibFloat);
            GibFloat tmpval_24396 = *(GibFloat *) tmpcur_24395;
            GibCursor tmpcur_24397 = tmpcur_24395 + sizeof(GibFloat);
            GibFloat tmpval_24398 = *(GibFloat *) tmpcur_24397;
            GibCursor tmpcur_24399 = tmpcur_24397 + sizeof(GibFloat);
            GibInt tmpval_24400 = *(GibInt *) tmpcur_24399;
            GibCursor tmpcur_24401 = tmpcur_24399 + sizeof(GibInt);
            GibFloat tmpval_24402 = *(GibFloat *) tmpcur_24401;
            GibCursor tmpcur_24403 = tmpcur_24401 + sizeof(GibFloat);
            unsigned char wildcard_7408_10462_13804 = gib_print_symbol(21868);
            unsigned char y_7399_10463_13805 = printf("%.2f", tmpval_24394);
            unsigned char y_7400_10464_13806 = printf("%.2f", tmpval_24396);
            unsigned char y_7401_10465_13807 = printf("%.2f", tmpval_24398);
            unsigned char y_7402_10466_13808 = printf("%ld", tmpval_24400);
            unsigned char y_7403_10467_13809 = printf("%.2f", tmpval_24402);

            gib_shadowstack_push(rstack, tmpcur_24391, end_r_15787, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, tmpcur_24388, end_r_15787, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, tmpcur_24385, end_r_15787, Stk,
                                 BH_Tree_T);

            GibCursorGibCursorProd tmp_struct_507 =
                                    _print_BH_Tree(end_r_15787, tmpcur_24403);
            GibCursor pvrtmp_24404 = tmp_struct_507.field0;
            GibCursor pvrtmp_24405 = tmp_struct_507.field1;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_24385 = frame->ptr;
            end_r_15787 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tmpcur_24388 = frame->ptr;
            end_r_15787 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tmpcur_24391 = frame->ptr;
            end_r_15787 = frame->endptr;
            gib_shadowstack_push(rstack, tmpcur_24391, pvrtmp_24404, Stk,
                                 BH_Tree_T);
            gib_shadowstack_push(rstack, tmpcur_24388, pvrtmp_24404, Stk,
                                 BH_Tree_T);

            GibCursorGibCursorProd tmp_struct_508 =
                                    _print_BH_Tree(end_from_tagged_absran_15635, tmpcur_24385);
            GibCursor pvrtmp_24406 = tmp_struct_508.field0;
            GibCursor pvrtmp_24407 = tmp_struct_508.field1;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_24388 = frame->ptr;
            pvrtmp_24404 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tmpcur_24391 = frame->ptr;
            pvrtmp_24404 = frame->endptr;
            gib_shadowstack_push(rstack, tmpcur_24391, pvrtmp_24406, Stk,
                                 BH_Tree_T);

            GibCursorGibCursorProd tmp_struct_509 =
                                    _print_BH_Tree(end_from_tagged_absran_15636, tmpcur_24388);
            GibCursor pvrtmp_24408 = tmp_struct_509.field0;
            GibCursor pvrtmp_24409 = tmp_struct_509.field1;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_24391 = frame->ptr;
            pvrtmp_24406 = frame->endptr;

            GibCursorGibCursorProd tmp_struct_510 =
                                    _print_BH_Tree(end_from_tagged_absran_15637, tmpcur_24391);
            GibCursor pvrtmp_24410 = tmp_struct_510.field0;
            GibCursor pvrtmp_24411 = tmp_struct_510.field1;
            unsigned char wildcard_7409_10472_13814 = gib_print_symbol(21857);

            return (GibCursorGibCursorProd) {pvrtmp_24410, pvrtmp_24411};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_515 = *(uintptr_t *) tmpcur_24378;
            GibCursor tmpcur_24412 = GIB_UNTAG(tagged_tmpcur_515);
            GibCursor tmpaftercur_24413 = tmpcur_24378 + 8;
            uint16_t tmptag_24414 = GIB_GET_TAG(tagged_tmpcur_515);
            GibCursor end_from_tagged_indr_18150 = tmpcur_24412 + tmptag_24414;
            GibCursor jump_18152 = tmpcur_24378 + 8;
            unsigned char wildcard_18155 = gib_print_symbol(21876);
            GibCursorGibCursorProd tmp_struct_514 =
                                    _print_BH_Tree(end_from_tagged_indr_18150, tmpcur_24412);
            GibCursor pvrtmp_24415 = tmp_struct_514.field0;
            GibCursor pvrtmp_24416 = tmp_struct_514.field1;

            return (GibCursorGibCursorProd) {end_r_15787, jump_18152};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_517 = *(uintptr_t *) tmpcur_24378;
            GibCursor tmpcur_24417 = GIB_UNTAG(tagged_tmpcur_517);
            GibCursor tmpaftercur_24418 = tmpcur_24378 + 8;
            uint16_t tmptag_24419 = GIB_GET_TAG(tagged_tmpcur_517);
            GibCursor end_from_tagged_indr_18150 = tmpcur_24417 + tmptag_24419;
            unsigned char wildcard_18155 = gib_print_symbol(21875);
            GibCursorGibCursorProd tmp_struct_516 =
                                    _print_BH_Tree(end_from_tagged_indr_18150, tmpcur_24417);
            GibCursor pvrtmp_24420 = tmp_struct_516.field0;
            GibCursor pvrtmp_24421 = tmp_struct_516.field1;

            return (GibCursorGibCursorProd) {pvrtmp_24420, pvrtmp_24421};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_24377");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_AList(GibCursor end_r_15790,
                                                              GibCursor end_r_15791,
                                                              GibCursor loc_15789,
                                                              GibCursor arg_7410_10473_13815)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_15789 + 18 > end_r_15791) {
        gib_grow_region(&loc_15789, &end_r_15791);
    }

    GibPackedTag tmpval_24423 = *(GibPackedTag *) arg_7410_10473_13815;
    GibCursor tmpcur_24424 = arg_7410_10473_13815 + 1;


  switch_24487:
    ;
    switch (tmpval_24423) {

      case 0:
        {
            GibInt tmpval_24425 = *(GibInt *) tmpcur_24424;
            GibCursor tmpcur_24426 = tmpcur_24424 + sizeof(GibInt);
            GibCursor jump_17864 = tmpcur_24424 + 8;

            *(GibPackedTag *) loc_15789 = 0;

            GibCursor writetag_20307 = loc_15789 + 1;
            GibCursor after_tag_20308 = loc_15789 + 1;

            *(GibInt *) after_tag_20308 = tmpval_24425;

            GibCursor writecur_20312 = after_tag_20308 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15790,
                                                                        end_r_15791,
                                                                        jump_17864,
                                                                        loc_15789,
                                                                        writecur_20312};
            break;
        }

      case 1:
        {
            GibInt tmpval_24431 = *(GibInt *) tmpcur_24424;
            GibCursor tmpcur_24432 = tmpcur_24424 + sizeof(GibInt);
            GibCursor jump_17866 = tmpcur_24424 + 8;

            *(GibPackedTag *) loc_15789 = 1;

            GibCursor writetag_20317 = loc_15789 + 1;
            GibCursor after_tag_20318 = loc_15789 + 1;

            *(GibInt *) after_tag_20318 = tmpval_24431;

            GibCursor writecur_20322 = after_tag_20318 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15790,
                                                                        end_r_15791,
                                                                        jump_17866,
                                                                        loc_15789,
                                                                        writecur_20322};
            break;
        }

      case 2:
        {
            GibCursor loc_17010 = loc_15789 + 1;

            *(GibPackedTag *) loc_15789 = 2;

            GibCursor writetag_20332 = loc_15789 + 1;

            gib_shadowstack_push(rstack, loc_15789, end_r_15791, Stk, AList_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_518 =
                                                               _copy_AList(end_r_15790, end_r_15791, loc_17010, tmpcur_24424);
            GibCursor pvrtmp_24437 = tmp_struct_518.field0;
            GibCursor pvrtmp_24438 = tmp_struct_518.field1;
            GibCursor pvrtmp_24439 = tmp_struct_518.field2;
            GibCursor pvrtmp_24440 = tmp_struct_518.field3;
            GibCursor pvrtmp_24441 = tmp_struct_518.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_15789 = frame->ptr;
            end_r_15791 = frame->endptr;
            gib_shadowstack_push(rstack, loc_15789, pvrtmp_24438, Stk, AList_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_519 =
                                                               _copy_AList(pvrtmp_24437, pvrtmp_24438, pvrtmp_24441, pvrtmp_24439);
            GibCursor pvrtmp_24446 = tmp_struct_519.field0;
            GibCursor pvrtmp_24447 = tmp_struct_519.field1;
            GibCursor pvrtmp_24448 = tmp_struct_519.field2;
            GibCursor pvrtmp_24449 = tmp_struct_519.field3;
            GibCursor pvrtmp_24450 = tmp_struct_519.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_15789 = frame->ptr;
            pvrtmp_24438 = frame->endptr;

            GibCursor after_tag_20333 = loc_15789 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_24446,
                                                                        pvrtmp_24447,
                                                                        pvrtmp_24448,
                                                                        loc_15789,
                                                                        pvrtmp_24450};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_521 = *(uintptr_t *) tmpcur_24424;
            GibCursor tmpcur_24459 = GIB_UNTAG(tagged_tmpcur_521);
            GibCursor tmpaftercur_24460 = tmpcur_24424 + 8;
            uint16_t tmptag_24461 = GIB_GET_TAG(tagged_tmpcur_521);
            GibCursor end_from_tagged_indr_18156 = tmpcur_24459 + tmptag_24461;
            GibCursor jump_18158 = tmpcur_24424 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_520 =
                                                               _copy_AList(end_from_tagged_indr_18156, end_r_15791, loc_15789, tmpcur_24459);
            GibCursor pvrtmp_24462 = tmp_struct_520.field0;
            GibCursor pvrtmp_24463 = tmp_struct_520.field1;
            GibCursor pvrtmp_24464 = tmp_struct_520.field2;
            GibCursor pvrtmp_24465 = tmp_struct_520.field3;
            GibCursor pvrtmp_24466 = tmp_struct_520.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15790,
                                                                        pvrtmp_24463,
                                                                        jump_18158,
                                                                        pvrtmp_24465,
                                                                        pvrtmp_24466};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_523 = *(uintptr_t *) tmpcur_24424;
            GibCursor tmpcur_24473 = GIB_UNTAG(tagged_tmpcur_523);
            GibCursor tmpaftercur_24474 = tmpcur_24424 + 8;
            uint16_t tmptag_24475 = GIB_GET_TAG(tagged_tmpcur_523);
            GibCursor end_from_tagged_indr_18156 = tmpcur_24473 + tmptag_24475;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_522 =
                                                               _copy_AList(end_from_tagged_indr_18156, end_r_15791, loc_15789, tmpcur_24473);
            GibCursor pvrtmp_24476 = tmp_struct_522.field0;
            GibCursor pvrtmp_24477 = tmp_struct_522.field1;
            GibCursor pvrtmp_24478 = tmp_struct_522.field2;
            GibCursor pvrtmp_24479 = tmp_struct_522.field3;
            GibCursor pvrtmp_24480 = tmp_struct_522.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_24476,
                                                                        pvrtmp_24477,
                                                                        pvrtmp_24478,
                                                                        pvrtmp_24479,
                                                                        pvrtmp_24480};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_24423");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_AList(GibCursor end_r_15794,
                                                                           GibCursor end_r_15795,
                                                                           GibCursor loc_15793,
                                                                           GibCursor arg_7419_10482_13824)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_24488 = *(GibPackedTag *) arg_7419_10482_13824;
    GibCursor tmpcur_24489 = arg_7419_10482_13824 + 1;


  switch_24552:
    ;
    switch (tmpval_24488) {

      case 0:
        {
            GibInt tmpval_24490 = *(GibInt *) tmpcur_24489;
            GibCursor tmpcur_24491 = tmpcur_24489 + sizeof(GibInt);
            GibCursor jump_17871 = tmpcur_24489 + 8;

            *(GibPackedTag *) loc_15793 = 0;

            GibCursor writetag_20354 = loc_15793 + 1;
            GibCursor after_tag_20355 = loc_15793 + 1;

            *(GibInt *) after_tag_20355 = tmpval_24490;

            GibCursor writecur_20359 = after_tag_20355 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15794,
                                                                        end_r_15795,
                                                                        jump_17871,
                                                                        loc_15793,
                                                                        writecur_20359};
            break;
        }

      case 1:
        {
            GibInt tmpval_24496 = *(GibInt *) tmpcur_24489;
            GibCursor tmpcur_24497 = tmpcur_24489 + sizeof(GibInt);
            GibCursor jump_17873 = tmpcur_24489 + 8;

            *(GibPackedTag *) loc_15793 = 1;

            GibCursor writetag_20364 = loc_15793 + 1;
            GibCursor after_tag_20365 = loc_15793 + 1;

            *(GibInt *) after_tag_20365 = tmpval_24496;

            GibCursor writecur_20369 = after_tag_20365 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15794,
                                                                        end_r_15795,
                                                                        jump_17873,
                                                                        loc_15793,
                                                                        writecur_20369};
            break;
        }

      case 2:
        {
            GibCursor loc_17032 = loc_15793 + 1;

            *(GibPackedTag *) loc_15793 = 2;

            GibCursor writetag_20379 = loc_15793 + 1;

            gib_shadowstack_push(rstack, loc_15793, end_r_15795, Stk, AList_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_527 =
                                                               _copy_without_ptrs_AList(end_r_15794, end_r_15795, loc_17032, tmpcur_24489);
            GibCursor pvrtmp_24502 = tmp_struct_527.field0;
            GibCursor pvrtmp_24503 = tmp_struct_527.field1;
            GibCursor pvrtmp_24504 = tmp_struct_527.field2;
            GibCursor pvrtmp_24505 = tmp_struct_527.field3;
            GibCursor pvrtmp_24506 = tmp_struct_527.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_15793 = frame->ptr;
            end_r_15795 = frame->endptr;
            gib_shadowstack_push(rstack, loc_15793, pvrtmp_24503, Stk, AList_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_528 =
                                                               _copy_without_ptrs_AList(pvrtmp_24502, pvrtmp_24503, pvrtmp_24506, pvrtmp_24504);
            GibCursor pvrtmp_24511 = tmp_struct_528.field0;
            GibCursor pvrtmp_24512 = tmp_struct_528.field1;
            GibCursor pvrtmp_24513 = tmp_struct_528.field2;
            GibCursor pvrtmp_24514 = tmp_struct_528.field3;
            GibCursor pvrtmp_24515 = tmp_struct_528.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_15793 = frame->ptr;
            pvrtmp_24503 = frame->endptr;

            GibCursor after_tag_20380 = loc_15793 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_24511,
                                                                        pvrtmp_24512,
                                                                        pvrtmp_24513,
                                                                        loc_15793,
                                                                        pvrtmp_24515};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_530 = *(uintptr_t *) tmpcur_24489;
            GibCursor tmpcur_24524 = GIB_UNTAG(tagged_tmpcur_530);
            GibCursor tmpaftercur_24525 = tmpcur_24489 + 8;
            uint16_t tmptag_24526 = GIB_GET_TAG(tagged_tmpcur_530);
            GibCursor end_from_tagged_indr_18162 = tmpcur_24524 + tmptag_24526;
            GibCursor jump_18164 = tmpcur_24489 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_529 =
                                                               _copy_without_ptrs_AList(end_from_tagged_indr_18162, end_r_15795, loc_15793, tmpcur_24524);
            GibCursor pvrtmp_24527 = tmp_struct_529.field0;
            GibCursor pvrtmp_24528 = tmp_struct_529.field1;
            GibCursor pvrtmp_24529 = tmp_struct_529.field2;
            GibCursor pvrtmp_24530 = tmp_struct_529.field3;
            GibCursor pvrtmp_24531 = tmp_struct_529.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15794,
                                                                        pvrtmp_24528,
                                                                        jump_18164,
                                                                        pvrtmp_24530,
                                                                        pvrtmp_24531};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_532 = *(uintptr_t *) tmpcur_24489;
            GibCursor tmpcur_24538 = GIB_UNTAG(tagged_tmpcur_532);
            GibCursor tmpaftercur_24539 = tmpcur_24489 + 8;
            uint16_t tmptag_24540 = GIB_GET_TAG(tagged_tmpcur_532);
            GibCursor end_from_tagged_indr_18162 = tmpcur_24538 + tmptag_24540;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_531 =
                                                               _copy_without_ptrs_AList(end_from_tagged_indr_18162, end_r_15795, loc_15793, tmpcur_24538);
            GibCursor pvrtmp_24541 = tmp_struct_531.field0;
            GibCursor pvrtmp_24542 = tmp_struct_531.field1;
            GibCursor pvrtmp_24543 = tmp_struct_531.field2;
            GibCursor pvrtmp_24544 = tmp_struct_531.field3;
            GibCursor pvrtmp_24545 = tmp_struct_531.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_24541,
                                                                        pvrtmp_24542,
                                                                        pvrtmp_24543,
                                                                        pvrtmp_24544,
                                                                        pvrtmp_24545};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_24488");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_AList(GibCursor end_r_15797,
                                       GibCursor arg_7428_10491_13833)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_24553 = *(GibPackedTag *) arg_7428_10491_13833;
    GibCursor tmpcur_24554 = arg_7428_10491_13833 + 1;


  switch_24573:
    ;
    switch (tmpval_24553) {

      case 0:
        {
            GibInt tmpval_24555 = *(GibInt *) tmpcur_24554;
            GibCursor tmpcur_24556 = tmpcur_24554 + sizeof(GibInt);
            GibCursor jump_17878 = tmpcur_24554 + 8;

            return (GibCursorGibCursorProd) {end_r_15797, jump_17878};
            break;
        }

      case 1:
        {
            GibInt tmpval_24557 = *(GibInt *) tmpcur_24554;
            GibCursor tmpcur_24558 = tmpcur_24554 + sizeof(GibInt);
            GibCursor jump_17880 = tmpcur_24554 + 8;

            return (GibCursorGibCursorProd) {end_r_15797, jump_17880};
            break;
        }

      case 2:
        {
            GibCursorGibCursorProd tmp_struct_533 =
                                    _traverse_AList(end_r_15797, tmpcur_24554);
            GibCursor pvrtmp_24559 = tmp_struct_533.field0;
            GibCursor pvrtmp_24560 = tmp_struct_533.field1;
            GibCursorGibCursorProd tmp_struct_534 =
                                    _traverse_AList(pvrtmp_24559, pvrtmp_24560);
            GibCursor pvrtmp_24561 = tmp_struct_534.field0;
            GibCursor pvrtmp_24562 = tmp_struct_534.field1;

            return (GibCursorGibCursorProd) {pvrtmp_24561, pvrtmp_24562};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_536 = *(uintptr_t *) tmpcur_24554;
            GibCursor tmpcur_24563 = GIB_UNTAG(tagged_tmpcur_536);
            GibCursor tmpaftercur_24564 = tmpcur_24554 + 8;
            uint16_t tmptag_24565 = GIB_GET_TAG(tagged_tmpcur_536);
            GibCursor end_from_tagged_indr_18168 = tmpcur_24563 + tmptag_24565;
            GibCursor jump_18170 = tmpcur_24554 + 8;
            GibCursorGibCursorProd tmp_struct_535 =
                                    _traverse_AList(end_from_tagged_indr_18168, tmpcur_24563);
            GibCursor pvrtmp_24566 = tmp_struct_535.field0;
            GibCursor pvrtmp_24567 = tmp_struct_535.field1;

            return (GibCursorGibCursorProd) {end_r_15797, jump_18170};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_538 = *(uintptr_t *) tmpcur_24554;
            GibCursor tmpcur_24568 = GIB_UNTAG(tagged_tmpcur_538);
            GibCursor tmpaftercur_24569 = tmpcur_24554 + 8;
            uint16_t tmptag_24570 = GIB_GET_TAG(tagged_tmpcur_538);
            GibCursor end_from_tagged_indr_18168 = tmpcur_24568 + tmptag_24570;
            GibCursorGibCursorProd tmp_struct_537 =
                                    _traverse_AList(end_from_tagged_indr_18168, tmpcur_24568);
            GibCursor pvrtmp_24571 = tmp_struct_537.field0;
            GibCursor pvrtmp_24572 = tmp_struct_537.field1;

            return (GibCursorGibCursorProd) {pvrtmp_24571, pvrtmp_24572};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_24553");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_AList(GibCursor end_r_15799,
                                    GibCursor arg_7437_10498_13840)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_24574 = *(GibPackedTag *) arg_7437_10498_13840;
    GibCursor tmpcur_24575 = arg_7437_10498_13840 + 1;


  switch_24594:
    ;
    switch (tmpval_24574) {

      case 0:
        {
            GibInt tmpval_24576 = *(GibInt *) tmpcur_24575;
            GibCursor tmpcur_24577 = tmpcur_24575 + sizeof(GibInt);
            GibCursor jump_17885 = tmpcur_24575 + 8;
            unsigned char wildcard_7440_10500_13842 = gib_print_symbol(21874);
            unsigned char y_7439_10501_13843 = printf("%ld", tmpval_24576);
            unsigned char wildcard_7441_10502_13844 = gib_print_symbol(21857);

            return (GibCursorGibCursorProd) {end_r_15799, jump_17885};
            break;
        }

      case 1:
        {
            GibInt tmpval_24578 = *(GibInt *) tmpcur_24575;
            GibCursor tmpcur_24579 = tmpcur_24575 + sizeof(GibInt);
            GibCursor jump_17887 = tmpcur_24575 + 8;
            unsigned char wildcard_7444_10504_13846 = gib_print_symbol(21873);
            unsigned char y_7443_10505_13847 = printf("%ld", tmpval_24578);
            unsigned char wildcard_7445_10506_13848 = gib_print_symbol(21857);

            return (GibCursorGibCursorProd) {end_r_15799, jump_17887};
            break;
        }

      case 2:
        {
            unsigned char wildcard_7450_10509_13851 = gib_print_symbol(21871);
            GibCursorGibCursorProd tmp_struct_539 =
                                    _print_AList(end_r_15799, tmpcur_24575);
            GibCursor pvrtmp_24580 = tmp_struct_539.field0;
            GibCursor pvrtmp_24581 = tmp_struct_539.field1;
            GibCursorGibCursorProd tmp_struct_540 =
                                    _print_AList(pvrtmp_24580, pvrtmp_24581);
            GibCursor pvrtmp_24582 = tmp_struct_540.field0;
            GibCursor pvrtmp_24583 = tmp_struct_540.field1;
            unsigned char wildcard_7451_10512_13854 = gib_print_symbol(21857);

            return (GibCursorGibCursorProd) {pvrtmp_24582, pvrtmp_24583};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_542 = *(uintptr_t *) tmpcur_24575;
            GibCursor tmpcur_24584 = GIB_UNTAG(tagged_tmpcur_542);
            GibCursor tmpaftercur_24585 = tmpcur_24575 + 8;
            uint16_t tmptag_24586 = GIB_GET_TAG(tagged_tmpcur_542);
            GibCursor end_from_tagged_indr_18174 = tmpcur_24584 + tmptag_24586;
            GibCursor jump_18176 = tmpcur_24575 + 8;
            unsigned char wildcard_18179 = gib_print_symbol(21876);
            GibCursorGibCursorProd tmp_struct_541 =
                                    _print_AList(end_from_tagged_indr_18174, tmpcur_24584);
            GibCursor pvrtmp_24587 = tmp_struct_541.field0;
            GibCursor pvrtmp_24588 = tmp_struct_541.field1;

            return (GibCursorGibCursorProd) {end_r_15799, jump_18176};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_544 = *(uintptr_t *) tmpcur_24575;
            GibCursor tmpcur_24589 = GIB_UNTAG(tagged_tmpcur_544);
            GibCursor tmpaftercur_24590 = tmpcur_24575 + 8;
            uint16_t tmptag_24591 = GIB_GET_TAG(tagged_tmpcur_544);
            GibCursor end_from_tagged_indr_18174 = tmpcur_24589 + tmptag_24591;
            unsigned char wildcard_18179 = gib_print_symbol(21875);
            GibCursorGibCursorProd tmp_struct_543 =
                                    _print_AList(end_from_tagged_indr_18174, tmpcur_24589);
            GibCursor pvrtmp_24592 = tmp_struct_543.field0;
            GibCursor pvrtmp_24593 = tmp_struct_543.field1;

            return (GibCursorGibCursorProd) {pvrtmp_24592, pvrtmp_24593};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_24574");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_Exp(GibCursor end_r_15802,
                                                            GibCursor end_r_15803,
                                                            GibCursor loc_15801,
                                                            GibCursor arg_7452_10513_13855)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_15801 + 18 > end_r_15803) {
        gib_grow_region(&loc_15801, &end_r_15803);
    }

    GibPackedTag tmpval_24595 = *(GibPackedTag *) arg_7452_10513_13855;
    GibCursor tmpcur_24596 = arg_7452_10513_13855 + 1;


  switch_24705:
    ;
    switch (tmpval_24595) {

      case 0:
        {
            GibInt tmpval_24597 = *(GibInt *) tmpcur_24596;
            GibCursor tmpcur_24598 = tmpcur_24596 + sizeof(GibInt);
            GibCursor jump_17892 = tmpcur_24596 + 8;

            *(GibPackedTag *) loc_15801 = 0;

            GibCursor writetag_20435 = loc_15801 + 1;
            GibCursor after_tag_20436 = loc_15801 + 1;

            *(GibInt *) after_tag_20436 = tmpval_24597;

            GibCursor writecur_20440 = after_tag_20436 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15802,
                                                                        end_r_15803,
                                                                        jump_17892,
                                                                        loc_15801,
                                                                        writecur_20440};
            break;
        }

      case 1:
        {
            GibCursor jump_17894 = arg_7452_10513_13855 + 1;

            *(GibPackedTag *) loc_15801 = 1;

            GibCursor writetag_20444 = loc_15801 + 1;
            GibCursor after_tag_20445 = loc_15801 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15802,
                                                                        end_r_15803,
                                                                        jump_17894,
                                                                        loc_15801,
                                                                        after_tag_20445};
            break;
        }

      case 2:
        {
            GibCursor jump_17896 = arg_7452_10513_13855 + 1;

            *(GibPackedTag *) loc_15801 = 2;

            GibCursor writetag_20452 = loc_15801 + 1;
            GibCursor after_tag_20453 = loc_15801 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15802,
                                                                        end_r_15803,
                                                                        jump_17896,
                                                                        loc_15801,
                                                                        after_tag_20453};
            break;
        }

      case 3:
        {
            GibCursor loc_17072 = loc_15801 + 1;

            *(GibPackedTag *) loc_15801 = 3;

            GibCursor writetag_20466 = loc_15801 + 1;

            gib_shadowstack_push(rstack, loc_15801, end_r_15803, Stk, Exp_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_545 =
                                                               _copy_Exp(end_r_15802, end_r_15803, loc_17072, tmpcur_24596);
            GibCursor pvrtmp_24611 = tmp_struct_545.field0;
            GibCursor pvrtmp_24612 = tmp_struct_545.field1;
            GibCursor pvrtmp_24613 = tmp_struct_545.field2;
            GibCursor pvrtmp_24614 = tmp_struct_545.field3;
            GibCursor pvrtmp_24615 = tmp_struct_545.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_15801 = frame->ptr;
            end_r_15803 = frame->endptr;
            gib_shadowstack_push(rstack, loc_15801, pvrtmp_24612, Stk, Exp_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_546 =
                                                               _copy_Exp(pvrtmp_24611, pvrtmp_24612, pvrtmp_24615, pvrtmp_24613);
            GibCursor pvrtmp_24620 = tmp_struct_546.field0;
            GibCursor pvrtmp_24621 = tmp_struct_546.field1;
            GibCursor pvrtmp_24622 = tmp_struct_546.field2;
            GibCursor pvrtmp_24623 = tmp_struct_546.field3;
            GibCursor pvrtmp_24624 = tmp_struct_546.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_15801 = frame->ptr;
            pvrtmp_24612 = frame->endptr;

            GibCursor after_tag_20467 = loc_15801 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_24620,
                                                                        pvrtmp_24621,
                                                                        pvrtmp_24622,
                                                                        loc_15801,
                                                                        pvrtmp_24624};
            break;
        }

      case 4:
        {
            GibCursor loc_17084 = loc_15801 + 1;

            *(GibPackedTag *) loc_15801 = 4;

            GibCursor writetag_20483 = loc_15801 + 1;

            gib_shadowstack_push(rstack, loc_15801, end_r_15803, Stk, Exp_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_547 =
                                                               _copy_Exp(end_r_15802, end_r_15803, loc_17084, tmpcur_24596);
            GibCursor pvrtmp_24633 = tmp_struct_547.field0;
            GibCursor pvrtmp_24634 = tmp_struct_547.field1;
            GibCursor pvrtmp_24635 = tmp_struct_547.field2;
            GibCursor pvrtmp_24636 = tmp_struct_547.field3;
            GibCursor pvrtmp_24637 = tmp_struct_547.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_15801 = frame->ptr;
            end_r_15803 = frame->endptr;
            gib_shadowstack_push(rstack, loc_15801, pvrtmp_24634, Stk, Exp_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_548 =
                                                               _copy_Exp(pvrtmp_24633, pvrtmp_24634, pvrtmp_24637, pvrtmp_24635);
            GibCursor pvrtmp_24642 = tmp_struct_548.field0;
            GibCursor pvrtmp_24643 = tmp_struct_548.field1;
            GibCursor pvrtmp_24644 = tmp_struct_548.field2;
            GibCursor pvrtmp_24645 = tmp_struct_548.field3;
            GibCursor pvrtmp_24646 = tmp_struct_548.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_15801 = frame->ptr;
            pvrtmp_24634 = frame->endptr;

            GibCursor after_tag_20484 = loc_15801 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_24642,
                                                                        pvrtmp_24643,
                                                                        pvrtmp_24644,
                                                                        loc_15801,
                                                                        pvrtmp_24646};
            break;
        }

      case 5:
        {
            GibCursor loc_17096 = loc_15801 + 1;

            *(GibPackedTag *) loc_15801 = 5;

            GibCursor writetag_20500 = loc_15801 + 1;

            gib_shadowstack_push(rstack, loc_15801, end_r_15803, Stk, Exp_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_549 =
                                                               _copy_Exp(end_r_15802, end_r_15803, loc_17096, tmpcur_24596);
            GibCursor pvrtmp_24655 = tmp_struct_549.field0;
            GibCursor pvrtmp_24656 = tmp_struct_549.field1;
            GibCursor pvrtmp_24657 = tmp_struct_549.field2;
            GibCursor pvrtmp_24658 = tmp_struct_549.field3;
            GibCursor pvrtmp_24659 = tmp_struct_549.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_15801 = frame->ptr;
            end_r_15803 = frame->endptr;
            gib_shadowstack_push(rstack, loc_15801, pvrtmp_24656, Stk, Exp_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_550 =
                                                               _copy_Exp(pvrtmp_24655, pvrtmp_24656, pvrtmp_24659, pvrtmp_24657);
            GibCursor pvrtmp_24664 = tmp_struct_550.field0;
            GibCursor pvrtmp_24665 = tmp_struct_550.field1;
            GibCursor pvrtmp_24666 = tmp_struct_550.field2;
            GibCursor pvrtmp_24667 = tmp_struct_550.field3;
            GibCursor pvrtmp_24668 = tmp_struct_550.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_15801 = frame->ptr;
            pvrtmp_24656 = frame->endptr;

            GibCursor after_tag_20501 = loc_15801 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_24664,
                                                                        pvrtmp_24665,
                                                                        pvrtmp_24666,
                                                                        loc_15801,
                                                                        pvrtmp_24668};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_552 = *(uintptr_t *) tmpcur_24596;
            GibCursor tmpcur_24677 = GIB_UNTAG(tagged_tmpcur_552);
            GibCursor tmpaftercur_24678 = tmpcur_24596 + 8;
            uint16_t tmptag_24679 = GIB_GET_TAG(tagged_tmpcur_552);
            GibCursor end_from_tagged_indr_18180 = tmpcur_24677 + tmptag_24679;
            GibCursor jump_18182 = tmpcur_24596 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_551 =
                                                               _copy_Exp(end_from_tagged_indr_18180, end_r_15803, loc_15801, tmpcur_24677);
            GibCursor pvrtmp_24680 = tmp_struct_551.field0;
            GibCursor pvrtmp_24681 = tmp_struct_551.field1;
            GibCursor pvrtmp_24682 = tmp_struct_551.field2;
            GibCursor pvrtmp_24683 = tmp_struct_551.field3;
            GibCursor pvrtmp_24684 = tmp_struct_551.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15802,
                                                                        pvrtmp_24681,
                                                                        jump_18182,
                                                                        pvrtmp_24683,
                                                                        pvrtmp_24684};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_554 = *(uintptr_t *) tmpcur_24596;
            GibCursor tmpcur_24691 = GIB_UNTAG(tagged_tmpcur_554);
            GibCursor tmpaftercur_24692 = tmpcur_24596 + 8;
            uint16_t tmptag_24693 = GIB_GET_TAG(tagged_tmpcur_554);
            GibCursor end_from_tagged_indr_18180 = tmpcur_24691 + tmptag_24693;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_553 =
                                                               _copy_Exp(end_from_tagged_indr_18180, end_r_15803, loc_15801, tmpcur_24691);
            GibCursor pvrtmp_24694 = tmp_struct_553.field0;
            GibCursor pvrtmp_24695 = tmp_struct_553.field1;
            GibCursor pvrtmp_24696 = tmp_struct_553.field2;
            GibCursor pvrtmp_24697 = tmp_struct_553.field3;
            GibCursor pvrtmp_24698 = tmp_struct_553.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_24694,
                                                                        pvrtmp_24695,
                                                                        pvrtmp_24696,
                                                                        pvrtmp_24697,
                                                                        pvrtmp_24698};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_24595");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_Exp(GibCursor end_r_15806,
                                                                         GibCursor end_r_15807,
                                                                         GibCursor loc_15805,
                                                                         GibCursor arg_7467_10528_13870)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_24706 = *(GibPackedTag *) arg_7467_10528_13870;
    GibCursor tmpcur_24707 = arg_7467_10528_13870 + 1;


  switch_24816:
    ;
    switch (tmpval_24706) {

      case 0:
        {
            GibInt tmpval_24708 = *(GibInt *) tmpcur_24707;
            GibCursor tmpcur_24709 = tmpcur_24707 + sizeof(GibInt);
            GibCursor jump_17907 = tmpcur_24707 + 8;

            *(GibPackedTag *) loc_15805 = 0;

            GibCursor writetag_20522 = loc_15805 + 1;
            GibCursor after_tag_20523 = loc_15805 + 1;

            *(GibInt *) after_tag_20523 = tmpval_24708;

            GibCursor writecur_20527 = after_tag_20523 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15806,
                                                                        end_r_15807,
                                                                        jump_17907,
                                                                        loc_15805,
                                                                        writecur_20527};
            break;
        }

      case 1:
        {
            GibCursor jump_17909 = arg_7467_10528_13870 + 1;

            *(GibPackedTag *) loc_15805 = 1;

            GibCursor writetag_20531 = loc_15805 + 1;
            GibCursor after_tag_20532 = loc_15805 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15806,
                                                                        end_r_15807,
                                                                        jump_17909,
                                                                        loc_15805,
                                                                        after_tag_20532};
            break;
        }

      case 2:
        {
            GibCursor jump_17911 = arg_7467_10528_13870 + 1;

            *(GibPackedTag *) loc_15805 = 2;

            GibCursor writetag_20539 = loc_15805 + 1;
            GibCursor after_tag_20540 = loc_15805 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15806,
                                                                        end_r_15807,
                                                                        jump_17911,
                                                                        loc_15805,
                                                                        after_tag_20540};
            break;
        }

      case 3:
        {
            GibCursor loc_17116 = loc_15805 + 1;

            *(GibPackedTag *) loc_15805 = 3;

            GibCursor writetag_20553 = loc_15805 + 1;

            gib_shadowstack_push(rstack, loc_15805, end_r_15807, Stk, Exp_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_558 =
                                                               _copy_without_ptrs_Exp(end_r_15806, end_r_15807, loc_17116, tmpcur_24707);
            GibCursor pvrtmp_24722 = tmp_struct_558.field0;
            GibCursor pvrtmp_24723 = tmp_struct_558.field1;
            GibCursor pvrtmp_24724 = tmp_struct_558.field2;
            GibCursor pvrtmp_24725 = tmp_struct_558.field3;
            GibCursor pvrtmp_24726 = tmp_struct_558.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_15805 = frame->ptr;
            end_r_15807 = frame->endptr;
            gib_shadowstack_push(rstack, loc_15805, pvrtmp_24723, Stk, Exp_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_559 =
                                                               _copy_without_ptrs_Exp(pvrtmp_24722, pvrtmp_24723, pvrtmp_24726, pvrtmp_24724);
            GibCursor pvrtmp_24731 = tmp_struct_559.field0;
            GibCursor pvrtmp_24732 = tmp_struct_559.field1;
            GibCursor pvrtmp_24733 = tmp_struct_559.field2;
            GibCursor pvrtmp_24734 = tmp_struct_559.field3;
            GibCursor pvrtmp_24735 = tmp_struct_559.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_15805 = frame->ptr;
            pvrtmp_24723 = frame->endptr;

            GibCursor after_tag_20554 = loc_15805 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_24731,
                                                                        pvrtmp_24732,
                                                                        pvrtmp_24733,
                                                                        loc_15805,
                                                                        pvrtmp_24735};
            break;
        }

      case 4:
        {
            GibCursor loc_17128 = loc_15805 + 1;

            *(GibPackedTag *) loc_15805 = 4;

            GibCursor writetag_20570 = loc_15805 + 1;

            gib_shadowstack_push(rstack, loc_15805, end_r_15807, Stk, Exp_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_560 =
                                                               _copy_without_ptrs_Exp(end_r_15806, end_r_15807, loc_17128, tmpcur_24707);
            GibCursor pvrtmp_24744 = tmp_struct_560.field0;
            GibCursor pvrtmp_24745 = tmp_struct_560.field1;
            GibCursor pvrtmp_24746 = tmp_struct_560.field2;
            GibCursor pvrtmp_24747 = tmp_struct_560.field3;
            GibCursor pvrtmp_24748 = tmp_struct_560.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_15805 = frame->ptr;
            end_r_15807 = frame->endptr;
            gib_shadowstack_push(rstack, loc_15805, pvrtmp_24745, Stk, Exp_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_561 =
                                                               _copy_without_ptrs_Exp(pvrtmp_24744, pvrtmp_24745, pvrtmp_24748, pvrtmp_24746);
            GibCursor pvrtmp_24753 = tmp_struct_561.field0;
            GibCursor pvrtmp_24754 = tmp_struct_561.field1;
            GibCursor pvrtmp_24755 = tmp_struct_561.field2;
            GibCursor pvrtmp_24756 = tmp_struct_561.field3;
            GibCursor pvrtmp_24757 = tmp_struct_561.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_15805 = frame->ptr;
            pvrtmp_24745 = frame->endptr;

            GibCursor after_tag_20571 = loc_15805 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_24753,
                                                                        pvrtmp_24754,
                                                                        pvrtmp_24755,
                                                                        loc_15805,
                                                                        pvrtmp_24757};
            break;
        }

      case 5:
        {
            GibCursor loc_17140 = loc_15805 + 1;

            *(GibPackedTag *) loc_15805 = 5;

            GibCursor writetag_20587 = loc_15805 + 1;

            gib_shadowstack_push(rstack, loc_15805, end_r_15807, Stk, Exp_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_562 =
                                                               _copy_without_ptrs_Exp(end_r_15806, end_r_15807, loc_17140, tmpcur_24707);
            GibCursor pvrtmp_24766 = tmp_struct_562.field0;
            GibCursor pvrtmp_24767 = tmp_struct_562.field1;
            GibCursor pvrtmp_24768 = tmp_struct_562.field2;
            GibCursor pvrtmp_24769 = tmp_struct_562.field3;
            GibCursor pvrtmp_24770 = tmp_struct_562.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_15805 = frame->ptr;
            end_r_15807 = frame->endptr;
            gib_shadowstack_push(rstack, loc_15805, pvrtmp_24767, Stk, Exp_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_563 =
                                                               _copy_without_ptrs_Exp(pvrtmp_24766, pvrtmp_24767, pvrtmp_24770, pvrtmp_24768);
            GibCursor pvrtmp_24775 = tmp_struct_563.field0;
            GibCursor pvrtmp_24776 = tmp_struct_563.field1;
            GibCursor pvrtmp_24777 = tmp_struct_563.field2;
            GibCursor pvrtmp_24778 = tmp_struct_563.field3;
            GibCursor pvrtmp_24779 = tmp_struct_563.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_15805 = frame->ptr;
            pvrtmp_24767 = frame->endptr;

            GibCursor after_tag_20588 = loc_15805 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_24775,
                                                                        pvrtmp_24776,
                                                                        pvrtmp_24777,
                                                                        loc_15805,
                                                                        pvrtmp_24779};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_565 = *(uintptr_t *) tmpcur_24707;
            GibCursor tmpcur_24788 = GIB_UNTAG(tagged_tmpcur_565);
            GibCursor tmpaftercur_24789 = tmpcur_24707 + 8;
            uint16_t tmptag_24790 = GIB_GET_TAG(tagged_tmpcur_565);
            GibCursor end_from_tagged_indr_18186 = tmpcur_24788 + tmptag_24790;
            GibCursor jump_18188 = tmpcur_24707 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_564 =
                                                               _copy_without_ptrs_Exp(end_from_tagged_indr_18186, end_r_15807, loc_15805, tmpcur_24788);
            GibCursor pvrtmp_24791 = tmp_struct_564.field0;
            GibCursor pvrtmp_24792 = tmp_struct_564.field1;
            GibCursor pvrtmp_24793 = tmp_struct_564.field2;
            GibCursor pvrtmp_24794 = tmp_struct_564.field3;
            GibCursor pvrtmp_24795 = tmp_struct_564.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_15806,
                                                                        pvrtmp_24792,
                                                                        jump_18188,
                                                                        pvrtmp_24794,
                                                                        pvrtmp_24795};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_567 = *(uintptr_t *) tmpcur_24707;
            GibCursor tmpcur_24802 = GIB_UNTAG(tagged_tmpcur_567);
            GibCursor tmpaftercur_24803 = tmpcur_24707 + 8;
            uint16_t tmptag_24804 = GIB_GET_TAG(tagged_tmpcur_567);
            GibCursor end_from_tagged_indr_18186 = tmpcur_24802 + tmptag_24804;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_566 =
                                                               _copy_without_ptrs_Exp(end_from_tagged_indr_18186, end_r_15807, loc_15805, tmpcur_24802);
            GibCursor pvrtmp_24805 = tmp_struct_566.field0;
            GibCursor pvrtmp_24806 = tmp_struct_566.field1;
            GibCursor pvrtmp_24807 = tmp_struct_566.field2;
            GibCursor pvrtmp_24808 = tmp_struct_566.field3;
            GibCursor pvrtmp_24809 = tmp_struct_566.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_24805,
                                                                        pvrtmp_24806,
                                                                        pvrtmp_24807,
                                                                        pvrtmp_24808,
                                                                        pvrtmp_24809};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_24706");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_Exp(GibCursor end_r_15809,
                                     GibCursor arg_7482_10543_13885)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_24817 = *(GibPackedTag *) arg_7482_10543_13885;
    GibCursor tmpcur_24818 = arg_7482_10543_13885 + 1;


  switch_24843:
    ;
    switch (tmpval_24817) {

      case 0:
        {
            GibInt tmpval_24819 = *(GibInt *) tmpcur_24818;
            GibCursor tmpcur_24820 = tmpcur_24818 + sizeof(GibInt);
            GibCursor jump_17922 = tmpcur_24818 + 8;

            return (GibCursorGibCursorProd) {end_r_15809, jump_17922};
            break;
        }

      case 1:
        {
            GibCursor jump_17924 = arg_7482_10543_13885 + 1;

            return (GibCursorGibCursorProd) {end_r_15809, jump_17924};
            break;
        }

      case 2:
        {
            GibCursor jump_17926 = arg_7482_10543_13885 + 1;

            return (GibCursorGibCursorProd) {end_r_15809, jump_17926};
            break;
        }

      case 3:
        {
            GibCursorGibCursorProd tmp_struct_568 =
                                    _traverse_Exp(end_r_15809, tmpcur_24818);
            GibCursor pvrtmp_24821 = tmp_struct_568.field0;
            GibCursor pvrtmp_24822 = tmp_struct_568.field1;
            GibCursorGibCursorProd tmp_struct_569 =
                                    _traverse_Exp(pvrtmp_24821, pvrtmp_24822);
            GibCursor pvrtmp_24823 = tmp_struct_569.field0;
            GibCursor pvrtmp_24824 = tmp_struct_569.field1;

            return (GibCursorGibCursorProd) {pvrtmp_24823, pvrtmp_24824};
            break;
        }

      case 4:
        {
            GibCursorGibCursorProd tmp_struct_570 =
                                    _traverse_Exp(end_r_15809, tmpcur_24818);
            GibCursor pvrtmp_24825 = tmp_struct_570.field0;
            GibCursor pvrtmp_24826 = tmp_struct_570.field1;
            GibCursorGibCursorProd tmp_struct_571 =
                                    _traverse_Exp(pvrtmp_24825, pvrtmp_24826);
            GibCursor pvrtmp_24827 = tmp_struct_571.field0;
            GibCursor pvrtmp_24828 = tmp_struct_571.field1;

            return (GibCursorGibCursorProd) {pvrtmp_24827, pvrtmp_24828};
            break;
        }

      case 5:
        {
            GibCursorGibCursorProd tmp_struct_572 =
                                    _traverse_Exp(end_r_15809, tmpcur_24818);
            GibCursor pvrtmp_24829 = tmp_struct_572.field0;
            GibCursor pvrtmp_24830 = tmp_struct_572.field1;
            GibCursorGibCursorProd tmp_struct_573 =
                                    _traverse_Exp(pvrtmp_24829, pvrtmp_24830);
            GibCursor pvrtmp_24831 = tmp_struct_573.field0;
            GibCursor pvrtmp_24832 = tmp_struct_573.field1;

            return (GibCursorGibCursorProd) {pvrtmp_24831, pvrtmp_24832};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_575 = *(uintptr_t *) tmpcur_24818;
            GibCursor tmpcur_24833 = GIB_UNTAG(tagged_tmpcur_575);
            GibCursor tmpaftercur_24834 = tmpcur_24818 + 8;
            uint16_t tmptag_24835 = GIB_GET_TAG(tagged_tmpcur_575);
            GibCursor end_from_tagged_indr_18192 = tmpcur_24833 + tmptag_24835;
            GibCursor jump_18194 = tmpcur_24818 + 8;
            GibCursorGibCursorProd tmp_struct_574 =
                                    _traverse_Exp(end_from_tagged_indr_18192, tmpcur_24833);
            GibCursor pvrtmp_24836 = tmp_struct_574.field0;
            GibCursor pvrtmp_24837 = tmp_struct_574.field1;

            return (GibCursorGibCursorProd) {end_r_15809, jump_18194};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_577 = *(uintptr_t *) tmpcur_24818;
            GibCursor tmpcur_24838 = GIB_UNTAG(tagged_tmpcur_577);
            GibCursor tmpaftercur_24839 = tmpcur_24818 + 8;
            uint16_t tmptag_24840 = GIB_GET_TAG(tagged_tmpcur_577);
            GibCursor end_from_tagged_indr_18192 = tmpcur_24838 + tmptag_24840;
            GibCursorGibCursorProd tmp_struct_576 =
                                    _traverse_Exp(end_from_tagged_indr_18192, tmpcur_24838);
            GibCursor pvrtmp_24841 = tmp_struct_576.field0;
            GibCursor pvrtmp_24842 = tmp_struct_576.field1;

            return (GibCursorGibCursorProd) {pvrtmp_24841, pvrtmp_24842};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_24817");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_Exp(GibCursor end_r_15811,
                                  GibCursor arg_7497_10557_13899)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_24844 = *(GibPackedTag *) arg_7497_10557_13899;
    GibCursor tmpcur_24845 = arg_7497_10557_13899 + 1;


  switch_24870:
    ;
    switch (tmpval_24844) {

      case 0:
        {
            GibInt tmpval_24846 = *(GibInt *) tmpcur_24845;
            GibCursor tmpcur_24847 = tmpcur_24845 + sizeof(GibInt);
            GibCursor jump_17937 = tmpcur_24845 + 8;
            unsigned char wildcard_7500_10559_13901 = gib_print_symbol(21863);
            unsigned char y_7499_10560_13902 = printf("%ld", tmpval_24846);
            unsigned char wildcard_7501_10561_13903 = gib_print_symbol(21857);

            return (GibCursorGibCursorProd) {end_r_15811, jump_17937};
            break;
        }

      case 1:
        {
            GibCursor jump_17939 = arg_7497_10557_13899 + 1;
            unsigned char wildcard_7502_10562_13904 = gib_print_symbol(21861);
            unsigned char wildcard_7503_10563_13905 = gib_print_symbol(21857);

            return (GibCursorGibCursorProd) {end_r_15811, jump_17939};
            break;
        }

      case 2:
        {
            GibCursor jump_17941 = arg_7497_10557_13899 + 1;
            unsigned char wildcard_7504_10564_13906 = gib_print_symbol(21862);
            unsigned char wildcard_7505_10565_13907 = gib_print_symbol(21857);

            return (GibCursorGibCursorProd) {end_r_15811, jump_17941};
            break;
        }

      case 3:
        {
            unsigned char wildcard_7510_10568_13910 = gib_print_symbol(21858);
            GibCursorGibCursorProd tmp_struct_578 =
                                    _print_Exp(end_r_15811, tmpcur_24845);
            GibCursor pvrtmp_24848 = tmp_struct_578.field0;
            GibCursor pvrtmp_24849 = tmp_struct_578.field1;
            GibCursorGibCursorProd tmp_struct_579 =
                                    _print_Exp(pvrtmp_24848, pvrtmp_24849);
            GibCursor pvrtmp_24850 = tmp_struct_579.field0;
            GibCursor pvrtmp_24851 = tmp_struct_579.field1;
            unsigned char wildcard_7511_10571_13913 = gib_print_symbol(21857);

            return (GibCursorGibCursorProd) {pvrtmp_24850, pvrtmp_24851};
            break;
        }

      case 4:
        {
            unsigned char wildcard_7516_10574_13916 = gib_print_symbol(21872);
            GibCursorGibCursorProd tmp_struct_580 =
                                    _print_Exp(end_r_15811, tmpcur_24845);
            GibCursor pvrtmp_24852 = tmp_struct_580.field0;
            GibCursor pvrtmp_24853 = tmp_struct_580.field1;
            GibCursorGibCursorProd tmp_struct_581 =
                                    _print_Exp(pvrtmp_24852, pvrtmp_24853);
            GibCursor pvrtmp_24854 = tmp_struct_581.field0;
            GibCursor pvrtmp_24855 = tmp_struct_581.field1;
            unsigned char wildcard_7517_10577_13919 = gib_print_symbol(21857);

            return (GibCursorGibCursorProd) {pvrtmp_24854, pvrtmp_24855};
            break;
        }

      case 5:
        {
            unsigned char wildcard_7522_10580_13922 = gib_print_symbol(21859);
            GibCursorGibCursorProd tmp_struct_582 =
                                    _print_Exp(end_r_15811, tmpcur_24845);
            GibCursor pvrtmp_24856 = tmp_struct_582.field0;
            GibCursor pvrtmp_24857 = tmp_struct_582.field1;
            GibCursorGibCursorProd tmp_struct_583 =
                                    _print_Exp(pvrtmp_24856, pvrtmp_24857);
            GibCursor pvrtmp_24858 = tmp_struct_583.field0;
            GibCursor pvrtmp_24859 = tmp_struct_583.field1;
            unsigned char wildcard_7523_10583_13925 = gib_print_symbol(21857);

            return (GibCursorGibCursorProd) {pvrtmp_24858, pvrtmp_24859};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_585 = *(uintptr_t *) tmpcur_24845;
            GibCursor tmpcur_24860 = GIB_UNTAG(tagged_tmpcur_585);
            GibCursor tmpaftercur_24861 = tmpcur_24845 + 8;
            uint16_t tmptag_24862 = GIB_GET_TAG(tagged_tmpcur_585);
            GibCursor end_from_tagged_indr_18198 = tmpcur_24860 + tmptag_24862;
            GibCursor jump_18200 = tmpcur_24845 + 8;
            unsigned char wildcard_18203 = gib_print_symbol(21876);
            GibCursorGibCursorProd tmp_struct_584 =
                                    _print_Exp(end_from_tagged_indr_18198, tmpcur_24860);
            GibCursor pvrtmp_24863 = tmp_struct_584.field0;
            GibCursor pvrtmp_24864 = tmp_struct_584.field1;

            return (GibCursorGibCursorProd) {end_r_15811, jump_18200};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_587 = *(uintptr_t *) tmpcur_24845;
            GibCursor tmpcur_24865 = GIB_UNTAG(tagged_tmpcur_587);
            GibCursor tmpaftercur_24866 = tmpcur_24845 + 8;
            uint16_t tmptag_24867 = GIB_GET_TAG(tagged_tmpcur_587);
            GibCursor end_from_tagged_indr_18198 = tmpcur_24865 + tmptag_24867;
            unsigned char wildcard_18203 = gib_print_symbol(21875);
            GibCursorGibCursorProd tmp_struct_586 =
                                    _print_Exp(end_from_tagged_indr_18198, tmpcur_24865);
            GibCursor pvrtmp_24868 = tmp_struct_586.field0;
            GibCursor pvrtmp_24869 = tmp_struct_586.field1;

            return (GibCursorGibCursorProd) {pvrtmp_24868, pvrtmp_24869};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_24844");
            exit(1);
        }
    }
}
int gib_main_expr(void)
{
    info_table_initialize();
    symbol_table_initialize();

    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_11782_12135 = strcmp("seqfib", gib_read_bench_prog_param()) ==
            0;

    if (fltIf_11782_12135) {
        unsigned char tailapp_17952 =  bench_seqfib();

        printf("'#()");
        printf("\n");
        return 0;
    } else {
        GibBool fltIf_11783_12136 = strcmp("seqbuildfib",
                                           gib_read_bench_prog_param()) == 0;

        if (fltIf_11783_12136) {
            unsigned char tailapp_17953 =  bench_seqbuildfib();

            printf("'#()");
            printf("\n");
            return 0;
        } else {
            GibBool fltIf_11784_12137 = strcmp("seqbuildtree",
                                               gib_read_bench_prog_param()) ==
                    0;

            if (fltIf_11784_12137) {
                unsigned char tailapp_17954 =  bench_seqbuildtree();

                printf("'#()");
                printf("\n");
                return 0;
            } else {
                GibBool fltIf_11785_12138 = strcmp("seqadd1tree",
                                                   gib_read_bench_prog_param()) ==
                        0;

                if (fltIf_11785_12138) {
                    unsigned char tailapp_17955 =  bench_seqadd1tree();

                    printf("'#()");
                    printf("\n");
                    return 0;
                } else {
                    GibBool fltIf_11786_12139 = strcmp("seqsumtree",
                                                       gib_read_bench_prog_param()) ==
                            0;

                    if (fltIf_11786_12139) {
                        unsigned char tailapp_17956 =  bench_seqsumtree();

                        printf("'#()");
                        printf("\n");
                        return 0;
                    } else {
                        GibBool fltIf_11787_12140 = strcmp("seqbuildkdtree",
                                                           gib_read_bench_prog_param()) ==
                                0;

                        if (fltIf_11787_12140) {
                            unsigned char tailapp_17957 =
                                           bench_seqbuildkdtree();

                            printf("'#()");
                            printf("\n");
                            return 0;
                        } else {
                            GibBool fltIf_11788_12141 = strcmp("seqcountcorr",
                                                               gib_read_bench_prog_param()) ==
                                    0;

                            if (fltIf_11788_12141) {
                                unsigned char tailapp_17958 =
                                               bench_seqcountcorr();

                                printf("'#()");
                                printf("\n");
                                return 0;
                            } else {
                                GibBool fltIf_11789_12142 = strcmp("seqnearest",
                                                                   gib_read_bench_prog_param()) ==
                                        0;

                                if (fltIf_11789_12142) {
                                    unsigned char tailapp_17959 =
                                                   bench_seqnearest();

                                    printf("'#()");
                                    printf("\n");
                                    return 0;
                                } else {
                                    GibBool fltIf_11790_12143 =
                                            strcmp("seqbuildquadtree",
                                                   gib_read_bench_prog_param()) ==
                                            0;

                                    if (fltIf_11790_12143) {
                                        unsigned char tailapp_17960 =
                                                       bench_seqbuildquadtree();

                                        printf("'#()");
                                        printf("\n");
                                        return 0;
                                    } else {
                                        GibBool fltIf_11791_12144 =
                                                strcmp("seqbhut",
                                                       gib_read_bench_prog_param()) ==
                                                0;

                                        if (fltIf_11791_12144) {
                                            unsigned char tailapp_17961 =
                                                           bench_seqbhut();

                                            printf("'#()");
                                            printf("\n");
                                            return 0;
                                        } else {
                                            GibBool fltIf_11792_12145 =
                                                    strcmp("seqcoins",
                                                           gib_read_bench_prog_param()) ==
                                                    0;

                                            if (fltIf_11792_12145) {
                                                unsigned char tailapp_17962 =
                                                               bench_seqcoins();

                                                printf("'#()");
                                                printf("\n");
                                                return 0;
                                            } else {
                                                GibBool fltIf_11793_12146 =
                                                        strcmp("seqfoldconstants",
                                                               gib_read_bench_prog_param()) ==
                                                        0;

                                                if (fltIf_11793_12146) {
                                                    unsigned char tailapp_17963
                                                                  =
                                                                   bench_seqfoldconstants();

                                                    printf("'#()");
                                                    printf("\n");
                                                    return 0;
                                                } else {
                                                    unsigned char tailprim_17964
                                                                  =
                                                                  gib_print_symbol(21850);

                                                    printf("'#()");
                                                    printf("\n");
                                                    return 0;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}
