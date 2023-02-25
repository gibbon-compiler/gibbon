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
typedef struct GibIntGibIntGibIntProd_struct {
            GibInt field0;
            GibInt field1;
            GibInt field2;
        } GibIntGibIntGibIntProd;
typedef struct GibIntGibIntGibIntGibIntGibIntGibIntProd_struct {
            GibInt field0;
            GibInt field1;
            GibInt field2;
            GibInt field3;
            GibInt field4;
            GibInt field5;
        } GibIntGibIntGibIntGibIntGibIntGibIntProd;
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
typedef struct GibCursorGibCursorGibBoolProd_struct {
            GibCursor field0;
            GibCursor field1;
            GibBool field2;
        } GibCursorGibCursorGibBoolProd;
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
typedef struct GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd_struct {
            GibCursor field0;
            GibCursor field1;
            GibCursor field2;
            GibCursor field3;
            GibCursor field4;
            GibCursor field5;
        } GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd;
typedef struct GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd_struct {
            GibCursor field0;
            GibCursor field1;
            GibCursor field2;
            GibCursor field3;
            GibCursor field4;
            GibCursor field5;
            GibCursor field6;
        } GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd;
GibIntGibIntGibIntProd very_small_opts_answer();
GibIntGibIntGibIntProd small_opts_answer();
GibIntGibIntGibIntProd fast_opts_answer();
GibIntGibIntGibIntProd norm_opts_answer();
GibIntGibIntGibIntProd slow_opts_answer();
GibIntGibIntGibIntGibIntGibIntGibIntProd very_small_opts();
GibIntGibIntGibIntGibIntGibIntGibIntProd small_opts();
GibIntGibIntGibIntGibIntGibIntGibIntProd fast_opts();
GibIntGibIntGibIntGibIntGibIntGibIntProd norm_opts();
GibIntGibIntGibIntGibIntGibIntGibIntProd slow_opts();
GibBool bench_lcss(GibIntGibIntGibIntGibIntGibIntGibIntProd opts_104_1242_1564,
                   GibIntGibIntGibIntProd answer_105_1243_1565);
GibCursorGibCursorGibBoolProd check_lcss(GibCursor end_r_2446,
                                         GibInt start_120_1258_1582,
                                         GibInt step_121_1259_1583,
                                         GibInt end_122_1260_1584,
                                         GibCursor list2_123_1261_1585);
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
lcss(GibCursor end_r_2450, GibCursor end_r_2451, GibCursor end_r_2452,
     GibCursor loc_2449, GibCursor xs_126_1264_1591,
     GibCursor ys_127_1265_1592);
GibCursorGibCursorGibCursorProd mkList(GibCursor end_r_2454, GibCursor loc_2453,
                                       GibInt start_128_1266_1596,
                                       GibInt end_129_1267_1597,
                                       GibInt skipFactor_130_1268_1598);
GibCursorGibCursorGibIntProd findk(GibCursor end_r_2456, GibInt k_132_1270_1602,
                                   GibInt km_133_1271_1603,
                                   GibInt m_134_1272_1604,
                                   GibCursor ls_135_1273_1605);
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
algc(GibCursor end_r_2461, GibCursor end_r_2462, GibCursor end_r_2463,
     GibCursor end_r_2464, GibCursor loc_2460, GibInt m_141_1280_1617,
     GibInt n_142_1281_1618, GibCursor xs_143_1282_1619,
     GibCursor ys_144_1283_1620, GibCursor zs_145_1284_1621);
GibCursorGibCursorGibCursorGibCursorGibCursorProd algb2(GibCursor end_r_2467,
                                                        GibCursor end_r_2468,
                                                        GibCursor loc_2466,
                                                        GibInt x_161_1285_1623,
                                                        GibInt k0j1_162_1286_1624,
                                                        GibInt k1j1_163_1287_1625,
                                                        GibCursor ls_164_1288_1626);
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
algb1(GibCursor end_r_2472, GibCursor end_r_2473, GibCursor end_r_2474,
      GibCursor loc_2471, GibCursor xs_171_1296_1636,
      GibCursor ys_172_1297_1637);
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
algb(GibCursor end_r_2478, GibCursor end_r_2479, GibCursor end_r_2480,
     GibCursor loc_2477, GibCursor xs_178_1300_1641,
     GibCursor ys_179_1301_1642);
GibCursorGibCursorGibCursorGibCursorGibCursorProd zip0(GibCursor end_r_2483,
                                                       GibCursor end_r_2484,
                                                       GibCursor loc_2482,
                                                       GibCursor ls_180_1302_1645);
GibInt maxInt(GibInt a_189_1305_1649, GibInt b_190_1306_1650);
GibCursorGibCursorGibIntProd length_plist_779(GibCursor end_r_2486,
                                              GibCursor a_226_1325_1652);
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
reverse_plist_785(GibCursor end_r_2490, GibCursor end_r_2491,
                  GibCursor end_r_2492, GibCursor loc_2489,
                  GibCursor xs_221_1328_1656, GibCursor acc_222_1329_1657);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
zip_plist_786(GibCursor end_r_2496, GibCursor end_r_2497, GibCursor end_r_2498,
              GibCursor loc_2495, GibCursor as_213_1332_1661,
              GibCursor bs_214_1333_1662);
GibCursorGibCursorGibCursorGibCursorProd drop_plist_784(GibCursor end_r_2501,
                                                        GibCursor end_r_2502,
                                                        GibCursor loc_2500,
                                                        GibInt num_208_1336_1665,
                                                        GibCursor list_209_1337_1666);
GibCursorGibCursorGibCursorGibCursorProd take_plist_783(GibCursor end_r_2505,
                                                        GibCursor end_r_2506,
                                                        GibCursor loc_2504,
                                                        GibInt n_203_1340_1671,
                                                        GibCursor a_204_1341_1672);
GibCursorGibBoolProd is_empty_plist_781(GibCursor end_r_2508,
                                        GibCursor ls_191_1342_1674);
GibCursorGibBoolProd elem_plist_782_1069(GibCursor end_r_2510,
                                         GibInt a_196_1348_1677,
                                         GibCursor list_197_1349_1678);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
map_plist_787_1071(GibCursor end_r_2513, GibCursor end_r_2514,
                   GibCursor loc_2512, GibCursor ls_184_1352_1687);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_PList_v_778(GibCursor end_r_2517, GibCursor end_r_2518,
                  GibCursor loc_2516, GibCursor arg_1136_1356_1696);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_PList_v_778(GibCursor end_r_2521, GibCursor end_r_2522,
                               GibCursor loc_2520,
                               GibCursor arg_1141_1361_1701);
GibCursorGibCursorProd _traverse_PList_v_778(GibCursor end_r_2524,
                                             GibCursor arg_1146_1366_1706);
GibCursorGibCursorProd _print_PList_v_778(GibCursor end_r_2526,
                                          GibCursor arg_1151_1370_1710);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_PList_v_780(GibCursor end_r_2529, GibCursor end_r_2530,
                  GibCursor loc_2528, GibCursor arg_1164_1385_1725);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_PList_v_780(GibCursor end_r_2533, GibCursor end_r_2534,
                               GibCursor loc_2532,
                               GibCursor arg_1171_1392_1732);
GibCursorGibCursorProd _traverse_PList_v_780(GibCursor end_r_2536,
                                             GibCursor arg_1178_1399_1739);
GibCursorGibCursorProd _print_PList_v_780(GibCursor end_r_2538,
                                          GibCursor arg_1185_1404_1744);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_Maybe_v_788(GibCursor end_r_2541, GibCursor end_r_2542,
                  GibCursor loc_2540, GibCursor arg_1202_1424_1764);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_Maybe_v_788(GibCursor end_r_2545, GibCursor end_r_2546,
                               GibCursor loc_2544,
                               GibCursor arg_1205_1427_1767);
GibCursorGibCursorProd _traverse_Maybe_v_788(GibCursor end_r_2548,
                                             GibCursor arg_1208_1430_1770);
GibCursorGibCursorProd _print_Maybe_v_788(GibCursor end_r_2550,
                                          GibCursor arg_1211_1432_1772);
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
caseFn_1220(GibCursor end_r_2556, GibCursor end_r_2557, GibCursor end_r_2558,
            GibCursor end_r_2559, GibCursor end_r_2560, GibCursor loc_2555,
            GibInt m_141_1221_1442_1782, GibInt n_142_1222_1443_1783,
            GibCursor xs_143_1223_1444_1784, GibCursor ys_144_1224_1445_1785,
            GibCursor zs_145_1225_1446_1786, GibCursor xs__147_1226_1447_1787,
            GibInt x_146_1227_1448_1788);
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
caseFn_1228(GibCursor end_r_2565, GibCursor end_r_2566, GibCursor end_r_2567,
            GibCursor end_r_2568, GibCursor loc_2564,
            GibInt m_141_1229_1462_1813, GibInt n_142_1230_1463_1814,
            GibCursor xs_143_1231_1464_1815, GibCursor ys_144_1232_1465_1816,
            GibCursor zs_145_1233_1466_1817);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
caseFn_1234(GibCursor end_r_2572, GibCursor end_r_2573, GibCursor end_r_2574,
            GibCursor loc_2571, GibCursor bs_214_1235_1469_1820,
            GibInt z_217_1236_1470_1821, GibCursor zs_218_1237_1471_1822);
GibCursorGibCursorGibCursorGibCursorProd caseFn_1238(GibCursor end_r_2577,
                                                     GibCursor end_r_2578,
                                                     GibCursor loc_2576,
                                                     GibInt n_203_1239_1474_1826,
                                                     GibCursor a_204_1240_1475_1827);
typedef enum {
            GibInt_T,
            GibFloat_T,
            GibSym_T,
            GibBool_T,
            GibVector_T,
            GibList_T,
            GibCursor_T,
            Maybe_v_788_T,
            PList_v_778_T,
            PList_v_780_T,
        } GibDatatype;
void info_table_initialize(void)
{
    int error = gib_info_table_initialize(10);

    if (error < 0) {
        fprintf(stderr, "Couldn't initialize info table, errorno=%d", error);
        exit(1);
    }

    GibDatatype field_tys[3];

    error = gib_info_table_insert_packed_dcon(Maybe_v_788_T, 0, 8, 0, 1, 0,
                                              field_tys, 0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, Maybe_v_788_T, 0);
        exit(1);
    }
    error = gib_info_table_insert_packed_dcon(Maybe_v_788_T, 1, 0, 0, 0, 0,
                                              field_tys, 0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, Maybe_v_788_T, 1);
        exit(1);
    }
    field_tys[0] = PList_v_778_T;
    error = gib_info_table_insert_packed_dcon(PList_v_778_T, 1, 8, 0, 1, 1,
                                              field_tys, 1);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, PList_v_778_T, 1);
        exit(1);
    }
    error = gib_info_table_insert_packed_dcon(PList_v_778_T, 0, 0, 0, 0, 0,
                                              field_tys, 0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, PList_v_778_T, 0);
        exit(1);
    }
    field_tys[0] = PList_v_780_T;
    error = gib_info_table_insert_packed_dcon(PList_v_780_T, 1, 16, 0, 2, 1,
                                              field_tys, 1);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, PList_v_780_T, 1);
        exit(1);
    }
    error = gib_info_table_insert_packed_dcon(PList_v_780_T, 0, 0, 0, 0, 0,
                                              field_tys, 0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, PList_v_780_T, 0);
        exit(1);
    }
    gib_info_table_finalize();
}
void symbol_table_initialize(void)
{
    gib_add_symbol(5734, ")");
    gib_add_symbol(5735, "(Nothing_v_788");
    gib_add_symbol(5736, "(Nil_v_780");
    gib_add_symbol(5737, "(Nil_v_778");
    gib_add_symbol(5738, "(Just_v_788");
    gib_add_symbol(5739, "(Cons_v_780");
    gib_add_symbol(5740, "(Cons_v_778");
    gib_add_symbol(5741, " ->r ");
    gib_add_symbol(5742, " ->i ");
    gib_add_symbol(5743, " ");
}
GibIntGibIntGibIntProd very_small_opts_answer()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    return (GibIntGibIntGibIntProd) {1300, 1, 2000};
}
GibIntGibIntGibIntProd small_opts_answer()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    return (GibIntGibIntGibIntProd) {1000, 1, 2000};
}
GibIntGibIntGibIntProd fast_opts_answer()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    return (GibIntGibIntGibIntProd) {1000, 1, 2000};
}
GibIntGibIntGibIntProd norm_opts_answer()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    return (GibIntGibIntGibIntProd) {1000, 1, 3100};
}
GibIntGibIntGibIntProd slow_opts_answer()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    return (GibIntGibIntGibIntProd) {100, 1, 3500};
}
GibIntGibIntGibIntGibIntGibIntGibIntProd very_small_opts()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    return (GibIntGibIntGibIntGibIntGibIntGibIntProd) {1, 2, 2000, 1300, 1301,
                                                       2000};
}
GibIntGibIntGibIntGibIntGibIntGibIntProd small_opts()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    return (GibIntGibIntGibIntGibIntGibIntGibIntProd) {1, 2, 2000, 1000, 1001,
                                                       2000};
}
GibIntGibIntGibIntGibIntGibIntGibIntProd fast_opts()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    return (GibIntGibIntGibIntGibIntGibIntGibIntProd) {1, 2, 2000, 1000, 1001,
                                                       3000};
}
GibIntGibIntGibIntGibIntGibIntGibIntProd norm_opts()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    return (GibIntGibIntGibIntGibIntGibIntGibIntProd) {1, 2, 3100, 1000, 1001,
                                                       4000};
}
GibIntGibIntGibIntGibIntGibIntGibIntProd slow_opts()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    return (GibIntGibIntGibIntGibIntGibIntGibIntProd) {1, 2, 4000, 100, 101,
                                                       3500};
}
GibBool bench_lcss(GibIntGibIntGibIntGibIntGibIntGibIntProd opts_104_1242_1564,
                   GibIntGibIntGibIntProd answer_105_1243_1565)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibInt fltAppE_1499_1573 = opts_104_1242_1564.field1 -
           opts_104_1242_1564.field0;
    GibChunk region_5879 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_2595 = region_5879.start;
    GibCursor end_r_2595 = region_5879.end;
    GibCursorGibCursorGibCursorProd tmp_struct_0 =
                                     mkList(end_r_2595, r_2595, opts_104_1242_1564.field0, opts_104_1242_1564.field2, fltAppE_1499_1573);
    GibCursor pvrtmp_5880 = tmp_struct_0.field0;
    GibCursor pvrtmp_5881 = tmp_struct_0.field1;
    GibCursor pvrtmp_5882 = tmp_struct_0.field2;
    GibInt fltAppE_1500_1575 = opts_104_1242_1564.field4 -
           opts_104_1242_1564.field3;

    gib_shadowstack_push(rstack, pvrtmp_5881, pvrtmp_5880, Stk, PList_v_778_T);

    GibChunk region_5887 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_2594 = region_5887.start;
    GibCursor end_r_2594 = region_5887.end;

    frame = gib_shadowstack_pop(rstack);
    pvrtmp_5881 = frame->ptr;
    pvrtmp_5880 = frame->endptr;

    GibCursorGibCursorGibCursorProd tmp_struct_1 =
                                     mkList(end_r_2594, r_2594, opts_104_1242_1564.field3, opts_104_1242_1564.field5, fltAppE_1500_1575);
    GibCursor pvrtmp_5888 = tmp_struct_1.field0;
    GibCursor pvrtmp_5889 = tmp_struct_1.field1;
    GibCursor pvrtmp_5890 = tmp_struct_1.field2;

    gib_shadowstack_push(rstack, pvrtmp_5881, pvrtmp_5880, Stk, PList_v_778_T);
    gib_shadowstack_push(rstack, pvrtmp_5889, pvrtmp_5888, Stk, PList_v_778_T);

    GibChunk region_5895 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_2593 = region_5895.start;
    GibCursor end_r_2593 = region_5895.end;

    frame = gib_shadowstack_pop(rstack);
    pvrtmp_5889 = frame->ptr;
    pvrtmp_5888 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_5881 = frame->ptr;
    pvrtmp_5880 = frame->endptr;

    GibCursor pvrtmp_5909;
    GibCursor pvrtmp_5910;
    GibCursor pvrtmp_5911;
    GibVector *times_6 = gib_vector_alloc(gib_get_iters_param(),
                                          sizeof(double));
    struct timespec begin_pvrtmp_5909;
    struct timespec end_pvrtmp_5909;

    GibGcStateSnapshot *snapshot = gib_gc_init_state(3);

    for (long long iters_pvrtmp_5909 = 0; iters_pvrtmp_5909 <
         gib_get_iters_param(); iters_pvrtmp_5909++) {
        if (iters_pvrtmp_5909 != gib_get_iters_param() - 1) {
            gib_gc_save_state(snapshot, 3, region_5895.end, region_5887.end, region_5879.end);
            gib_list_bumpalloc_save_state();
            gib_ptr_bumpalloc_save_state();
        }
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_5909);

        GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
        tmp_struct_2 =
         lcss(pvrtmp_5880, pvrtmp_5888, end_r_2593, r_2593, pvrtmp_5881, pvrtmp_5889);
        GibCursor pvrtmp_5896 = tmp_struct_2.field0;
        GibCursor pvrtmp_5897 = tmp_struct_2.field1;
        GibCursor pvrtmp_5898 = tmp_struct_2.field2;
        GibCursor pvrtmp_5899 = tmp_struct_2.field3;
        GibCursor pvrtmp_5900 = tmp_struct_2.field4;
        GibCursor pvrtmp_5901 = tmp_struct_2.field5;
        GibCursor pvrtmp_5902 = tmp_struct_2.field6;

        pvrtmp_5909 = pvrtmp_5898;
        pvrtmp_5910 = pvrtmp_5901;
        pvrtmp_5911 = pvrtmp_5902;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_5909);
        if (iters_pvrtmp_5909 != gib_get_iters_param() - 1) {
            gib_gc_restore_state(snapshot);
            gib_list_bumpalloc_restore_state();
            gib_ptr_bumpalloc_restore_state();
        }

        double itertime_3 = gib_difftimespecs(&begin_pvrtmp_5909,
                                              &end_pvrtmp_5909);

        printf("itertime: %lf\n", itertime_3);
        gib_vector_inplace_update(times_6, iters_pvrtmp_5909, &itertime_3);
    }
    gib_vector_inplace_sort(times_6, gib_compare_doubles);

    double *tmp_7 = (double *) gib_vector_nth(times_6, gib_get_iters_param() /
                                              2);
    double selftimed_5 = *tmp_7;
    double batchtime_4 = gib_sum_timing_array(times_6);

    gib_print_timing_array(times_6);
    gib_vector_free(times_6);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_4);
    printf("SELFTIMED: %e\n", selftimed_5);

    GibCursorGibCursorGibBoolProd tmp_struct_8 =
                                   check_lcss(end_r_2593, answer_105_1243_1565.field0, answer_105_1243_1565.field1, answer_105_1243_1565.field2, pvrtmp_5910);
    GibCursor pvrtmp_5919 = tmp_struct_8.field0;
    GibCursor pvrtmp_5920 = tmp_struct_8.field1;
    GibBool pvrtmp_5921 = tmp_struct_8.field2;

    return pvrtmp_5921;
}
GibCursorGibCursorGibBoolProd check_lcss(GibCursor end_r_2446,
                                         GibInt start_120_1258_1582,
                                         GibInt step_121_1259_1583,
                                         GibInt end_122_1260_1584,
                                         GibCursor list2_123_1261_1585)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_5922 = *(GibPackedTag *) list2_123_1261_1585;
    GibCursor tmpcur_5923 = list2_123_1261_1585 + 1;


  switch_5941:
    ;
    switch (tmpval_5922) {

      case 0:
        {
            GibCursor jump_3097 = list2_123_1261_1585 + 1;
            GibBool tailprim_3098 = start_120_1258_1582 > end_122_1260_1584;

            return (GibCursorGibCursorGibBoolProd) {end_r_2446, jump_3097,
                                                    tailprim_3098};
            break;
        }

      case 1:
        {
            GibInt tmpval_5924 = *(GibInt *) tmpcur_5923;
            GibCursor tmpcur_5925 = tmpcur_5923 + sizeof(GibInt);
            GibBool fltPrm_1501_1588 = tmpval_5924 == start_120_1258_1582;
            GibInt fltAppE_1503_1589 = start_120_1258_1582 + step_121_1259_1583;
            GibCursorGibCursorGibBoolProd tmp_struct_9 =
                                           check_lcss(end_r_2446, fltAppE_1503_1589, step_121_1259_1583, end_122_1260_1584, tmpcur_5925);
            GibCursor pvrtmp_5926 = tmp_struct_9.field0;
            GibCursor pvrtmp_5927 = tmp_struct_9.field1;
            GibBool pvrtmp_5928 = tmp_struct_9.field2;
            GibBool tailprim_3101 = fltPrm_1501_1588 && pvrtmp_5928;

            return (GibCursorGibCursorGibBoolProd) {pvrtmp_5926, pvrtmp_5927,
                                                    tailprim_3101};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_11 = *(uintptr_t *) tmpcur_5923;
            GibCursor tmpcur_5929 = GIB_UNTAG(tagged_tmpcur_11);
            GibCursor tmpaftercur_5930 = tmpcur_5923 + 8;
            uint16_t tmptag_5931 = GIB_GET_TAG(tagged_tmpcur_11);
            GibCursor end_from_tagged_indr_3264 = tmpcur_5929 + tmptag_5931;
            GibCursor jump_3266 = tmpcur_5923 + 8;
            GibCursorGibCursorGibBoolProd tmp_struct_10 =
                                           check_lcss(end_from_tagged_indr_3264, start_120_1258_1582, step_121_1259_1583, end_122_1260_1584, tmpcur_5929);
            GibCursor pvrtmp_5932 = tmp_struct_10.field0;
            GibCursor pvrtmp_5933 = tmp_struct_10.field1;
            GibBool pvrtmp_5934 = tmp_struct_10.field2;

            return (GibCursorGibCursorGibBoolProd) {end_r_2446, jump_3266,
                                                    pvrtmp_5934};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_13 = *(uintptr_t *) tmpcur_5923;
            GibCursor tmpcur_5935 = GIB_UNTAG(tagged_tmpcur_13);
            GibCursor tmpaftercur_5936 = tmpcur_5923 + 8;
            uint16_t tmptag_5937 = GIB_GET_TAG(tagged_tmpcur_13);
            GibCursor end_from_tagged_indr_3264 = tmpcur_5935 + tmptag_5937;
            GibCursorGibCursorGibBoolProd tmp_struct_12 =
                                           check_lcss(end_from_tagged_indr_3264, start_120_1258_1582, step_121_1259_1583, end_122_1260_1584, tmpcur_5935);
            GibCursor pvrtmp_5938 = tmp_struct_12.field0;
            GibCursor pvrtmp_5939 = tmp_struct_12.field1;
            GibBool pvrtmp_5940 = tmp_struct_12.field2;

            return (GibCursorGibCursorGibBoolProd) {pvrtmp_5938, pvrtmp_5939,
                                                    pvrtmp_5940};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5922");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd lcss(GibCursor end_r_2450,
                                                                         GibCursor end_r_2451,
                                                                         GibCursor end_r_2452,
                                                                         GibCursor loc_2449,
                                                                         GibCursor xs_126_1264_1591,
                                                                         GibCursor ys_127_1265_1592)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2449 + 18 > end_r_2452) {
        gib_grow_region(&loc_2449, &end_r_2452);
    }

    GibCursorGibCursorGibIntProd tmp_struct_14 =
                                  length_plist_779(end_r_2450, xs_126_1264_1591);
    GibCursor pvrtmp_5942 = tmp_struct_14.field0;
    GibCursor pvrtmp_5943 = tmp_struct_14.field1;
    GibInt pvrtmp_5944 = tmp_struct_14.field2;
    GibCursorGibCursorGibIntProd tmp_struct_15 =
                                  length_plist_779(end_r_2451, ys_127_1265_1592);
    GibCursor pvrtmp_5945 = tmp_struct_15.field0;
    GibCursor pvrtmp_5946 = tmp_struct_15.field1;
    GibInt pvrtmp_5947 = tmp_struct_15.field2;

    gib_shadowstack_push(rstack, xs_126_1264_1591, end_r_2450, Stk,
                         PList_v_778_T);
    gib_shadowstack_push(rstack, ys_127_1265_1592, end_r_2451, Stk,
                         PList_v_778_T);
    gib_shadowstack_push(wstack, loc_2449, end_r_2452, Stk, PList_v_778_T);

    GibChunk region_5948 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_2617 = region_5948.start;
    GibCursor end_r_2617 = region_5948.end;

    frame = gib_shadowstack_pop(wstack);
    loc_2449 = frame->ptr;
    end_r_2452 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    ys_127_1265_1592 = frame->ptr;
    end_r_2451 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    xs_126_1264_1591 = frame->ptr;
    end_r_2450 = frame->endptr;
    *(GibPackedTag *) r_2617 = 0;

    GibCursor writetag_4203 = r_2617 + 1;
    GibCursor after_tag_4204 = r_2617 + 1;
    GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_16 =
                                                                algc(end_r_2450, end_r_2451, end_r_2617, end_r_2452, loc_2449, pvrtmp_5944, pvrtmp_5947, xs_126_1264_1591, ys_127_1265_1592, r_2617);
    GibCursor pvrtmp_5951 = tmp_struct_16.field0;
    GibCursor pvrtmp_5952 = tmp_struct_16.field1;
    GibCursor pvrtmp_5953 = tmp_struct_16.field2;
    GibCursor pvrtmp_5954 = tmp_struct_16.field3;
    GibCursor pvrtmp_5955 = tmp_struct_16.field4;
    GibCursor pvrtmp_5956 = tmp_struct_16.field5;

    return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_5951,
                                                                                  pvrtmp_5952,
                                                                                  pvrtmp_5954,
                                                                                  pvrtmp_5943,
                                                                                  pvrtmp_5946,
                                                                                  pvrtmp_5955,
                                                                                  pvrtmp_5956};
}
GibCursorGibCursorGibCursorProd mkList(GibCursor end_r_2454, GibCursor loc_2453,
                                       GibInt start_128_1266_1596,
                                       GibInt end_129_1267_1597,
                                       GibInt skipFactor_130_1268_1598)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2453 + 18 > end_r_2454) {
        gib_grow_region(&loc_2453, &end_r_2454);
    }

    GibBool fltIf_1507_1599 = start_128_1266_1596 <= end_129_1267_1597;

    if (fltIf_1507_1599) {
        GibInt fltAppE_1508_1600 = start_128_1266_1596 +
               skipFactor_130_1268_1598;
        GibCursor loc_2620 = loc_2453 + 9;

        *(GibPackedTag *) loc_2453 = 1;

        GibCursor writetag_4217 = loc_2453 + 1;
        GibCursor after_tag_4218 = loc_2453 + 1;

        *(GibInt *) after_tag_4218 = start_128_1266_1596;

        GibCursor writecur_4222 = after_tag_4218 + sizeof(GibInt);
        GibCursorGibCursorGibCursorProd tmp_struct_20 =
                                         mkList(end_r_2454, loc_2620, fltAppE_1508_1600, end_129_1267_1597, skipFactor_130_1268_1598);
        GibCursor pvrtmp_5963 = tmp_struct_20.field0;
        GibCursor pvrtmp_5964 = tmp_struct_20.field1;
        GibCursor pvrtmp_5965 = tmp_struct_20.field2;

        return (GibCursorGibCursorGibCursorProd) {pvrtmp_5963, loc_2453,
                                                  pvrtmp_5965};
    } else {
        *(GibPackedTag *) loc_2453 = 0;

        GibCursor writetag_4226 = loc_2453 + 1;
        GibCursor after_tag_4227 = loc_2453 + 1;

        return (GibCursorGibCursorGibCursorProd) {end_r_2454, loc_2453,
                                                  after_tag_4227};
    }
}
GibCursorGibCursorGibIntProd findk(GibCursor end_r_2456, GibInt k_132_1270_1602,
                                   GibInt km_133_1271_1603,
                                   GibInt m_134_1272_1604,
                                   GibCursor ls_135_1273_1605)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_5978 = *(GibPackedTag *) ls_135_1273_1605;
    GibCursor tmpcur_5979 = ls_135_1273_1605 + 1;


  switch_6004:
    ;
    switch (tmpval_5978) {

      case 0:
        {
            GibCursor jump_3107 = ls_135_1273_1605 + 1;

            return (GibCursorGibCursorGibIntProd) {end_r_2456, jump_3107,
                                                   km_133_1271_1603};
            break;
        }

      case 1:
        {
            GibInt tmpval_5980 = *(GibInt *) tmpcur_5979;
            GibCursor tmpcur_5981 = tmpcur_5979 + sizeof(GibInt);
            GibInt tmpval_5982 = *(GibInt *) tmpcur_5981;
            GibCursor tmpcur_5983 = tmpcur_5981 + sizeof(GibInt);
            GibInt fltPrm_1510_1612 = tmpval_5980 + tmpval_5982;
            GibBool fltIf_1509_1613 = fltPrm_1510_1612 >= m_134_1272_1604;

            if (fltIf_1509_1613) {
                GibInt fltAppE_1511_1614 = k_132_1270_1602 + 1;
                GibInt fltAppE_1512_1615 = tmpval_5980 + tmpval_5982;
                GibCursorGibCursorGibIntProd tmp_struct_24 =
                                              findk(end_r_2456, fltAppE_1511_1614, k_132_1270_1602, fltAppE_1512_1615, tmpcur_5983);
                GibCursor pvrtmp_5986 = tmp_struct_24.field0;
                GibCursor pvrtmp_5987 = tmp_struct_24.field1;
                GibInt pvrtmp_5988 = tmp_struct_24.field2;

                return (GibCursorGibCursorGibIntProd) {pvrtmp_5986, pvrtmp_5987,
                                                       pvrtmp_5988};
            } else {
                GibInt fltAppE_1513_1616 = k_132_1270_1602 + 1;
                GibCursorGibCursorGibIntProd tmp_struct_25 =
                                              findk(end_r_2456, fltAppE_1513_1616, km_133_1271_1603, m_134_1272_1604, tmpcur_5983);
                GibCursor pvrtmp_5989 = tmp_struct_25.field0;
                GibCursor pvrtmp_5990 = tmp_struct_25.field1;
                GibInt pvrtmp_5991 = tmp_struct_25.field2;

                return (GibCursorGibCursorGibIntProd) {pvrtmp_5989, pvrtmp_5990,
                                                       pvrtmp_5991};
            }
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_27 = *(uintptr_t *) tmpcur_5979;
            GibCursor tmpcur_5992 = GIB_UNTAG(tagged_tmpcur_27);
            GibCursor tmpaftercur_5993 = tmpcur_5979 + 8;
            uint16_t tmptag_5994 = GIB_GET_TAG(tagged_tmpcur_27);
            GibCursor end_from_tagged_indr_3270 = tmpcur_5992 + tmptag_5994;
            GibCursor jump_3272 = tmpcur_5979 + 8;
            GibCursorGibCursorGibIntProd tmp_struct_26 =
                                          findk(end_from_tagged_indr_3270, k_132_1270_1602, km_133_1271_1603, m_134_1272_1604, tmpcur_5992);
            GibCursor pvrtmp_5995 = tmp_struct_26.field0;
            GibCursor pvrtmp_5996 = tmp_struct_26.field1;
            GibInt pvrtmp_5997 = tmp_struct_26.field2;

            return (GibCursorGibCursorGibIntProd) {end_r_2456, jump_3272,
                                                   pvrtmp_5997};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_29 = *(uintptr_t *) tmpcur_5979;
            GibCursor tmpcur_5998 = GIB_UNTAG(tagged_tmpcur_29);
            GibCursor tmpaftercur_5999 = tmpcur_5979 + 8;
            uint16_t tmptag_6000 = GIB_GET_TAG(tagged_tmpcur_29);
            GibCursor end_from_tagged_indr_3270 = tmpcur_5998 + tmptag_6000;
            GibCursorGibCursorGibIntProd tmp_struct_28 =
                                          findk(end_from_tagged_indr_3270, k_132_1270_1602, km_133_1271_1603, m_134_1272_1604, tmpcur_5998);
            GibCursor pvrtmp_6001 = tmp_struct_28.field0;
            GibCursor pvrtmp_6002 = tmp_struct_28.field1;
            GibInt pvrtmp_6003 = tmp_struct_28.field2;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_6001, pvrtmp_6002,
                                                   pvrtmp_6003};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5978");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd algc(GibCursor end_r_2461,
                                                                GibCursor end_r_2462,
                                                                GibCursor end_r_2463,
                                                                GibCursor end_r_2464,
                                                                GibCursor loc_2460,
                                                                GibInt m_141_1280_1617,
                                                                GibInt n_142_1281_1618,
                                                                GibCursor xs_143_1282_1619,
                                                                GibCursor ys_144_1283_1620,
                                                                GibCursor zs_145_1284_1621)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2460 + 18 > end_r_2464) {
        gib_grow_region(&loc_2460, &end_r_2464);
    }

    GibCursorGibBoolProd tmp_struct_30 =
                          is_empty_plist_781(end_r_2462, ys_144_1283_1620);
    GibCursor pvrtmp_6005 = tmp_struct_30.field0;
    GibBool pvrtmp_6006 = tmp_struct_30.field1;

    if (pvrtmp_6006) {
        if (loc_2460 + 18 > end_r_2464) {
            gib_grow_region(&loc_2460, &end_r_2464);
        }
        gib_indirection_barrier(loc_2460, end_r_2464, zs_145_1284_1621,
                                end_r_2463, PList_v_778_T);

        GibCursor end_4252 = loc_2460 + 9;

        return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2461,
                                                                             pvrtmp_6005,
                                                                             end_r_2463,
                                                                             end_r_2464,
                                                                             loc_2460,
                                                                             end_4252};
    } else {
        GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_34
                                                                   =
                                                                    caseFn_1228(end_r_2461, end_r_2462, end_r_2463, end_r_2464, loc_2460, m_141_1280_1617, n_142_1281_1618, xs_143_1282_1619, ys_144_1283_1620, zs_145_1284_1621);
        GibCursor pvrtmp_6011 = tmp_struct_34.field0;
        GibCursor pvrtmp_6012 = tmp_struct_34.field1;
        GibCursor pvrtmp_6013 = tmp_struct_34.field2;
        GibCursor pvrtmp_6014 = tmp_struct_34.field3;
        GibCursor pvrtmp_6015 = tmp_struct_34.field4;
        GibCursor pvrtmp_6016 = tmp_struct_34.field5;

        return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6011,
                                                                             pvrtmp_6012,
                                                                             pvrtmp_6013,
                                                                             pvrtmp_6014,
                                                                             pvrtmp_6015,
                                                                             pvrtmp_6016};
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd algb2(GibCursor end_r_2467,
                                                        GibCursor end_r_2468,
                                                        GibCursor loc_2466,
                                                        GibInt x_161_1285_1623,
                                                        GibInt k0j1_162_1286_1624,
                                                        GibInt k1j1_163_1287_1625,
                                                        GibCursor ls_164_1288_1626)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2466 + 26 > end_r_2468) {
        gib_grow_region(&loc_2466, &end_r_2468);
    }

    GibPackedTag tmpval_6023 = *(GibPackedTag *) ls_164_1288_1626;
    GibCursor tmpcur_6024 = ls_164_1288_1626 + 1;


  switch_6077:
    ;
    switch (tmpval_6023) {

      case 0:
        {
            GibCursor jump_3115 = ls_164_1288_1626 + 1;

            *(GibPackedTag *) loc_2466 = 0;

            GibCursor writetag_4260 = loc_2466 + 1;
            GibCursor after_tag_4261 = loc_2466 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2467,
                                                                        end_r_2468,
                                                                        jump_3115,
                                                                        loc_2466,
                                                                        after_tag_4261};
            break;
        }

      case 1:
        {
            GibInt tmpval_6029 = *(GibInt *) tmpcur_6024;
            GibCursor tmpcur_6030 = tmpcur_6024 + sizeof(GibInt);
            GibInt tmpval_6031 = *(GibInt *) tmpcur_6030;
            GibCursor tmpcur_6032 = tmpcur_6030 + sizeof(GibInt);
            GibBool fltIf_1515_1633 = x_161_1285_1623 == tmpval_6029;
            GibInt kjcurr_170_1295_1634;

            if (fltIf_1515_1633) {
                GibInt flt_6035 = k0j1_162_1286_1624 + 1;

                kjcurr_170_1295_1634 = flt_6035;
            } else {
                GibInt kjcurr_170_1295_1634hack =
                        maxInt(k1j1_163_1287_1625, tmpval_6031);

                kjcurr_170_1295_1634 = kjcurr_170_1295_1634hack;
            }

            GibCursor loc_2655 = loc_2466 + 17;

            *(GibPackedTag *) loc_2466 = 1;

            GibCursor writetag_4273 = loc_2466 + 1;
            GibCursor after_tag_4274 = loc_2466 + 1;

            *(GibInt *) after_tag_4274 = tmpval_6029;

            GibCursor writecur_4278 = after_tag_4274 + sizeof(GibInt);

            *(GibInt *) writecur_4278 = kjcurr_170_1295_1634;

            GibCursor writecur_4279 = writecur_4278 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_38 =
                                                               algb2(end_r_2467, end_r_2468, loc_2655, x_161_1285_1623, tmpval_6031, kjcurr_170_1295_1634, tmpcur_6032);
            GibCursor pvrtmp_6036 = tmp_struct_38.field0;
            GibCursor pvrtmp_6037 = tmp_struct_38.field1;
            GibCursor pvrtmp_6038 = tmp_struct_38.field2;
            GibCursor pvrtmp_6039 = tmp_struct_38.field3;
            GibCursor pvrtmp_6040 = tmp_struct_38.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6036,
                                                                        pvrtmp_6037,
                                                                        pvrtmp_6038,
                                                                        loc_2466,
                                                                        pvrtmp_6040};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_40 = *(uintptr_t *) tmpcur_6024;
            GibCursor tmpcur_6049 = GIB_UNTAG(tagged_tmpcur_40);
            GibCursor tmpaftercur_6050 = tmpcur_6024 + 8;
            uint16_t tmptag_6051 = GIB_GET_TAG(tagged_tmpcur_40);
            GibCursor end_from_tagged_indr_3276 = tmpcur_6049 + tmptag_6051;
            GibCursor jump_3278 = tmpcur_6024 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_39 =
                                                               algb2(end_from_tagged_indr_3276, end_r_2468, loc_2466, x_161_1285_1623, k0j1_162_1286_1624, k1j1_163_1287_1625, tmpcur_6049);
            GibCursor pvrtmp_6052 = tmp_struct_39.field0;
            GibCursor pvrtmp_6053 = tmp_struct_39.field1;
            GibCursor pvrtmp_6054 = tmp_struct_39.field2;
            GibCursor pvrtmp_6055 = tmp_struct_39.field3;
            GibCursor pvrtmp_6056 = tmp_struct_39.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2467,
                                                                        pvrtmp_6053,
                                                                        jump_3278,
                                                                        pvrtmp_6055,
                                                                        pvrtmp_6056};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_42 = *(uintptr_t *) tmpcur_6024;
            GibCursor tmpcur_6063 = GIB_UNTAG(tagged_tmpcur_42);
            GibCursor tmpaftercur_6064 = tmpcur_6024 + 8;
            uint16_t tmptag_6065 = GIB_GET_TAG(tagged_tmpcur_42);
            GibCursor end_from_tagged_indr_3276 = tmpcur_6063 + tmptag_6065;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_41 =
                                                               algb2(end_from_tagged_indr_3276, end_r_2468, loc_2466, x_161_1285_1623, k0j1_162_1286_1624, k1j1_163_1287_1625, tmpcur_6063);
            GibCursor pvrtmp_6066 = tmp_struct_41.field0;
            GibCursor pvrtmp_6067 = tmp_struct_41.field1;
            GibCursor pvrtmp_6068 = tmp_struct_41.field2;
            GibCursor pvrtmp_6069 = tmp_struct_41.field3;
            GibCursor pvrtmp_6070 = tmp_struct_41.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6066,
                                                                        pvrtmp_6067,
                                                                        pvrtmp_6068,
                                                                        pvrtmp_6069,
                                                                        pvrtmp_6070};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6023");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd algb1(GibCursor end_r_2472,
                                                                          GibCursor end_r_2473,
                                                                          GibCursor end_r_2474,
                                                                          GibCursor loc_2471,
                                                                          GibCursor xs_171_1296_1636,
                                                                          GibCursor ys_172_1297_1637)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2471 + 18 > end_r_2474) {
        gib_grow_region(&loc_2471, &end_r_2474);
    }

    GibPackedTag tmpval_6078 = *(GibPackedTag *) xs_171_1296_1636;
    GibCursor tmpcur_6079 = xs_171_1296_1636 + 1;


  switch_6148:
    ;
    switch (tmpval_6078) {

      case 0:
        {
            GibCursor jump_3121 = xs_171_1296_1636 + 1;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_46 =
                                                               map_plist_787_1071(end_r_2473, end_r_2474, loc_2471, ys_172_1297_1637);
            GibCursor pvrtmp_6080 = tmp_struct_46.field0;
            GibCursor pvrtmp_6081 = tmp_struct_46.field1;
            GibCursor pvrtmp_6082 = tmp_struct_46.field2;
            GibCursor pvrtmp_6083 = tmp_struct_46.field3;
            GibCursor pvrtmp_6084 = tmp_struct_46.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2472,
                                                                                          pvrtmp_6080,
                                                                                          pvrtmp_6081,
                                                                                          jump_3121,
                                                                                          pvrtmp_6082,
                                                                                          pvrtmp_6083,
                                                                                          pvrtmp_6084};
            break;
        }

      case 1:
        {
            GibInt tmpval_6091 = *(GibInt *) tmpcur_6079;
            GibCursor tmpcur_6092 = tmpcur_6079 + sizeof(GibInt);

            gib_shadowstack_push(rstack, ys_172_1297_1637, end_r_2473, Stk,
                                 PList_v_780_T);
            gib_shadowstack_push(rstack, tmpcur_6092, end_r_2472, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(wstack, loc_2471, end_r_2474, Stk,
                                 PList_v_778_T);

            GibChunk region_6093 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_2679 = region_6093.start;
            GibCursor end_r_2679 = region_6093.end;

            frame = gib_shadowstack_pop(wstack);
            loc_2471 = frame->ptr;
            end_r_2474 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tmpcur_6092 = frame->ptr;
            end_r_2472 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_172_1297_1637 = frame->ptr;
            end_r_2473 = frame->endptr;

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_47 =
                                                               algb2(end_r_2473, end_r_2679, r_2679, tmpval_6091, 0, 0, ys_172_1297_1637);
            GibCursor pvrtmp_6094 = tmp_struct_47.field0;
            GibCursor pvrtmp_6095 = tmp_struct_47.field1;
            GibCursor pvrtmp_6096 = tmp_struct_47.field2;
            GibCursor pvrtmp_6097 = tmp_struct_47.field3;
            GibCursor pvrtmp_6098 = tmp_struct_47.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_48 =
             algb1(end_r_2472, pvrtmp_6095, end_r_2474, loc_2471, tmpcur_6092, pvrtmp_6097);
            GibCursor pvrtmp_6103 = tmp_struct_48.field0;
            GibCursor pvrtmp_6104 = tmp_struct_48.field1;
            GibCursor pvrtmp_6105 = tmp_struct_48.field2;
            GibCursor pvrtmp_6106 = tmp_struct_48.field3;
            GibCursor pvrtmp_6107 = tmp_struct_48.field4;
            GibCursor pvrtmp_6108 = tmp_struct_48.field5;
            GibCursor pvrtmp_6109 = tmp_struct_48.field6;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6103,
                                                                                          pvrtmp_6094,
                                                                                          pvrtmp_6105,
                                                                                          pvrtmp_6106,
                                                                                          pvrtmp_6096,
                                                                                          pvrtmp_6108,
                                                                                          pvrtmp_6109};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_50 = *(uintptr_t *) tmpcur_6079;
            GibCursor tmpcur_6116 = GIB_UNTAG(tagged_tmpcur_50);
            GibCursor tmpaftercur_6117 = tmpcur_6079 + 8;
            uint16_t tmptag_6118 = GIB_GET_TAG(tagged_tmpcur_50);
            GibCursor end_from_tagged_indr_3282 = tmpcur_6116 + tmptag_6118;
            GibCursor jump_3284 = tmpcur_6079 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_49 =
             algb1(end_from_tagged_indr_3282, end_r_2473, end_r_2474, loc_2471, tmpcur_6116, ys_172_1297_1637);
            GibCursor pvrtmp_6119 = tmp_struct_49.field0;
            GibCursor pvrtmp_6120 = tmp_struct_49.field1;
            GibCursor pvrtmp_6121 = tmp_struct_49.field2;
            GibCursor pvrtmp_6122 = tmp_struct_49.field3;
            GibCursor pvrtmp_6123 = tmp_struct_49.field4;
            GibCursor pvrtmp_6124 = tmp_struct_49.field5;
            GibCursor pvrtmp_6125 = tmp_struct_49.field6;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2472,
                                                                                          pvrtmp_6120,
                                                                                          pvrtmp_6121,
                                                                                          jump_3284,
                                                                                          pvrtmp_6123,
                                                                                          pvrtmp_6124,
                                                                                          pvrtmp_6125};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_52 = *(uintptr_t *) tmpcur_6079;
            GibCursor tmpcur_6132 = GIB_UNTAG(tagged_tmpcur_52);
            GibCursor tmpaftercur_6133 = tmpcur_6079 + 8;
            uint16_t tmptag_6134 = GIB_GET_TAG(tagged_tmpcur_52);
            GibCursor end_from_tagged_indr_3282 = tmpcur_6132 + tmptag_6134;
            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_51 =
             algb1(end_from_tagged_indr_3282, end_r_2473, end_r_2474, loc_2471, tmpcur_6132, ys_172_1297_1637);
            GibCursor pvrtmp_6135 = tmp_struct_51.field0;
            GibCursor pvrtmp_6136 = tmp_struct_51.field1;
            GibCursor pvrtmp_6137 = tmp_struct_51.field2;
            GibCursor pvrtmp_6138 = tmp_struct_51.field3;
            GibCursor pvrtmp_6139 = tmp_struct_51.field4;
            GibCursor pvrtmp_6140 = tmp_struct_51.field5;
            GibCursor pvrtmp_6141 = tmp_struct_51.field6;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6135,
                                                                                          pvrtmp_6136,
                                                                                          pvrtmp_6137,
                                                                                          pvrtmp_6138,
                                                                                          pvrtmp_6139,
                                                                                          pvrtmp_6140,
                                                                                          pvrtmp_6141};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6078");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd algb(GibCursor end_r_2478,
                                                                         GibCursor end_r_2479,
                                                                         GibCursor end_r_2480,
                                                                         GibCursor loc_2477,
                                                                         GibCursor xs_178_1300_1641,
                                                                         GibCursor ys_179_1301_1642)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2477 + 18 > end_r_2480) {
        gib_grow_region(&loc_2477, &end_r_2480);
    }
    gib_shadowstack_push(rstack, xs_178_1300_1641, end_r_2478, Stk,
                         PList_v_778_T);
    gib_shadowstack_push(rstack, ys_179_1301_1642, end_r_2479, Stk,
                         PList_v_778_T);
    gib_shadowstack_push(wstack, loc_2477, end_r_2480, Stk, PList_v_778_T);

    GibChunk region_6149 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_2692 = region_6149.start;
    GibCursor end_r_2692 = region_6149.end;

    frame = gib_shadowstack_pop(wstack);
    loc_2477 = frame->ptr;
    end_r_2480 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    ys_179_1301_1642 = frame->ptr;
    end_r_2479 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    xs_178_1300_1641 = frame->ptr;
    end_r_2478 = frame->endptr;

    GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_56 =
                                                       zip0(end_r_2479, end_r_2692, r_2692, ys_179_1301_1642);
    GibCursor pvrtmp_6150 = tmp_struct_56.field0;
    GibCursor pvrtmp_6151 = tmp_struct_56.field1;
    GibCursor pvrtmp_6152 = tmp_struct_56.field2;
    GibCursor pvrtmp_6153 = tmp_struct_56.field3;
    GibCursor pvrtmp_6154 = tmp_struct_56.field4;
    GibCursor loc_2690 = loc_2477 + 9;

    *(GibPackedTag *) loc_2477 = 1;

    GibCursor writetag_4325 = loc_2477 + 1;
    GibCursor after_tag_4326 = loc_2477 + 1;

    *(GibInt *) after_tag_4326 = 0;

    GibCursor writecur_4330 = after_tag_4326 + sizeof(GibInt);

    gib_shadowstack_push(rstack, loc_2477, end_r_2480, Stk, PList_v_778_T);

    GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
    tmp_struct_57 =
     algb1(end_r_2478, pvrtmp_6151, end_r_2480, loc_2690, xs_178_1300_1641, pvrtmp_6153);
    GibCursor pvrtmp_6159 = tmp_struct_57.field0;
    GibCursor pvrtmp_6160 = tmp_struct_57.field1;
    GibCursor pvrtmp_6161 = tmp_struct_57.field2;
    GibCursor pvrtmp_6162 = tmp_struct_57.field3;
    GibCursor pvrtmp_6163 = tmp_struct_57.field4;
    GibCursor pvrtmp_6164 = tmp_struct_57.field5;
    GibCursor pvrtmp_6165 = tmp_struct_57.field6;

    frame = gib_shadowstack_pop(rstack);
    loc_2477 = frame->ptr;
    end_r_2480 = frame->endptr;
    return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6159,
                                                                                  pvrtmp_6150,
                                                                                  pvrtmp_6161,
                                                                                  pvrtmp_6162,
                                                                                  pvrtmp_6152,
                                                                                  loc_2477,
                                                                                  pvrtmp_6165};
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd zip0(GibCursor end_r_2483,
                                                       GibCursor end_r_2484,
                                                       GibCursor loc_2482,
                                                       GibCursor ls_180_1302_1645)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2482 + 26 > end_r_2484) {
        gib_grow_region(&loc_2482, &end_r_2484);
    }

    GibPackedTag tmpval_6174 = *(GibPackedTag *) ls_180_1302_1645;
    GibCursor tmpcur_6175 = ls_180_1302_1645 + 1;


  switch_6223:
    ;
    switch (tmpval_6174) {

      case 0:
        {
            GibCursor jump_3133 = ls_180_1302_1645 + 1;

            *(GibPackedTag *) loc_2482 = 0;

            GibCursor writetag_4335 = loc_2482 + 1;
            GibCursor after_tag_4336 = loc_2482 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2483,
                                                                        end_r_2484,
                                                                        jump_3133,
                                                                        loc_2482,
                                                                        after_tag_4336};
            break;
        }

      case 1:
        {
            GibInt tmpval_6180 = *(GibInt *) tmpcur_6175;
            GibCursor tmpcur_6181 = tmpcur_6175 + sizeof(GibInt);
            GibCursor loc_2703 = loc_2482 + 17;

            *(GibPackedTag *) loc_2482 = 1;

            GibCursor writetag_4347 = loc_2482 + 1;
            GibCursor after_tag_4348 = loc_2482 + 1;

            *(GibInt *) after_tag_4348 = tmpval_6180;

            GibCursor writecur_4352 = after_tag_4348 + sizeof(GibInt);

            *(GibInt *) writecur_4352 = 0;

            GibCursor writecur_4353 = writecur_4352 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_61 =
                                                               zip0(end_r_2483, end_r_2484, loc_2703, tmpcur_6181);
            GibCursor pvrtmp_6182 = tmp_struct_61.field0;
            GibCursor pvrtmp_6183 = tmp_struct_61.field1;
            GibCursor pvrtmp_6184 = tmp_struct_61.field2;
            GibCursor pvrtmp_6185 = tmp_struct_61.field3;
            GibCursor pvrtmp_6186 = tmp_struct_61.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6182,
                                                                        pvrtmp_6183,
                                                                        pvrtmp_6184,
                                                                        loc_2482,
                                                                        pvrtmp_6186};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_63 = *(uintptr_t *) tmpcur_6175;
            GibCursor tmpcur_6195 = GIB_UNTAG(tagged_tmpcur_63);
            GibCursor tmpaftercur_6196 = tmpcur_6175 + 8;
            uint16_t tmptag_6197 = GIB_GET_TAG(tagged_tmpcur_63);
            GibCursor end_from_tagged_indr_3289 = tmpcur_6195 + tmptag_6197;
            GibCursor jump_3291 = tmpcur_6175 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_62 =
                                                               zip0(end_from_tagged_indr_3289, end_r_2484, loc_2482, tmpcur_6195);
            GibCursor pvrtmp_6198 = tmp_struct_62.field0;
            GibCursor pvrtmp_6199 = tmp_struct_62.field1;
            GibCursor pvrtmp_6200 = tmp_struct_62.field2;
            GibCursor pvrtmp_6201 = tmp_struct_62.field3;
            GibCursor pvrtmp_6202 = tmp_struct_62.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2483,
                                                                        pvrtmp_6199,
                                                                        jump_3291,
                                                                        pvrtmp_6201,
                                                                        pvrtmp_6202};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_65 = *(uintptr_t *) tmpcur_6175;
            GibCursor tmpcur_6209 = GIB_UNTAG(tagged_tmpcur_65);
            GibCursor tmpaftercur_6210 = tmpcur_6175 + 8;
            uint16_t tmptag_6211 = GIB_GET_TAG(tagged_tmpcur_65);
            GibCursor end_from_tagged_indr_3289 = tmpcur_6209 + tmptag_6211;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_64 =
                                                               zip0(end_from_tagged_indr_3289, end_r_2484, loc_2482, tmpcur_6209);
            GibCursor pvrtmp_6212 = tmp_struct_64.field0;
            GibCursor pvrtmp_6213 = tmp_struct_64.field1;
            GibCursor pvrtmp_6214 = tmp_struct_64.field2;
            GibCursor pvrtmp_6215 = tmp_struct_64.field3;
            GibCursor pvrtmp_6216 = tmp_struct_64.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6212,
                                                                        pvrtmp_6213,
                                                                        pvrtmp_6214,
                                                                        pvrtmp_6215,
                                                                        pvrtmp_6216};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6174");
            exit(1);
        }
    }
}
GibInt maxInt(GibInt a_189_1305_1649, GibInt b_190_1306_1650)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_1521_1651 = a_189_1305_1649 > b_190_1306_1650;

    if (fltIf_1521_1651) {
        return a_189_1305_1649;
    } else {
        return b_190_1306_1650;
    }
}
GibCursorGibCursorGibIntProd length_plist_779(GibCursor end_r_2486,
                                              GibCursor a_226_1325_1652)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_6224 = *(GibPackedTag *) a_226_1325_1652;
    GibCursor tmpcur_6225 = a_226_1325_1652 + 1;


  switch_6243:
    ;
    switch (tmpval_6224) {

      case 0:
        {
            GibCursor jump_3139 = a_226_1325_1652 + 1;

            return (GibCursorGibCursorGibIntProd) {end_r_2486, jump_3139, 0};
            break;
        }

      case 1:
        {
            GibInt tmpval_6226 = *(GibInt *) tmpcur_6225;
            GibCursor tmpcur_6227 = tmpcur_6225 + sizeof(GibInt);
            GibCursorGibCursorGibIntProd tmp_struct_69 =
                                          length_plist_779(end_r_2486, tmpcur_6227);
            GibCursor pvrtmp_6228 = tmp_struct_69.field0;
            GibCursor pvrtmp_6229 = tmp_struct_69.field1;
            GibInt pvrtmp_6230 = tmp_struct_69.field2;
            GibInt tailprim_3142 = 1 + pvrtmp_6230;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_6228, pvrtmp_6229,
                                                   tailprim_3142};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_71 = *(uintptr_t *) tmpcur_6225;
            GibCursor tmpcur_6231 = GIB_UNTAG(tagged_tmpcur_71);
            GibCursor tmpaftercur_6232 = tmpcur_6225 + 8;
            uint16_t tmptag_6233 = GIB_GET_TAG(tagged_tmpcur_71);
            GibCursor end_from_tagged_indr_3295 = tmpcur_6231 + tmptag_6233;
            GibCursor jump_3297 = tmpcur_6225 + 8;
            GibCursorGibCursorGibIntProd tmp_struct_70 =
                                          length_plist_779(end_from_tagged_indr_3295, tmpcur_6231);
            GibCursor pvrtmp_6234 = tmp_struct_70.field0;
            GibCursor pvrtmp_6235 = tmp_struct_70.field1;
            GibInt pvrtmp_6236 = tmp_struct_70.field2;

            return (GibCursorGibCursorGibIntProd) {end_r_2486, jump_3297,
                                                   pvrtmp_6236};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_73 = *(uintptr_t *) tmpcur_6225;
            GibCursor tmpcur_6237 = GIB_UNTAG(tagged_tmpcur_73);
            GibCursor tmpaftercur_6238 = tmpcur_6225 + 8;
            uint16_t tmptag_6239 = GIB_GET_TAG(tagged_tmpcur_73);
            GibCursor end_from_tagged_indr_3295 = tmpcur_6237 + tmptag_6239;
            GibCursorGibCursorGibIntProd tmp_struct_72 =
                                          length_plist_779(end_from_tagged_indr_3295, tmpcur_6237);
            GibCursor pvrtmp_6240 = tmp_struct_72.field0;
            GibCursor pvrtmp_6241 = tmp_struct_72.field1;
            GibInt pvrtmp_6242 = tmp_struct_72.field2;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_6240, pvrtmp_6241,
                                                   pvrtmp_6242};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6224");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd reverse_plist_785(GibCursor end_r_2490,
                                                                             GibCursor end_r_2491,
                                                                             GibCursor end_r_2492,
                                                                             GibCursor loc_2489,
                                                                             GibCursor xs_221_1328_1656,
                                                                             GibCursor acc_222_1329_1657)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2489 + 18 > end_r_2492) {
        gib_grow_region(&loc_2489, &end_r_2492);
    }

    GibPackedTag tmpval_6244 = *(GibPackedTag *) xs_221_1328_1656;
    GibCursor tmpcur_6245 = xs_221_1328_1656 + 1;


  switch_6299:
    ;
    switch (tmpval_6244) {

      case 0:
        {
            GibCursor jump_3143 = xs_221_1328_1656 + 1;

            if (loc_2489 + 18 > end_r_2492) {
                gib_grow_region(&loc_2489, &end_r_2492);
            }
            gib_indirection_barrier(loc_2489, end_r_2492, acc_222_1329_1657,
                                    end_r_2491, PList_v_778_T);

            GibCursor end_4382 = loc_2489 + 9;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2490,
                                                                                 end_r_2491,
                                                                                 end_r_2492,
                                                                                 jump_3143,
                                                                                 loc_2489,
                                                                                 end_4382};
            break;
        }

      case 1:
        {
            GibInt tmpval_6250 = *(GibInt *) tmpcur_6245;
            GibCursor tmpcur_6251 = tmpcur_6245 + sizeof(GibInt);

            gib_shadowstack_push(rstack, acc_222_1329_1657, end_r_2491, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, tmpcur_6251, end_r_2490, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(wstack, loc_2489, end_r_2492, Stk,
                                 PList_v_778_T);

            GibChunk region_6252 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_2730 = region_6252.start;
            GibCursor end_r_2730 = region_6252.end;

            frame = gib_shadowstack_pop(wstack);
            loc_2489 = frame->ptr;
            end_r_2492 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tmpcur_6251 = frame->ptr;
            end_r_2490 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            acc_222_1329_1657 = frame->ptr;
            end_r_2491 = frame->endptr;

            GibCursor loc_2719 = r_2730 + 9;

            *(GibPackedTag *) r_2730 = 1;

            GibCursor writetag_4389 = r_2730 + 1;
            GibCursor after_tag_4390 = r_2730 + 1;

            *(GibInt *) after_tag_4390 = tmpval_6250;

            GibCursor writecur_4394 = after_tag_4390 + sizeof(GibInt);

            if (loc_2719 + 18 > end_r_2730) {
                gib_grow_region(&loc_2719, &end_r_2730);
            }
            gib_indirection_barrier(loc_2719, end_r_2730, acc_222_1329_1657,
                                    end_r_2491, PList_v_778_T);

            GibCursor end_4387 = loc_2719 + 9;
            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_77 =
             reverse_plist_785(end_r_2490, end_r_2730, end_r_2492, loc_2489, tmpcur_6251, r_2730);
            GibCursor pvrtmp_6257 = tmp_struct_77.field0;
            GibCursor pvrtmp_6258 = tmp_struct_77.field1;
            GibCursor pvrtmp_6259 = tmp_struct_77.field2;
            GibCursor pvrtmp_6260 = tmp_struct_77.field3;
            GibCursor pvrtmp_6261 = tmp_struct_77.field4;
            GibCursor pvrtmp_6262 = tmp_struct_77.field5;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6257,
                                                                                 end_r_2491,
                                                                                 pvrtmp_6259,
                                                                                 pvrtmp_6260,
                                                                                 pvrtmp_6261,
                                                                                 pvrtmp_6262};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_82 = *(uintptr_t *) tmpcur_6245;
            GibCursor tmpcur_6269 = GIB_UNTAG(tagged_tmpcur_82);
            GibCursor tmpaftercur_6270 = tmpcur_6245 + 8;
            uint16_t tmptag_6271 = GIB_GET_TAG(tagged_tmpcur_82);
            GibCursor end_from_tagged_indr_3301 = tmpcur_6269 + tmptag_6271;
            GibCursor jump_3303 = tmpcur_6245 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_81 =
             reverse_plist_785(end_from_tagged_indr_3301, end_r_2491, end_r_2492, loc_2489, tmpcur_6269, acc_222_1329_1657);
            GibCursor pvrtmp_6272 = tmp_struct_81.field0;
            GibCursor pvrtmp_6273 = tmp_struct_81.field1;
            GibCursor pvrtmp_6274 = tmp_struct_81.field2;
            GibCursor pvrtmp_6275 = tmp_struct_81.field3;
            GibCursor pvrtmp_6276 = tmp_struct_81.field4;
            GibCursor pvrtmp_6277 = tmp_struct_81.field5;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2490,
                                                                                 pvrtmp_6273,
                                                                                 pvrtmp_6274,
                                                                                 jump_3303,
                                                                                 pvrtmp_6276,
                                                                                 pvrtmp_6277};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_84 = *(uintptr_t *) tmpcur_6245;
            GibCursor tmpcur_6284 = GIB_UNTAG(tagged_tmpcur_84);
            GibCursor tmpaftercur_6285 = tmpcur_6245 + 8;
            uint16_t tmptag_6286 = GIB_GET_TAG(tagged_tmpcur_84);
            GibCursor end_from_tagged_indr_3301 = tmpcur_6284 + tmptag_6286;
            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_83 =
             reverse_plist_785(end_from_tagged_indr_3301, end_r_2491, end_r_2492, loc_2489, tmpcur_6284, acc_222_1329_1657);
            GibCursor pvrtmp_6287 = tmp_struct_83.field0;
            GibCursor pvrtmp_6288 = tmp_struct_83.field1;
            GibCursor pvrtmp_6289 = tmp_struct_83.field2;
            GibCursor pvrtmp_6290 = tmp_struct_83.field3;
            GibCursor pvrtmp_6291 = tmp_struct_83.field4;
            GibCursor pvrtmp_6292 = tmp_struct_83.field5;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6287,
                                                                                 pvrtmp_6288,
                                                                                 pvrtmp_6289,
                                                                                 pvrtmp_6290,
                                                                                 pvrtmp_6291,
                                                                                 pvrtmp_6292};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6244");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd zip_plist_786(GibCursor end_r_2496,
                                                                GibCursor end_r_2497,
                                                                GibCursor end_r_2498,
                                                                GibCursor loc_2495,
                                                                GibCursor as_213_1332_1661,
                                                                GibCursor bs_214_1333_1662)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2495 + 26 > end_r_2498) {
        gib_grow_region(&loc_2495, &end_r_2498);
    }

    GibPackedTag tmpval_6300 = *(GibPackedTag *) as_213_1332_1661;
    GibCursor tmpcur_6301 = as_213_1332_1661 + 1;


  switch_6347:
    ;
    switch (tmpval_6300) {

      case 0:
        {
            *(GibPackedTag *) loc_2495 = 0;

            GibCursor writetag_4415 = loc_2495 + 1;
            GibCursor after_tag_4416 = loc_2495 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2496,
                                                                        end_r_2497,
                                                                        end_r_2498,
                                                                        loc_2495,
                                                                        after_tag_4416};
            break;
        }

      case 1:
        {
            GibInt tmpval_6306 = *(GibInt *) tmpcur_6301;
            GibCursor tmpcur_6307 = tmpcur_6301 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_88 =
                                                               caseFn_1234(end_r_2497, end_r_2496, end_r_2498, loc_2495, bs_214_1333_1662, tmpval_6306, tmpcur_6307);
            GibCursor pvrtmp_6308 = tmp_struct_88.field0;
            GibCursor pvrtmp_6309 = tmp_struct_88.field1;
            GibCursor pvrtmp_6310 = tmp_struct_88.field2;
            GibCursor pvrtmp_6311 = tmp_struct_88.field3;
            GibCursor pvrtmp_6312 = tmp_struct_88.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6309,
                                                                        pvrtmp_6308,
                                                                        pvrtmp_6310,
                                                                        pvrtmp_6311,
                                                                        pvrtmp_6312};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_90 = *(uintptr_t *) tmpcur_6301;
            GibCursor tmpcur_6319 = GIB_UNTAG(tagged_tmpcur_90);
            GibCursor tmpaftercur_6320 = tmpcur_6301 + 8;
            uint16_t tmptag_6321 = GIB_GET_TAG(tagged_tmpcur_90);
            GibCursor end_from_tagged_indr_3307 = tmpcur_6319 + tmptag_6321;
            GibCursor jump_3309 = tmpcur_6301 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_89 =
                                                               zip_plist_786(end_from_tagged_indr_3307, end_r_2497, end_r_2498, loc_2495, tmpcur_6319, bs_214_1333_1662);
            GibCursor pvrtmp_6322 = tmp_struct_89.field0;
            GibCursor pvrtmp_6323 = tmp_struct_89.field1;
            GibCursor pvrtmp_6324 = tmp_struct_89.field2;
            GibCursor pvrtmp_6325 = tmp_struct_89.field3;
            GibCursor pvrtmp_6326 = tmp_struct_89.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2496,
                                                                        pvrtmp_6323,
                                                                        pvrtmp_6324,
                                                                        pvrtmp_6325,
                                                                        pvrtmp_6326};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_92 = *(uintptr_t *) tmpcur_6301;
            GibCursor tmpcur_6333 = GIB_UNTAG(tagged_tmpcur_92);
            GibCursor tmpaftercur_6334 = tmpcur_6301 + 8;
            uint16_t tmptag_6335 = GIB_GET_TAG(tagged_tmpcur_92);
            GibCursor end_from_tagged_indr_3307 = tmpcur_6333 + tmptag_6335;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_91 =
                                                               zip_plist_786(end_from_tagged_indr_3307, end_r_2497, end_r_2498, loc_2495, tmpcur_6333, bs_214_1333_1662);
            GibCursor pvrtmp_6336 = tmp_struct_91.field0;
            GibCursor pvrtmp_6337 = tmp_struct_91.field1;
            GibCursor pvrtmp_6338 = tmp_struct_91.field2;
            GibCursor pvrtmp_6339 = tmp_struct_91.field3;
            GibCursor pvrtmp_6340 = tmp_struct_91.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6336,
                                                                        pvrtmp_6337,
                                                                        pvrtmp_6338,
                                                                        pvrtmp_6339,
                                                                        pvrtmp_6340};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6300");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd drop_plist_784(GibCursor end_r_2501,
                                                        GibCursor end_r_2502,
                                                        GibCursor loc_2500,
                                                        GibInt num_208_1336_1665,
                                                        GibCursor list_209_1337_1666)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2500 + 18 > end_r_2502) {
        gib_grow_region(&loc_2500, &end_r_2502);
    }

    GibPackedTag tmpval_6348 = *(GibPackedTag *) list_209_1337_1666;
    GibCursor tmpcur_6349 = list_209_1337_1666 + 1;


  switch_6398:
    ;
    switch (tmpval_6348) {

      case 0:
        {
            *(GibPackedTag *) loc_2500 = 0;

            GibCursor writetag_4441 = loc_2500 + 1;
            GibCursor after_tag_4442 = loc_2500 + 1;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_2501,
                                                               end_r_2502,
                                                               loc_2500,
                                                               after_tag_4442};
            break;
        }

      case 1:
        {
            GibInt tmpval_6354 = *(GibInt *) tmpcur_6349;
            GibCursor tmpcur_6355 = tmpcur_6349 + sizeof(GibInt);
            GibBool fltIf_1524_1669 = num_208_1336_1665 <= 0;

            if (fltIf_1524_1669) {
                GibCursor loc_2748 = loc_2500 + 9;

                *(GibPackedTag *) loc_2500 = 1;

                GibCursor writetag_4453 = loc_2500 + 1;
                GibCursor after_tag_4454 = loc_2500 + 1;

                *(GibInt *) after_tag_4454 = tmpval_6354;

                GibCursor writecur_4458 = after_tag_4454 + sizeof(GibInt);

                if (loc_2748 + 18 > end_r_2502) {
                    gib_grow_region(&loc_2748, &end_r_2502);
                }
                gib_indirection_barrier(loc_2748, end_r_2502, tmpcur_6355,
                                        end_r_2501, PList_v_778_T);

                GibCursor end_4451 = loc_2748 + 9;

                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_2501,
                                                                   end_r_2502,
                                                                   loc_2500,
                                                                   end_4451};
            } else {
                GibInt fltAppE_1525_1670 = num_208_1336_1665 - 1;
                GibCursorGibCursorGibCursorGibCursorProd tmp_struct_99 =
                                                          drop_plist_784(end_r_2501, end_r_2502, loc_2500, fltAppE_1525_1670, tmpcur_6355);
                GibCursor pvrtmp_6362 = tmp_struct_99.field0;
                GibCursor pvrtmp_6363 = tmp_struct_99.field1;
                GibCursor pvrtmp_6364 = tmp_struct_99.field2;
                GibCursor pvrtmp_6365 = tmp_struct_99.field3;

                return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6362,
                                                                   pvrtmp_6363,
                                                                   pvrtmp_6364,
                                                                   pvrtmp_6365};
            }
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_101 = *(uintptr_t *) tmpcur_6349;
            GibCursor tmpcur_6372 = GIB_UNTAG(tagged_tmpcur_101);
            GibCursor tmpaftercur_6373 = tmpcur_6349 + 8;
            uint16_t tmptag_6374 = GIB_GET_TAG(tagged_tmpcur_101);
            GibCursor end_from_tagged_indr_3312 = tmpcur_6372 + tmptag_6374;
            GibCursor jump_3314 = tmpcur_6349 + 8;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_100 =
                                                      drop_plist_784(end_from_tagged_indr_3312, end_r_2502, loc_2500, num_208_1336_1665, tmpcur_6372);
            GibCursor pvrtmp_6375 = tmp_struct_100.field0;
            GibCursor pvrtmp_6376 = tmp_struct_100.field1;
            GibCursor pvrtmp_6377 = tmp_struct_100.field2;
            GibCursor pvrtmp_6378 = tmp_struct_100.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_2501,
                                                               pvrtmp_6376,
                                                               pvrtmp_6377,
                                                               pvrtmp_6378};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_103 = *(uintptr_t *) tmpcur_6349;
            GibCursor tmpcur_6385 = GIB_UNTAG(tagged_tmpcur_103);
            GibCursor tmpaftercur_6386 = tmpcur_6349 + 8;
            uint16_t tmptag_6387 = GIB_GET_TAG(tagged_tmpcur_103);
            GibCursor end_from_tagged_indr_3312 = tmpcur_6385 + tmptag_6387;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_102 =
                                                      drop_plist_784(end_from_tagged_indr_3312, end_r_2502, loc_2500, num_208_1336_1665, tmpcur_6385);
            GibCursor pvrtmp_6388 = tmp_struct_102.field0;
            GibCursor pvrtmp_6389 = tmp_struct_102.field1;
            GibCursor pvrtmp_6390 = tmp_struct_102.field2;
            GibCursor pvrtmp_6391 = tmp_struct_102.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6388,
                                                               pvrtmp_6389,
                                                               pvrtmp_6390,
                                                               pvrtmp_6391};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6348");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd take_plist_783(GibCursor end_r_2505,
                                                        GibCursor end_r_2506,
                                                        GibCursor loc_2504,
                                                        GibInt n_203_1340_1671,
                                                        GibCursor a_204_1341_1672)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2504 + 18 > end_r_2506) {
        gib_grow_region(&loc_2504, &end_r_2506);
    }

    GibBool fltIf_1526_1673 = n_203_1340_1671 == 0;

    if (fltIf_1526_1673) {
        *(GibPackedTag *) loc_2504 = 0;

        GibCursor writetag_4475 = loc_2504 + 1;
        GibCursor after_tag_4476 = loc_2504 + 1;

        return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_2505,
                                                           end_r_2506, loc_2504,
                                                           after_tag_4476};
    } else {
        GibCursorGibCursorGibCursorGibCursorProd tmp_struct_107 =
                                                  caseFn_1238(end_r_2505, end_r_2506, loc_2504, n_203_1340_1671, a_204_1341_1672);
        GibCursor pvrtmp_6403 = tmp_struct_107.field0;
        GibCursor pvrtmp_6404 = tmp_struct_107.field1;
        GibCursor pvrtmp_6405 = tmp_struct_107.field2;
        GibCursor pvrtmp_6406 = tmp_struct_107.field3;

        return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6403,
                                                           pvrtmp_6404,
                                                           pvrtmp_6405,
                                                           pvrtmp_6406};
    }
}
GibCursorGibBoolProd is_empty_plist_781(GibCursor end_r_2508,
                                        GibCursor ls_191_1342_1674)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_6413 = *(GibPackedTag *) ls_191_1342_1674;
    GibCursor tmpcur_6414 = ls_191_1342_1674 + 1;


  switch_6427:
    ;
    switch (tmpval_6413) {

      case 0:
        {
            return (GibCursorGibBoolProd) {end_r_2508, true};
            break;
        }

      case 1:
        {
            GibInt tmpval_6415 = *(GibInt *) tmpcur_6414;
            GibCursor tmpcur_6416 = tmpcur_6414 + sizeof(GibInt);

            return (GibCursorGibBoolProd) {end_r_2508, false};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_112 = *(uintptr_t *) tmpcur_6414;
            GibCursor tmpcur_6417 = GIB_UNTAG(tagged_tmpcur_112);
            GibCursor tmpaftercur_6418 = tmpcur_6414 + 8;
            uint16_t tmptag_6419 = GIB_GET_TAG(tagged_tmpcur_112);
            GibCursor end_from_tagged_indr_3317 = tmpcur_6417 + tmptag_6419;
            GibCursor jump_3319 = tmpcur_6414 + 8;
            GibCursorGibBoolProd tmp_struct_111 =
                                  is_empty_plist_781(end_from_tagged_indr_3317, tmpcur_6417);
            GibCursor pvrtmp_6420 = tmp_struct_111.field0;
            GibBool pvrtmp_6421 = tmp_struct_111.field1;

            return (GibCursorGibBoolProd) {end_r_2508, pvrtmp_6421};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_114 = *(uintptr_t *) tmpcur_6414;
            GibCursor tmpcur_6422 = GIB_UNTAG(tagged_tmpcur_114);
            GibCursor tmpaftercur_6423 = tmpcur_6414 + 8;
            uint16_t tmptag_6424 = GIB_GET_TAG(tagged_tmpcur_114);
            GibCursor end_from_tagged_indr_3317 = tmpcur_6422 + tmptag_6424;
            GibCursorGibBoolProd tmp_struct_113 =
                                  is_empty_plist_781(end_from_tagged_indr_3317, tmpcur_6422);
            GibCursor pvrtmp_6425 = tmp_struct_113.field0;
            GibBool pvrtmp_6426 = tmp_struct_113.field1;

            return (GibCursorGibBoolProd) {pvrtmp_6425, pvrtmp_6426};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6413");
            exit(1);
        }
    }
}
GibCursorGibBoolProd elem_plist_782_1069(GibCursor end_r_2510,
                                         GibInt a_196_1348_1677,
                                         GibCursor list_197_1349_1678)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_6428 = *(GibPackedTag *) list_197_1349_1678;
    GibCursor tmpcur_6429 = list_197_1349_1678 + 1;


  switch_6445:
    ;
    switch (tmpval_6428) {

      case 0:
        {
            return (GibCursorGibBoolProd) {end_r_2510, false};
            break;
        }

      case 1:
        {
            GibInt tmpval_6430 = *(GibInt *) tmpcur_6429;
            GibCursor tmpcur_6431 = tmpcur_6429 + sizeof(GibInt);
            GibBool fltIf_1529_1683 = tmpval_6430 < a_196_1348_1677;
            GibInt fltPrm_1528_1685;

            if (fltIf_1529_1683) {
                GibInt flt_6432 = 0 - 1;

                fltPrm_1528_1685 = flt_6432;
            } else {
                GibBool fltIf_1530_1684 = tmpval_6430 > a_196_1348_1677;

                if (fltIf_1530_1684) {
                    fltPrm_1528_1685 = 1;
                } else {
                    fltPrm_1528_1685 = 0;
                }
            }

            GibBool fltIf_1527_1686 = fltPrm_1528_1685 == 0;

            if (fltIf_1527_1686) {
                return (GibCursorGibBoolProd) {end_r_2510, true};
            } else {
                GibCursorGibBoolProd tmp_struct_115 =
                                      elem_plist_782_1069(end_r_2510, a_196_1348_1677, tmpcur_6431);
                GibCursor pvrtmp_6433 = tmp_struct_115.field0;
                GibBool pvrtmp_6434 = tmp_struct_115.field1;

                return (GibCursorGibBoolProd) {pvrtmp_6433, pvrtmp_6434};
            }
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_117 = *(uintptr_t *) tmpcur_6429;
            GibCursor tmpcur_6435 = GIB_UNTAG(tagged_tmpcur_117);
            GibCursor tmpaftercur_6436 = tmpcur_6429 + 8;
            uint16_t tmptag_6437 = GIB_GET_TAG(tagged_tmpcur_117);
            GibCursor end_from_tagged_indr_3322 = tmpcur_6435 + tmptag_6437;
            GibCursor jump_3324 = tmpcur_6429 + 8;
            GibCursorGibBoolProd tmp_struct_116 =
                                  elem_plist_782_1069(end_from_tagged_indr_3322, a_196_1348_1677, tmpcur_6435);
            GibCursor pvrtmp_6438 = tmp_struct_116.field0;
            GibBool pvrtmp_6439 = tmp_struct_116.field1;

            return (GibCursorGibBoolProd) {end_r_2510, pvrtmp_6439};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_119 = *(uintptr_t *) tmpcur_6429;
            GibCursor tmpcur_6440 = GIB_UNTAG(tagged_tmpcur_119);
            GibCursor tmpaftercur_6441 = tmpcur_6429 + 8;
            uint16_t tmptag_6442 = GIB_GET_TAG(tagged_tmpcur_119);
            GibCursor end_from_tagged_indr_3322 = tmpcur_6440 + tmptag_6442;
            GibCursorGibBoolProd tmp_struct_118 =
                                  elem_plist_782_1069(end_from_tagged_indr_3322, a_196_1348_1677, tmpcur_6440);
            GibCursor pvrtmp_6443 = tmp_struct_118.field0;
            GibBool pvrtmp_6444 = tmp_struct_118.field1;

            return (GibCursorGibBoolProd) {pvrtmp_6443, pvrtmp_6444};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6428");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd map_plist_787_1071(GibCursor end_r_2513,
                                                                     GibCursor end_r_2514,
                                                                     GibCursor loc_2512,
                                                                     GibCursor ls_184_1352_1687)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2512 + 18 > end_r_2514) {
        gib_grow_region(&loc_2512, &end_r_2514);
    }

    GibPackedTag tmpval_6446 = *(GibPackedTag *) ls_184_1352_1687;
    GibCursor tmpcur_6447 = ls_184_1352_1687 + 1;


  switch_6499:
    ;
    switch (tmpval_6446) {

      case 0:
        {
            GibCursor jump_3167 = ls_184_1352_1687 + 1;

            *(GibPackedTag *) loc_2512 = 0;

            GibCursor writetag_4510 = loc_2512 + 1;
            GibCursor after_tag_4511 = loc_2512 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2513,
                                                                        end_r_2514,
                                                                        jump_3167,
                                                                        loc_2512,
                                                                        after_tag_4511};
            break;
        }

      case 1:
        {
            GibInt tmpval_6452 = *(GibInt *) tmpcur_6447;
            GibCursor tmpcur_6453 = tmpcur_6447 + sizeof(GibInt);
            GibInt tmpval_6454 = *(GibInt *) tmpcur_6453;
            GibCursor tmpcur_6455 = tmpcur_6453 + sizeof(GibInt);
            GibCursor loc_2781 = loc_2512 + 9;

            *(GibPackedTag *) loc_2512 = 1;

            GibCursor writetag_4523 = loc_2512 + 1;
            GibCursor after_tag_4524 = loc_2512 + 1;

            *(GibInt *) after_tag_4524 = tmpval_6454;

            GibCursor writecur_4528 = after_tag_4524 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_120 =
                                                               map_plist_787_1071(end_r_2513, end_r_2514, loc_2781, tmpcur_6455);
            GibCursor pvrtmp_6458 = tmp_struct_120.field0;
            GibCursor pvrtmp_6459 = tmp_struct_120.field1;
            GibCursor pvrtmp_6460 = tmp_struct_120.field2;
            GibCursor pvrtmp_6461 = tmp_struct_120.field3;
            GibCursor pvrtmp_6462 = tmp_struct_120.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6458,
                                                                        pvrtmp_6459,
                                                                        pvrtmp_6460,
                                                                        loc_2512,
                                                                        pvrtmp_6462};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_122 = *(uintptr_t *) tmpcur_6447;
            GibCursor tmpcur_6471 = GIB_UNTAG(tagged_tmpcur_122);
            GibCursor tmpaftercur_6472 = tmpcur_6447 + 8;
            uint16_t tmptag_6473 = GIB_GET_TAG(tagged_tmpcur_122);
            GibCursor end_from_tagged_indr_3327 = tmpcur_6471 + tmptag_6473;
            GibCursor jump_3329 = tmpcur_6447 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_121 =
                                                               map_plist_787_1071(end_from_tagged_indr_3327, end_r_2514, loc_2512, tmpcur_6471);
            GibCursor pvrtmp_6474 = tmp_struct_121.field0;
            GibCursor pvrtmp_6475 = tmp_struct_121.field1;
            GibCursor pvrtmp_6476 = tmp_struct_121.field2;
            GibCursor pvrtmp_6477 = tmp_struct_121.field3;
            GibCursor pvrtmp_6478 = tmp_struct_121.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2513,
                                                                        pvrtmp_6475,
                                                                        jump_3329,
                                                                        pvrtmp_6477,
                                                                        pvrtmp_6478};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_124 = *(uintptr_t *) tmpcur_6447;
            GibCursor tmpcur_6485 = GIB_UNTAG(tagged_tmpcur_124);
            GibCursor tmpaftercur_6486 = tmpcur_6447 + 8;
            uint16_t tmptag_6487 = GIB_GET_TAG(tagged_tmpcur_124);
            GibCursor end_from_tagged_indr_3327 = tmpcur_6485 + tmptag_6487;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_123 =
                                                               map_plist_787_1071(end_from_tagged_indr_3327, end_r_2514, loc_2512, tmpcur_6485);
            GibCursor pvrtmp_6488 = tmp_struct_123.field0;
            GibCursor pvrtmp_6489 = tmp_struct_123.field1;
            GibCursor pvrtmp_6490 = tmp_struct_123.field2;
            GibCursor pvrtmp_6491 = tmp_struct_123.field3;
            GibCursor pvrtmp_6492 = tmp_struct_123.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6488,
                                                                        pvrtmp_6489,
                                                                        pvrtmp_6490,
                                                                        pvrtmp_6491,
                                                                        pvrtmp_6492};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6446");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_PList_v_778(GibCursor end_r_2517,
                                                                    GibCursor end_r_2518,
                                                                    GibCursor loc_2516,
                                                                    GibCursor arg_1136_1356_1696)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2516 + 18 > end_r_2518) {
        gib_grow_region(&loc_2516, &end_r_2518);
    }

    GibPackedTag tmpval_6500 = *(GibPackedTag *) arg_1136_1356_1696;
    GibCursor tmpcur_6501 = arg_1136_1356_1696 + 1;


  switch_6549:
    ;
    switch (tmpval_6500) {

      case 0:
        {
            GibCursor jump_3173 = arg_1136_1356_1696 + 1;

            *(GibPackedTag *) loc_2516 = 0;

            GibCursor writetag_4543 = loc_2516 + 1;
            GibCursor after_tag_4544 = loc_2516 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2517,
                                                                        end_r_2518,
                                                                        jump_3173,
                                                                        loc_2516,
                                                                        after_tag_4544};
            break;
        }

      case 1:
        {
            GibInt tmpval_6506 = *(GibInt *) tmpcur_6501;
            GibCursor tmpcur_6507 = tmpcur_6501 + sizeof(GibInt);
            GibCursor loc_2794 = loc_2516 + 9;

            *(GibPackedTag *) loc_2516 = 1;

            GibCursor writetag_4555 = loc_2516 + 1;
            GibCursor after_tag_4556 = loc_2516 + 1;

            *(GibInt *) after_tag_4556 = tmpval_6506;

            GibCursor writecur_4560 = after_tag_4556 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_128 =
                                                               _copy_PList_v_778(end_r_2517, end_r_2518, loc_2794, tmpcur_6507);
            GibCursor pvrtmp_6508 = tmp_struct_128.field0;
            GibCursor pvrtmp_6509 = tmp_struct_128.field1;
            GibCursor pvrtmp_6510 = tmp_struct_128.field2;
            GibCursor pvrtmp_6511 = tmp_struct_128.field3;
            GibCursor pvrtmp_6512 = tmp_struct_128.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6508,
                                                                        pvrtmp_6509,
                                                                        pvrtmp_6510,
                                                                        loc_2516,
                                                                        pvrtmp_6512};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_130 = *(uintptr_t *) tmpcur_6501;
            GibCursor tmpcur_6521 = GIB_UNTAG(tagged_tmpcur_130);
            GibCursor tmpaftercur_6522 = tmpcur_6501 + 8;
            uint16_t tmptag_6523 = GIB_GET_TAG(tagged_tmpcur_130);
            GibCursor end_from_tagged_indr_3333 = tmpcur_6521 + tmptag_6523;
            GibCursor jump_3335 = tmpcur_6501 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_129 =
                                                               _copy_PList_v_778(end_from_tagged_indr_3333, end_r_2518, loc_2516, tmpcur_6521);
            GibCursor pvrtmp_6524 = tmp_struct_129.field0;
            GibCursor pvrtmp_6525 = tmp_struct_129.field1;
            GibCursor pvrtmp_6526 = tmp_struct_129.field2;
            GibCursor pvrtmp_6527 = tmp_struct_129.field3;
            GibCursor pvrtmp_6528 = tmp_struct_129.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2517,
                                                                        pvrtmp_6525,
                                                                        jump_3335,
                                                                        pvrtmp_6527,
                                                                        pvrtmp_6528};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_132 = *(uintptr_t *) tmpcur_6501;
            GibCursor tmpcur_6535 = GIB_UNTAG(tagged_tmpcur_132);
            GibCursor tmpaftercur_6536 = tmpcur_6501 + 8;
            uint16_t tmptag_6537 = GIB_GET_TAG(tagged_tmpcur_132);
            GibCursor end_from_tagged_indr_3333 = tmpcur_6535 + tmptag_6537;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_131 =
                                                               _copy_PList_v_778(end_from_tagged_indr_3333, end_r_2518, loc_2516, tmpcur_6535);
            GibCursor pvrtmp_6538 = tmp_struct_131.field0;
            GibCursor pvrtmp_6539 = tmp_struct_131.field1;
            GibCursor pvrtmp_6540 = tmp_struct_131.field2;
            GibCursor pvrtmp_6541 = tmp_struct_131.field3;
            GibCursor pvrtmp_6542 = tmp_struct_131.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6538,
                                                                        pvrtmp_6539,
                                                                        pvrtmp_6540,
                                                                        pvrtmp_6541,
                                                                        pvrtmp_6542};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6500");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_PList_v_778(GibCursor end_r_2521,
                                                                                 GibCursor end_r_2522,
                                                                                 GibCursor loc_2520,
                                                                                 GibCursor arg_1141_1361_1701)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_6550 = *(GibPackedTag *) arg_1141_1361_1701;
    GibCursor tmpcur_6551 = arg_1141_1361_1701 + 1;


  switch_6599:
    ;
    switch (tmpval_6550) {

      case 0:
        {
            GibCursor jump_3178 = arg_1141_1361_1701 + 1;

            *(GibPackedTag *) loc_2520 = 0;

            GibCursor writetag_4575 = loc_2520 + 1;
            GibCursor after_tag_4576 = loc_2520 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2521,
                                                                        end_r_2522,
                                                                        jump_3178,
                                                                        loc_2520,
                                                                        after_tag_4576};
            break;
        }

      case 1:
        {
            GibInt tmpval_6556 = *(GibInt *) tmpcur_6551;
            GibCursor tmpcur_6557 = tmpcur_6551 + sizeof(GibInt);
            GibCursor loc_2807 = loc_2520 + 9;

            *(GibPackedTag *) loc_2520 = 1;

            GibCursor writetag_4587 = loc_2520 + 1;
            GibCursor after_tag_4588 = loc_2520 + 1;

            *(GibInt *) after_tag_4588 = tmpval_6556;

            GibCursor writecur_4592 = after_tag_4588 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_136 =
                                                               _copy_without_ptrs_PList_v_778(end_r_2521, end_r_2522, loc_2807, tmpcur_6557);
            GibCursor pvrtmp_6558 = tmp_struct_136.field0;
            GibCursor pvrtmp_6559 = tmp_struct_136.field1;
            GibCursor pvrtmp_6560 = tmp_struct_136.field2;
            GibCursor pvrtmp_6561 = tmp_struct_136.field3;
            GibCursor pvrtmp_6562 = tmp_struct_136.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6558,
                                                                        pvrtmp_6559,
                                                                        pvrtmp_6560,
                                                                        loc_2520,
                                                                        pvrtmp_6562};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_138 = *(uintptr_t *) tmpcur_6551;
            GibCursor tmpcur_6571 = GIB_UNTAG(tagged_tmpcur_138);
            GibCursor tmpaftercur_6572 = tmpcur_6551 + 8;
            uint16_t tmptag_6573 = GIB_GET_TAG(tagged_tmpcur_138);
            GibCursor end_from_tagged_indr_3339 = tmpcur_6571 + tmptag_6573;
            GibCursor jump_3341 = tmpcur_6551 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_137 =
                                                               _copy_without_ptrs_PList_v_778(end_from_tagged_indr_3339, end_r_2522, loc_2520, tmpcur_6571);
            GibCursor pvrtmp_6574 = tmp_struct_137.field0;
            GibCursor pvrtmp_6575 = tmp_struct_137.field1;
            GibCursor pvrtmp_6576 = tmp_struct_137.field2;
            GibCursor pvrtmp_6577 = tmp_struct_137.field3;
            GibCursor pvrtmp_6578 = tmp_struct_137.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2521,
                                                                        pvrtmp_6575,
                                                                        jump_3341,
                                                                        pvrtmp_6577,
                                                                        pvrtmp_6578};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_140 = *(uintptr_t *) tmpcur_6551;
            GibCursor tmpcur_6585 = GIB_UNTAG(tagged_tmpcur_140);
            GibCursor tmpaftercur_6586 = tmpcur_6551 + 8;
            uint16_t tmptag_6587 = GIB_GET_TAG(tagged_tmpcur_140);
            GibCursor end_from_tagged_indr_3339 = tmpcur_6585 + tmptag_6587;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_139 =
                                                               _copy_without_ptrs_PList_v_778(end_from_tagged_indr_3339, end_r_2522, loc_2520, tmpcur_6585);
            GibCursor pvrtmp_6588 = tmp_struct_139.field0;
            GibCursor pvrtmp_6589 = tmp_struct_139.field1;
            GibCursor pvrtmp_6590 = tmp_struct_139.field2;
            GibCursor pvrtmp_6591 = tmp_struct_139.field3;
            GibCursor pvrtmp_6592 = tmp_struct_139.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6588,
                                                                        pvrtmp_6589,
                                                                        pvrtmp_6590,
                                                                        pvrtmp_6591,
                                                                        pvrtmp_6592};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6550");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_PList_v_778(GibCursor end_r_2524,
                                             GibCursor arg_1146_1366_1706)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_6600 = *(GibPackedTag *) arg_1146_1366_1706;
    GibCursor tmpcur_6601 = arg_1146_1366_1706 + 1;


  switch_6616:
    ;
    switch (tmpval_6600) {

      case 0:
        {
            GibCursor jump_3183 = arg_1146_1366_1706 + 1;

            return (GibCursorGibCursorProd) {end_r_2524, jump_3183};
            break;
        }

      case 1:
        {
            GibInt tmpval_6602 = *(GibInt *) tmpcur_6601;
            GibCursor tmpcur_6603 = tmpcur_6601 + sizeof(GibInt);
            GibCursorGibCursorProd tmp_struct_141 =
                                    _traverse_PList_v_778(end_r_2524, tmpcur_6603);
            GibCursor pvrtmp_6604 = tmp_struct_141.field0;
            GibCursor pvrtmp_6605 = tmp_struct_141.field1;

            return (GibCursorGibCursorProd) {pvrtmp_6604, pvrtmp_6605};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_143 = *(uintptr_t *) tmpcur_6601;
            GibCursor tmpcur_6606 = GIB_UNTAG(tagged_tmpcur_143);
            GibCursor tmpaftercur_6607 = tmpcur_6601 + 8;
            uint16_t tmptag_6608 = GIB_GET_TAG(tagged_tmpcur_143);
            GibCursor end_from_tagged_indr_3345 = tmpcur_6606 + tmptag_6608;
            GibCursor jump_3347 = tmpcur_6601 + 8;
            GibCursorGibCursorProd tmp_struct_142 =
                                    _traverse_PList_v_778(end_from_tagged_indr_3345, tmpcur_6606);
            GibCursor pvrtmp_6609 = tmp_struct_142.field0;
            GibCursor pvrtmp_6610 = tmp_struct_142.field1;

            return (GibCursorGibCursorProd) {end_r_2524, jump_3347};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_145 = *(uintptr_t *) tmpcur_6601;
            GibCursor tmpcur_6611 = GIB_UNTAG(tagged_tmpcur_145);
            GibCursor tmpaftercur_6612 = tmpcur_6601 + 8;
            uint16_t tmptag_6613 = GIB_GET_TAG(tagged_tmpcur_145);
            GibCursor end_from_tagged_indr_3345 = tmpcur_6611 + tmptag_6613;
            GibCursorGibCursorProd tmp_struct_144 =
                                    _traverse_PList_v_778(end_from_tagged_indr_3345, tmpcur_6611);
            GibCursor pvrtmp_6614 = tmp_struct_144.field0;
            GibCursor pvrtmp_6615 = tmp_struct_144.field1;

            return (GibCursorGibCursorProd) {pvrtmp_6614, pvrtmp_6615};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6600");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_PList_v_778(GibCursor end_r_2526,
                                          GibCursor arg_1151_1370_1710)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_6617 = *(GibPackedTag *) arg_1151_1370_1710;
    GibCursor tmpcur_6618 = arg_1151_1370_1710 + 1;


  switch_6633:
    ;
    switch (tmpval_6617) {

      case 0:
        {
            GibCursor jump_3188 = arg_1151_1370_1710 + 1;
            unsigned char wildcard_1152_1371_1711 = gib_print_symbol(5737);
            unsigned char wildcard_1153_1372_1712 = gib_print_symbol(5734);

            return (GibCursorGibCursorProd) {end_r_2526, jump_3188};
            break;
        }

      case 1:
        {
            GibInt tmpval_6619 = *(GibInt *) tmpcur_6618;
            GibCursor tmpcur_6620 = tmpcur_6618 + sizeof(GibInt);
            unsigned char wildcard_1158_1375_1715 = gib_print_symbol(5740);
            unsigned char wildcard_1163_1376_1716 = gib_print_symbol(5743);
            unsigned char y_1156_1377_1717 = printf("%ld", tmpval_6619);
            unsigned char wildcard_1162_1378_1718 = gib_print_symbol(5743);
            unsigned char y_1156_1379_1719 = gib_print_symbol(5743);
            unsigned char wildcard_1161_1380_1720 = gib_print_symbol(5743);
            GibCursorGibCursorProd tmp_struct_146 =
                                    _print_PList_v_778(end_r_2526, tmpcur_6620);
            GibCursor pvrtmp_6621 = tmp_struct_146.field0;
            GibCursor pvrtmp_6622 = tmp_struct_146.field1;
            unsigned char wildcard_1160_1382_1722 = gib_print_symbol(5743);
            unsigned char y_1157_1383_1723 = gib_print_symbol(5743);
            unsigned char wildcard_1159_1384_1724 = gib_print_symbol(5734);

            return (GibCursorGibCursorProd) {pvrtmp_6621, pvrtmp_6622};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_148 = *(uintptr_t *) tmpcur_6618;
            GibCursor tmpcur_6623 = GIB_UNTAG(tagged_tmpcur_148);
            GibCursor tmpaftercur_6624 = tmpcur_6618 + 8;
            uint16_t tmptag_6625 = GIB_GET_TAG(tagged_tmpcur_148);
            GibCursor end_from_tagged_indr_3351 = tmpcur_6623 + tmptag_6625;
            GibCursor jump_3353 = tmpcur_6618 + 8;
            unsigned char wildcard_3356 = gib_print_symbol(5742);
            GibCursorGibCursorProd tmp_struct_147 =
                                    _print_PList_v_778(end_from_tagged_indr_3351, tmpcur_6623);
            GibCursor pvrtmp_6626 = tmp_struct_147.field0;
            GibCursor pvrtmp_6627 = tmp_struct_147.field1;

            return (GibCursorGibCursorProd) {end_r_2526, jump_3353};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_150 = *(uintptr_t *) tmpcur_6618;
            GibCursor tmpcur_6628 = GIB_UNTAG(tagged_tmpcur_150);
            GibCursor tmpaftercur_6629 = tmpcur_6618 + 8;
            uint16_t tmptag_6630 = GIB_GET_TAG(tagged_tmpcur_150);
            GibCursor end_from_tagged_indr_3351 = tmpcur_6628 + tmptag_6630;
            unsigned char wildcard_3356 = gib_print_symbol(5741);
            GibCursorGibCursorProd tmp_struct_149 =
                                    _print_PList_v_778(end_from_tagged_indr_3351, tmpcur_6628);
            GibCursor pvrtmp_6631 = tmp_struct_149.field0;
            GibCursor pvrtmp_6632 = tmp_struct_149.field1;

            return (GibCursorGibCursorProd) {pvrtmp_6631, pvrtmp_6632};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6617");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_PList_v_780(GibCursor end_r_2529,
                                                                    GibCursor end_r_2530,
                                                                    GibCursor loc_2528,
                                                                    GibCursor arg_1164_1385_1725)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2528 + 26 > end_r_2530) {
        gib_grow_region(&loc_2528, &end_r_2530);
    }

    GibPackedTag tmpval_6634 = *(GibPackedTag *) arg_1164_1385_1725;
    GibCursor tmpcur_6635 = arg_1164_1385_1725 + 1;


  switch_6685:
    ;
    switch (tmpval_6634) {

      case 0:
        {
            GibCursor jump_3193 = arg_1164_1385_1725 + 1;

            *(GibPackedTag *) loc_2528 = 0;

            GibCursor writetag_4633 = loc_2528 + 1;
            GibCursor after_tag_4634 = loc_2528 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2529,
                                                                        end_r_2530,
                                                                        jump_3193,
                                                                        loc_2528,
                                                                        after_tag_4634};
            break;
        }

      case 1:
        {
            GibInt tmpval_6640 = *(GibInt *) tmpcur_6635;
            GibCursor tmpcur_6641 = tmpcur_6635 + sizeof(GibInt);
            GibInt tmpval_6642 = *(GibInt *) tmpcur_6641;
            GibCursor tmpcur_6643 = tmpcur_6641 + sizeof(GibInt);
            GibCursor loc_2834 = loc_2528 + 17;

            *(GibPackedTag *) loc_2528 = 1;

            GibCursor writetag_4646 = loc_2528 + 1;
            GibCursor after_tag_4647 = loc_2528 + 1;

            *(GibInt *) after_tag_4647 = tmpval_6640;

            GibCursor writecur_4651 = after_tag_4647 + sizeof(GibInt);

            *(GibInt *) writecur_4651 = tmpval_6642;

            GibCursor writecur_4652 = writecur_4651 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_151 =
                                                               _copy_PList_v_780(end_r_2529, end_r_2530, loc_2834, tmpcur_6643);
            GibCursor pvrtmp_6644 = tmp_struct_151.field0;
            GibCursor pvrtmp_6645 = tmp_struct_151.field1;
            GibCursor pvrtmp_6646 = tmp_struct_151.field2;
            GibCursor pvrtmp_6647 = tmp_struct_151.field3;
            GibCursor pvrtmp_6648 = tmp_struct_151.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6644,
                                                                        pvrtmp_6645,
                                                                        pvrtmp_6646,
                                                                        loc_2528,
                                                                        pvrtmp_6648};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_153 = *(uintptr_t *) tmpcur_6635;
            GibCursor tmpcur_6657 = GIB_UNTAG(tagged_tmpcur_153);
            GibCursor tmpaftercur_6658 = tmpcur_6635 + 8;
            uint16_t tmptag_6659 = GIB_GET_TAG(tagged_tmpcur_153);
            GibCursor end_from_tagged_indr_3357 = tmpcur_6657 + tmptag_6659;
            GibCursor jump_3359 = tmpcur_6635 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_152 =
                                                               _copy_PList_v_780(end_from_tagged_indr_3357, end_r_2530, loc_2528, tmpcur_6657);
            GibCursor pvrtmp_6660 = tmp_struct_152.field0;
            GibCursor pvrtmp_6661 = tmp_struct_152.field1;
            GibCursor pvrtmp_6662 = tmp_struct_152.field2;
            GibCursor pvrtmp_6663 = tmp_struct_152.field3;
            GibCursor pvrtmp_6664 = tmp_struct_152.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2529,
                                                                        pvrtmp_6661,
                                                                        jump_3359,
                                                                        pvrtmp_6663,
                                                                        pvrtmp_6664};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_155 = *(uintptr_t *) tmpcur_6635;
            GibCursor tmpcur_6671 = GIB_UNTAG(tagged_tmpcur_155);
            GibCursor tmpaftercur_6672 = tmpcur_6635 + 8;
            uint16_t tmptag_6673 = GIB_GET_TAG(tagged_tmpcur_155);
            GibCursor end_from_tagged_indr_3357 = tmpcur_6671 + tmptag_6673;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_154 =
                                                               _copy_PList_v_780(end_from_tagged_indr_3357, end_r_2530, loc_2528, tmpcur_6671);
            GibCursor pvrtmp_6674 = tmp_struct_154.field0;
            GibCursor pvrtmp_6675 = tmp_struct_154.field1;
            GibCursor pvrtmp_6676 = tmp_struct_154.field2;
            GibCursor pvrtmp_6677 = tmp_struct_154.field3;
            GibCursor pvrtmp_6678 = tmp_struct_154.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6674,
                                                                        pvrtmp_6675,
                                                                        pvrtmp_6676,
                                                                        pvrtmp_6677,
                                                                        pvrtmp_6678};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6634");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_PList_v_780(GibCursor end_r_2533,
                                                                                 GibCursor end_r_2534,
                                                                                 GibCursor loc_2532,
                                                                                 GibCursor arg_1171_1392_1732)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_6686 = *(GibPackedTag *) arg_1171_1392_1732;
    GibCursor tmpcur_6687 = arg_1171_1392_1732 + 1;


  switch_6737:
    ;
    switch (tmpval_6686) {

      case 0:
        {
            GibCursor jump_3199 = arg_1171_1392_1732 + 1;

            *(GibPackedTag *) loc_2532 = 0;

            GibCursor writetag_4667 = loc_2532 + 1;
            GibCursor after_tag_4668 = loc_2532 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2533,
                                                                        end_r_2534,
                                                                        jump_3199,
                                                                        loc_2532,
                                                                        after_tag_4668};
            break;
        }

      case 1:
        {
            GibInt tmpval_6692 = *(GibInt *) tmpcur_6687;
            GibCursor tmpcur_6693 = tmpcur_6687 + sizeof(GibInt);
            GibInt tmpval_6694 = *(GibInt *) tmpcur_6693;
            GibCursor tmpcur_6695 = tmpcur_6693 + sizeof(GibInt);
            GibCursor loc_2851 = loc_2532 + 17;

            *(GibPackedTag *) loc_2532 = 1;

            GibCursor writetag_4680 = loc_2532 + 1;
            GibCursor after_tag_4681 = loc_2532 + 1;

            *(GibInt *) after_tag_4681 = tmpval_6692;

            GibCursor writecur_4685 = after_tag_4681 + sizeof(GibInt);

            *(GibInt *) writecur_4685 = tmpval_6694;

            GibCursor writecur_4686 = writecur_4685 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_159 =
                                                               _copy_without_ptrs_PList_v_780(end_r_2533, end_r_2534, loc_2851, tmpcur_6695);
            GibCursor pvrtmp_6696 = tmp_struct_159.field0;
            GibCursor pvrtmp_6697 = tmp_struct_159.field1;
            GibCursor pvrtmp_6698 = tmp_struct_159.field2;
            GibCursor pvrtmp_6699 = tmp_struct_159.field3;
            GibCursor pvrtmp_6700 = tmp_struct_159.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6696,
                                                                        pvrtmp_6697,
                                                                        pvrtmp_6698,
                                                                        loc_2532,
                                                                        pvrtmp_6700};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_161 = *(uintptr_t *) tmpcur_6687;
            GibCursor tmpcur_6709 = GIB_UNTAG(tagged_tmpcur_161);
            GibCursor tmpaftercur_6710 = tmpcur_6687 + 8;
            uint16_t tmptag_6711 = GIB_GET_TAG(tagged_tmpcur_161);
            GibCursor end_from_tagged_indr_3363 = tmpcur_6709 + tmptag_6711;
            GibCursor jump_3365 = tmpcur_6687 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_160 =
                                                               _copy_without_ptrs_PList_v_780(end_from_tagged_indr_3363, end_r_2534, loc_2532, tmpcur_6709);
            GibCursor pvrtmp_6712 = tmp_struct_160.field0;
            GibCursor pvrtmp_6713 = tmp_struct_160.field1;
            GibCursor pvrtmp_6714 = tmp_struct_160.field2;
            GibCursor pvrtmp_6715 = tmp_struct_160.field3;
            GibCursor pvrtmp_6716 = tmp_struct_160.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2533,
                                                                        pvrtmp_6713,
                                                                        jump_3365,
                                                                        pvrtmp_6715,
                                                                        pvrtmp_6716};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_163 = *(uintptr_t *) tmpcur_6687;
            GibCursor tmpcur_6723 = GIB_UNTAG(tagged_tmpcur_163);
            GibCursor tmpaftercur_6724 = tmpcur_6687 + 8;
            uint16_t tmptag_6725 = GIB_GET_TAG(tagged_tmpcur_163);
            GibCursor end_from_tagged_indr_3363 = tmpcur_6723 + tmptag_6725;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_162 =
                                                               _copy_without_ptrs_PList_v_780(end_from_tagged_indr_3363, end_r_2534, loc_2532, tmpcur_6723);
            GibCursor pvrtmp_6726 = tmp_struct_162.field0;
            GibCursor pvrtmp_6727 = tmp_struct_162.field1;
            GibCursor pvrtmp_6728 = tmp_struct_162.field2;
            GibCursor pvrtmp_6729 = tmp_struct_162.field3;
            GibCursor pvrtmp_6730 = tmp_struct_162.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6726,
                                                                        pvrtmp_6727,
                                                                        pvrtmp_6728,
                                                                        pvrtmp_6729,
                                                                        pvrtmp_6730};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6686");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_PList_v_780(GibCursor end_r_2536,
                                             GibCursor arg_1178_1399_1739)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_6738 = *(GibPackedTag *) arg_1178_1399_1739;
    GibCursor tmpcur_6739 = arg_1178_1399_1739 + 1;


  switch_6756:
    ;
    switch (tmpval_6738) {

      case 0:
        {
            GibCursor jump_3205 = arg_1178_1399_1739 + 1;

            return (GibCursorGibCursorProd) {end_r_2536, jump_3205};
            break;
        }

      case 1:
        {
            GibInt tmpval_6740 = *(GibInt *) tmpcur_6739;
            GibCursor tmpcur_6741 = tmpcur_6739 + sizeof(GibInt);
            GibInt tmpval_6742 = *(GibInt *) tmpcur_6741;
            GibCursor tmpcur_6743 = tmpcur_6741 + sizeof(GibInt);
            GibCursorGibCursorProd tmp_struct_164 =
                                    _traverse_PList_v_780(end_r_2536, tmpcur_6743);
            GibCursor pvrtmp_6744 = tmp_struct_164.field0;
            GibCursor pvrtmp_6745 = tmp_struct_164.field1;

            return (GibCursorGibCursorProd) {pvrtmp_6744, pvrtmp_6745};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_166 = *(uintptr_t *) tmpcur_6739;
            GibCursor tmpcur_6746 = GIB_UNTAG(tagged_tmpcur_166);
            GibCursor tmpaftercur_6747 = tmpcur_6739 + 8;
            uint16_t tmptag_6748 = GIB_GET_TAG(tagged_tmpcur_166);
            GibCursor end_from_tagged_indr_3369 = tmpcur_6746 + tmptag_6748;
            GibCursor jump_3371 = tmpcur_6739 + 8;
            GibCursorGibCursorProd tmp_struct_165 =
                                    _traverse_PList_v_780(end_from_tagged_indr_3369, tmpcur_6746);
            GibCursor pvrtmp_6749 = tmp_struct_165.field0;
            GibCursor pvrtmp_6750 = tmp_struct_165.field1;

            return (GibCursorGibCursorProd) {end_r_2536, jump_3371};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_168 = *(uintptr_t *) tmpcur_6739;
            GibCursor tmpcur_6751 = GIB_UNTAG(tagged_tmpcur_168);
            GibCursor tmpaftercur_6752 = tmpcur_6739 + 8;
            uint16_t tmptag_6753 = GIB_GET_TAG(tagged_tmpcur_168);
            GibCursor end_from_tagged_indr_3369 = tmpcur_6751 + tmptag_6753;
            GibCursorGibCursorProd tmp_struct_167 =
                                    _traverse_PList_v_780(end_from_tagged_indr_3369, tmpcur_6751);
            GibCursor pvrtmp_6754 = tmp_struct_167.field0;
            GibCursor pvrtmp_6755 = tmp_struct_167.field1;

            return (GibCursorGibCursorProd) {pvrtmp_6754, pvrtmp_6755};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6738");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_PList_v_780(GibCursor end_r_2538,
                                          GibCursor arg_1185_1404_1744)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_6757 = *(GibPackedTag *) arg_1185_1404_1744;
    GibCursor tmpcur_6758 = arg_1185_1404_1744 + 1;


  switch_6775:
    ;
    switch (tmpval_6757) {

      case 0:
        {
            GibCursor jump_3211 = arg_1185_1404_1744 + 1;
            unsigned char wildcard_1186_1405_1745 = gib_print_symbol(5736);
            unsigned char wildcard_1187_1406_1746 = gib_print_symbol(5734);

            return (GibCursorGibCursorProd) {end_r_2538, jump_3211};
            break;
        }

      case 1:
        {
            GibInt tmpval_6759 = *(GibInt *) tmpcur_6758;
            GibCursor tmpcur_6760 = tmpcur_6758 + sizeof(GibInt);
            GibInt tmpval_6761 = *(GibInt *) tmpcur_6760;
            GibCursor tmpcur_6762 = tmpcur_6760 + sizeof(GibInt);
            unsigned char wildcard_1194_1410_1750 = gib_print_symbol(5739);
            unsigned char wildcard_1201_1411_1751 = gib_print_symbol(5743);
            unsigned char y_1191_1412_1752 = printf("%ld", tmpval_6759);
            unsigned char wildcard_1200_1413_1753 = gib_print_symbol(5743);
            unsigned char y_1191_1414_1754 = gib_print_symbol(5743);
            unsigned char wildcard_1199_1415_1755 = gib_print_symbol(5743);
            unsigned char y_1192_1416_1756 = printf("%ld", tmpval_6761);
            unsigned char wildcard_1198_1417_1757 = gib_print_symbol(5743);
            unsigned char y_1192_1418_1758 = gib_print_symbol(5743);
            unsigned char wildcard_1197_1419_1759 = gib_print_symbol(5743);
            GibCursorGibCursorProd tmp_struct_169 =
                                    _print_PList_v_780(end_r_2538, tmpcur_6762);
            GibCursor pvrtmp_6763 = tmp_struct_169.field0;
            GibCursor pvrtmp_6764 = tmp_struct_169.field1;
            unsigned char wildcard_1196_1421_1761 = gib_print_symbol(5743);
            unsigned char y_1193_1422_1762 = gib_print_symbol(5743);
            unsigned char wildcard_1195_1423_1763 = gib_print_symbol(5734);

            return (GibCursorGibCursorProd) {pvrtmp_6763, pvrtmp_6764};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_171 = *(uintptr_t *) tmpcur_6758;
            GibCursor tmpcur_6765 = GIB_UNTAG(tagged_tmpcur_171);
            GibCursor tmpaftercur_6766 = tmpcur_6758 + 8;
            uint16_t tmptag_6767 = GIB_GET_TAG(tagged_tmpcur_171);
            GibCursor end_from_tagged_indr_3375 = tmpcur_6765 + tmptag_6767;
            GibCursor jump_3377 = tmpcur_6758 + 8;
            unsigned char wildcard_3380 = gib_print_symbol(5742);
            GibCursorGibCursorProd tmp_struct_170 =
                                    _print_PList_v_780(end_from_tagged_indr_3375, tmpcur_6765);
            GibCursor pvrtmp_6768 = tmp_struct_170.field0;
            GibCursor pvrtmp_6769 = tmp_struct_170.field1;

            return (GibCursorGibCursorProd) {end_r_2538, jump_3377};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_173 = *(uintptr_t *) tmpcur_6758;
            GibCursor tmpcur_6770 = GIB_UNTAG(tagged_tmpcur_173);
            GibCursor tmpaftercur_6771 = tmpcur_6758 + 8;
            uint16_t tmptag_6772 = GIB_GET_TAG(tagged_tmpcur_173);
            GibCursor end_from_tagged_indr_3375 = tmpcur_6770 + tmptag_6772;
            unsigned char wildcard_3380 = gib_print_symbol(5741);
            GibCursorGibCursorProd tmp_struct_172 =
                                    _print_PList_v_780(end_from_tagged_indr_3375, tmpcur_6770);
            GibCursor pvrtmp_6773 = tmp_struct_172.field0;
            GibCursor pvrtmp_6774 = tmp_struct_172.field1;

            return (GibCursorGibCursorProd) {pvrtmp_6773, pvrtmp_6774};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6757");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_Maybe_v_788(GibCursor end_r_2541,
                                                                    GibCursor end_r_2542,
                                                                    GibCursor loc_2540,
                                                                    GibCursor arg_1202_1424_1764)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2540 + 18 > end_r_2542) {
        gib_grow_region(&loc_2540, &end_r_2542);
    }

    GibPackedTag tmpval_6776 = *(GibPackedTag *) arg_1202_1424_1764;
    GibCursor tmpcur_6777 = arg_1202_1424_1764 + 1;


  switch_6816:
    ;
    switch (tmpval_6776) {

      case 0:
        {
            GibInt tmpval_6778 = *(GibInt *) tmpcur_6777;
            GibCursor tmpcur_6779 = tmpcur_6777 + sizeof(GibInt);
            GibCursor jump_3217 = tmpcur_6777 + 8;

            *(GibPackedTag *) loc_2540 = 0;

            GibCursor writetag_4730 = loc_2540 + 1;
            GibCursor after_tag_4731 = loc_2540 + 1;

            *(GibInt *) after_tag_4731 = tmpval_6778;

            GibCursor writecur_4735 = after_tag_4731 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2541,
                                                                        end_r_2542,
                                                                        jump_3217,
                                                                        loc_2540,
                                                                        writecur_4735};
            break;
        }

      case 1:
        {
            GibCursor jump_3219 = arg_1202_1424_1764 + 1;

            *(GibPackedTag *) loc_2540 = 1;

            GibCursor writetag_4739 = loc_2540 + 1;
            GibCursor after_tag_4740 = loc_2540 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2541,
                                                                        end_r_2542,
                                                                        jump_3219,
                                                                        loc_2540,
                                                                        after_tag_4740};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_175 = *(uintptr_t *) tmpcur_6777;
            GibCursor tmpcur_6788 = GIB_UNTAG(tagged_tmpcur_175);
            GibCursor tmpaftercur_6789 = tmpcur_6777 + 8;
            uint16_t tmptag_6790 = GIB_GET_TAG(tagged_tmpcur_175);
            GibCursor end_from_tagged_indr_3381 = tmpcur_6788 + tmptag_6790;
            GibCursor jump_3383 = tmpcur_6777 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_174 =
                                                               _copy_Maybe_v_788(end_from_tagged_indr_3381, end_r_2542, loc_2540, tmpcur_6788);
            GibCursor pvrtmp_6791 = tmp_struct_174.field0;
            GibCursor pvrtmp_6792 = tmp_struct_174.field1;
            GibCursor pvrtmp_6793 = tmp_struct_174.field2;
            GibCursor pvrtmp_6794 = tmp_struct_174.field3;
            GibCursor pvrtmp_6795 = tmp_struct_174.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2541,
                                                                        pvrtmp_6792,
                                                                        jump_3383,
                                                                        pvrtmp_6794,
                                                                        pvrtmp_6795};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_177 = *(uintptr_t *) tmpcur_6777;
            GibCursor tmpcur_6802 = GIB_UNTAG(tagged_tmpcur_177);
            GibCursor tmpaftercur_6803 = tmpcur_6777 + 8;
            uint16_t tmptag_6804 = GIB_GET_TAG(tagged_tmpcur_177);
            GibCursor end_from_tagged_indr_3381 = tmpcur_6802 + tmptag_6804;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_176 =
                                                               _copy_Maybe_v_788(end_from_tagged_indr_3381, end_r_2542, loc_2540, tmpcur_6802);
            GibCursor pvrtmp_6805 = tmp_struct_176.field0;
            GibCursor pvrtmp_6806 = tmp_struct_176.field1;
            GibCursor pvrtmp_6807 = tmp_struct_176.field2;
            GibCursor pvrtmp_6808 = tmp_struct_176.field3;
            GibCursor pvrtmp_6809 = tmp_struct_176.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6805,
                                                                        pvrtmp_6806,
                                                                        pvrtmp_6807,
                                                                        pvrtmp_6808,
                                                                        pvrtmp_6809};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6776");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_Maybe_v_788(GibCursor end_r_2545,
                                                                                 GibCursor end_r_2546,
                                                                                 GibCursor loc_2544,
                                                                                 GibCursor arg_1205_1427_1767)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_6817 = *(GibPackedTag *) arg_1205_1427_1767;
    GibCursor tmpcur_6818 = arg_1205_1427_1767 + 1;


  switch_6857:
    ;
    switch (tmpval_6817) {

      case 0:
        {
            GibInt tmpval_6819 = *(GibInt *) tmpcur_6818;
            GibCursor tmpcur_6820 = tmpcur_6818 + sizeof(GibInt);
            GibCursor jump_3221 = tmpcur_6818 + 8;

            *(GibPackedTag *) loc_2544 = 0;

            GibCursor writetag_4758 = loc_2544 + 1;
            GibCursor after_tag_4759 = loc_2544 + 1;

            *(GibInt *) after_tag_4759 = tmpval_6819;

            GibCursor writecur_4763 = after_tag_4759 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2545,
                                                                        end_r_2546,
                                                                        jump_3221,
                                                                        loc_2544,
                                                                        writecur_4763};
            break;
        }

      case 1:
        {
            GibCursor jump_3223 = arg_1205_1427_1767 + 1;

            *(GibPackedTag *) loc_2544 = 1;

            GibCursor writetag_4767 = loc_2544 + 1;
            GibCursor after_tag_4768 = loc_2544 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2545,
                                                                        end_r_2546,
                                                                        jump_3223,
                                                                        loc_2544,
                                                                        after_tag_4768};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_182 = *(uintptr_t *) tmpcur_6818;
            GibCursor tmpcur_6829 = GIB_UNTAG(tagged_tmpcur_182);
            GibCursor tmpaftercur_6830 = tmpcur_6818 + 8;
            uint16_t tmptag_6831 = GIB_GET_TAG(tagged_tmpcur_182);
            GibCursor end_from_tagged_indr_3387 = tmpcur_6829 + tmptag_6831;
            GibCursor jump_3389 = tmpcur_6818 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_181 =
                                                               _copy_without_ptrs_Maybe_v_788(end_from_tagged_indr_3387, end_r_2546, loc_2544, tmpcur_6829);
            GibCursor pvrtmp_6832 = tmp_struct_181.field0;
            GibCursor pvrtmp_6833 = tmp_struct_181.field1;
            GibCursor pvrtmp_6834 = tmp_struct_181.field2;
            GibCursor pvrtmp_6835 = tmp_struct_181.field3;
            GibCursor pvrtmp_6836 = tmp_struct_181.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2545,
                                                                        pvrtmp_6833,
                                                                        jump_3389,
                                                                        pvrtmp_6835,
                                                                        pvrtmp_6836};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_184 = *(uintptr_t *) tmpcur_6818;
            GibCursor tmpcur_6843 = GIB_UNTAG(tagged_tmpcur_184);
            GibCursor tmpaftercur_6844 = tmpcur_6818 + 8;
            uint16_t tmptag_6845 = GIB_GET_TAG(tagged_tmpcur_184);
            GibCursor end_from_tagged_indr_3387 = tmpcur_6843 + tmptag_6845;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_183 =
                                                               _copy_without_ptrs_Maybe_v_788(end_from_tagged_indr_3387, end_r_2546, loc_2544, tmpcur_6843);
            GibCursor pvrtmp_6846 = tmp_struct_183.field0;
            GibCursor pvrtmp_6847 = tmp_struct_183.field1;
            GibCursor pvrtmp_6848 = tmp_struct_183.field2;
            GibCursor pvrtmp_6849 = tmp_struct_183.field3;
            GibCursor pvrtmp_6850 = tmp_struct_183.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6846,
                                                                        pvrtmp_6847,
                                                                        pvrtmp_6848,
                                                                        pvrtmp_6849,
                                                                        pvrtmp_6850};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6817");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_Maybe_v_788(GibCursor end_r_2548,
                                             GibCursor arg_1208_1430_1770)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_6858 = *(GibPackedTag *) arg_1208_1430_1770;
    GibCursor tmpcur_6859 = arg_1208_1430_1770 + 1;


  switch_6872:
    ;
    switch (tmpval_6858) {

      case 0:
        {
            GibInt tmpval_6860 = *(GibInt *) tmpcur_6859;
            GibCursor tmpcur_6861 = tmpcur_6859 + sizeof(GibInt);
            GibCursor jump_3225 = tmpcur_6859 + 8;

            return (GibCursorGibCursorProd) {end_r_2548, jump_3225};
            break;
        }

      case 1:
        {
            GibCursor jump_3227 = arg_1208_1430_1770 + 1;

            return (GibCursorGibCursorProd) {end_r_2548, jump_3227};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_186 = *(uintptr_t *) tmpcur_6859;
            GibCursor tmpcur_6862 = GIB_UNTAG(tagged_tmpcur_186);
            GibCursor tmpaftercur_6863 = tmpcur_6859 + 8;
            uint16_t tmptag_6864 = GIB_GET_TAG(tagged_tmpcur_186);
            GibCursor end_from_tagged_indr_3393 = tmpcur_6862 + tmptag_6864;
            GibCursor jump_3395 = tmpcur_6859 + 8;
            GibCursorGibCursorProd tmp_struct_185 =
                                    _traverse_Maybe_v_788(end_from_tagged_indr_3393, tmpcur_6862);
            GibCursor pvrtmp_6865 = tmp_struct_185.field0;
            GibCursor pvrtmp_6866 = tmp_struct_185.field1;

            return (GibCursorGibCursorProd) {end_r_2548, jump_3395};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_188 = *(uintptr_t *) tmpcur_6859;
            GibCursor tmpcur_6867 = GIB_UNTAG(tagged_tmpcur_188);
            GibCursor tmpaftercur_6868 = tmpcur_6859 + 8;
            uint16_t tmptag_6869 = GIB_GET_TAG(tagged_tmpcur_188);
            GibCursor end_from_tagged_indr_3393 = tmpcur_6867 + tmptag_6869;
            GibCursorGibCursorProd tmp_struct_187 =
                                    _traverse_Maybe_v_788(end_from_tagged_indr_3393, tmpcur_6867);
            GibCursor pvrtmp_6870 = tmp_struct_187.field0;
            GibCursor pvrtmp_6871 = tmp_struct_187.field1;

            return (GibCursorGibCursorProd) {pvrtmp_6870, pvrtmp_6871};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6858");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_Maybe_v_788(GibCursor end_r_2550,
                                          GibCursor arg_1211_1432_1772)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_6873 = *(GibPackedTag *) arg_1211_1432_1772;
    GibCursor tmpcur_6874 = arg_1211_1432_1772 + 1;


  switch_6887:
    ;
    switch (tmpval_6873) {

      case 0:
        {
            GibInt tmpval_6875 = *(GibInt *) tmpcur_6874;
            GibCursor tmpcur_6876 = tmpcur_6874 + sizeof(GibInt);
            GibCursor jump_3229 = tmpcur_6874 + 8;
            unsigned char wildcard_1214_1434_1774 = gib_print_symbol(5738);
            unsigned char wildcard_1217_1435_1775 = gib_print_symbol(5743);
            unsigned char y_1213_1436_1776 = printf("%ld", tmpval_6875);
            unsigned char wildcard_1216_1437_1777 = gib_print_symbol(5743);
            unsigned char y_1213_1438_1778 = gib_print_symbol(5743);
            unsigned char wildcard_1215_1439_1779 = gib_print_symbol(5734);

            return (GibCursorGibCursorProd) {end_r_2550, jump_3229};
            break;
        }

      case 1:
        {
            GibCursor jump_3231 = arg_1211_1432_1772 + 1;
            unsigned char wildcard_1218_1440_1780 = gib_print_symbol(5735);
            unsigned char wildcard_1219_1441_1781 = gib_print_symbol(5734);

            return (GibCursorGibCursorProd) {end_r_2550, jump_3231};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_190 = *(uintptr_t *) tmpcur_6874;
            GibCursor tmpcur_6877 = GIB_UNTAG(tagged_tmpcur_190);
            GibCursor tmpaftercur_6878 = tmpcur_6874 + 8;
            uint16_t tmptag_6879 = GIB_GET_TAG(tagged_tmpcur_190);
            GibCursor end_from_tagged_indr_3399 = tmpcur_6877 + tmptag_6879;
            GibCursor jump_3401 = tmpcur_6874 + 8;
            unsigned char wildcard_3404 = gib_print_symbol(5742);
            GibCursorGibCursorProd tmp_struct_189 =
                                    _print_Maybe_v_788(end_from_tagged_indr_3399, tmpcur_6877);
            GibCursor pvrtmp_6880 = tmp_struct_189.field0;
            GibCursor pvrtmp_6881 = tmp_struct_189.field1;

            return (GibCursorGibCursorProd) {end_r_2550, jump_3401};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_192 = *(uintptr_t *) tmpcur_6874;
            GibCursor tmpcur_6882 = GIB_UNTAG(tagged_tmpcur_192);
            GibCursor tmpaftercur_6883 = tmpcur_6874 + 8;
            uint16_t tmptag_6884 = GIB_GET_TAG(tagged_tmpcur_192);
            GibCursor end_from_tagged_indr_3399 = tmpcur_6882 + tmptag_6884;
            unsigned char wildcard_3404 = gib_print_symbol(5741);
            GibCursorGibCursorProd tmp_struct_191 =
                                    _print_Maybe_v_788(end_from_tagged_indr_3399, tmpcur_6882);
            GibCursor pvrtmp_6885 = tmp_struct_191.field0;
            GibCursor pvrtmp_6886 = tmp_struct_191.field1;

            return (GibCursorGibCursorProd) {pvrtmp_6885, pvrtmp_6886};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6873");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd caseFn_1220(GibCursor end_r_2556,
                                                                                GibCursor end_r_2557,
                                                                                GibCursor end_r_2558,
                                                                                GibCursor end_r_2559,
                                                                                GibCursor end_r_2560,
                                                                                GibCursor loc_2555,
                                                                                GibInt m_141_1221_1442_1782,
                                                                                GibInt n_142_1222_1443_1783,
                                                                                GibCursor xs_143_1223_1444_1784,
                                                                                GibCursor ys_144_1224_1445_1785,
                                                                                GibCursor zs_145_1225_1446_1786,
                                                                                GibCursor xs__147_1226_1447_1787,
                                                                                GibInt x_146_1227_1448_1788)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2555 + 18 > end_r_2560) {
        gib_grow_region(&loc_2555, &end_r_2560);
    }

    GibPackedTag tmpval_6888 = *(GibPackedTag *) xs__147_1226_1447_1787;
    GibCursor tmpcur_6889 = xs__147_1226_1447_1787 + 1;


  switch_7074:
    ;
    switch (tmpval_6888) {

      case 0:
        {
            GibCursorGibBoolProd tmp_struct_193 =
                                  elem_plist_782_1069(end_r_2557, x_146_1227_1448_1788, ys_144_1224_1445_1785);
            GibCursor pvrtmp_6890 = tmp_struct_193.field0;
            GibBool pvrtmp_6891 = tmp_struct_193.field1;

            if (pvrtmp_6891) {
                GibCursor loc_2899 = loc_2555 + 9;

                *(GibPackedTag *) loc_2555 = 1;

                GibCursor writetag_4812 = loc_2555 + 1;
                GibCursor after_tag_4813 = loc_2555 + 1;

                *(GibInt *) after_tag_4813 = x_146_1227_1448_1788;

                GibCursor writecur_4817 = after_tag_4813 + sizeof(GibInt);

                if (loc_2899 + 18 > end_r_2560) {
                    gib_grow_region(&loc_2899, &end_r_2560);
                }
                gib_indirection_barrier(loc_2899, end_r_2560,
                                        zs_145_1225_1446_1786, end_r_2558,
                                        PList_v_778_T);

                GibCursor end_4810 = loc_2899 + 9;

                return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2556,
                                                                                              pvrtmp_6890,
                                                                                              end_r_2558,
                                                                                              end_r_2559,
                                                                                              end_r_2560,
                                                                                              loc_2555,
                                                                                              end_4810};
            } else {
                if (loc_2555 + 18 > end_r_2560) {
                    gib_grow_region(&loc_2555, &end_r_2560);
                }
                gib_indirection_barrier(loc_2555, end_r_2560,
                                        zs_145_1225_1446_1786, end_r_2558,
                                        PList_v_778_T);

                GibCursor end_4822 = loc_2555 + 9;

                return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2556,
                                                                                              pvrtmp_6890,
                                                                                              end_r_2558,
                                                                                              end_r_2559,
                                                                                              end_r_2560,
                                                                                              loc_2555,
                                                                                              end_4822};
            }
            break;
        }

      case 1:
        {
            GibInt tmpval_6902 = *(GibInt *) tmpcur_6889;
            GibCursor tmpcur_6903 = tmpcur_6889 + sizeof(GibInt);
            GibInt m2_150_1451_1793 = m_141_1221_1442_1782 / 2;

            gib_shadowstack_push(rstack, zs_145_1225_1446_1786, end_r_2558, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, ys_144_1224_1445_1785, end_r_2557, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, xs_143_1223_1444_1784, end_r_2556, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(wstack, loc_2555, end_r_2560, Stk,
                                 PList_v_778_T);

            GibChunk region_6904 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_3001 = region_6904.start;
            GibCursor end_r_3001 = region_6904.end;

            frame = gib_shadowstack_pop(wstack);
            loc_2555 = frame->ptr;
            end_r_2560 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            xs_143_1223_1444_1784 = frame->ptr;
            end_r_2556 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1224_1445_1785 = frame->ptr;
            end_r_2557 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1225_1446_1786 = frame->ptr;
            end_r_2558 = frame->endptr;

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_200 =
                                                      take_plist_783(end_r_2556, end_r_3001, r_3001, m2_150_1451_1793, xs_143_1223_1444_1784);
            GibCursor pvrtmp_6905 = tmp_struct_200.field0;
            GibCursor pvrtmp_6906 = tmp_struct_200.field1;
            GibCursor pvrtmp_6907 = tmp_struct_200.field2;
            GibCursor pvrtmp_6908 = tmp_struct_200.field3;

            gib_shadowstack_push(rstack, zs_145_1225_1446_1786, end_r_2558, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, ys_144_1224_1445_1785, end_r_2557, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6907, pvrtmp_6906, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, xs_143_1223_1444_1784, end_r_2556, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(wstack, loc_2555, end_r_2560, Stk,
                                 PList_v_778_T);

            GibChunk region_6913 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_3000 = region_6913.start;
            GibCursor end_r_3000 = region_6913.end;

            frame = gib_shadowstack_pop(wstack);
            loc_2555 = frame->ptr;
            end_r_2560 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            xs_143_1223_1444_1784 = frame->ptr;
            end_r_2556 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6907 = frame->ptr;
            pvrtmp_6906 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1224_1445_1785 = frame->ptr;
            end_r_2557 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1225_1446_1786 = frame->ptr;
            end_r_2558 = frame->endptr;

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_201 =
                                                      drop_plist_784(end_r_2556, end_r_3000, r_3000, m2_150_1451_1793, xs_143_1223_1444_1784);
            GibCursor pvrtmp_6914 = tmp_struct_201.field0;
            GibCursor pvrtmp_6915 = tmp_struct_201.field1;
            GibCursor pvrtmp_6916 = tmp_struct_201.field2;
            GibCursor pvrtmp_6917 = tmp_struct_201.field3;

            gib_shadowstack_push(rstack, zs_145_1225_1446_1786, end_r_2558, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, ys_144_1224_1445_1785, end_r_2557, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6907, pvrtmp_6906, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6916, pvrtmp_6915, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(wstack, loc_2555, end_r_2560, Stk,
                                 PList_v_778_T);

            GibChunk region_6922 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_2999 = region_6922.start;
            GibCursor end_r_2999 = region_6922.end;

            frame = gib_shadowstack_pop(wstack);
            loc_2555 = frame->ptr;
            end_r_2560 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6916 = frame->ptr;
            pvrtmp_6915 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6907 = frame->ptr;
            pvrtmp_6906 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1224_1445_1785 = frame->ptr;
            end_r_2557 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1225_1446_1786 = frame->ptr;
            end_r_2558 = frame->endptr;
            gib_shadowstack_push(rstack, zs_145_1225_1446_1786, end_r_2558, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, ys_144_1224_1445_1785, end_r_2557, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6907, pvrtmp_6906, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6916, pvrtmp_6915, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(wstack, loc_2555, end_r_2560, Stk,
                                 PList_v_778_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_202 =
             algb(pvrtmp_6906, end_r_2557, end_r_2999, r_2999, pvrtmp_6907, ys_144_1224_1445_1785);
            GibCursor pvrtmp_6923 = tmp_struct_202.field0;
            GibCursor pvrtmp_6924 = tmp_struct_202.field1;
            GibCursor pvrtmp_6925 = tmp_struct_202.field2;
            GibCursor pvrtmp_6926 = tmp_struct_202.field3;
            GibCursor pvrtmp_6927 = tmp_struct_202.field4;
            GibCursor pvrtmp_6928 = tmp_struct_202.field5;
            GibCursor pvrtmp_6929 = tmp_struct_202.field6;

            frame = gib_shadowstack_pop(wstack);
            loc_2555 = frame->ptr;
            end_r_2560 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6916 = frame->ptr;
            pvrtmp_6915 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6907 = frame->ptr;
            pvrtmp_6906 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1224_1445_1785 = frame->ptr;
            end_r_2557 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1225_1446_1786 = frame->ptr;
            end_r_2558 = frame->endptr;
            gib_shadowstack_push(rstack, zs_145_1225_1446_1786, end_r_2558, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, ys_144_1224_1445_1785, end_r_2557, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6907, pvrtmp_6906, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6916, pvrtmp_6915, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6928, pvrtmp_6925, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(wstack, loc_2555, end_r_2560, Stk,
                                 PList_v_778_T);

            GibChunk region_6934 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_2998 = region_6934.start;
            GibCursor end_r_2998 = region_6934.end;

            frame = gib_shadowstack_pop(wstack);
            loc_2555 = frame->ptr;
            end_r_2560 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6928 = frame->ptr;
            pvrtmp_6925 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6916 = frame->ptr;
            pvrtmp_6915 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6907 = frame->ptr;
            pvrtmp_6906 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1224_1445_1785 = frame->ptr;
            end_r_2557 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1225_1446_1786 = frame->ptr;
            end_r_2558 = frame->endptr;
            *(GibPackedTag *) r_2998 = 0;

            GibCursor writetag_4836 = r_2998 + 1;
            GibCursor after_tag_4837 = r_2998 + 1;

            gib_shadowstack_push(rstack, zs_145_1225_1446_1786, end_r_2558, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, ys_144_1224_1445_1785, end_r_2557, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6907, pvrtmp_6906, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6916, pvrtmp_6915, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6928, pvrtmp_6925, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, r_2998, end_r_2998, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(wstack, loc_2555, end_r_2560, Stk,
                                 PList_v_778_T);

            GibChunk region_6937 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_2997 = region_6937.start;
            GibCursor end_r_2997 = region_6937.end;

            frame = gib_shadowstack_pop(wstack);
            loc_2555 = frame->ptr;
            end_r_2560 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            r_2998 = frame->ptr;
            end_r_2998 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6928 = frame->ptr;
            pvrtmp_6925 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6916 = frame->ptr;
            pvrtmp_6915 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6907 = frame->ptr;
            pvrtmp_6906 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1224_1445_1785 = frame->ptr;
            end_r_2557 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1225_1446_1786 = frame->ptr;
            end_r_2558 = frame->endptr;
            gib_shadowstack_push(rstack, zs_145_1225_1446_1786, end_r_2558, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, ys_144_1224_1445_1785, end_r_2557, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6907, pvrtmp_6906, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6916, pvrtmp_6915, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6928, pvrtmp_6925, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(wstack, loc_2555, end_r_2560, Stk,
                                 PList_v_778_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_203 =
             reverse_plist_785(pvrtmp_6915, end_r_2998, end_r_2997, r_2997, pvrtmp_6916, r_2998);
            GibCursor pvrtmp_6938 = tmp_struct_203.field0;
            GibCursor pvrtmp_6939 = tmp_struct_203.field1;
            GibCursor pvrtmp_6940 = tmp_struct_203.field2;
            GibCursor pvrtmp_6941 = tmp_struct_203.field3;
            GibCursor pvrtmp_6942 = tmp_struct_203.field4;
            GibCursor pvrtmp_6943 = tmp_struct_203.field5;

            frame = gib_shadowstack_pop(wstack);
            loc_2555 = frame->ptr;
            end_r_2560 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6928 = frame->ptr;
            pvrtmp_6925 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6916 = frame->ptr;
            pvrtmp_6915 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6907 = frame->ptr;
            pvrtmp_6906 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1224_1445_1785 = frame->ptr;
            end_r_2557 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1225_1446_1786 = frame->ptr;
            end_r_2558 = frame->endptr;
            gib_shadowstack_push(rstack, zs_145_1225_1446_1786, end_r_2558, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, ys_144_1224_1445_1785, end_r_2557, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6907, pvrtmp_6906, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6916, pvrtmp_6915, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6928, pvrtmp_6925, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6942, pvrtmp_6940, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(wstack, loc_2555, end_r_2560, Stk,
                                 PList_v_778_T);

            GibChunk region_6948 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_2996 = region_6948.start;
            GibCursor end_r_2996 = region_6948.end;

            frame = gib_shadowstack_pop(wstack);
            loc_2555 = frame->ptr;
            end_r_2560 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6942 = frame->ptr;
            pvrtmp_6940 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6928 = frame->ptr;
            pvrtmp_6925 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6916 = frame->ptr;
            pvrtmp_6915 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6907 = frame->ptr;
            pvrtmp_6906 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1224_1445_1785 = frame->ptr;
            end_r_2557 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1225_1446_1786 = frame->ptr;
            end_r_2558 = frame->endptr;
            *(GibPackedTag *) r_2996 = 0;

            GibCursor writetag_4847 = r_2996 + 1;
            GibCursor after_tag_4848 = r_2996 + 1;

            gib_shadowstack_push(rstack, zs_145_1225_1446_1786, end_r_2558, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, ys_144_1224_1445_1785, end_r_2557, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6907, pvrtmp_6906, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6916, pvrtmp_6915, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6928, pvrtmp_6925, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6942, pvrtmp_6940, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, r_2996, end_r_2996, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(wstack, loc_2555, end_r_2560, Stk,
                                 PList_v_778_T);

            GibChunk region_6951 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_2995 = region_6951.start;
            GibCursor end_r_2995 = region_6951.end;

            frame = gib_shadowstack_pop(wstack);
            loc_2555 = frame->ptr;
            end_r_2560 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            r_2996 = frame->ptr;
            end_r_2996 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6942 = frame->ptr;
            pvrtmp_6940 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6928 = frame->ptr;
            pvrtmp_6925 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6916 = frame->ptr;
            pvrtmp_6915 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6907 = frame->ptr;
            pvrtmp_6906 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1224_1445_1785 = frame->ptr;
            end_r_2557 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1225_1446_1786 = frame->ptr;
            end_r_2558 = frame->endptr;
            gib_shadowstack_push(rstack, zs_145_1225_1446_1786, end_r_2558, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, ys_144_1224_1445_1785, end_r_2557, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6907, pvrtmp_6906, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6916, pvrtmp_6915, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6928, pvrtmp_6925, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6942, pvrtmp_6940, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(wstack, loc_2555, end_r_2560, Stk,
                                 PList_v_778_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_204 =
             reverse_plist_785(end_r_2557, end_r_2996, end_r_2995, r_2995, ys_144_1224_1445_1785, r_2996);
            GibCursor pvrtmp_6952 = tmp_struct_204.field0;
            GibCursor pvrtmp_6953 = tmp_struct_204.field1;
            GibCursor pvrtmp_6954 = tmp_struct_204.field2;
            GibCursor pvrtmp_6955 = tmp_struct_204.field3;
            GibCursor pvrtmp_6956 = tmp_struct_204.field4;
            GibCursor pvrtmp_6957 = tmp_struct_204.field5;

            frame = gib_shadowstack_pop(wstack);
            loc_2555 = frame->ptr;
            end_r_2560 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6942 = frame->ptr;
            pvrtmp_6940 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6928 = frame->ptr;
            pvrtmp_6925 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6916 = frame->ptr;
            pvrtmp_6915 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6907 = frame->ptr;
            pvrtmp_6906 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1224_1445_1785 = frame->ptr;
            end_r_2557 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1225_1446_1786 = frame->ptr;
            end_r_2558 = frame->endptr;
            gib_shadowstack_push(rstack, zs_145_1225_1446_1786, end_r_2558, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, ys_144_1224_1445_1785, end_r_2557, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6907, pvrtmp_6906, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6916, pvrtmp_6915, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6928, pvrtmp_6925, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6942, pvrtmp_6940, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6956, pvrtmp_6954, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(wstack, loc_2555, end_r_2560, Stk,
                                 PList_v_778_T);

            GibChunk region_6962 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_2994 = region_6962.start;
            GibCursor end_r_2994 = region_6962.end;

            frame = gib_shadowstack_pop(wstack);
            loc_2555 = frame->ptr;
            end_r_2560 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6956 = frame->ptr;
            pvrtmp_6954 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6942 = frame->ptr;
            pvrtmp_6940 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6928 = frame->ptr;
            pvrtmp_6925 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6916 = frame->ptr;
            pvrtmp_6915 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6907 = frame->ptr;
            pvrtmp_6906 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1224_1445_1785 = frame->ptr;
            end_r_2557 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1225_1446_1786 = frame->ptr;
            end_r_2558 = frame->endptr;
            gib_shadowstack_push(rstack, zs_145_1225_1446_1786, end_r_2558, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, ys_144_1224_1445_1785, end_r_2557, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6907, pvrtmp_6906, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6916, pvrtmp_6915, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6928, pvrtmp_6925, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(wstack, loc_2555, end_r_2560, Stk,
                                 PList_v_778_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_205 =
             algb(pvrtmp_6940, pvrtmp_6954, end_r_2994, r_2994, pvrtmp_6942, pvrtmp_6956);
            GibCursor pvrtmp_6963 = tmp_struct_205.field0;
            GibCursor pvrtmp_6964 = tmp_struct_205.field1;
            GibCursor pvrtmp_6965 = tmp_struct_205.field2;
            GibCursor pvrtmp_6966 = tmp_struct_205.field3;
            GibCursor pvrtmp_6967 = tmp_struct_205.field4;
            GibCursor pvrtmp_6968 = tmp_struct_205.field5;
            GibCursor pvrtmp_6969 = tmp_struct_205.field6;

            frame = gib_shadowstack_pop(wstack);
            loc_2555 = frame->ptr;
            end_r_2560 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6928 = frame->ptr;
            pvrtmp_6925 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6916 = frame->ptr;
            pvrtmp_6915 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6907 = frame->ptr;
            pvrtmp_6906 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1224_1445_1785 = frame->ptr;
            end_r_2557 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1225_1446_1786 = frame->ptr;
            end_r_2558 = frame->endptr;
            gib_shadowstack_push(rstack, zs_145_1225_1446_1786, end_r_2558, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, ys_144_1224_1445_1785, end_r_2557, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6907, pvrtmp_6906, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6916, pvrtmp_6915, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6928, pvrtmp_6925, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6968, pvrtmp_6965, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(wstack, loc_2555, end_r_2560, Stk,
                                 PList_v_778_T);

            GibChunk region_6974 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_2993 = region_6974.start;
            GibCursor end_r_2993 = region_6974.end;

            frame = gib_shadowstack_pop(wstack);
            loc_2555 = frame->ptr;
            end_r_2560 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6968 = frame->ptr;
            pvrtmp_6965 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6928 = frame->ptr;
            pvrtmp_6925 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6916 = frame->ptr;
            pvrtmp_6915 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6907 = frame->ptr;
            pvrtmp_6906 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1224_1445_1785 = frame->ptr;
            end_r_2557 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1225_1446_1786 = frame->ptr;
            end_r_2558 = frame->endptr;
            *(GibPackedTag *) r_2993 = 0;

            GibCursor writetag_4862 = r_2993 + 1;
            GibCursor after_tag_4863 = r_2993 + 1;

            gib_shadowstack_push(rstack, zs_145_1225_1446_1786, end_r_2558, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, ys_144_1224_1445_1785, end_r_2557, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6907, pvrtmp_6906, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6916, pvrtmp_6915, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6928, pvrtmp_6925, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6968, pvrtmp_6965, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, r_2993, end_r_2993, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(wstack, loc_2555, end_r_2560, Stk,
                                 PList_v_778_T);

            GibChunk region_6977 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_2992 = region_6977.start;
            GibCursor end_r_2992 = region_6977.end;

            frame = gib_shadowstack_pop(wstack);
            loc_2555 = frame->ptr;
            end_r_2560 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            r_2993 = frame->ptr;
            end_r_2993 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6968 = frame->ptr;
            pvrtmp_6965 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6928 = frame->ptr;
            pvrtmp_6925 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6916 = frame->ptr;
            pvrtmp_6915 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6907 = frame->ptr;
            pvrtmp_6906 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1224_1445_1785 = frame->ptr;
            end_r_2557 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1225_1446_1786 = frame->ptr;
            end_r_2558 = frame->endptr;
            gib_shadowstack_push(rstack, zs_145_1225_1446_1786, end_r_2558, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, ys_144_1224_1445_1785, end_r_2557, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6907, pvrtmp_6906, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6916, pvrtmp_6915, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6928, pvrtmp_6925, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(wstack, loc_2555, end_r_2560, Stk,
                                 PList_v_778_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_206 =
             reverse_plist_785(pvrtmp_6965, end_r_2993, end_r_2992, r_2992, pvrtmp_6968, r_2993);
            GibCursor pvrtmp_6978 = tmp_struct_206.field0;
            GibCursor pvrtmp_6979 = tmp_struct_206.field1;
            GibCursor pvrtmp_6980 = tmp_struct_206.field2;
            GibCursor pvrtmp_6981 = tmp_struct_206.field3;
            GibCursor pvrtmp_6982 = tmp_struct_206.field4;
            GibCursor pvrtmp_6983 = tmp_struct_206.field5;

            frame = gib_shadowstack_pop(wstack);
            loc_2555 = frame->ptr;
            end_r_2560 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6928 = frame->ptr;
            pvrtmp_6925 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6916 = frame->ptr;
            pvrtmp_6915 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6907 = frame->ptr;
            pvrtmp_6906 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1224_1445_1785 = frame->ptr;
            end_r_2557 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1225_1446_1786 = frame->ptr;
            end_r_2558 = frame->endptr;

            GibInt fltAppE_1538_1804 = 0 - 1;

            gib_shadowstack_push(rstack, zs_145_1225_1446_1786, end_r_2558, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, ys_144_1224_1445_1785, end_r_2557, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6907, pvrtmp_6906, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6916, pvrtmp_6915, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6928, pvrtmp_6925, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6982, pvrtmp_6980, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(wstack, loc_2555, end_r_2560, Stk,
                                 PList_v_778_T);

            GibChunk region_6988 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_2991 = region_6988.start;
            GibCursor end_r_2991 = region_6988.end;

            frame = gib_shadowstack_pop(wstack);
            loc_2555 = frame->ptr;
            end_r_2560 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6982 = frame->ptr;
            pvrtmp_6980 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6928 = frame->ptr;
            pvrtmp_6925 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6916 = frame->ptr;
            pvrtmp_6915 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6907 = frame->ptr;
            pvrtmp_6906 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1224_1445_1785 = frame->ptr;
            end_r_2557 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1225_1446_1786 = frame->ptr;
            end_r_2558 = frame->endptr;

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_207 =
                                                               zip_plist_786(pvrtmp_6925, pvrtmp_6980, end_r_2991, r_2991, pvrtmp_6928, pvrtmp_6982);
            GibCursor pvrtmp_6989 = tmp_struct_207.field0;
            GibCursor pvrtmp_6990 = tmp_struct_207.field1;
            GibCursor pvrtmp_6991 = tmp_struct_207.field2;
            GibCursor pvrtmp_6992 = tmp_struct_207.field3;
            GibCursor pvrtmp_6993 = tmp_struct_207.field4;
            GibCursorGibCursorGibIntProd tmp_struct_208 =
                                          findk(pvrtmp_6991, 0, 0, fltAppE_1538_1804, pvrtmp_6992);
            GibCursor pvrtmp_6998 = tmp_struct_208.field0;
            GibCursor pvrtmp_6999 = tmp_struct_208.field1;
            GibInt pvrtmp_7000 = tmp_struct_208.field2;
            GibInt fltAppE_1540_1807 = m_141_1221_1442_1782 - m2_150_1451_1793;
            GibInt fltAppE_1541_1808 = n_142_1222_1443_1783 - pvrtmp_7000;

            gib_shadowstack_push(rstack, zs_145_1225_1446_1786, end_r_2558, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, ys_144_1224_1445_1785, end_r_2557, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6907, pvrtmp_6906, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6916, pvrtmp_6915, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(wstack, loc_2555, end_r_2560, Stk,
                                 PList_v_778_T);

            GibChunk region_7001 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_2990 = region_7001.start;
            GibCursor end_r_2990 = region_7001.end;

            frame = gib_shadowstack_pop(wstack);
            loc_2555 = frame->ptr;
            end_r_2560 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6916 = frame->ptr;
            pvrtmp_6915 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6907 = frame->ptr;
            pvrtmp_6906 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1224_1445_1785 = frame->ptr;
            end_r_2557 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1225_1446_1786 = frame->ptr;
            end_r_2558 = frame->endptr;

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_209 =
                                                      drop_plist_784(end_r_2557, end_r_2990, r_2990, pvrtmp_7000, ys_144_1224_1445_1785);
            GibCursor pvrtmp_7002 = tmp_struct_209.field0;
            GibCursor pvrtmp_7003 = tmp_struct_209.field1;
            GibCursor pvrtmp_7004 = tmp_struct_209.field2;
            GibCursor pvrtmp_7005 = tmp_struct_209.field3;

            gib_shadowstack_push(rstack, zs_145_1225_1446_1786, end_r_2558, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, ys_144_1224_1445_1785, end_r_2557, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6907, pvrtmp_6906, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6916, pvrtmp_6915, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_7004, pvrtmp_7003, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(wstack, loc_2555, end_r_2560, Stk,
                                 PList_v_778_T);

            GibChunk region_7010 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_2989 = region_7010.start;
            GibCursor end_r_2989 = region_7010.end;

            frame = gib_shadowstack_pop(wstack);
            loc_2555 = frame->ptr;
            end_r_2560 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_7004 = frame->ptr;
            pvrtmp_7003 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6916 = frame->ptr;
            pvrtmp_6915 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6907 = frame->ptr;
            pvrtmp_6906 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1224_1445_1785 = frame->ptr;
            end_r_2557 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1225_1446_1786 = frame->ptr;
            end_r_2558 = frame->endptr;
            gib_shadowstack_push(rstack, ys_144_1224_1445_1785, end_r_2557, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6907, pvrtmp_6906, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(wstack, loc_2555, end_r_2560, Stk,
                                 PList_v_778_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_210 =
             algc(pvrtmp_6915, pvrtmp_7003, end_r_2558, end_r_2989, r_2989, fltAppE_1540_1807, fltAppE_1541_1808, pvrtmp_6916, pvrtmp_7004, zs_145_1225_1446_1786);
            GibCursor pvrtmp_7011 = tmp_struct_210.field0;
            GibCursor pvrtmp_7012 = tmp_struct_210.field1;
            GibCursor pvrtmp_7013 = tmp_struct_210.field2;
            GibCursor pvrtmp_7014 = tmp_struct_210.field3;
            GibCursor pvrtmp_7015 = tmp_struct_210.field4;
            GibCursor pvrtmp_7016 = tmp_struct_210.field5;

            frame = gib_shadowstack_pop(wstack);
            loc_2555 = frame->ptr;
            end_r_2560 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6907 = frame->ptr;
            pvrtmp_6906 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1224_1445_1785 = frame->ptr;
            end_r_2557 = frame->endptr;
            gib_shadowstack_push(rstack, ys_144_1224_1445_1785, end_r_2557, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_6907, pvrtmp_6906, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(rstack, pvrtmp_7015, pvrtmp_7014, Stk,
                                 PList_v_778_T);
            gib_shadowstack_push(wstack, loc_2555, end_r_2560, Stk,
                                 PList_v_778_T);

            GibChunk region_7021 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_2988 = region_7021.start;
            GibCursor end_r_2988 = region_7021.end;

            frame = gib_shadowstack_pop(wstack);
            loc_2555 = frame->ptr;
            end_r_2560 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_7015 = frame->ptr;
            pvrtmp_7014 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6907 = frame->ptr;
            pvrtmp_6906 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1224_1445_1785 = frame->ptr;
            end_r_2557 = frame->endptr;

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_211 =
                                                      take_plist_783(end_r_2557, end_r_2988, r_2988, pvrtmp_7000, ys_144_1224_1445_1785);
            GibCursor pvrtmp_7022 = tmp_struct_211.field0;
            GibCursor pvrtmp_7023 = tmp_struct_211.field1;
            GibCursor pvrtmp_7024 = tmp_struct_211.field2;
            GibCursor pvrtmp_7025 = tmp_struct_211.field3;
            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_212 =
             algc(pvrtmp_6906, pvrtmp_7023, pvrtmp_7014, end_r_2560, loc_2555, m2_150_1451_1793, pvrtmp_7000, pvrtmp_6907, pvrtmp_7024, pvrtmp_7015);
            GibCursor pvrtmp_7030 = tmp_struct_212.field0;
            GibCursor pvrtmp_7031 = tmp_struct_212.field1;
            GibCursor pvrtmp_7032 = tmp_struct_212.field2;
            GibCursor pvrtmp_7033 = tmp_struct_212.field3;
            GibCursor pvrtmp_7034 = tmp_struct_212.field4;
            GibCursor pvrtmp_7035 = tmp_struct_212.field5;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6914,
                                                                                          pvrtmp_7022,
                                                                                          pvrtmp_7013,
                                                                                          end_r_2559,
                                                                                          pvrtmp_7033,
                                                                                          pvrtmp_7034,
                                                                                          pvrtmp_7035};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_214 = *(uintptr_t *) tmpcur_6889;
            GibCursor tmpcur_7042 = GIB_UNTAG(tagged_tmpcur_214);
            GibCursor tmpaftercur_7043 = tmpcur_6889 + 8;
            uint16_t tmptag_7044 = GIB_GET_TAG(tagged_tmpcur_214);
            GibCursor end_from_tagged_indr_3405 = tmpcur_7042 + tmptag_7044;
            GibCursor jump_3407 = tmpcur_6889 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_213 =
             caseFn_1220(end_r_2556, end_r_2557, end_r_2558, end_from_tagged_indr_3405, end_r_2560, loc_2555, m_141_1221_1442_1782, n_142_1222_1443_1783, xs_143_1223_1444_1784, ys_144_1224_1445_1785, zs_145_1225_1446_1786, tmpcur_7042, x_146_1227_1448_1788);
            GibCursor pvrtmp_7045 = tmp_struct_213.field0;
            GibCursor pvrtmp_7046 = tmp_struct_213.field1;
            GibCursor pvrtmp_7047 = tmp_struct_213.field2;
            GibCursor pvrtmp_7048 = tmp_struct_213.field3;
            GibCursor pvrtmp_7049 = tmp_struct_213.field4;
            GibCursor pvrtmp_7050 = tmp_struct_213.field5;
            GibCursor pvrtmp_7051 = tmp_struct_213.field6;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_7045,
                                                                                          pvrtmp_7046,
                                                                                          pvrtmp_7047,
                                                                                          end_r_2559,
                                                                                          pvrtmp_7049,
                                                                                          pvrtmp_7050,
                                                                                          pvrtmp_7051};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_216 = *(uintptr_t *) tmpcur_6889;
            GibCursor tmpcur_7058 = GIB_UNTAG(tagged_tmpcur_216);
            GibCursor tmpaftercur_7059 = tmpcur_6889 + 8;
            uint16_t tmptag_7060 = GIB_GET_TAG(tagged_tmpcur_216);
            GibCursor end_from_tagged_indr_3405 = tmpcur_7058 + tmptag_7060;
            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_215 =
             caseFn_1220(end_r_2556, end_r_2557, end_r_2558, end_from_tagged_indr_3405, end_r_2560, loc_2555, m_141_1221_1442_1782, n_142_1222_1443_1783, xs_143_1223_1444_1784, ys_144_1224_1445_1785, zs_145_1225_1446_1786, tmpcur_7058, x_146_1227_1448_1788);
            GibCursor pvrtmp_7061 = tmp_struct_215.field0;
            GibCursor pvrtmp_7062 = tmp_struct_215.field1;
            GibCursor pvrtmp_7063 = tmp_struct_215.field2;
            GibCursor pvrtmp_7064 = tmp_struct_215.field3;
            GibCursor pvrtmp_7065 = tmp_struct_215.field4;
            GibCursor pvrtmp_7066 = tmp_struct_215.field5;
            GibCursor pvrtmp_7067 = tmp_struct_215.field6;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_7061,
                                                                                          pvrtmp_7062,
                                                                                          pvrtmp_7063,
                                                                                          pvrtmp_7064,
                                                                                          pvrtmp_7065,
                                                                                          pvrtmp_7066,
                                                                                          pvrtmp_7067};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6888");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd caseFn_1228(GibCursor end_r_2565,
                                                                       GibCursor end_r_2566,
                                                                       GibCursor end_r_2567,
                                                                       GibCursor end_r_2568,
                                                                       GibCursor loc_2564,
                                                                       GibInt m_141_1229_1462_1813,
                                                                       GibInt n_142_1230_1463_1814,
                                                                       GibCursor xs_143_1231_1464_1815,
                                                                       GibCursor ys_144_1232_1465_1816,
                                                                       GibCursor zs_145_1233_1466_1817)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2564 + 18 > end_r_2568) {
        gib_grow_region(&loc_2564, &end_r_2568);
    }

    GibPackedTag tmpval_7075 = *(GibPackedTag *) xs_143_1231_1464_1815;
    GibCursor tmpcur_7076 = xs_143_1231_1464_1815 + 1;


  switch_7126:
    ;
    switch (tmpval_7075) {

      case 0:
        {
            *(GibPackedTag *) loc_2564 = 0;

            GibCursor writetag_4912 = loc_2564 + 1;
            GibCursor after_tag_4913 = loc_2564 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2565,
                                                                                 end_r_2566,
                                                                                 end_r_2567,
                                                                                 end_r_2568,
                                                                                 loc_2564,
                                                                                 after_tag_4913};
            break;
        }

      case 1:
        {
            GibInt tmpval_7081 = *(GibInt *) tmpcur_7076;
            GibCursor tmpcur_7082 = tmpcur_7076 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_220 =
             caseFn_1220(end_r_2565, end_r_2566, end_r_2567, end_r_2565, end_r_2568, loc_2564, m_141_1229_1462_1813, n_142_1230_1463_1814, xs_143_1231_1464_1815, ys_144_1232_1465_1816, zs_145_1233_1466_1817, tmpcur_7082, tmpval_7081);
            GibCursor pvrtmp_7083 = tmp_struct_220.field0;
            GibCursor pvrtmp_7084 = tmp_struct_220.field1;
            GibCursor pvrtmp_7085 = tmp_struct_220.field2;
            GibCursor pvrtmp_7086 = tmp_struct_220.field3;
            GibCursor pvrtmp_7087 = tmp_struct_220.field4;
            GibCursor pvrtmp_7088 = tmp_struct_220.field5;
            GibCursor pvrtmp_7089 = tmp_struct_220.field6;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_7086,
                                                                                 pvrtmp_7084,
                                                                                 pvrtmp_7085,
                                                                                 pvrtmp_7087,
                                                                                 pvrtmp_7088,
                                                                                 pvrtmp_7089};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_222 = *(uintptr_t *) tmpcur_7076;
            GibCursor tmpcur_7096 = GIB_UNTAG(tagged_tmpcur_222);
            GibCursor tmpaftercur_7097 = tmpcur_7076 + 8;
            uint16_t tmptag_7098 = GIB_GET_TAG(tagged_tmpcur_222);
            GibCursor end_from_tagged_indr_3410 = tmpcur_7096 + tmptag_7098;
            GibCursor jump_3412 = tmpcur_7076 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_221 =
             caseFn_1228(end_from_tagged_indr_3410, end_r_2566, end_r_2567, end_r_2568, loc_2564, m_141_1229_1462_1813, n_142_1230_1463_1814, tmpcur_7096, ys_144_1232_1465_1816, zs_145_1233_1466_1817);
            GibCursor pvrtmp_7099 = tmp_struct_221.field0;
            GibCursor pvrtmp_7100 = tmp_struct_221.field1;
            GibCursor pvrtmp_7101 = tmp_struct_221.field2;
            GibCursor pvrtmp_7102 = tmp_struct_221.field3;
            GibCursor pvrtmp_7103 = tmp_struct_221.field4;
            GibCursor pvrtmp_7104 = tmp_struct_221.field5;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2565,
                                                                                 pvrtmp_7100,
                                                                                 pvrtmp_7101,
                                                                                 pvrtmp_7102,
                                                                                 pvrtmp_7103,
                                                                                 pvrtmp_7104};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_224 = *(uintptr_t *) tmpcur_7076;
            GibCursor tmpcur_7111 = GIB_UNTAG(tagged_tmpcur_224);
            GibCursor tmpaftercur_7112 = tmpcur_7076 + 8;
            uint16_t tmptag_7113 = GIB_GET_TAG(tagged_tmpcur_224);
            GibCursor end_from_tagged_indr_3410 = tmpcur_7111 + tmptag_7113;
            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_223 =
             caseFn_1228(end_from_tagged_indr_3410, end_r_2566, end_r_2567, end_r_2568, loc_2564, m_141_1229_1462_1813, n_142_1230_1463_1814, tmpcur_7111, ys_144_1232_1465_1816, zs_145_1233_1466_1817);
            GibCursor pvrtmp_7114 = tmp_struct_223.field0;
            GibCursor pvrtmp_7115 = tmp_struct_223.field1;
            GibCursor pvrtmp_7116 = tmp_struct_223.field2;
            GibCursor pvrtmp_7117 = tmp_struct_223.field3;
            GibCursor pvrtmp_7118 = tmp_struct_223.field4;
            GibCursor pvrtmp_7119 = tmp_struct_223.field5;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_7114,
                                                                                 pvrtmp_7115,
                                                                                 pvrtmp_7116,
                                                                                 pvrtmp_7117,
                                                                                 pvrtmp_7118,
                                                                                 pvrtmp_7119};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7075");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd caseFn_1234(GibCursor end_r_2572,
                                                              GibCursor end_r_2573,
                                                              GibCursor end_r_2574,
                                                              GibCursor loc_2571,
                                                              GibCursor bs_214_1235_1469_1820,
                                                              GibInt z_217_1236_1470_1821,
                                                              GibCursor zs_218_1237_1471_1822)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2571 + 26 > end_r_2574) {
        gib_grow_region(&loc_2571, &end_r_2574);
    }

    GibPackedTag tmpval_7127 = *(GibPackedTag *) bs_214_1235_1469_1820;
    GibCursor tmpcur_7128 = bs_214_1235_1469_1820 + 1;


  switch_7176:
    ;
    switch (tmpval_7127) {

      case 0:
        {
            *(GibPackedTag *) loc_2571 = 0;

            GibCursor writetag_4942 = loc_2571 + 1;
            GibCursor after_tag_4943 = loc_2571 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2572,
                                                                        end_r_2573,
                                                                        end_r_2574,
                                                                        loc_2571,
                                                                        after_tag_4943};
            break;
        }

      case 1:
        {
            GibInt tmpval_7133 = *(GibInt *) tmpcur_7128;
            GibCursor tmpcur_7134 = tmpcur_7128 + sizeof(GibInt);
            GibCursor loc_3029 = loc_2571 + 17;

            *(GibPackedTag *) loc_2571 = 1;

            GibCursor writetag_4955 = loc_2571 + 1;
            GibCursor after_tag_4956 = loc_2571 + 1;

            *(GibInt *) after_tag_4956 = z_217_1236_1470_1821;

            GibCursor writecur_4960 = after_tag_4956 + sizeof(GibInt);

            *(GibInt *) writecur_4960 = tmpval_7133;

            GibCursor writecur_4961 = writecur_4960 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_228 =
                                                               zip_plist_786(end_r_2573, end_r_2572, end_r_2574, loc_3029, zs_218_1237_1471_1822, tmpcur_7134);
            GibCursor pvrtmp_7135 = tmp_struct_228.field0;
            GibCursor pvrtmp_7136 = tmp_struct_228.field1;
            GibCursor pvrtmp_7137 = tmp_struct_228.field2;
            GibCursor pvrtmp_7138 = tmp_struct_228.field3;
            GibCursor pvrtmp_7139 = tmp_struct_228.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_7136,
                                                                        pvrtmp_7135,
                                                                        pvrtmp_7137,
                                                                        loc_2571,
                                                                        pvrtmp_7139};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_230 = *(uintptr_t *) tmpcur_7128;
            GibCursor tmpcur_7148 = GIB_UNTAG(tagged_tmpcur_230);
            GibCursor tmpaftercur_7149 = tmpcur_7128 + 8;
            uint16_t tmptag_7150 = GIB_GET_TAG(tagged_tmpcur_230);
            GibCursor end_from_tagged_indr_3415 = tmpcur_7148 + tmptag_7150;
            GibCursor jump_3417 = tmpcur_7128 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_229 =
                                                               caseFn_1234(end_from_tagged_indr_3415, end_r_2573, end_r_2574, loc_2571, tmpcur_7148, z_217_1236_1470_1821, zs_218_1237_1471_1822);
            GibCursor pvrtmp_7151 = tmp_struct_229.field0;
            GibCursor pvrtmp_7152 = tmp_struct_229.field1;
            GibCursor pvrtmp_7153 = tmp_struct_229.field2;
            GibCursor pvrtmp_7154 = tmp_struct_229.field3;
            GibCursor pvrtmp_7155 = tmp_struct_229.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2572,
                                                                        pvrtmp_7152,
                                                                        pvrtmp_7153,
                                                                        pvrtmp_7154,
                                                                        pvrtmp_7155};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_232 = *(uintptr_t *) tmpcur_7128;
            GibCursor tmpcur_7162 = GIB_UNTAG(tagged_tmpcur_232);
            GibCursor tmpaftercur_7163 = tmpcur_7128 + 8;
            uint16_t tmptag_7164 = GIB_GET_TAG(tagged_tmpcur_232);
            GibCursor end_from_tagged_indr_3415 = tmpcur_7162 + tmptag_7164;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_231 =
                                                               caseFn_1234(end_from_tagged_indr_3415, end_r_2573, end_r_2574, loc_2571, tmpcur_7162, z_217_1236_1470_1821, zs_218_1237_1471_1822);
            GibCursor pvrtmp_7165 = tmp_struct_231.field0;
            GibCursor pvrtmp_7166 = tmp_struct_231.field1;
            GibCursor pvrtmp_7167 = tmp_struct_231.field2;
            GibCursor pvrtmp_7168 = tmp_struct_231.field3;
            GibCursor pvrtmp_7169 = tmp_struct_231.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_7165,
                                                                        pvrtmp_7166,
                                                                        pvrtmp_7167,
                                                                        pvrtmp_7168,
                                                                        pvrtmp_7169};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7127");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd caseFn_1238(GibCursor end_r_2577,
                                                     GibCursor end_r_2578,
                                                     GibCursor loc_2576,
                                                     GibInt n_203_1239_1474_1826,
                                                     GibCursor a_204_1240_1475_1827)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2576 + 18 > end_r_2578) {
        gib_grow_region(&loc_2576, &end_r_2578);
    }

    GibPackedTag tmpval_7177 = *(GibPackedTag *) a_204_1240_1475_1827;
    GibCursor tmpcur_7178 = a_204_1240_1475_1827 + 1;


  switch_7223:
    ;
    switch (tmpval_7177) {

      case 0:
        {
            *(GibPackedTag *) loc_2576 = 0;

            GibCursor writetag_4978 = loc_2576 + 1;
            GibCursor after_tag_4979 = loc_2576 + 1;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_2577,
                                                               end_r_2578,
                                                               loc_2576,
                                                               after_tag_4979};
            break;
        }

      case 1:
        {
            GibInt tmpval_7183 = *(GibInt *) tmpcur_7178;
            GibCursor tmpcur_7184 = tmpcur_7178 + sizeof(GibInt);
            GibInt fltAppE_1546_1830 = n_203_1239_1474_1826 - 1;
            GibCursor loc_3044 = loc_2576 + 9;

            *(GibPackedTag *) loc_2576 = 1;

            GibCursor writetag_4990 = loc_2576 + 1;
            GibCursor after_tag_4991 = loc_2576 + 1;

            *(GibInt *) after_tag_4991 = tmpval_7183;

            GibCursor writecur_4995 = after_tag_4991 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_236 =
                                                      take_plist_783(end_r_2577, end_r_2578, loc_3044, fltAppE_1546_1830, tmpcur_7184);
            GibCursor pvrtmp_7185 = tmp_struct_236.field0;
            GibCursor pvrtmp_7186 = tmp_struct_236.field1;
            GibCursor pvrtmp_7187 = tmp_struct_236.field2;
            GibCursor pvrtmp_7188 = tmp_struct_236.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_7185,
                                                               pvrtmp_7186,
                                                               loc_2576,
                                                               pvrtmp_7188};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_238 = *(uintptr_t *) tmpcur_7178;
            GibCursor tmpcur_7197 = GIB_UNTAG(tagged_tmpcur_238);
            GibCursor tmpaftercur_7198 = tmpcur_7178 + 8;
            uint16_t tmptag_7199 = GIB_GET_TAG(tagged_tmpcur_238);
            GibCursor end_from_tagged_indr_3420 = tmpcur_7197 + tmptag_7199;
            GibCursor jump_3422 = tmpcur_7178 + 8;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_237 =
                                                      caseFn_1238(end_from_tagged_indr_3420, end_r_2578, loc_2576, n_203_1239_1474_1826, tmpcur_7197);
            GibCursor pvrtmp_7200 = tmp_struct_237.field0;
            GibCursor pvrtmp_7201 = tmp_struct_237.field1;
            GibCursor pvrtmp_7202 = tmp_struct_237.field2;
            GibCursor pvrtmp_7203 = tmp_struct_237.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_2577,
                                                               pvrtmp_7201,
                                                               pvrtmp_7202,
                                                               pvrtmp_7203};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_240 = *(uintptr_t *) tmpcur_7178;
            GibCursor tmpcur_7210 = GIB_UNTAG(tagged_tmpcur_240);
            GibCursor tmpaftercur_7211 = tmpcur_7178 + 8;
            uint16_t tmptag_7212 = GIB_GET_TAG(tagged_tmpcur_240);
            GibCursor end_from_tagged_indr_3420 = tmpcur_7210 + tmptag_7212;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_239 =
                                                      caseFn_1238(end_from_tagged_indr_3420, end_r_2578, loc_2576, n_203_1239_1474_1826, tmpcur_7210);
            GibCursor pvrtmp_7213 = tmp_struct_239.field0;
            GibCursor pvrtmp_7214 = tmp_struct_239.field1;
            GibCursor pvrtmp_7215 = tmp_struct_239.field2;
            GibCursor pvrtmp_7216 = tmp_struct_239.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_7213,
                                                               pvrtmp_7214,
                                                               pvrtmp_7215,
                                                               pvrtmp_7216};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7177");
            exit(1);
        }
    }
}
int main(int argc, char **argv)
{
    int init_254 = gib_init(argc, argv);

    info_table_initialize();
    symbol_table_initialize();

    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibInt n_101_1241_1547 = gib_get_size_param();
    GibBool fltPrm_1484_1548 = n_101_1241_1547 < 1;
    GibBool fltPrm_1485_1549 = n_101_1241_1547 == 1;
    GibBool fltIf_1483_1550 = fltPrm_1484_1548 || fltPrm_1485_1549;

    if (fltIf_1483_1550) {
        GibIntGibIntGibIntGibIntGibIntGibIntProd tmp_struct_244 =
                                                  very_small_opts();
        GibInt pvrtmp_5744 = tmp_struct_244.field0;
        GibInt pvrtmp_5745 = tmp_struct_244.field1;
        GibInt pvrtmp_5746 = tmp_struct_244.field2;
        GibInt pvrtmp_5747 = tmp_struct_244.field3;
        GibInt pvrtmp_5748 = tmp_struct_244.field4;
        GibInt pvrtmp_5749 = tmp_struct_244.field5;
        GibIntGibIntGibIntProd tmp_struct_245 =  very_small_opts_answer();
        GibInt pvrtmp_5750 = tmp_struct_245.field0;
        GibInt pvrtmp_5751 = tmp_struct_245.field1;
        GibInt pvrtmp_5752 = tmp_struct_245.field2;
        GibBool tailapp_3256 =
                 bench_lcss((GibIntGibIntGibIntGibIntGibIntGibIntProd) {pvrtmp_5744, pvrtmp_5745, pvrtmp_5746, pvrtmp_5747, pvrtmp_5748, pvrtmp_5749}, (GibIntGibIntGibIntProd) {pvrtmp_5750, pvrtmp_5751, pvrtmp_5752});

        if (tailapp_3256) {
            printf("#t");
            printf("\n");
            // return 0;
        } else {
            printf("#f");
            printf("\n");
            // return 0;
        }
    } else {
        GibBool fltIf_1488_1553 = n_101_1241_1547 == 2;

        if (fltIf_1488_1553) {
            GibIntGibIntGibIntGibIntGibIntGibIntProd tmp_struct_246 =
                                                      small_opts();
            GibInt pvrtmp_5762 = tmp_struct_246.field0;
            GibInt pvrtmp_5763 = tmp_struct_246.field1;
            GibInt pvrtmp_5764 = tmp_struct_246.field2;
            GibInt pvrtmp_5765 = tmp_struct_246.field3;
            GibInt pvrtmp_5766 = tmp_struct_246.field4;
            GibInt pvrtmp_5767 = tmp_struct_246.field5;
            GibIntGibIntGibIntProd tmp_struct_247 =  small_opts_answer();
            GibInt pvrtmp_5768 = tmp_struct_247.field0;
            GibInt pvrtmp_5769 = tmp_struct_247.field1;
            GibInt pvrtmp_5770 = tmp_struct_247.field2;
            GibBool tailapp_3257 =
                     bench_lcss((GibIntGibIntGibIntGibIntGibIntGibIntProd) {pvrtmp_5762, pvrtmp_5763, pvrtmp_5764, pvrtmp_5765, pvrtmp_5766, pvrtmp_5767}, (GibIntGibIntGibIntProd) {pvrtmp_5768, pvrtmp_5769, pvrtmp_5770});

            if (tailapp_3257) {
                printf("#t");
                printf("\n");
                // return 0;
            } else {
                printf("#f");
                printf("\n");
                // return 0;
            }
        } else {
            GibBool fltIf_1491_1556 = n_101_1241_1547 == 3;

            if (fltIf_1491_1556) {
                GibIntGibIntGibIntGibIntGibIntGibIntProd tmp_struct_248 =
                                                          fast_opts();
                GibInt pvrtmp_5780 = tmp_struct_248.field0;
                GibInt pvrtmp_5781 = tmp_struct_248.field1;
                GibInt pvrtmp_5782 = tmp_struct_248.field2;
                GibInt pvrtmp_5783 = tmp_struct_248.field3;
                GibInt pvrtmp_5784 = tmp_struct_248.field4;
                GibInt pvrtmp_5785 = tmp_struct_248.field5;
                GibIntGibIntGibIntProd tmp_struct_249 =  fast_opts_answer();
                GibInt pvrtmp_5786 = tmp_struct_249.field0;
                GibInt pvrtmp_5787 = tmp_struct_249.field1;
                GibInt pvrtmp_5788 = tmp_struct_249.field2;
                GibBool tailapp_3258 =
                         bench_lcss((GibIntGibIntGibIntGibIntGibIntGibIntProd) {pvrtmp_5780, pvrtmp_5781, pvrtmp_5782, pvrtmp_5783, pvrtmp_5784, pvrtmp_5785}, (GibIntGibIntGibIntProd) {pvrtmp_5786, pvrtmp_5787, pvrtmp_5788});

                if (tailapp_3258) {
                    printf("#t");
                    printf("\n");
                    return 0;
                } else {
                    printf("#f");
                    printf("\n");
                    // return 0;
                }
            } else {
                GibBool fltIf_1494_1559 = n_101_1241_1547 == 4;

                if (fltIf_1494_1559) {
                    GibIntGibIntGibIntGibIntGibIntGibIntProd tmp_struct_250 =
                                                              norm_opts();
                    GibInt pvrtmp_5798 = tmp_struct_250.field0;
                    GibInt pvrtmp_5799 = tmp_struct_250.field1;
                    GibInt pvrtmp_5800 = tmp_struct_250.field2;
                    GibInt pvrtmp_5801 = tmp_struct_250.field3;
                    GibInt pvrtmp_5802 = tmp_struct_250.field4;
                    GibInt pvrtmp_5803 = tmp_struct_250.field5;
                    GibIntGibIntGibIntProd tmp_struct_251 =  norm_opts_answer();
                    GibInt pvrtmp_5804 = tmp_struct_251.field0;
                    GibInt pvrtmp_5805 = tmp_struct_251.field1;
                    GibInt pvrtmp_5806 = tmp_struct_251.field2;
                    GibBool tailapp_3259 =
                             bench_lcss((GibIntGibIntGibIntGibIntGibIntGibIntProd) {pvrtmp_5798, pvrtmp_5799, pvrtmp_5800, pvrtmp_5801, pvrtmp_5802, pvrtmp_5803}, (GibIntGibIntGibIntProd) {pvrtmp_5804, pvrtmp_5805, pvrtmp_5806});

                    if (tailapp_3259) {
                        printf("#t");
                        printf("\n");
                        // return 0;
                    } else {
                        printf("#f");
                        printf("\n");
                        // return 0;
                    }
                } else {
                    GibIntGibIntGibIntGibIntGibIntGibIntProd tmp_struct_252 =
                                                              slow_opts();
                    GibInt pvrtmp_5816 = tmp_struct_252.field0;
                    GibInt pvrtmp_5817 = tmp_struct_252.field1;
                    GibInt pvrtmp_5818 = tmp_struct_252.field2;
                    GibInt pvrtmp_5819 = tmp_struct_252.field3;
                    GibInt pvrtmp_5820 = tmp_struct_252.field4;
                    GibInt pvrtmp_5821 = tmp_struct_252.field5;
                    GibIntGibIntGibIntProd tmp_struct_253 =  slow_opts_answer();
                    GibInt pvrtmp_5822 = tmp_struct_253.field0;
                    GibInt pvrtmp_5823 = tmp_struct_253.field1;
                    GibInt pvrtmp_5824 = tmp_struct_253.field2;
                    GibBool tailapp_3260 =
                             bench_lcss((GibIntGibIntGibIntGibIntGibIntGibIntProd) {pvrtmp_5816, pvrtmp_5817, pvrtmp_5818, pvrtmp_5819, pvrtmp_5820, pvrtmp_5821}, (GibIntGibIntGibIntProd) {pvrtmp_5822, pvrtmp_5823, pvrtmp_5824});

                    if (tailapp_3260) {
                        printf("#t");
                        printf("\n");
                        // return 0;
                    } else {
                        printf("#f");
                        printf("\n");
                        // return 0;
                    }
                }
            }
        }
    }

    int exit_255 = gib_exit();

    return exit_255;
}
