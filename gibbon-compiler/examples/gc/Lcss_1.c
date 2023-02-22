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
GibIntGibIntGibIntProd test_opts_answer();
GibIntGibIntGibIntProd fast_opts_answer();
GibIntGibIntGibIntProd norm_opts_answer();
GibIntGibIntGibIntProd slow_opts_answer();
GibIntGibIntGibIntGibIntGibIntGibIntProd test_opts();
GibIntGibIntGibIntGibIntGibIntGibIntProd fast_opts();
GibIntGibIntGibIntGibIntGibIntGibIntProd norm_opts();
GibIntGibIntGibIntGibIntGibIntGibIntProd slow_opts();
GibBool bench_lcss(GibIntGibIntGibIntGibIntGibIntGibIntProd opts_104_1230_1546,
                   GibIntGibIntGibIntProd answer_105_1231_1547);
GibCursorGibCursorGibBoolProd check_lcss(GibCursor end_r_2428,
                                         GibInt start_120_1246_1564,
                                         GibInt step_121_1247_1565,
                                         GibInt end_122_1248_1566,
                                         GibCursor list2_123_1249_1567);
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
lcss(GibCursor end_r_2432, GibCursor end_r_2433, GibCursor end_r_2434,
     GibCursor loc_2431, GibCursor xs_126_1252_1573,
     GibCursor ys_127_1253_1574);
GibCursorGibCursorGibCursorProd mkList(GibCursor end_r_2436, GibCursor loc_2435,
                                       GibInt start_128_1254_1578,
                                       GibInt end_129_1255_1579,
                                       GibInt skipFactor_130_1256_1580);
GibCursorGibCursorGibIntProd findk(GibCursor end_r_2438, GibInt k_132_1258_1584,
                                   GibInt km_133_1259_1585,
                                   GibInt m_134_1260_1586,
                                   GibCursor ls_135_1261_1587);
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
algc(GibCursor end_r_2443, GibCursor end_r_2444, GibCursor end_r_2445,
     GibCursor end_r_2446, GibCursor loc_2442, GibInt m_141_1268_1599,
     GibInt n_142_1269_1600, GibCursor xs_143_1270_1601,
     GibCursor ys_144_1271_1602, GibCursor zs_145_1272_1603);
GibCursorGibCursorGibCursorGibCursorGibCursorProd algb2(GibCursor end_r_2449,
                                                        GibCursor end_r_2450,
                                                        GibCursor loc_2448,
                                                        GibInt x_161_1273_1605,
                                                        GibInt k0j1_162_1274_1606,
                                                        GibInt k1j1_163_1275_1607,
                                                        GibCursor ls_164_1276_1608);
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
algb1(GibCursor end_r_2454, GibCursor end_r_2455, GibCursor end_r_2456,
      GibCursor loc_2453, GibCursor xs_171_1284_1618,
      GibCursor ys_172_1285_1619);
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
algb(GibCursor end_r_2460, GibCursor end_r_2461, GibCursor end_r_2462,
     GibCursor loc_2459, GibCursor xs_178_1288_1623,
     GibCursor ys_179_1289_1624);
GibCursorGibCursorGibCursorGibCursorGibCursorProd zip0(GibCursor end_r_2465,
                                                       GibCursor end_r_2466,
                                                       GibCursor loc_2464,
                                                       GibCursor ls_180_1290_1627);
static inline GibInt maxInt(GibInt a_189_1293_1631, GibInt b_190_1294_1632);
GibCursorGibCursorGibIntProd length_plist_776(GibCursor end_r_2468,
                                              GibCursor a_226_1313_1634);
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
reverse_plist_782(GibCursor end_r_2472, GibCursor end_r_2473,
                  GibCursor end_r_2474, GibCursor loc_2471,
                  GibCursor xs_221_1316_1638, GibCursor acc_222_1317_1639);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
zip_plist_783(GibCursor end_r_2478, GibCursor end_r_2479, GibCursor end_r_2480,
              GibCursor loc_2477, GibCursor as_213_1320_1643,
              GibCursor bs_214_1321_1644);
GibCursorGibCursorGibCursorGibCursorProd drop_plist_781(GibCursor end_r_2483,
                                                        GibCursor end_r_2484,
                                                        GibCursor loc_2482,
                                                        GibInt num_208_1324_1647,
                                                        GibCursor list_209_1325_1648);
GibCursorGibCursorGibCursorGibCursorProd take_plist_780(GibCursor end_r_2487,
                                                        GibCursor end_r_2488,
                                                        GibCursor loc_2486,
                                                        GibInt n_203_1328_1653,
                                                        GibCursor a_204_1329_1654);
static inline
GibCursorGibBoolProd is_empty_plist_778(GibCursor end_r_2490,
                                        GibCursor ls_191_1330_1656);
GibCursorGibBoolProd elem_plist_779_1060(GibCursor end_r_2492,
                                         GibInt a_196_1336_1659,
                                         GibCursor list_197_1337_1660);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
map_plist_784_1062(GibCursor end_r_2495, GibCursor end_r_2496,
                   GibCursor loc_2494, GibCursor ls_184_1340_1669);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_PList_v_775(GibCursor end_r_2499, GibCursor end_r_2500,
                  GibCursor loc_2498, GibCursor arg_1124_1344_1678);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_PList_v_775(GibCursor end_r_2503, GibCursor end_r_2504,
                               GibCursor loc_2502,
                               GibCursor arg_1129_1349_1683);
GibCursorGibCursorProd _traverse_PList_v_775(GibCursor end_r_2506,
                                             GibCursor arg_1134_1354_1688);
GibCursorGibCursorProd _print_PList_v_775(GibCursor end_r_2508,
                                          GibCursor arg_1139_1358_1692);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_PList_v_777(GibCursor end_r_2511, GibCursor end_r_2512,
                  GibCursor loc_2510, GibCursor arg_1152_1373_1707);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_PList_v_777(GibCursor end_r_2515, GibCursor end_r_2516,
                               GibCursor loc_2514,
                               GibCursor arg_1159_1380_1714);
GibCursorGibCursorProd _traverse_PList_v_777(GibCursor end_r_2518,
                                             GibCursor arg_1166_1387_1721);
GibCursorGibCursorProd _print_PList_v_777(GibCursor end_r_2520,
                                          GibCursor arg_1173_1392_1726);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_Maybe_v_785(GibCursor end_r_2523, GibCursor end_r_2524,
                  GibCursor loc_2522, GibCursor arg_1190_1412_1746);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_Maybe_v_785(GibCursor end_r_2527, GibCursor end_r_2528,
                               GibCursor loc_2526,
                               GibCursor arg_1193_1415_1749);
GibCursorGibCursorProd _traverse_Maybe_v_785(GibCursor end_r_2530,
                                             GibCursor arg_1196_1418_1752);
GibCursorGibCursorProd _print_Maybe_v_785(GibCursor end_r_2532,
                                          GibCursor arg_1199_1420_1754);
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
caseFn_1208(GibCursor end_r_2538, GibCursor end_r_2539, GibCursor end_r_2540,
            GibCursor end_r_2541, GibCursor end_r_2542, GibCursor loc_2537,
            GibInt m_141_1209_1430_1764, GibInt n_142_1210_1431_1765,
            GibCursor xs_143_1211_1432_1766, GibCursor ys_144_1212_1433_1767,
            GibCursor zs_145_1213_1434_1768, GibCursor xs__147_1214_1435_1769,
            GibInt x_146_1215_1436_1770);
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
caseFn_1216(GibCursor end_r_2547, GibCursor end_r_2548, GibCursor end_r_2549,
            GibCursor end_r_2550, GibCursor loc_2546,
            GibInt m_141_1217_1450_1795, GibInt n_142_1218_1451_1796,
            GibCursor xs_143_1219_1452_1797, GibCursor ys_144_1220_1453_1798,
            GibCursor zs_145_1221_1454_1799);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
caseFn_1222(GibCursor end_r_2554, GibCursor end_r_2555, GibCursor end_r_2556,
            GibCursor loc_2553, GibCursor bs_214_1223_1457_1802,
            GibInt z_217_1224_1458_1803, GibCursor zs_218_1225_1459_1804);
GibCursorGibCursorGibCursorGibCursorProd caseFn_1226(GibCursor end_r_2559,
                                                     GibCursor end_r_2560,
                                                     GibCursor loc_2558,
                                                     GibInt n_203_1227_1462_1808,
                                                     GibCursor a_204_1228_1463_1809);
typedef enum {
            GibInt_T,
            GibFloat_T,
            GibSym_T,
            GibBool_T,
            GibVector_T,
            GibList_T,
            GibCursor_T,
            Maybe_v_785_T,
            PList_v_775_T,
            PList_v_777_T,
        } GibDatatype;
void info_table_initialize(void)
{
    int error = gib_info_table_initialize(10);

    if (error < 0) {
        fprintf(stderr, "Couldn't initialize info table, errorno=%d", error);
        exit(1);
    }

    GibDatatype field_tys[3];

    error = gib_info_table_insert_packed_dcon(Maybe_v_785_T, 0, 8, 0, 1, 0,
                                              field_tys, 0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, Maybe_v_785_T, 0);
        exit(1);
    }
    error = gib_info_table_insert_packed_dcon(Maybe_v_785_T, 1, 0, 0, 0, 0,
                                              field_tys, 0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, Maybe_v_785_T, 1);
        exit(1);
    }
    field_tys[0] = PList_v_775_T;
    error = gib_info_table_insert_packed_dcon(PList_v_775_T, 1, 8, 0, 1, 1,
                                              field_tys, 1);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, PList_v_775_T, 1);
        exit(1);
    }
    error = gib_info_table_insert_packed_dcon(PList_v_775_T, 0, 0, 0, 0, 0,
                                              field_tys, 0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, PList_v_775_T, 0);
        exit(1);
    }
    field_tys[0] = PList_v_777_T;
    error = gib_info_table_insert_packed_dcon(PList_v_777_T, 1, 16, 0, 2, 1,
                                              field_tys, 1);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, PList_v_777_T, 1);
        exit(1);
    }
    error = gib_info_table_insert_packed_dcon(PList_v_777_T, 0, 0, 0, 0, 0,
                                              field_tys, 0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, PList_v_777_T, 0);
        exit(1);
    }
    gib_info_table_finalize();
}
void symbol_table_initialize(void)
{
    gib_add_symbol(5702, ")");
    gib_add_symbol(5703, "(Nothing_v_785");
    gib_add_symbol(5704, "(Nil_v_777");
    gib_add_symbol(5705, "(Nil_v_775");
    gib_add_symbol(5706, "(Just_v_785");
    gib_add_symbol(5707, "(Cons_v_777");
    gib_add_symbol(5708, "(Cons_v_775");
    gib_add_symbol(5709, " ->r ");
    gib_add_symbol(5710, " ->i ");
    gib_add_symbol(5711, " ");
}
GibIntGibIntGibIntProd test_opts_answer()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    return (GibIntGibIntGibIntProd) {1050, 1, 2000};
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

    return (GibIntGibIntGibIntProd) {1000, 1, 2000};
}
GibIntGibIntGibIntProd slow_opts_answer()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    return (GibIntGibIntGibIntProd) {1000, 1, 4000};
}
GibIntGibIntGibIntGibIntGibIntGibIntProd test_opts()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    return (GibIntGibIntGibIntGibIntGibIntGibIntProd) {1, 2, 2000, 1050, 1051,
                                                       2000};
}
GibIntGibIntGibIntGibIntGibIntGibIntProd fast_opts()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    return (GibIntGibIntGibIntGibIntGibIntGibIntProd) {1, 2, 2000, 1000, 1001,
                                                       2000};
}
GibIntGibIntGibIntGibIntGibIntGibIntProd norm_opts()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    return (GibIntGibIntGibIntGibIntGibIntGibIntProd) {1, 2, 2000, 1000, 1001,
                                                       4000};
}
GibIntGibIntGibIntGibIntGibIntGibIntProd slow_opts()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    return (GibIntGibIntGibIntGibIntGibIntGibIntProd) {1, 2, 4000, 1000, 1001,
                                                       4000};
}
GibBool bench_lcss(GibIntGibIntGibIntGibIntGibIntGibIntProd opts_104_1230_1546,
                   GibIntGibIntGibIntProd answer_105_1231_1547)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibInt fltAppE_1484_1555 = opts_104_1230_1546.field1 -
           opts_104_1230_1546.field0;
    GibChunk region_5820 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_2577 = region_5820.start;
    GibCursor end_r_2577 = region_5820.end;
    GibCursorGibCursorGibCursorProd tmp_struct_0 =
                                     mkList(end_r_2577, r_2577, opts_104_1230_1546.field0, opts_104_1230_1546.field2, fltAppE_1484_1555);
    GibCursor pvrtmp_5821 = tmp_struct_0.field0;
    GibCursor pvrtmp_5822 = tmp_struct_0.field1;
    GibCursor pvrtmp_5823 = tmp_struct_0.field2;
    GibInt fltAppE_1485_1557 = opts_104_1230_1546.field4 -
           opts_104_1230_1546.field3;

    gib_shadowstack_push(rstack, pvrtmp_5822, pvrtmp_5821, Stk, PList_v_775_T);

    GibChunk region_5828 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_2576 = region_5828.start;
    GibCursor end_r_2576 = region_5828.end;

    frame = gib_shadowstack_pop(rstack);
    pvrtmp_5822 = frame->ptr;
    pvrtmp_5821 = frame->endptr;

    GibCursorGibCursorGibCursorProd tmp_struct_1 =
                                     mkList(end_r_2576, r_2576, opts_104_1230_1546.field3, opts_104_1230_1546.field5, fltAppE_1485_1557);
    GibCursor pvrtmp_5829 = tmp_struct_1.field0;
    GibCursor pvrtmp_5830 = tmp_struct_1.field1;
    GibCursor pvrtmp_5831 = tmp_struct_1.field2;

    gib_shadowstack_push(rstack, pvrtmp_5822, pvrtmp_5821, Stk, PList_v_775_T);
    gib_shadowstack_push(rstack, pvrtmp_5830, pvrtmp_5829, Stk, PList_v_775_T);

    GibChunk region_5836 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_2575 = region_5836.start;
    GibCursor end_r_2575 = region_5836.end;

    frame = gib_shadowstack_pop(rstack);
    pvrtmp_5830 = frame->ptr;
    pvrtmp_5829 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_5822 = frame->ptr;
    pvrtmp_5821 = frame->endptr;

    GibCursor pvrtmp_5850;
    GibCursor pvrtmp_5851;
    GibCursor pvrtmp_5852;
    GibVector *times_6 = gib_vector_alloc(gib_get_iters_param(),
                                          sizeof(double));
    struct timespec begin_pvrtmp_5850;
    struct timespec end_pvrtmp_5850;

    GibGcStateSnapshot *snapshot = gib_gc_init_state(3);

    for (long long iters_pvrtmp_5850 = 0; iters_pvrtmp_5850 <
         gib_get_iters_param(); iters_pvrtmp_5850++) {

        if (iters_pvrtmp_5850 != gib_get_iters_param() - 1) {
            gib_gc_save_state(snapshot, 3, region_5836.end, region_5828.end, region_5820.end);
            gib_list_bumpalloc_save_state();
            gib_ptr_bumpalloc_save_state();
        }
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_5850);

        GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
        tmp_struct_2 =
         lcss(pvrtmp_5821, pvrtmp_5829, end_r_2575, r_2575, pvrtmp_5822, pvrtmp_5830);
        GibCursor pvrtmp_5837 = tmp_struct_2.field0;
        GibCursor pvrtmp_5838 = tmp_struct_2.field1;
        GibCursor pvrtmp_5839 = tmp_struct_2.field2;
        GibCursor pvrtmp_5840 = tmp_struct_2.field3;
        GibCursor pvrtmp_5841 = tmp_struct_2.field4;
        GibCursor pvrtmp_5842 = tmp_struct_2.field5;
        GibCursor pvrtmp_5843 = tmp_struct_2.field6;

        pvrtmp_5850 = pvrtmp_5839;
        pvrtmp_5851 = pvrtmp_5842;
        pvrtmp_5852 = pvrtmp_5843;

        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_5850);
        if (iters_pvrtmp_5850 != gib_get_iters_param() - 1) {
            gib_gc_restore_state(snapshot);
            gib_list_bumpalloc_restore_state();
            gib_ptr_bumpalloc_restore_state();
        }

        double itertime_3 = gib_difftimespecs(&begin_pvrtmp_5850,
                                              &end_pvrtmp_5850);

        printf("itertime: %lf\n", itertime_3);
        gib_vector_inplace_update(times_6, iters_pvrtmp_5850, &itertime_3);
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
                                   check_lcss(end_r_2575, answer_105_1231_1547.field0, answer_105_1231_1547.field1, answer_105_1231_1547.field2, pvrtmp_5851);
    GibCursor pvrtmp_5860 = tmp_struct_8.field0;
    GibCursor pvrtmp_5861 = tmp_struct_8.field1;
    GibBool pvrtmp_5862 = tmp_struct_8.field2;

    return pvrtmp_5862;
}
GibCursorGibCursorGibBoolProd check_lcss(GibCursor end_r_2428,
                                         GibInt start_120_1246_1564,
                                         GibInt step_121_1247_1565,
                                         GibInt end_122_1248_1566,
                                         GibCursor list2_123_1249_1567)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_5863 = *(GibPackedTag *) list2_123_1249_1567;
    GibCursor tmpcur_5864 = list2_123_1249_1567 + 1;


  switch_5882:
    ;
    switch (tmpval_5863) {

      case 0:
        {
            GibCursor jump_3077 = list2_123_1249_1567 + 1;
            GibBool tailprim_3078 = start_120_1246_1564 > end_122_1248_1566;

            return (GibCursorGibCursorGibBoolProd) {end_r_2428, jump_3077,
                                                    tailprim_3078};
            break;
        }

      case 1:
        {
            GibInt tmpval_5865 = *(GibInt *) tmpcur_5864;
            GibCursor tmpcur_5866 = tmpcur_5864 + sizeof(GibInt);
            GibBool fltPrm_1486_1570 = tmpval_5865 == start_120_1246_1564;
            GibInt fltAppE_1488_1571 = start_120_1246_1564 + step_121_1247_1565;
            GibCursorGibCursorGibBoolProd tmp_struct_9 =
                                           check_lcss(end_r_2428, fltAppE_1488_1571, step_121_1247_1565, end_122_1248_1566, tmpcur_5866);
            GibCursor pvrtmp_5867 = tmp_struct_9.field0;
            GibCursor pvrtmp_5868 = tmp_struct_9.field1;
            GibBool pvrtmp_5869 = tmp_struct_9.field2;
            GibBool tailprim_3081 = fltPrm_1486_1570 && pvrtmp_5869;

            return (GibCursorGibCursorGibBoolProd) {pvrtmp_5867, pvrtmp_5868,
                                                    tailprim_3081};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_11 = *(uintptr_t *) tmpcur_5864;
            GibCursor tmpcur_5870 = GIB_UNTAG(tagged_tmpcur_11);
            GibCursor tmpaftercur_5871 = tmpcur_5864 + 8;
            uint16_t tmptag_5872 = GIB_GET_TAG(tagged_tmpcur_11);
            GibCursor end_from_tagged_indr_3243 = tmpcur_5870 + tmptag_5872;
            GibCursor jump_3245 = tmpcur_5864 + 8;
            GibCursorGibCursorGibBoolProd tmp_struct_10 =
                                           check_lcss(end_from_tagged_indr_3243, start_120_1246_1564, step_121_1247_1565, end_122_1248_1566, tmpcur_5870);
            GibCursor pvrtmp_5873 = tmp_struct_10.field0;
            GibCursor pvrtmp_5874 = tmp_struct_10.field1;
            GibBool pvrtmp_5875 = tmp_struct_10.field2;

            return (GibCursorGibCursorGibBoolProd) {end_r_2428, jump_3245,
                                                    pvrtmp_5875};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_13 = *(uintptr_t *) tmpcur_5864;
            GibCursor tmpcur_5876 = GIB_UNTAG(tagged_tmpcur_13);
            GibCursor tmpaftercur_5877 = tmpcur_5864 + 8;
            uint16_t tmptag_5878 = GIB_GET_TAG(tagged_tmpcur_13);
            GibCursor end_from_tagged_indr_3243 = tmpcur_5876 + tmptag_5878;
            GibCursorGibCursorGibBoolProd tmp_struct_12 =
                                           check_lcss(end_from_tagged_indr_3243, start_120_1246_1564, step_121_1247_1565, end_122_1248_1566, tmpcur_5876);
            GibCursor pvrtmp_5879 = tmp_struct_12.field0;
            GibCursor pvrtmp_5880 = tmp_struct_12.field1;
            GibBool pvrtmp_5881 = tmp_struct_12.field2;

            return (GibCursorGibCursorGibBoolProd) {pvrtmp_5879, pvrtmp_5880,
                                                    pvrtmp_5881};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5863");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd lcss(GibCursor end_r_2432,
                                                                         GibCursor end_r_2433,
                                                                         GibCursor end_r_2434,
                                                                         GibCursor loc_2431,
                                                                         GibCursor xs_126_1252_1573,
                                                                         GibCursor ys_127_1253_1574)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2431 + 18 > end_r_2434) {
        gib_grow_region(&loc_2431, &end_r_2434);
    }

    GibCursorGibCursorGibIntProd tmp_struct_14 =
                                  length_plist_776(end_r_2432, xs_126_1252_1573);
    GibCursor pvrtmp_5883 = tmp_struct_14.field0;
    GibCursor pvrtmp_5884 = tmp_struct_14.field1;
    GibInt pvrtmp_5885 = tmp_struct_14.field2;
    GibCursorGibCursorGibIntProd tmp_struct_15 =
                                  length_plist_776(end_r_2433, ys_127_1253_1574);
    GibCursor pvrtmp_5886 = tmp_struct_15.field0;
    GibCursor pvrtmp_5887 = tmp_struct_15.field1;
    GibInt pvrtmp_5888 = tmp_struct_15.field2;

    gib_shadowstack_push(rstack, xs_126_1252_1573, end_r_2432, Stk,
                         PList_v_775_T);
    gib_shadowstack_push(rstack, ys_127_1253_1574, end_r_2433, Stk,
                         PList_v_775_T);
    gib_shadowstack_push(wstack, loc_2431, end_r_2434, Stk, PList_v_775_T);

    GibChunk region_5889 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_2599 = region_5889.start;
    GibCursor end_r_2599 = region_5889.end;

    frame = gib_shadowstack_pop(wstack);
    loc_2431 = frame->ptr;
    end_r_2434 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    ys_127_1253_1574 = frame->ptr;
    end_r_2433 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    xs_126_1252_1573 = frame->ptr;
    end_r_2432 = frame->endptr;
    *(GibPackedTag *) r_2599 = 0;

    GibCursor writetag_4182 = r_2599 + 1;
    GibCursor after_tag_4183 = r_2599 + 1;
    GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_16 =
                                                                algc(end_r_2432, end_r_2433, end_r_2599, end_r_2434, loc_2431, pvrtmp_5885, pvrtmp_5888, xs_126_1252_1573, ys_127_1253_1574, r_2599);
    GibCursor pvrtmp_5892 = tmp_struct_16.field0;
    GibCursor pvrtmp_5893 = tmp_struct_16.field1;
    GibCursor pvrtmp_5894 = tmp_struct_16.field2;
    GibCursor pvrtmp_5895 = tmp_struct_16.field3;
    GibCursor pvrtmp_5896 = tmp_struct_16.field4;
    GibCursor pvrtmp_5897 = tmp_struct_16.field5;

    return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_5892,
                                                                                  pvrtmp_5893,
                                                                                  pvrtmp_5895,
                                                                                  pvrtmp_5884,
                                                                                  pvrtmp_5887,
                                                                                  pvrtmp_5896,
                                                                                  pvrtmp_5897};
}
GibCursorGibCursorGibCursorProd mkList(GibCursor end_r_2436, GibCursor loc_2435,
                                       GibInt start_128_1254_1578,
                                       GibInt end_129_1255_1579,
                                       GibInt skipFactor_130_1256_1580)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2435 + 18 > end_r_2436) {
        gib_grow_region(&loc_2435, &end_r_2436);
    }

    GibBool fltIf_1492_1581 = start_128_1254_1578 <= end_129_1255_1579;

    if (fltIf_1492_1581) {
        GibInt fltAppE_1493_1582 = start_128_1254_1578 +
               skipFactor_130_1256_1580;
        GibCursor loc_2602 = loc_2435 + 9;

        *(GibPackedTag *) loc_2435 = 1;

        GibCursor writetag_4196 = loc_2435 + 1;
        GibCursor after_tag_4197 = loc_2435 + 1;

        *(GibInt *) after_tag_4197 = start_128_1254_1578;

        GibCursor writecur_4201 = after_tag_4197 + sizeof(GibInt);
        GibCursorGibCursorGibCursorProd tmp_struct_20 =
                                         mkList(end_r_2436, loc_2602, fltAppE_1493_1582, end_129_1255_1579, skipFactor_130_1256_1580);
        GibCursor pvrtmp_5904 = tmp_struct_20.field0;
        GibCursor pvrtmp_5905 = tmp_struct_20.field1;
        GibCursor pvrtmp_5906 = tmp_struct_20.field2;

        return (GibCursorGibCursorGibCursorProd) {pvrtmp_5904, loc_2435,
                                                  pvrtmp_5906};
    } else {
        *(GibPackedTag *) loc_2435 = 0;

        GibCursor writetag_4205 = loc_2435 + 1;
        GibCursor after_tag_4206 = loc_2435 + 1;

        return (GibCursorGibCursorGibCursorProd) {end_r_2436, loc_2435,
                                                  after_tag_4206};
    }
}
GibCursorGibCursorGibIntProd findk(GibCursor end_r_2438, GibInt k_132_1258_1584,
                                   GibInt km_133_1259_1585,
                                   GibInt m_134_1260_1586,
                                   GibCursor ls_135_1261_1587)
{
    // GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    // GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    // GibShadowstackFrame *frame;
    GibPackedTag tmpval_5919 = *(GibPackedTag *) ls_135_1261_1587;
    GibCursor tmpcur_5920 = ls_135_1261_1587 + 1;


  switch_5945:
    ;
    switch (tmpval_5919) {

      case 0:
        {
            GibCursor jump_3087 = ls_135_1261_1587 + 1;

            return (GibCursorGibCursorGibIntProd) {end_r_2438, jump_3087,
                                                   km_133_1259_1585};
            break;
        }

      case 1:
        {
            GibInt tmpval_5921 = *(GibInt *) tmpcur_5920;
            GibCursor tmpcur_5922 = tmpcur_5920 + sizeof(GibInt);
            GibInt tmpval_5923 = *(GibInt *) tmpcur_5922;
            GibCursor tmpcur_5924 = tmpcur_5922 + sizeof(GibInt);
            GibInt fltPrm_1495_1594 = tmpval_5921 + tmpval_5923;
            GibBool fltIf_1494_1595 = fltPrm_1495_1594 >= m_134_1260_1586;

            if (fltIf_1494_1595) {
                GibInt fltAppE_1496_1596 = k_132_1258_1584 + 1;
                GibInt fltAppE_1497_1597 = tmpval_5921 + tmpval_5923;
                // GibCursorGibCursorGibIntProd tmp_struct_24 =
                                              return findk(end_r_2438, fltAppE_1496_1596, k_132_1258_1584, fltAppE_1497_1597, tmpcur_5924);
                // GibCursor pvrtmp_5927 = tmp_struct_24.field0;
                // GibCursor pvrtmp_5928 = tmp_struct_24.field1;
                // GibInt pvrtmp_5929 = tmp_struct_24.field2;

                // return (GibCursorGibCursorGibIntProd) {pvrtmp_5927, pvrtmp_5928,
                //                                        pvrtmp_5929};
            } else {
                GibInt fltAppE_1498_1598 = k_132_1258_1584 + 1;
                // GibCursorGibCursorGibIntProd tmp_struct_25 =
                                              return findk(end_r_2438, fltAppE_1498_1598, km_133_1259_1585, m_134_1260_1586, tmpcur_5924);
                // GibCursor pvrtmp_5930 = tmp_struct_25.field0;
                // GibCursor pvrtmp_5931 = tmp_struct_25.field1;
                // GibInt pvrtmp_5932 = tmp_struct_25.field2;

                // return (GibCursorGibCursorGibIntProd) {pvrtmp_5930, pvrtmp_5931,
                //                                        pvrtmp_5932};
            }
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_27 = *(uintptr_t *) tmpcur_5920;
            GibCursor tmpcur_5933 = GIB_UNTAG(tagged_tmpcur_27);
            GibCursor tmpaftercur_5934 = tmpcur_5920 + 8;
            uint16_t tmptag_5935 = GIB_GET_TAG(tagged_tmpcur_27);
            GibCursor end_from_tagged_indr_3249 = tmpcur_5933 + tmptag_5935;
            GibCursor jump_3251 = tmpcur_5920 + 8;
            GibCursorGibCursorGibIntProd tmp_struct_26 =
                                          findk(end_from_tagged_indr_3249, k_132_1258_1584, km_133_1259_1585, m_134_1260_1586, tmpcur_5933);
            GibCursor pvrtmp_5936 = tmp_struct_26.field0;
            GibCursor pvrtmp_5937 = tmp_struct_26.field1;
            GibInt pvrtmp_5938 = tmp_struct_26.field2;

            return (GibCursorGibCursorGibIntProd) {end_r_2438, jump_3251,
                                                   pvrtmp_5938};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_29 = *(uintptr_t *) tmpcur_5920;
            GibCursor tmpcur_5939 = GIB_UNTAG(tagged_tmpcur_29);
            GibCursor tmpaftercur_5940 = tmpcur_5920 + 8;
            uint16_t tmptag_5941 = GIB_GET_TAG(tagged_tmpcur_29);
            GibCursor end_from_tagged_indr_3249 = tmpcur_5939 + tmptag_5941;
            GibCursorGibCursorGibIntProd tmp_struct_28 =
                                          findk(end_from_tagged_indr_3249, k_132_1258_1584, km_133_1259_1585, m_134_1260_1586, tmpcur_5939);
            GibCursor pvrtmp_5942 = tmp_struct_28.field0;
            GibCursor pvrtmp_5943 = tmp_struct_28.field1;
            GibInt pvrtmp_5944 = tmp_struct_28.field2;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_5942, pvrtmp_5943,
                                                   pvrtmp_5944};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5919");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd algc(GibCursor end_r_2443,
                                                                GibCursor end_r_2444,
                                                                GibCursor end_r_2445,
                                                                GibCursor end_r_2446,
                                                                GibCursor loc_2442,
                                                                GibInt m_141_1268_1599,
                                                                GibInt n_142_1269_1600,
                                                                GibCursor xs_143_1270_1601,
                                                                GibCursor ys_144_1271_1602,
                                                                GibCursor zs_145_1272_1603)
{
    // GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    // GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    // GibShadowstackFrame *frame;

    if (loc_2442 + 18 > end_r_2446) {
        gib_grow_region(&loc_2442, &end_r_2446);
    }

    GibCursorGibBoolProd tmp_struct_30 =
                          is_empty_plist_778(end_r_2444, ys_144_1271_1602);
    GibCursor pvrtmp_5946 = tmp_struct_30.field0;
    GibBool pvrtmp_5947 = tmp_struct_30.field1;

    if (pvrtmp_5947) {
        if (loc_2442 + 18 > end_r_2446) {
            gib_grow_region(&loc_2442, &end_r_2446);
        }
        gib_indirection_barrier(loc_2442, end_r_2446, zs_145_1272_1603,
                                end_r_2445, PList_v_775_T);

        GibCursor end_4231 = loc_2442 + 9;

        return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2443,
                                                                             pvrtmp_5946,
                                                                             end_r_2445,
                                                                             end_r_2446,
                                                                             loc_2442,
                                                                             end_4231};
    } else {
        GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_34
                                                                   =
                                                                    caseFn_1216(end_r_2443, end_r_2444, end_r_2445, end_r_2446, loc_2442, m_141_1268_1599, n_142_1269_1600, xs_143_1270_1601, ys_144_1271_1602, zs_145_1272_1603);
        GibCursor pvrtmp_5952 = tmp_struct_34.field0;
        GibCursor pvrtmp_5953 = tmp_struct_34.field1;
        GibCursor pvrtmp_5954 = tmp_struct_34.field2;
        GibCursor pvrtmp_5955 = tmp_struct_34.field3;
        GibCursor pvrtmp_5956 = tmp_struct_34.field4;
        GibCursor pvrtmp_5957 = tmp_struct_34.field5;

        return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_5952,
                                                                             pvrtmp_5953,
                                                                             pvrtmp_5954,
                                                                             pvrtmp_5955,
                                                                             pvrtmp_5956,
                                                                             pvrtmp_5957};
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd algb2(GibCursor end_r_2449,
                                                        GibCursor end_r_2450,
                                                        GibCursor loc_2448,
                                                        GibInt x_161_1273_1605,
                                                        GibInt k0j1_162_1274_1606,
                                                        GibInt k1j1_163_1275_1607,
                                                        GibCursor ls_164_1276_1608)
{
    // GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    // GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    // GibShadowstackFrame *frame;

    if (loc_2448 + 26 > end_r_2450) {
        gib_grow_region(&loc_2448, &end_r_2450);
    }

    GibPackedTag tmpval_5964 = *(GibPackedTag *) ls_164_1276_1608;
    GibCursor tmpcur_5965 = ls_164_1276_1608 + 1;


  switch_6018:
    ;
    switch (tmpval_5964) {

      case 0:
        {
            GibCursor jump_3095 = ls_164_1276_1608 + 1;

            *(GibPackedTag *) loc_2448 = 0;

            GibCursor writetag_4239 = loc_2448 + 1;
            GibCursor after_tag_4240 = loc_2448 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2449,
                                                                        end_r_2450,
                                                                        jump_3095,
                                                                        loc_2448,
                                                                        after_tag_4240};
            break;
        }

      case 1:
        {
            GibInt tmpval_5970 = *(GibInt *) tmpcur_5965;
            GibCursor tmpcur_5971 = tmpcur_5965 + sizeof(GibInt);
            GibInt tmpval_5972 = *(GibInt *) tmpcur_5971;
            GibCursor tmpcur_5973 = tmpcur_5971 + sizeof(GibInt);
            GibBool fltIf_1500_1615 = x_161_1273_1605 == tmpval_5970;
            GibInt kjcurr_170_1283_1616;

            if (fltIf_1500_1615) {
                GibInt flt_5976 = k0j1_162_1274_1606 + 1;

                kjcurr_170_1283_1616 = flt_5976;
            } else {
                GibInt kjcurr_170_1283_1616hack =
                        maxInt(k1j1_163_1275_1607, tmpval_5972);

                kjcurr_170_1283_1616 = kjcurr_170_1283_1616hack;
            }

            GibCursor loc_2637 = loc_2448 + 17;

            *(GibPackedTag *) loc_2448 = 1;

            GibCursor writetag_4252 = loc_2448 + 1;
            GibCursor after_tag_4253 = loc_2448 + 1;

            *(GibInt *) after_tag_4253 = tmpval_5970;

            GibCursor writecur_4257 = after_tag_4253 + sizeof(GibInt);

            *(GibInt *) writecur_4257 = kjcurr_170_1283_1616;

            GibCursor writecur_4258 = writecur_4257 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_38 =
                                                               algb2(end_r_2449, end_r_2450, loc_2637, x_161_1273_1605, tmpval_5972, kjcurr_170_1283_1616, tmpcur_5973);
            GibCursor pvrtmp_5977 = tmp_struct_38.field0;
            GibCursor pvrtmp_5978 = tmp_struct_38.field1;
            GibCursor pvrtmp_5979 = tmp_struct_38.field2;
            GibCursor pvrtmp_5980 = tmp_struct_38.field3;
            GibCursor pvrtmp_5981 = tmp_struct_38.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_5977,
                                                                        pvrtmp_5978,
                                                                        pvrtmp_5979,
                                                                        loc_2448,
                                                                        pvrtmp_5981};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_40 = *(uintptr_t *) tmpcur_5965;
            GibCursor tmpcur_5990 = GIB_UNTAG(tagged_tmpcur_40);
            GibCursor tmpaftercur_5991 = tmpcur_5965 + 8;
            uint16_t tmptag_5992 = GIB_GET_TAG(tagged_tmpcur_40);
            GibCursor end_from_tagged_indr_3255 = tmpcur_5990 + tmptag_5992;
            GibCursor jump_3257 = tmpcur_5965 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_39 =
                                                               algb2(end_from_tagged_indr_3255, end_r_2450, loc_2448, x_161_1273_1605, k0j1_162_1274_1606, k1j1_163_1275_1607, tmpcur_5990);
            GibCursor pvrtmp_5993 = tmp_struct_39.field0;
            GibCursor pvrtmp_5994 = tmp_struct_39.field1;
            GibCursor pvrtmp_5995 = tmp_struct_39.field2;
            GibCursor pvrtmp_5996 = tmp_struct_39.field3;
            GibCursor pvrtmp_5997 = tmp_struct_39.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2449,
                                                                        pvrtmp_5994,
                                                                        jump_3257,
                                                                        pvrtmp_5996,
                                                                        pvrtmp_5997};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_42 = *(uintptr_t *) tmpcur_5965;
            GibCursor tmpcur_6004 = GIB_UNTAG(tagged_tmpcur_42);
            GibCursor tmpaftercur_6005 = tmpcur_5965 + 8;
            uint16_t tmptag_6006 = GIB_GET_TAG(tagged_tmpcur_42);
            GibCursor end_from_tagged_indr_3255 = tmpcur_6004 + tmptag_6006;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_41 =
                                                               algb2(end_from_tagged_indr_3255, end_r_2450, loc_2448, x_161_1273_1605, k0j1_162_1274_1606, k1j1_163_1275_1607, tmpcur_6004);
            GibCursor pvrtmp_6007 = tmp_struct_41.field0;
            GibCursor pvrtmp_6008 = tmp_struct_41.field1;
            GibCursor pvrtmp_6009 = tmp_struct_41.field2;
            GibCursor pvrtmp_6010 = tmp_struct_41.field3;
            GibCursor pvrtmp_6011 = tmp_struct_41.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6007,
                                                                        pvrtmp_6008,
                                                                        pvrtmp_6009,
                                                                        pvrtmp_6010,
                                                                        pvrtmp_6011};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5964");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd algb1(GibCursor end_r_2454,
                                                                          GibCursor end_r_2455,
                                                                          GibCursor end_r_2456,
                                                                          GibCursor loc_2453,
                                                                          GibCursor xs_171_1284_1618,
                                                                          GibCursor ys_172_1285_1619)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2453 + 18 > end_r_2456) {
        gib_grow_region(&loc_2453, &end_r_2456);
    }

    GibPackedTag tmpval_6019 = *(GibPackedTag *) xs_171_1284_1618;
    GibCursor tmpcur_6020 = xs_171_1284_1618 + 1;


  switch_6089:
    ;
    switch (tmpval_6019) {

      case 0:
        {
            GibCursor jump_3101 = xs_171_1284_1618 + 1;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_46 =
                                                               map_plist_784_1062(end_r_2455, end_r_2456, loc_2453, ys_172_1285_1619);
            GibCursor pvrtmp_6021 = tmp_struct_46.field0;
            GibCursor pvrtmp_6022 = tmp_struct_46.field1;
            GibCursor pvrtmp_6023 = tmp_struct_46.field2;
            GibCursor pvrtmp_6024 = tmp_struct_46.field3;
            GibCursor pvrtmp_6025 = tmp_struct_46.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2454,
                                                                                          pvrtmp_6021,
                                                                                          pvrtmp_6022,
                                                                                          jump_3101,
                                                                                          pvrtmp_6023,
                                                                                          pvrtmp_6024,
                                                                                          pvrtmp_6025};
            break;
        }

      case 1:
        {
            GibInt tmpval_6032 = *(GibInt *) tmpcur_6020;
            GibCursor tmpcur_6033 = tmpcur_6020 + sizeof(GibInt);

            gib_shadowstack_push(rstack, ys_172_1285_1619, end_r_2455, Stk,
                                 PList_v_777_T);
            gib_shadowstack_push(rstack, tmpcur_6033, end_r_2454, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(wstack, loc_2453, end_r_2456, Stk,
                                 PList_v_775_T);

            GibChunk region_6034 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_2661 = region_6034.start;
            GibCursor end_r_2661 = region_6034.end;

            frame = gib_shadowstack_pop(wstack);
            loc_2453 = frame->ptr;
            end_r_2456 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tmpcur_6033 = frame->ptr;
            end_r_2454 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_172_1285_1619 = frame->ptr;
            end_r_2455 = frame->endptr;

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_47 =
                                                               algb2(end_r_2455, end_r_2661, r_2661, tmpval_6032, 0, 0, ys_172_1285_1619);
            GibCursor pvrtmp_6035 = tmp_struct_47.field0;
            GibCursor pvrtmp_6036 = tmp_struct_47.field1;
            GibCursor pvrtmp_6037 = tmp_struct_47.field2;
            GibCursor pvrtmp_6038 = tmp_struct_47.field3;
            GibCursor pvrtmp_6039 = tmp_struct_47.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_48 =
             algb1(end_r_2454, pvrtmp_6036, end_r_2456, loc_2453, tmpcur_6033, pvrtmp_6038);
            GibCursor pvrtmp_6044 = tmp_struct_48.field0;
            GibCursor pvrtmp_6045 = tmp_struct_48.field1;
            GibCursor pvrtmp_6046 = tmp_struct_48.field2;
            GibCursor pvrtmp_6047 = tmp_struct_48.field3;
            GibCursor pvrtmp_6048 = tmp_struct_48.field4;
            GibCursor pvrtmp_6049 = tmp_struct_48.field5;
            GibCursor pvrtmp_6050 = tmp_struct_48.field6;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6044,
                                                                                          pvrtmp_6035,
                                                                                          pvrtmp_6046,
                                                                                          pvrtmp_6047,
                                                                                          pvrtmp_6037,
                                                                                          pvrtmp_6049,
                                                                                          pvrtmp_6050};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_50 = *(uintptr_t *) tmpcur_6020;
            GibCursor tmpcur_6057 = GIB_UNTAG(tagged_tmpcur_50);
            GibCursor tmpaftercur_6058 = tmpcur_6020 + 8;
            uint16_t tmptag_6059 = GIB_GET_TAG(tagged_tmpcur_50);
            GibCursor end_from_tagged_indr_3261 = tmpcur_6057 + tmptag_6059;
            GibCursor jump_3263 = tmpcur_6020 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_49 =
             algb1(end_from_tagged_indr_3261, end_r_2455, end_r_2456, loc_2453, tmpcur_6057, ys_172_1285_1619);
            GibCursor pvrtmp_6060 = tmp_struct_49.field0;
            GibCursor pvrtmp_6061 = tmp_struct_49.field1;
            GibCursor pvrtmp_6062 = tmp_struct_49.field2;
            GibCursor pvrtmp_6063 = tmp_struct_49.field3;
            GibCursor pvrtmp_6064 = tmp_struct_49.field4;
            GibCursor pvrtmp_6065 = tmp_struct_49.field5;
            GibCursor pvrtmp_6066 = tmp_struct_49.field6;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2454,
                                                                                          pvrtmp_6061,
                                                                                          pvrtmp_6062,
                                                                                          jump_3263,
                                                                                          pvrtmp_6064,
                                                                                          pvrtmp_6065,
                                                                                          pvrtmp_6066};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_52 = *(uintptr_t *) tmpcur_6020;
            GibCursor tmpcur_6073 = GIB_UNTAG(tagged_tmpcur_52);
            GibCursor tmpaftercur_6074 = tmpcur_6020 + 8;
            uint16_t tmptag_6075 = GIB_GET_TAG(tagged_tmpcur_52);
            GibCursor end_from_tagged_indr_3261 = tmpcur_6073 + tmptag_6075;
            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_51 =
             algb1(end_from_tagged_indr_3261, end_r_2455, end_r_2456, loc_2453, tmpcur_6073, ys_172_1285_1619);
            GibCursor pvrtmp_6076 = tmp_struct_51.field0;
            GibCursor pvrtmp_6077 = tmp_struct_51.field1;
            GibCursor pvrtmp_6078 = tmp_struct_51.field2;
            GibCursor pvrtmp_6079 = tmp_struct_51.field3;
            GibCursor pvrtmp_6080 = tmp_struct_51.field4;
            GibCursor pvrtmp_6081 = tmp_struct_51.field5;
            GibCursor pvrtmp_6082 = tmp_struct_51.field6;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6076,
                                                                                          pvrtmp_6077,
                                                                                          pvrtmp_6078,
                                                                                          pvrtmp_6079,
                                                                                          pvrtmp_6080,
                                                                                          pvrtmp_6081,
                                                                                          pvrtmp_6082};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6019");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd algb(GibCursor end_r_2460,
                                                                         GibCursor end_r_2461,
                                                                         GibCursor end_r_2462,
                                                                         GibCursor loc_2459,
                                                                         GibCursor xs_178_1288_1623,
                                                                         GibCursor ys_179_1289_1624)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2459 + 18 > end_r_2462) {
        gib_grow_region(&loc_2459, &end_r_2462);
    }
    gib_shadowstack_push(rstack, xs_178_1288_1623, end_r_2460, Stk,
                         PList_v_775_T);
    gib_shadowstack_push(rstack, ys_179_1289_1624, end_r_2461, Stk,
                         PList_v_775_T);
    gib_shadowstack_push(wstack, loc_2459, end_r_2462, Stk, PList_v_775_T);

    GibChunk region_6090 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_2674 = region_6090.start;
    GibCursor end_r_2674 = region_6090.end;

    frame = gib_shadowstack_pop(wstack);
    loc_2459 = frame->ptr;
    end_r_2462 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    ys_179_1289_1624 = frame->ptr;
    end_r_2461 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    xs_178_1288_1623 = frame->ptr;
    end_r_2460 = frame->endptr;

    GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_56 =
                                                       zip0(end_r_2461, end_r_2674, r_2674, ys_179_1289_1624);
    GibCursor pvrtmp_6091 = tmp_struct_56.field0;
    GibCursor pvrtmp_6092 = tmp_struct_56.field1;
    GibCursor pvrtmp_6093 = tmp_struct_56.field2;
    GibCursor pvrtmp_6094 = tmp_struct_56.field3;
    GibCursor pvrtmp_6095 = tmp_struct_56.field4;
    GibCursor loc_2672 = loc_2459 + 9;

    *(GibPackedTag *) loc_2459 = 1;

    GibCursor writetag_4304 = loc_2459 + 1;
    GibCursor after_tag_4305 = loc_2459 + 1;

    *(GibInt *) after_tag_4305 = 0;

    GibCursor writecur_4309 = after_tag_4305 + sizeof(GibInt);

    gib_shadowstack_push(rstack, loc_2459, end_r_2462, Stk, PList_v_775_T);

    GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
    tmp_struct_57 =
     algb1(end_r_2460, pvrtmp_6092, end_r_2462, loc_2672, xs_178_1288_1623, pvrtmp_6094);
    GibCursor pvrtmp_6100 = tmp_struct_57.field0;
    GibCursor pvrtmp_6101 = tmp_struct_57.field1;
    GibCursor pvrtmp_6102 = tmp_struct_57.field2;
    GibCursor pvrtmp_6103 = tmp_struct_57.field3;
    GibCursor pvrtmp_6104 = tmp_struct_57.field4;
    GibCursor pvrtmp_6105 = tmp_struct_57.field5;
    GibCursor pvrtmp_6106 = tmp_struct_57.field6;

    frame = gib_shadowstack_pop(rstack);
    loc_2459 = frame->ptr;
    end_r_2462 = frame->endptr;
    return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6100,
                                                                                  pvrtmp_6091,
                                                                                  pvrtmp_6102,
                                                                                  pvrtmp_6103,
                                                                                  pvrtmp_6093,
                                                                                  loc_2459,
                                                                                  pvrtmp_6106};
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd zip0(GibCursor end_r_2465,
                                                       GibCursor end_r_2466,
                                                       GibCursor loc_2464,
                                                       GibCursor ls_180_1290_1627)
{
    // GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    // GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    // GibShadowstackFrame *frame;

    if (loc_2464 + 26 > end_r_2466) {
        gib_grow_region(&loc_2464, &end_r_2466);
    }

    GibPackedTag tmpval_6115 = *(GibPackedTag *) ls_180_1290_1627;
    GibCursor tmpcur_6116 = ls_180_1290_1627 + 1;


  switch_6164:
    ;
    switch (tmpval_6115) {

      case 0:
        {
            GibCursor jump_3113 = ls_180_1290_1627 + 1;

            *(GibPackedTag *) loc_2464 = 0;

            GibCursor writetag_4314 = loc_2464 + 1;
            GibCursor after_tag_4315 = loc_2464 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2465,
                                                                        end_r_2466,
                                                                        jump_3113,
                                                                        loc_2464,
                                                                        after_tag_4315};
            break;
        }

      case 1:
        {
            GibInt tmpval_6121 = *(GibInt *) tmpcur_6116;
            GibCursor tmpcur_6122 = tmpcur_6116 + sizeof(GibInt);
            GibCursor loc_2685 = loc_2464 + 17;

            *(GibPackedTag *) loc_2464 = 1;

            GibCursor writetag_4326 = loc_2464 + 1;
            GibCursor after_tag_4327 = loc_2464 + 1;

            *(GibInt *) after_tag_4327 = tmpval_6121;

            GibCursor writecur_4331 = after_tag_4327 + sizeof(GibInt);

            *(GibInt *) writecur_4331 = 0;

            GibCursor writecur_4332 = writecur_4331 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_61 =
                                                               zip0(end_r_2465, end_r_2466, loc_2685, tmpcur_6122);
            GibCursor pvrtmp_6123 = tmp_struct_61.field0;
            GibCursor pvrtmp_6124 = tmp_struct_61.field1;
            GibCursor pvrtmp_6125 = tmp_struct_61.field2;
            GibCursor pvrtmp_6126 = tmp_struct_61.field3;
            GibCursor pvrtmp_6127 = tmp_struct_61.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6123,
                                                                        pvrtmp_6124,
                                                                        pvrtmp_6125,
                                                                        loc_2464,
                                                                        pvrtmp_6127};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_63 = *(uintptr_t *) tmpcur_6116;
            GibCursor tmpcur_6136 = GIB_UNTAG(tagged_tmpcur_63);
            GibCursor tmpaftercur_6137 = tmpcur_6116 + 8;
            uint16_t tmptag_6138 = GIB_GET_TAG(tagged_tmpcur_63);
            GibCursor end_from_tagged_indr_3268 = tmpcur_6136 + tmptag_6138;
            GibCursor jump_3270 = tmpcur_6116 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_62 =
                                                               zip0(end_from_tagged_indr_3268, end_r_2466, loc_2464, tmpcur_6136);
            GibCursor pvrtmp_6139 = tmp_struct_62.field0;
            GibCursor pvrtmp_6140 = tmp_struct_62.field1;
            GibCursor pvrtmp_6141 = tmp_struct_62.field2;
            GibCursor pvrtmp_6142 = tmp_struct_62.field3;
            GibCursor pvrtmp_6143 = tmp_struct_62.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2465,
                                                                        pvrtmp_6140,
                                                                        jump_3270,
                                                                        pvrtmp_6142,
                                                                        pvrtmp_6143};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_65 = *(uintptr_t *) tmpcur_6116;
            GibCursor tmpcur_6150 = GIB_UNTAG(tagged_tmpcur_65);
            GibCursor tmpaftercur_6151 = tmpcur_6116 + 8;
            uint16_t tmptag_6152 = GIB_GET_TAG(tagged_tmpcur_65);
            GibCursor end_from_tagged_indr_3268 = tmpcur_6150 + tmptag_6152;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_64 =
                                                               zip0(end_from_tagged_indr_3268, end_r_2466, loc_2464, tmpcur_6150);
            GibCursor pvrtmp_6153 = tmp_struct_64.field0;
            GibCursor pvrtmp_6154 = tmp_struct_64.field1;
            GibCursor pvrtmp_6155 = tmp_struct_64.field2;
            GibCursor pvrtmp_6156 = tmp_struct_64.field3;
            GibCursor pvrtmp_6157 = tmp_struct_64.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6153,
                                                                        pvrtmp_6154,
                                                                        pvrtmp_6155,
                                                                        pvrtmp_6156,
                                                                        pvrtmp_6157};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6115");
            exit(1);
        }
    }
}
static inline
GibInt maxInt(GibInt a_189_1293_1631, GibInt b_190_1294_1632)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_1506_1633 = a_189_1293_1631 > b_190_1294_1632;

    if (fltIf_1506_1633) {
        return a_189_1293_1631;
    } else {
        return b_190_1294_1632;
    }
}
GibCursorGibCursorGibIntProd length_plist_776(GibCursor end_r_2468,
                                              GibCursor a_226_1313_1634)
{
    // GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    // GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    // GibShadowstackFrame *frame;

    GibPackedTag tmpval_6165 = *(GibPackedTag *) a_226_1313_1634;
    GibCursor tmpcur_6166 = a_226_1313_1634 + 1;


  switch_6184:
    ;
    switch (tmpval_6165) {

      case 0:
        {
            GibCursor jump_3119 = a_226_1313_1634 + 1;

            return (GibCursorGibCursorGibIntProd) {end_r_2468, jump_3119, 0};
            break;
        }

      case 1:
        {
            GibInt tmpval_6167 = *(GibInt *) tmpcur_6166;
            GibCursor tmpcur_6168 = tmpcur_6166 + sizeof(GibInt);
            GibCursorGibCursorGibIntProd tmp_struct_69 =
                                          length_plist_776(end_r_2468, tmpcur_6168);
            GibCursor pvrtmp_6169 = tmp_struct_69.field0;
            GibCursor pvrtmp_6170 = tmp_struct_69.field1;
            GibInt pvrtmp_6171 = tmp_struct_69.field2;
            GibInt tailprim_3122 = 1 + pvrtmp_6171;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_6169, pvrtmp_6170,
                                                   tailprim_3122};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_71 = *(uintptr_t *) tmpcur_6166;
            GibCursor tmpcur_6172 = GIB_UNTAG(tagged_tmpcur_71);
            GibCursor tmpaftercur_6173 = tmpcur_6166 + 8;
            uint16_t tmptag_6174 = GIB_GET_TAG(tagged_tmpcur_71);
            GibCursor end_from_tagged_indr_3274 = tmpcur_6172 + tmptag_6174;
            GibCursor jump_3276 = tmpcur_6166 + 8;
            GibCursorGibCursorGibIntProd tmp_struct_70 =
                                          length_plist_776(end_from_tagged_indr_3274, tmpcur_6172);
            GibCursor pvrtmp_6175 = tmp_struct_70.field0;
            GibCursor pvrtmp_6176 = tmp_struct_70.field1;
            GibInt pvrtmp_6177 = tmp_struct_70.field2;

            return (GibCursorGibCursorGibIntProd) {end_r_2468, jump_3276,
                                                   pvrtmp_6177};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_73 = *(uintptr_t *) tmpcur_6166;
            GibCursor tmpcur_6178 = GIB_UNTAG(tagged_tmpcur_73);
            GibCursor tmpaftercur_6179 = tmpcur_6166 + 8;
            uint16_t tmptag_6180 = GIB_GET_TAG(tagged_tmpcur_73);
            GibCursor end_from_tagged_indr_3274 = tmpcur_6178 + tmptag_6180;
            GibCursorGibCursorGibIntProd tmp_struct_72 =
                                          length_plist_776(end_from_tagged_indr_3274, tmpcur_6178);
            GibCursor pvrtmp_6181 = tmp_struct_72.field0;
            GibCursor pvrtmp_6182 = tmp_struct_72.field1;
            GibInt pvrtmp_6183 = tmp_struct_72.field2;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_6181, pvrtmp_6182,
                                                   pvrtmp_6183};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6165");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd reverse_plist_782(GibCursor end_r_2472,
                                                                             GibCursor end_r_2473,
                                                                             GibCursor end_r_2474,
                                                                             GibCursor loc_2471,
                                                                             GibCursor xs_221_1316_1638,
                                                                             GibCursor acc_222_1317_1639)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2471 + 18 > end_r_2474) {
        gib_grow_region(&loc_2471, &end_r_2474);
    }

    GibPackedTag tmpval_6185 = *(GibPackedTag *) xs_221_1316_1638;
    GibCursor tmpcur_6186 = xs_221_1316_1638 + 1;


  switch_6240:
    ;
    switch (tmpval_6185) {

      case 0:
        {
            GibCursor jump_3123 = xs_221_1316_1638 + 1;

            if (loc_2471 + 18 > end_r_2474) {
                gib_grow_region(&loc_2471, &end_r_2474);
            }
            gib_indirection_barrier(loc_2471, end_r_2474, acc_222_1317_1639,
                                    end_r_2473, PList_v_775_T);

            GibCursor end_4361 = loc_2471 + 9;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2472,
                                                                                 end_r_2473,
                                                                                 end_r_2474,
                                                                                 jump_3123,
                                                                                 loc_2471,
                                                                                 end_4361};
            break;
        }

      case 1:
        {
            GibInt tmpval_6191 = *(GibInt *) tmpcur_6186;
            GibCursor tmpcur_6192 = tmpcur_6186 + sizeof(GibInt);

            gib_shadowstack_push(rstack, acc_222_1317_1639, end_r_2473, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, tmpcur_6192, end_r_2472, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(wstack, loc_2471, end_r_2474, Stk,
                                 PList_v_775_T);

            GibChunk region_6193 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_2712 = region_6193.start;
            GibCursor end_r_2712 = region_6193.end;

            frame = gib_shadowstack_pop(wstack);
            loc_2471 = frame->ptr;
            end_r_2474 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tmpcur_6192 = frame->ptr;
            end_r_2472 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            acc_222_1317_1639 = frame->ptr;
            end_r_2473 = frame->endptr;

            GibCursor loc_2701 = r_2712 + 9;

            *(GibPackedTag *) r_2712 = 1;

            GibCursor writetag_4368 = r_2712 + 1;
            GibCursor after_tag_4369 = r_2712 + 1;

            *(GibInt *) after_tag_4369 = tmpval_6191;

            GibCursor writecur_4373 = after_tag_4369 + sizeof(GibInt);

            if (loc_2701 + 18 > end_r_2712) {
                gib_grow_region(&loc_2701, &end_r_2712);
            }
            gib_indirection_barrier(loc_2701, end_r_2712, acc_222_1317_1639,
                                    end_r_2473, PList_v_775_T);

            GibCursor end_4366 = loc_2701 + 9;
            // GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            // tmp_struct_77 =
             return reverse_plist_782(end_r_2472, end_r_2712, end_r_2474, loc_2471, tmpcur_6192, r_2712);
            // GibCursor pvrtmp_6198 = tmp_struct_77.field0;
            // GibCursor pvrtmp_6199 = tmp_struct_77.field1;
            // GibCursor pvrtmp_6200 = tmp_struct_77.field2;
            // GibCursor pvrtmp_6201 = tmp_struct_77.field3;
            // GibCursor pvrtmp_6202 = tmp_struct_77.field4;
            // GibCursor pvrtmp_6203 = tmp_struct_77.field5;

            // return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6198,
            //                                                                      end_r_2473,
            //                                                                      pvrtmp_6200,
            //                                                                      pvrtmp_6201,
            //                                                                      pvrtmp_6202,
            //                                                                      pvrtmp_6203};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_82 = *(uintptr_t *) tmpcur_6186;
            GibCursor tmpcur_6210 = GIB_UNTAG(tagged_tmpcur_82);
            GibCursor tmpaftercur_6211 = tmpcur_6186 + 8;
            uint16_t tmptag_6212 = GIB_GET_TAG(tagged_tmpcur_82);
            GibCursor end_from_tagged_indr_3280 = tmpcur_6210 + tmptag_6212;
            GibCursor jump_3282 = tmpcur_6186 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_81 =
             reverse_plist_782(end_from_tagged_indr_3280, end_r_2473, end_r_2474, loc_2471, tmpcur_6210, acc_222_1317_1639);
            GibCursor pvrtmp_6213 = tmp_struct_81.field0;
            GibCursor pvrtmp_6214 = tmp_struct_81.field1;
            GibCursor pvrtmp_6215 = tmp_struct_81.field2;
            GibCursor pvrtmp_6216 = tmp_struct_81.field3;
            GibCursor pvrtmp_6217 = tmp_struct_81.field4;
            GibCursor pvrtmp_6218 = tmp_struct_81.field5;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2472,
                                                                                 pvrtmp_6214,
                                                                                 pvrtmp_6215,
                                                                                 jump_3282,
                                                                                 pvrtmp_6217,
                                                                                 pvrtmp_6218};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_84 = *(uintptr_t *) tmpcur_6186;
            GibCursor tmpcur_6225 = GIB_UNTAG(tagged_tmpcur_84);
            GibCursor tmpaftercur_6226 = tmpcur_6186 + 8;
            uint16_t tmptag_6227 = GIB_GET_TAG(tagged_tmpcur_84);
            GibCursor end_from_tagged_indr_3280 = tmpcur_6225 + tmptag_6227;
            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_83 =
             reverse_plist_782(end_from_tagged_indr_3280, end_r_2473, end_r_2474, loc_2471, tmpcur_6225, acc_222_1317_1639);
            GibCursor pvrtmp_6228 = tmp_struct_83.field0;
            GibCursor pvrtmp_6229 = tmp_struct_83.field1;
            GibCursor pvrtmp_6230 = tmp_struct_83.field2;
            GibCursor pvrtmp_6231 = tmp_struct_83.field3;
            GibCursor pvrtmp_6232 = tmp_struct_83.field4;
            GibCursor pvrtmp_6233 = tmp_struct_83.field5;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6228,
                                                                                 pvrtmp_6229,
                                                                                 pvrtmp_6230,
                                                                                 pvrtmp_6231,
                                                                                 pvrtmp_6232,
                                                                                 pvrtmp_6233};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6185");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd zip_plist_783(GibCursor end_r_2478,
                                                                GibCursor end_r_2479,
                                                                GibCursor end_r_2480,
                                                                GibCursor loc_2477,
                                                                GibCursor as_213_1320_1643,
                                                                GibCursor bs_214_1321_1644)
{
    // GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    // GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    // GibShadowstackFrame *frame;

    if (loc_2477 + 26 > end_r_2480) {
        gib_grow_region(&loc_2477, &end_r_2480);
    }

    GibPackedTag tmpval_6241 = *(GibPackedTag *) as_213_1320_1643;
    GibCursor tmpcur_6242 = as_213_1320_1643 + 1;


  switch_6288:
    ;
    switch (tmpval_6241) {

      case 0:
        {
            *(GibPackedTag *) loc_2477 = 0;

            GibCursor writetag_4394 = loc_2477 + 1;
            GibCursor after_tag_4395 = loc_2477 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2478,
                                                                        end_r_2479,
                                                                        end_r_2480,
                                                                        loc_2477,
                                                                        after_tag_4395};
            break;
        }

      case 1:
        {
            GibInt tmpval_6247 = *(GibInt *) tmpcur_6242;
            GibCursor tmpcur_6248 = tmpcur_6242 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_88 =
                                                               caseFn_1222(end_r_2479, end_r_2478, end_r_2480, loc_2477, bs_214_1321_1644, tmpval_6247, tmpcur_6248);
            GibCursor pvrtmp_6249 = tmp_struct_88.field0;
            GibCursor pvrtmp_6250 = tmp_struct_88.field1;
            GibCursor pvrtmp_6251 = tmp_struct_88.field2;
            GibCursor pvrtmp_6252 = tmp_struct_88.field3;
            GibCursor pvrtmp_6253 = tmp_struct_88.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6250,
                                                                        pvrtmp_6249,
                                                                        pvrtmp_6251,
                                                                        pvrtmp_6252,
                                                                        pvrtmp_6253};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_90 = *(uintptr_t *) tmpcur_6242;
            GibCursor tmpcur_6260 = GIB_UNTAG(tagged_tmpcur_90);
            GibCursor tmpaftercur_6261 = tmpcur_6242 + 8;
            uint16_t tmptag_6262 = GIB_GET_TAG(tagged_tmpcur_90);
            GibCursor end_from_tagged_indr_3286 = tmpcur_6260 + tmptag_6262;
            GibCursor jump_3288 = tmpcur_6242 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_89 =
                                                               zip_plist_783(end_from_tagged_indr_3286, end_r_2479, end_r_2480, loc_2477, tmpcur_6260, bs_214_1321_1644);
            GibCursor pvrtmp_6263 = tmp_struct_89.field0;
            GibCursor pvrtmp_6264 = tmp_struct_89.field1;
            GibCursor pvrtmp_6265 = tmp_struct_89.field2;
            GibCursor pvrtmp_6266 = tmp_struct_89.field3;
            GibCursor pvrtmp_6267 = tmp_struct_89.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2478,
                                                                        pvrtmp_6264,
                                                                        pvrtmp_6265,
                                                                        pvrtmp_6266,
                                                                        pvrtmp_6267};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_92 = *(uintptr_t *) tmpcur_6242;
            GibCursor tmpcur_6274 = GIB_UNTAG(tagged_tmpcur_92);
            GibCursor tmpaftercur_6275 = tmpcur_6242 + 8;
            uint16_t tmptag_6276 = GIB_GET_TAG(tagged_tmpcur_92);
            GibCursor end_from_tagged_indr_3286 = tmpcur_6274 + tmptag_6276;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_91 =
                                                               zip_plist_783(end_from_tagged_indr_3286, end_r_2479, end_r_2480, loc_2477, tmpcur_6274, bs_214_1321_1644);
            GibCursor pvrtmp_6277 = tmp_struct_91.field0;
            GibCursor pvrtmp_6278 = tmp_struct_91.field1;
            GibCursor pvrtmp_6279 = tmp_struct_91.field2;
            GibCursor pvrtmp_6280 = tmp_struct_91.field3;
            GibCursor pvrtmp_6281 = tmp_struct_91.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6277,
                                                                        pvrtmp_6278,
                                                                        pvrtmp_6279,
                                                                        pvrtmp_6280,
                                                                        pvrtmp_6281};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6241");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd drop_plist_781(GibCursor end_r_2483,
                                                        GibCursor end_r_2484,
                                                        GibCursor loc_2482,
                                                        GibInt num_208_1324_1647,
                                                        GibCursor list_209_1325_1648)
{
    // GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    // GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    // GibShadowstackFrame *frame;

    if (loc_2482 + 18 > end_r_2484) {
        gib_grow_region(&loc_2482, &end_r_2484);
    }

    GibPackedTag tmpval_6289 = *(GibPackedTag *) list_209_1325_1648;
    GibCursor tmpcur_6290 = list_209_1325_1648 + 1;


  switch_6339:
    ;
    switch (tmpval_6289) {

      case 0:
        {
            *(GibPackedTag *) loc_2482 = 0;

            GibCursor writetag_4420 = loc_2482 + 1;
            GibCursor after_tag_4421 = loc_2482 + 1;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_2483,
                                                               end_r_2484,
                                                               loc_2482,
                                                               after_tag_4421};
            break;
        }

      case 1:
        {
            GibInt tmpval_6295 = *(GibInt *) tmpcur_6290;
            GibCursor tmpcur_6296 = tmpcur_6290 + sizeof(GibInt);
            GibBool fltIf_1509_1651 = num_208_1324_1647 <= 0;

            if (fltIf_1509_1651) {
                GibCursor loc_2730 = loc_2482 + 9;

                *(GibPackedTag *) loc_2482 = 1;

                GibCursor writetag_4432 = loc_2482 + 1;
                GibCursor after_tag_4433 = loc_2482 + 1;

                *(GibInt *) after_tag_4433 = tmpval_6295;

                GibCursor writecur_4437 = after_tag_4433 + sizeof(GibInt);

                // if (loc_2730 + 18 > end_r_2484) {
                //     gib_grow_region(&loc_2730, &end_r_2484);
                // }
                gib_indirection_barrier(loc_2730, end_r_2484, tmpcur_6296,
                                        end_r_2483, PList_v_775_T);

                GibCursor end_4430 = loc_2730 + 9;

                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_2483,
                                                                   end_r_2484,
                                                                   loc_2482,
                                                                   end_4430};
            } else {
                GibInt fltAppE_1510_1652 = num_208_1324_1647 - 1;
                GibCursorGibCursorGibCursorGibCursorProd tmp_struct_99 =
                                                          drop_plist_781(end_r_2483, end_r_2484, loc_2482, fltAppE_1510_1652, tmpcur_6296);
                GibCursor pvrtmp_6303 = tmp_struct_99.field0;
                GibCursor pvrtmp_6304 = tmp_struct_99.field1;
                GibCursor pvrtmp_6305 = tmp_struct_99.field2;
                GibCursor pvrtmp_6306 = tmp_struct_99.field3;

                return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6303,
                                                                   pvrtmp_6304,
                                                                   pvrtmp_6305,
                                                                   pvrtmp_6306};
            }
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_101 = *(uintptr_t *) tmpcur_6290;
            GibCursor tmpcur_6313 = GIB_UNTAG(tagged_tmpcur_101);
            GibCursor tmpaftercur_6314 = tmpcur_6290 + 8;
            uint16_t tmptag_6315 = GIB_GET_TAG(tagged_tmpcur_101);
            GibCursor end_from_tagged_indr_3291 = tmpcur_6313 + tmptag_6315;
            GibCursor jump_3293 = tmpcur_6290 + 8;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_100 =
                                                      drop_plist_781(end_from_tagged_indr_3291, end_r_2484, loc_2482, num_208_1324_1647, tmpcur_6313);
            GibCursor pvrtmp_6316 = tmp_struct_100.field0;
            GibCursor pvrtmp_6317 = tmp_struct_100.field1;
            GibCursor pvrtmp_6318 = tmp_struct_100.field2;
            GibCursor pvrtmp_6319 = tmp_struct_100.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_2483,
                                                               pvrtmp_6317,
                                                               pvrtmp_6318,
                                                               pvrtmp_6319};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_103 = *(uintptr_t *) tmpcur_6290;
            GibCursor tmpcur_6326 = GIB_UNTAG(tagged_tmpcur_103);
            GibCursor tmpaftercur_6327 = tmpcur_6290 + 8;
            uint16_t tmptag_6328 = GIB_GET_TAG(tagged_tmpcur_103);
            GibCursor end_from_tagged_indr_3291 = tmpcur_6326 + tmptag_6328;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_102 =
                                                      drop_plist_781(end_from_tagged_indr_3291, end_r_2484, loc_2482, num_208_1324_1647, tmpcur_6326);
            GibCursor pvrtmp_6329 = tmp_struct_102.field0;
            GibCursor pvrtmp_6330 = tmp_struct_102.field1;
            GibCursor pvrtmp_6331 = tmp_struct_102.field2;
            GibCursor pvrtmp_6332 = tmp_struct_102.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6329,
                                                               pvrtmp_6330,
                                                               pvrtmp_6331,
                                                               pvrtmp_6332};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6289");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd take_plist_780(GibCursor end_r_2487,
                                                        GibCursor end_r_2488,
                                                        GibCursor loc_2486,
                                                        GibInt n_203_1328_1653,
                                                        GibCursor a_204_1329_1654)
{
    // GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    // GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    // GibShadowstackFrame *frame;

    if (loc_2486 + 18 > end_r_2488) {
        gib_grow_region(&loc_2486, &end_r_2488);
    }

    GibBool fltIf_1511_1655 = n_203_1328_1653 == 0;

    if (fltIf_1511_1655) {
        *(GibPackedTag *) loc_2486 = 0;

        GibCursor writetag_4454 = loc_2486 + 1;
        GibCursor after_tag_4455 = loc_2486 + 1;

        return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_2487,
                                                           end_r_2488, loc_2486,
                                                           after_tag_4455};
    } else {
        GibCursorGibCursorGibCursorGibCursorProd tmp_struct_107 =
                                                  caseFn_1226(end_r_2487, end_r_2488, loc_2486, n_203_1328_1653, a_204_1329_1654);
        GibCursor pvrtmp_6344 = tmp_struct_107.field0;
        GibCursor pvrtmp_6345 = tmp_struct_107.field1;
        GibCursor pvrtmp_6346 = tmp_struct_107.field2;
        GibCursor pvrtmp_6347 = tmp_struct_107.field3;

        return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6344,
                                                           pvrtmp_6345,
                                                           pvrtmp_6346,
                                                           pvrtmp_6347};
    }
}
static inline
GibCursorGibBoolProd is_empty_plist_778(GibCursor end_r_2490,
                                        GibCursor ls_191_1330_1656)
{
    // GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    // GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    // GibShadowstackFrame *frame;
    GibPackedTag tmpval_6354 = *(GibPackedTag *) ls_191_1330_1656;
    GibCursor tmpcur_6355 = ls_191_1330_1656 + 1;


  switch_6368:
    ;
    switch (tmpval_6354) {

      case 0:
        {
            return (GibCursorGibBoolProd) {end_r_2490, true};
            break;
        }

      case 1:
        {
            GibInt tmpval_6356 = *(GibInt *) tmpcur_6355;
            GibCursor tmpcur_6357 = tmpcur_6355 + sizeof(GibInt);

            return (GibCursorGibBoolProd) {end_r_2490, false};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_112 = *(uintptr_t *) tmpcur_6355;
            GibCursor tmpcur_6358 = GIB_UNTAG(tagged_tmpcur_112);
            GibCursor tmpaftercur_6359 = tmpcur_6355 + 8;
            uint16_t tmptag_6360 = GIB_GET_TAG(tagged_tmpcur_112);
            GibCursor end_from_tagged_indr_3296 = tmpcur_6358 + tmptag_6360;
            GibCursor jump_3298 = tmpcur_6355 + 8;
            GibCursorGibBoolProd tmp_struct_111 =
                                  is_empty_plist_778(end_from_tagged_indr_3296, tmpcur_6358);
            GibCursor pvrtmp_6361 = tmp_struct_111.field0;
            GibBool pvrtmp_6362 = tmp_struct_111.field1;

            return (GibCursorGibBoolProd) {end_r_2490, pvrtmp_6362};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_114 = *(uintptr_t *) tmpcur_6355;
            GibCursor tmpcur_6363 = GIB_UNTAG(tagged_tmpcur_114);
            GibCursor tmpaftercur_6364 = tmpcur_6355 + 8;
            uint16_t tmptag_6365 = GIB_GET_TAG(tagged_tmpcur_114);
            GibCursor end_from_tagged_indr_3296 = tmpcur_6363 + tmptag_6365;
            GibCursorGibBoolProd tmp_struct_113 =
                                  is_empty_plist_778(end_from_tagged_indr_3296, tmpcur_6363);
            GibCursor pvrtmp_6366 = tmp_struct_113.field0;
            GibBool pvrtmp_6367 = tmp_struct_113.field1;

            return (GibCursorGibBoolProd) {pvrtmp_6366, pvrtmp_6367};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6354");
            exit(1);
        }
    }
}
GibCursorGibBoolProd elem_plist_779_1060(GibCursor end_r_2492,
                                         GibInt a_196_1336_1659,
                                         GibCursor list_197_1337_1660)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_6369 = *(GibPackedTag *) list_197_1337_1660;
    GibCursor tmpcur_6370 = list_197_1337_1660 + 1;


  switch_6386:
    ;
    switch (tmpval_6369) {

      case 0:
        {
            return (GibCursorGibBoolProd) {end_r_2492, false};
            break;
        }

      case 1:
        {
            GibInt tmpval_6371 = *(GibInt *) tmpcur_6370;
            GibCursor tmpcur_6372 = tmpcur_6370 + sizeof(GibInt);
            GibBool fltIf_1514_1665 = tmpval_6371 < a_196_1336_1659;
            GibInt fltPrm_1513_1667;

            if (fltIf_1514_1665) {
                GibInt flt_6373 = 0 - 1;

                fltPrm_1513_1667 = flt_6373;
            } else {
                GibBool fltIf_1515_1666 = tmpval_6371 > a_196_1336_1659;

                if (fltIf_1515_1666) {
                    fltPrm_1513_1667 = 1;
                } else {
                    fltPrm_1513_1667 = 0;
                }
            }

            GibBool fltIf_1512_1668 = fltPrm_1513_1667 == 0;

            if (fltIf_1512_1668) {
                return (GibCursorGibBoolProd) {end_r_2492, true};
            } else {
                // GibCursorGibBoolProd tmp_struct_115 =
                                      return elem_plist_779_1060(end_r_2492, a_196_1336_1659, tmpcur_6372);
                // GibCursor pvrtmp_6374 = tmp_struct_115.field0;
                // GibBool pvrtmp_6375 = tmp_struct_115.field1;

                // return (GibCursorGibBoolProd) {pvrtmp_6374, pvrtmp_6375};
            }
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_117 = *(uintptr_t *) tmpcur_6370;
            GibCursor tmpcur_6376 = GIB_UNTAG(tagged_tmpcur_117);
            GibCursor tmpaftercur_6377 = tmpcur_6370 + 8;
            uint16_t tmptag_6378 = GIB_GET_TAG(tagged_tmpcur_117);
            GibCursor end_from_tagged_indr_3301 = tmpcur_6376 + tmptag_6378;
            GibCursor jump_3303 = tmpcur_6370 + 8;
            GibCursorGibBoolProd tmp_struct_116 =
                                  elem_plist_779_1060(end_from_tagged_indr_3301, a_196_1336_1659, tmpcur_6376);
            GibCursor pvrtmp_6379 = tmp_struct_116.field0;
            GibBool pvrtmp_6380 = tmp_struct_116.field1;

            return (GibCursorGibBoolProd) {end_r_2492, pvrtmp_6380};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_119 = *(uintptr_t *) tmpcur_6370;
            GibCursor tmpcur_6381 = GIB_UNTAG(tagged_tmpcur_119);
            GibCursor tmpaftercur_6382 = tmpcur_6370 + 8;
            uint16_t tmptag_6383 = GIB_GET_TAG(tagged_tmpcur_119);
            GibCursor end_from_tagged_indr_3301 = tmpcur_6381 + tmptag_6383;
            GibCursorGibBoolProd tmp_struct_118 =
                                  elem_plist_779_1060(end_from_tagged_indr_3301, a_196_1336_1659, tmpcur_6381);
            GibCursor pvrtmp_6384 = tmp_struct_118.field0;
            GibBool pvrtmp_6385 = tmp_struct_118.field1;

            return (GibCursorGibBoolProd) {pvrtmp_6384, pvrtmp_6385};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6369");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd map_plist_784_1062(GibCursor end_r_2495,
                                                                     GibCursor end_r_2496,
                                                                     GibCursor loc_2494,
                                                                     GibCursor ls_184_1340_1669)
{
    // GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    // GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    // GibShadowstackFrame *frame;

    if (loc_2494 + 18 > end_r_2496) {
        gib_grow_region(&loc_2494, &end_r_2496);
    }

    GibPackedTag tmpval_6387 = *(GibPackedTag *) ls_184_1340_1669;
    GibCursor tmpcur_6388 = ls_184_1340_1669 + 1;


  switch_6440:
    ;
    switch (tmpval_6387) {

      case 0:
        {
            GibCursor jump_3147 = ls_184_1340_1669 + 1;

            *(GibPackedTag *) loc_2494 = 0;

            GibCursor writetag_4489 = loc_2494 + 1;
            GibCursor after_tag_4490 = loc_2494 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2495,
                                                                        end_r_2496,
                                                                        jump_3147,
                                                                        loc_2494,
                                                                        after_tag_4490};
            break;
        }

      case 1:
        {
            GibInt tmpval_6393 = *(GibInt *) tmpcur_6388;
            GibCursor tmpcur_6394 = tmpcur_6388 + sizeof(GibInt);
            GibInt tmpval_6395 = *(GibInt *) tmpcur_6394;
            GibCursor tmpcur_6396 = tmpcur_6394 + sizeof(GibInt);
            GibCursor loc_2763 = loc_2494 + 9;

            *(GibPackedTag *) loc_2494 = 1;

            GibCursor writetag_4502 = loc_2494 + 1;
            GibCursor after_tag_4503 = loc_2494 + 1;

            *(GibInt *) after_tag_4503 = tmpval_6395;

            GibCursor writecur_4507 = after_tag_4503 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_120 =
                                                               map_plist_784_1062(end_r_2495, end_r_2496, loc_2763, tmpcur_6396);
            GibCursor pvrtmp_6399 = tmp_struct_120.field0;
            GibCursor pvrtmp_6400 = tmp_struct_120.field1;
            GibCursor pvrtmp_6401 = tmp_struct_120.field2;
            GibCursor pvrtmp_6402 = tmp_struct_120.field3;
            GibCursor pvrtmp_6403 = tmp_struct_120.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6399,
                                                                        pvrtmp_6400,
                                                                        pvrtmp_6401,
                                                                        loc_2494,
                                                                        pvrtmp_6403};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_122 = *(uintptr_t *) tmpcur_6388;
            GibCursor tmpcur_6412 = GIB_UNTAG(tagged_tmpcur_122);
            GibCursor tmpaftercur_6413 = tmpcur_6388 + 8;
            uint16_t tmptag_6414 = GIB_GET_TAG(tagged_tmpcur_122);
            GibCursor end_from_tagged_indr_3306 = tmpcur_6412 + tmptag_6414;
            GibCursor jump_3308 = tmpcur_6388 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_121 =
                                                               map_plist_784_1062(end_from_tagged_indr_3306, end_r_2496, loc_2494, tmpcur_6412);
            GibCursor pvrtmp_6415 = tmp_struct_121.field0;
            GibCursor pvrtmp_6416 = tmp_struct_121.field1;
            GibCursor pvrtmp_6417 = tmp_struct_121.field2;
            GibCursor pvrtmp_6418 = tmp_struct_121.field3;
            GibCursor pvrtmp_6419 = tmp_struct_121.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2495,
                                                                        pvrtmp_6416,
                                                                        jump_3308,
                                                                        pvrtmp_6418,
                                                                        pvrtmp_6419};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_124 = *(uintptr_t *) tmpcur_6388;
            GibCursor tmpcur_6426 = GIB_UNTAG(tagged_tmpcur_124);
            GibCursor tmpaftercur_6427 = tmpcur_6388 + 8;
            uint16_t tmptag_6428 = GIB_GET_TAG(tagged_tmpcur_124);
            GibCursor end_from_tagged_indr_3306 = tmpcur_6426 + tmptag_6428;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_123 =
                                                               map_plist_784_1062(end_from_tagged_indr_3306, end_r_2496, loc_2494, tmpcur_6426);
            GibCursor pvrtmp_6429 = tmp_struct_123.field0;
            GibCursor pvrtmp_6430 = tmp_struct_123.field1;
            GibCursor pvrtmp_6431 = tmp_struct_123.field2;
            GibCursor pvrtmp_6432 = tmp_struct_123.field3;
            GibCursor pvrtmp_6433 = tmp_struct_123.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6429,
                                                                        pvrtmp_6430,
                                                                        pvrtmp_6431,
                                                                        pvrtmp_6432,
                                                                        pvrtmp_6433};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6387");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_PList_v_775(GibCursor end_r_2499,
                                                                    GibCursor end_r_2500,
                                                                    GibCursor loc_2498,
                                                                    GibCursor arg_1124_1344_1678)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2498 + 18 > end_r_2500) {
        gib_grow_region(&loc_2498, &end_r_2500);
    }

    GibPackedTag tmpval_6441 = *(GibPackedTag *) arg_1124_1344_1678;
    GibCursor tmpcur_6442 = arg_1124_1344_1678 + 1;


  switch_6490:
    ;
    switch (tmpval_6441) {

      case 0:
        {
            GibCursor jump_3153 = arg_1124_1344_1678 + 1;

            *(GibPackedTag *) loc_2498 = 0;

            GibCursor writetag_4522 = loc_2498 + 1;
            GibCursor after_tag_4523 = loc_2498 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2499,
                                                                        end_r_2500,
                                                                        jump_3153,
                                                                        loc_2498,
                                                                        after_tag_4523};
            break;
        }

      case 1:
        {
            GibInt tmpval_6447 = *(GibInt *) tmpcur_6442;
            GibCursor tmpcur_6448 = tmpcur_6442 + sizeof(GibInt);
            GibCursor loc_2776 = loc_2498 + 9;

            *(GibPackedTag *) loc_2498 = 1;

            GibCursor writetag_4534 = loc_2498 + 1;
            GibCursor after_tag_4535 = loc_2498 + 1;

            *(GibInt *) after_tag_4535 = tmpval_6447;

            GibCursor writecur_4539 = after_tag_4535 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_128 =
                                                               _copy_PList_v_775(end_r_2499, end_r_2500, loc_2776, tmpcur_6448);
            GibCursor pvrtmp_6449 = tmp_struct_128.field0;
            GibCursor pvrtmp_6450 = tmp_struct_128.field1;
            GibCursor pvrtmp_6451 = tmp_struct_128.field2;
            GibCursor pvrtmp_6452 = tmp_struct_128.field3;
            GibCursor pvrtmp_6453 = tmp_struct_128.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6449,
                                                                        pvrtmp_6450,
                                                                        pvrtmp_6451,
                                                                        loc_2498,
                                                                        pvrtmp_6453};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_130 = *(uintptr_t *) tmpcur_6442;
            GibCursor tmpcur_6462 = GIB_UNTAG(tagged_tmpcur_130);
            GibCursor tmpaftercur_6463 = tmpcur_6442 + 8;
            uint16_t tmptag_6464 = GIB_GET_TAG(tagged_tmpcur_130);
            GibCursor end_from_tagged_indr_3312 = tmpcur_6462 + tmptag_6464;
            GibCursor jump_3314 = tmpcur_6442 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_129 =
                                                               _copy_PList_v_775(end_from_tagged_indr_3312, end_r_2500, loc_2498, tmpcur_6462);
            GibCursor pvrtmp_6465 = tmp_struct_129.field0;
            GibCursor pvrtmp_6466 = tmp_struct_129.field1;
            GibCursor pvrtmp_6467 = tmp_struct_129.field2;
            GibCursor pvrtmp_6468 = tmp_struct_129.field3;
            GibCursor pvrtmp_6469 = tmp_struct_129.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2499,
                                                                        pvrtmp_6466,
                                                                        jump_3314,
                                                                        pvrtmp_6468,
                                                                        pvrtmp_6469};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_132 = *(uintptr_t *) tmpcur_6442;
            GibCursor tmpcur_6476 = GIB_UNTAG(tagged_tmpcur_132);
            GibCursor tmpaftercur_6477 = tmpcur_6442 + 8;
            uint16_t tmptag_6478 = GIB_GET_TAG(tagged_tmpcur_132);
            GibCursor end_from_tagged_indr_3312 = tmpcur_6476 + tmptag_6478;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_131 =
                                                               _copy_PList_v_775(end_from_tagged_indr_3312, end_r_2500, loc_2498, tmpcur_6476);
            GibCursor pvrtmp_6479 = tmp_struct_131.field0;
            GibCursor pvrtmp_6480 = tmp_struct_131.field1;
            GibCursor pvrtmp_6481 = tmp_struct_131.field2;
            GibCursor pvrtmp_6482 = tmp_struct_131.field3;
            GibCursor pvrtmp_6483 = tmp_struct_131.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6479,
                                                                        pvrtmp_6480,
                                                                        pvrtmp_6481,
                                                                        pvrtmp_6482,
                                                                        pvrtmp_6483};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6441");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_PList_v_775(GibCursor end_r_2503,
                                                                                 GibCursor end_r_2504,
                                                                                 GibCursor loc_2502,
                                                                                 GibCursor arg_1129_1349_1683)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_6491 = *(GibPackedTag *) arg_1129_1349_1683;
    GibCursor tmpcur_6492 = arg_1129_1349_1683 + 1;


  switch_6540:
    ;
    switch (tmpval_6491) {

      case 0:
        {
            GibCursor jump_3158 = arg_1129_1349_1683 + 1;

            *(GibPackedTag *) loc_2502 = 0;

            GibCursor writetag_4554 = loc_2502 + 1;
            GibCursor after_tag_4555 = loc_2502 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2503,
                                                                        end_r_2504,
                                                                        jump_3158,
                                                                        loc_2502,
                                                                        after_tag_4555};
            break;
        }

      case 1:
        {
            GibInt tmpval_6497 = *(GibInt *) tmpcur_6492;
            GibCursor tmpcur_6498 = tmpcur_6492 + sizeof(GibInt);
            GibCursor loc_2789 = loc_2502 + 9;

            *(GibPackedTag *) loc_2502 = 1;

            GibCursor writetag_4566 = loc_2502 + 1;
            GibCursor after_tag_4567 = loc_2502 + 1;

            *(GibInt *) after_tag_4567 = tmpval_6497;

            GibCursor writecur_4571 = after_tag_4567 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_136 =
                                                               _copy_without_ptrs_PList_v_775(end_r_2503, end_r_2504, loc_2789, tmpcur_6498);
            GibCursor pvrtmp_6499 = tmp_struct_136.field0;
            GibCursor pvrtmp_6500 = tmp_struct_136.field1;
            GibCursor pvrtmp_6501 = tmp_struct_136.field2;
            GibCursor pvrtmp_6502 = tmp_struct_136.field3;
            GibCursor pvrtmp_6503 = tmp_struct_136.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6499,
                                                                        pvrtmp_6500,
                                                                        pvrtmp_6501,
                                                                        loc_2502,
                                                                        pvrtmp_6503};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_138 = *(uintptr_t *) tmpcur_6492;
            GibCursor tmpcur_6512 = GIB_UNTAG(tagged_tmpcur_138);
            GibCursor tmpaftercur_6513 = tmpcur_6492 + 8;
            uint16_t tmptag_6514 = GIB_GET_TAG(tagged_tmpcur_138);
            GibCursor end_from_tagged_indr_3318 = tmpcur_6512 + tmptag_6514;
            GibCursor jump_3320 = tmpcur_6492 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_137 =
                                                               _copy_without_ptrs_PList_v_775(end_from_tagged_indr_3318, end_r_2504, loc_2502, tmpcur_6512);
            GibCursor pvrtmp_6515 = tmp_struct_137.field0;
            GibCursor pvrtmp_6516 = tmp_struct_137.field1;
            GibCursor pvrtmp_6517 = tmp_struct_137.field2;
            GibCursor pvrtmp_6518 = tmp_struct_137.field3;
            GibCursor pvrtmp_6519 = tmp_struct_137.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2503,
                                                                        pvrtmp_6516,
                                                                        jump_3320,
                                                                        pvrtmp_6518,
                                                                        pvrtmp_6519};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_140 = *(uintptr_t *) tmpcur_6492;
            GibCursor tmpcur_6526 = GIB_UNTAG(tagged_tmpcur_140);
            GibCursor tmpaftercur_6527 = tmpcur_6492 + 8;
            uint16_t tmptag_6528 = GIB_GET_TAG(tagged_tmpcur_140);
            GibCursor end_from_tagged_indr_3318 = tmpcur_6526 + tmptag_6528;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_139 =
                                                               _copy_without_ptrs_PList_v_775(end_from_tagged_indr_3318, end_r_2504, loc_2502, tmpcur_6526);
            GibCursor pvrtmp_6529 = tmp_struct_139.field0;
            GibCursor pvrtmp_6530 = tmp_struct_139.field1;
            GibCursor pvrtmp_6531 = tmp_struct_139.field2;
            GibCursor pvrtmp_6532 = tmp_struct_139.field3;
            GibCursor pvrtmp_6533 = tmp_struct_139.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6529,
                                                                        pvrtmp_6530,
                                                                        pvrtmp_6531,
                                                                        pvrtmp_6532,
                                                                        pvrtmp_6533};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6491");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_PList_v_775(GibCursor end_r_2506,
                                             GibCursor arg_1134_1354_1688)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_6541 = *(GibPackedTag *) arg_1134_1354_1688;
    GibCursor tmpcur_6542 = arg_1134_1354_1688 + 1;


  switch_6557:
    ;
    switch (tmpval_6541) {

      case 0:
        {
            GibCursor jump_3163 = arg_1134_1354_1688 + 1;

            return (GibCursorGibCursorProd) {end_r_2506, jump_3163};
            break;
        }

      case 1:
        {
            GibInt tmpval_6543 = *(GibInt *) tmpcur_6542;
            GibCursor tmpcur_6544 = tmpcur_6542 + sizeof(GibInt);
            GibCursorGibCursorProd tmp_struct_141 =
                                    _traverse_PList_v_775(end_r_2506, tmpcur_6544);
            GibCursor pvrtmp_6545 = tmp_struct_141.field0;
            GibCursor pvrtmp_6546 = tmp_struct_141.field1;

            return (GibCursorGibCursorProd) {pvrtmp_6545, pvrtmp_6546};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_143 = *(uintptr_t *) tmpcur_6542;
            GibCursor tmpcur_6547 = GIB_UNTAG(tagged_tmpcur_143);
            GibCursor tmpaftercur_6548 = tmpcur_6542 + 8;
            uint16_t tmptag_6549 = GIB_GET_TAG(tagged_tmpcur_143);
            GibCursor end_from_tagged_indr_3324 = tmpcur_6547 + tmptag_6549;
            GibCursor jump_3326 = tmpcur_6542 + 8;
            GibCursorGibCursorProd tmp_struct_142 =
                                    _traverse_PList_v_775(end_from_tagged_indr_3324, tmpcur_6547);
            GibCursor pvrtmp_6550 = tmp_struct_142.field0;
            GibCursor pvrtmp_6551 = tmp_struct_142.field1;

            return (GibCursorGibCursorProd) {end_r_2506, jump_3326};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_145 = *(uintptr_t *) tmpcur_6542;
            GibCursor tmpcur_6552 = GIB_UNTAG(tagged_tmpcur_145);
            GibCursor tmpaftercur_6553 = tmpcur_6542 + 8;
            uint16_t tmptag_6554 = GIB_GET_TAG(tagged_tmpcur_145);
            GibCursor end_from_tagged_indr_3324 = tmpcur_6552 + tmptag_6554;
            GibCursorGibCursorProd tmp_struct_144 =
                                    _traverse_PList_v_775(end_from_tagged_indr_3324, tmpcur_6552);
            GibCursor pvrtmp_6555 = tmp_struct_144.field0;
            GibCursor pvrtmp_6556 = tmp_struct_144.field1;

            return (GibCursorGibCursorProd) {pvrtmp_6555, pvrtmp_6556};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6541");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_PList_v_775(GibCursor end_r_2508,
                                          GibCursor arg_1139_1358_1692)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_6558 = *(GibPackedTag *) arg_1139_1358_1692;
    GibCursor tmpcur_6559 = arg_1139_1358_1692 + 1;


  switch_6574:
    ;
    switch (tmpval_6558) {

      case 0:
        {
            GibCursor jump_3168 = arg_1139_1358_1692 + 1;
            unsigned char wildcard_1140_1359_1693 = gib_print_symbol(5705);
            unsigned char wildcard_1141_1360_1694 = gib_print_symbol(5702);

            return (GibCursorGibCursorProd) {end_r_2508, jump_3168};
            break;
        }

      case 1:
        {
            GibInt tmpval_6560 = *(GibInt *) tmpcur_6559;
            GibCursor tmpcur_6561 = tmpcur_6559 + sizeof(GibInt);
            unsigned char wildcard_1146_1363_1697 = gib_print_symbol(5708);
            unsigned char wildcard_1151_1364_1698 = gib_print_symbol(5711);
            unsigned char y_1144_1365_1699 = printf("%ld", tmpval_6560);
            unsigned char wildcard_1150_1366_1700 = gib_print_symbol(5711);
            unsigned char y_1144_1367_1701 = gib_print_symbol(5711);
            unsigned char wildcard_1149_1368_1702 = gib_print_symbol(5711);
            GibCursorGibCursorProd tmp_struct_146 =
                                    _print_PList_v_775(end_r_2508, tmpcur_6561);
            GibCursor pvrtmp_6562 = tmp_struct_146.field0;
            GibCursor pvrtmp_6563 = tmp_struct_146.field1;
            unsigned char wildcard_1148_1370_1704 = gib_print_symbol(5711);
            unsigned char y_1145_1371_1705 = gib_print_symbol(5711);
            unsigned char wildcard_1147_1372_1706 = gib_print_symbol(5702);

            return (GibCursorGibCursorProd) {pvrtmp_6562, pvrtmp_6563};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_148 = *(uintptr_t *) tmpcur_6559;
            GibCursor tmpcur_6564 = GIB_UNTAG(tagged_tmpcur_148);
            GibCursor tmpaftercur_6565 = tmpcur_6559 + 8;
            uint16_t tmptag_6566 = GIB_GET_TAG(tagged_tmpcur_148);
            GibCursor end_from_tagged_indr_3330 = tmpcur_6564 + tmptag_6566;
            GibCursor jump_3332 = tmpcur_6559 + 8;
            unsigned char wildcard_3335 = gib_print_symbol(5710);
            GibCursorGibCursorProd tmp_struct_147 =
                                    _print_PList_v_775(end_from_tagged_indr_3330, tmpcur_6564);
            GibCursor pvrtmp_6567 = tmp_struct_147.field0;
            GibCursor pvrtmp_6568 = tmp_struct_147.field1;

            return (GibCursorGibCursorProd) {end_r_2508, jump_3332};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_150 = *(uintptr_t *) tmpcur_6559;
            GibCursor tmpcur_6569 = GIB_UNTAG(tagged_tmpcur_150);
            GibCursor tmpaftercur_6570 = tmpcur_6559 + 8;
            uint16_t tmptag_6571 = GIB_GET_TAG(tagged_tmpcur_150);
            GibCursor end_from_tagged_indr_3330 = tmpcur_6569 + tmptag_6571;
            unsigned char wildcard_3335 = gib_print_symbol(5709);
            GibCursorGibCursorProd tmp_struct_149 =
                                    _print_PList_v_775(end_from_tagged_indr_3330, tmpcur_6569);
            GibCursor pvrtmp_6572 = tmp_struct_149.field0;
            GibCursor pvrtmp_6573 = tmp_struct_149.field1;

            return (GibCursorGibCursorProd) {pvrtmp_6572, pvrtmp_6573};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6558");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_PList_v_777(GibCursor end_r_2511,
                                                                    GibCursor end_r_2512,
                                                                    GibCursor loc_2510,
                                                                    GibCursor arg_1152_1373_1707)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2510 + 26 > end_r_2512) {
        gib_grow_region(&loc_2510, &end_r_2512);
    }

    GibPackedTag tmpval_6575 = *(GibPackedTag *) arg_1152_1373_1707;
    GibCursor tmpcur_6576 = arg_1152_1373_1707 + 1;


  switch_6626:
    ;
    switch (tmpval_6575) {

      case 0:
        {
            GibCursor jump_3173 = arg_1152_1373_1707 + 1;

            *(GibPackedTag *) loc_2510 = 0;

            GibCursor writetag_4612 = loc_2510 + 1;
            GibCursor after_tag_4613 = loc_2510 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2511,
                                                                        end_r_2512,
                                                                        jump_3173,
                                                                        loc_2510,
                                                                        after_tag_4613};
            break;
        }

      case 1:
        {
            GibInt tmpval_6581 = *(GibInt *) tmpcur_6576;
            GibCursor tmpcur_6582 = tmpcur_6576 + sizeof(GibInt);
            GibInt tmpval_6583 = *(GibInt *) tmpcur_6582;
            GibCursor tmpcur_6584 = tmpcur_6582 + sizeof(GibInt);
            GibCursor loc_2816 = loc_2510 + 17;

            *(GibPackedTag *) loc_2510 = 1;

            GibCursor writetag_4625 = loc_2510 + 1;
            GibCursor after_tag_4626 = loc_2510 + 1;

            *(GibInt *) after_tag_4626 = tmpval_6581;

            GibCursor writecur_4630 = after_tag_4626 + sizeof(GibInt);

            *(GibInt *) writecur_4630 = tmpval_6583;

            GibCursor writecur_4631 = writecur_4630 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_151 =
                                                               _copy_PList_v_777(end_r_2511, end_r_2512, loc_2816, tmpcur_6584);
            GibCursor pvrtmp_6585 = tmp_struct_151.field0;
            GibCursor pvrtmp_6586 = tmp_struct_151.field1;
            GibCursor pvrtmp_6587 = tmp_struct_151.field2;
            GibCursor pvrtmp_6588 = tmp_struct_151.field3;
            GibCursor pvrtmp_6589 = tmp_struct_151.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6585,
                                                                        pvrtmp_6586,
                                                                        pvrtmp_6587,
                                                                        loc_2510,
                                                                        pvrtmp_6589};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_153 = *(uintptr_t *) tmpcur_6576;
            GibCursor tmpcur_6598 = GIB_UNTAG(tagged_tmpcur_153);
            GibCursor tmpaftercur_6599 = tmpcur_6576 + 8;
            uint16_t tmptag_6600 = GIB_GET_TAG(tagged_tmpcur_153);
            GibCursor end_from_tagged_indr_3336 = tmpcur_6598 + tmptag_6600;
            GibCursor jump_3338 = tmpcur_6576 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_152 =
                                                               _copy_PList_v_777(end_from_tagged_indr_3336, end_r_2512, loc_2510, tmpcur_6598);
            GibCursor pvrtmp_6601 = tmp_struct_152.field0;
            GibCursor pvrtmp_6602 = tmp_struct_152.field1;
            GibCursor pvrtmp_6603 = tmp_struct_152.field2;
            GibCursor pvrtmp_6604 = tmp_struct_152.field3;
            GibCursor pvrtmp_6605 = tmp_struct_152.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2511,
                                                                        pvrtmp_6602,
                                                                        jump_3338,
                                                                        pvrtmp_6604,
                                                                        pvrtmp_6605};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_155 = *(uintptr_t *) tmpcur_6576;
            GibCursor tmpcur_6612 = GIB_UNTAG(tagged_tmpcur_155);
            GibCursor tmpaftercur_6613 = tmpcur_6576 + 8;
            uint16_t tmptag_6614 = GIB_GET_TAG(tagged_tmpcur_155);
            GibCursor end_from_tagged_indr_3336 = tmpcur_6612 + tmptag_6614;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_154 =
                                                               _copy_PList_v_777(end_from_tagged_indr_3336, end_r_2512, loc_2510, tmpcur_6612);
            GibCursor pvrtmp_6615 = tmp_struct_154.field0;
            GibCursor pvrtmp_6616 = tmp_struct_154.field1;
            GibCursor pvrtmp_6617 = tmp_struct_154.field2;
            GibCursor pvrtmp_6618 = tmp_struct_154.field3;
            GibCursor pvrtmp_6619 = tmp_struct_154.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6615,
                                                                        pvrtmp_6616,
                                                                        pvrtmp_6617,
                                                                        pvrtmp_6618,
                                                                        pvrtmp_6619};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6575");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_PList_v_777(GibCursor end_r_2515,
                                                                                 GibCursor end_r_2516,
                                                                                 GibCursor loc_2514,
                                                                                 GibCursor arg_1159_1380_1714)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_6627 = *(GibPackedTag *) arg_1159_1380_1714;
    GibCursor tmpcur_6628 = arg_1159_1380_1714 + 1;


  switch_6678:
    ;
    switch (tmpval_6627) {

      case 0:
        {
            GibCursor jump_3179 = arg_1159_1380_1714 + 1;

            *(GibPackedTag *) loc_2514 = 0;

            GibCursor writetag_4646 = loc_2514 + 1;
            GibCursor after_tag_4647 = loc_2514 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2515,
                                                                        end_r_2516,
                                                                        jump_3179,
                                                                        loc_2514,
                                                                        after_tag_4647};
            break;
        }

      case 1:
        {
            GibInt tmpval_6633 = *(GibInt *) tmpcur_6628;
            GibCursor tmpcur_6634 = tmpcur_6628 + sizeof(GibInt);
            GibInt tmpval_6635 = *(GibInt *) tmpcur_6634;
            GibCursor tmpcur_6636 = tmpcur_6634 + sizeof(GibInt);
            GibCursor loc_2833 = loc_2514 + 17;

            *(GibPackedTag *) loc_2514 = 1;

            GibCursor writetag_4659 = loc_2514 + 1;
            GibCursor after_tag_4660 = loc_2514 + 1;

            *(GibInt *) after_tag_4660 = tmpval_6633;

            GibCursor writecur_4664 = after_tag_4660 + sizeof(GibInt);

            *(GibInt *) writecur_4664 = tmpval_6635;

            GibCursor writecur_4665 = writecur_4664 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_159 =
                                                               _copy_without_ptrs_PList_v_777(end_r_2515, end_r_2516, loc_2833, tmpcur_6636);
            GibCursor pvrtmp_6637 = tmp_struct_159.field0;
            GibCursor pvrtmp_6638 = tmp_struct_159.field1;
            GibCursor pvrtmp_6639 = tmp_struct_159.field2;
            GibCursor pvrtmp_6640 = tmp_struct_159.field3;
            GibCursor pvrtmp_6641 = tmp_struct_159.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6637,
                                                                        pvrtmp_6638,
                                                                        pvrtmp_6639,
                                                                        loc_2514,
                                                                        pvrtmp_6641};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_161 = *(uintptr_t *) tmpcur_6628;
            GibCursor tmpcur_6650 = GIB_UNTAG(tagged_tmpcur_161);
            GibCursor tmpaftercur_6651 = tmpcur_6628 + 8;
            uint16_t tmptag_6652 = GIB_GET_TAG(tagged_tmpcur_161);
            GibCursor end_from_tagged_indr_3342 = tmpcur_6650 + tmptag_6652;
            GibCursor jump_3344 = tmpcur_6628 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_160 =
                                                               _copy_without_ptrs_PList_v_777(end_from_tagged_indr_3342, end_r_2516, loc_2514, tmpcur_6650);
            GibCursor pvrtmp_6653 = tmp_struct_160.field0;
            GibCursor pvrtmp_6654 = tmp_struct_160.field1;
            GibCursor pvrtmp_6655 = tmp_struct_160.field2;
            GibCursor pvrtmp_6656 = tmp_struct_160.field3;
            GibCursor pvrtmp_6657 = tmp_struct_160.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2515,
                                                                        pvrtmp_6654,
                                                                        jump_3344,
                                                                        pvrtmp_6656,
                                                                        pvrtmp_6657};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_163 = *(uintptr_t *) tmpcur_6628;
            GibCursor tmpcur_6664 = GIB_UNTAG(tagged_tmpcur_163);
            GibCursor tmpaftercur_6665 = tmpcur_6628 + 8;
            uint16_t tmptag_6666 = GIB_GET_TAG(tagged_tmpcur_163);
            GibCursor end_from_tagged_indr_3342 = tmpcur_6664 + tmptag_6666;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_162 =
                                                               _copy_without_ptrs_PList_v_777(end_from_tagged_indr_3342, end_r_2516, loc_2514, tmpcur_6664);
            GibCursor pvrtmp_6667 = tmp_struct_162.field0;
            GibCursor pvrtmp_6668 = tmp_struct_162.field1;
            GibCursor pvrtmp_6669 = tmp_struct_162.field2;
            GibCursor pvrtmp_6670 = tmp_struct_162.field3;
            GibCursor pvrtmp_6671 = tmp_struct_162.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6667,
                                                                        pvrtmp_6668,
                                                                        pvrtmp_6669,
                                                                        pvrtmp_6670,
                                                                        pvrtmp_6671};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6627");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_PList_v_777(GibCursor end_r_2518,
                                             GibCursor arg_1166_1387_1721)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_6679 = *(GibPackedTag *) arg_1166_1387_1721;
    GibCursor tmpcur_6680 = arg_1166_1387_1721 + 1;


  switch_6697:
    ;
    switch (tmpval_6679) {

      case 0:
        {
            GibCursor jump_3185 = arg_1166_1387_1721 + 1;

            return (GibCursorGibCursorProd) {end_r_2518, jump_3185};
            break;
        }

      case 1:
        {
            GibInt tmpval_6681 = *(GibInt *) tmpcur_6680;
            GibCursor tmpcur_6682 = tmpcur_6680 + sizeof(GibInt);
            GibInt tmpval_6683 = *(GibInt *) tmpcur_6682;
            GibCursor tmpcur_6684 = tmpcur_6682 + sizeof(GibInt);
            GibCursorGibCursorProd tmp_struct_164 =
                                    _traverse_PList_v_777(end_r_2518, tmpcur_6684);
            GibCursor pvrtmp_6685 = tmp_struct_164.field0;
            GibCursor pvrtmp_6686 = tmp_struct_164.field1;

            return (GibCursorGibCursorProd) {pvrtmp_6685, pvrtmp_6686};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_166 = *(uintptr_t *) tmpcur_6680;
            GibCursor tmpcur_6687 = GIB_UNTAG(tagged_tmpcur_166);
            GibCursor tmpaftercur_6688 = tmpcur_6680 + 8;
            uint16_t tmptag_6689 = GIB_GET_TAG(tagged_tmpcur_166);
            GibCursor end_from_tagged_indr_3348 = tmpcur_6687 + tmptag_6689;
            GibCursor jump_3350 = tmpcur_6680 + 8;
            GibCursorGibCursorProd tmp_struct_165 =
                                    _traverse_PList_v_777(end_from_tagged_indr_3348, tmpcur_6687);
            GibCursor pvrtmp_6690 = tmp_struct_165.field0;
            GibCursor pvrtmp_6691 = tmp_struct_165.field1;

            return (GibCursorGibCursorProd) {end_r_2518, jump_3350};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_168 = *(uintptr_t *) tmpcur_6680;
            GibCursor tmpcur_6692 = GIB_UNTAG(tagged_tmpcur_168);
            GibCursor tmpaftercur_6693 = tmpcur_6680 + 8;
            uint16_t tmptag_6694 = GIB_GET_TAG(tagged_tmpcur_168);
            GibCursor end_from_tagged_indr_3348 = tmpcur_6692 + tmptag_6694;
            GibCursorGibCursorProd tmp_struct_167 =
                                    _traverse_PList_v_777(end_from_tagged_indr_3348, tmpcur_6692);
            GibCursor pvrtmp_6695 = tmp_struct_167.field0;
            GibCursor pvrtmp_6696 = tmp_struct_167.field1;

            return (GibCursorGibCursorProd) {pvrtmp_6695, pvrtmp_6696};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6679");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_PList_v_777(GibCursor end_r_2520,
                                          GibCursor arg_1173_1392_1726)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_6698 = *(GibPackedTag *) arg_1173_1392_1726;
    GibCursor tmpcur_6699 = arg_1173_1392_1726 + 1;


  switch_6716:
    ;
    switch (tmpval_6698) {

      case 0:
        {
            GibCursor jump_3191 = arg_1173_1392_1726 + 1;
            unsigned char wildcard_1174_1393_1727 = gib_print_symbol(5704);
            unsigned char wildcard_1175_1394_1728 = gib_print_symbol(5702);

            return (GibCursorGibCursorProd) {end_r_2520, jump_3191};
            break;
        }

      case 1:
        {
            GibInt tmpval_6700 = *(GibInt *) tmpcur_6699;
            GibCursor tmpcur_6701 = tmpcur_6699 + sizeof(GibInt);
            GibInt tmpval_6702 = *(GibInt *) tmpcur_6701;
            GibCursor tmpcur_6703 = tmpcur_6701 + sizeof(GibInt);
            unsigned char wildcard_1182_1398_1732 = gib_print_symbol(5707);
            unsigned char wildcard_1189_1399_1733 = gib_print_symbol(5711);
            unsigned char y_1179_1400_1734 = printf("%ld", tmpval_6700);
            unsigned char wildcard_1188_1401_1735 = gib_print_symbol(5711);
            unsigned char y_1179_1402_1736 = gib_print_symbol(5711);
            unsigned char wildcard_1187_1403_1737 = gib_print_symbol(5711);
            unsigned char y_1180_1404_1738 = printf("%ld", tmpval_6702);
            unsigned char wildcard_1186_1405_1739 = gib_print_symbol(5711);
            unsigned char y_1180_1406_1740 = gib_print_symbol(5711);
            unsigned char wildcard_1185_1407_1741 = gib_print_symbol(5711);
            GibCursorGibCursorProd tmp_struct_169 =
                                    _print_PList_v_777(end_r_2520, tmpcur_6703);
            GibCursor pvrtmp_6704 = tmp_struct_169.field0;
            GibCursor pvrtmp_6705 = tmp_struct_169.field1;
            unsigned char wildcard_1184_1409_1743 = gib_print_symbol(5711);
            unsigned char y_1181_1410_1744 = gib_print_symbol(5711);
            unsigned char wildcard_1183_1411_1745 = gib_print_symbol(5702);

            return (GibCursorGibCursorProd) {pvrtmp_6704, pvrtmp_6705};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_171 = *(uintptr_t *) tmpcur_6699;
            GibCursor tmpcur_6706 = GIB_UNTAG(tagged_tmpcur_171);
            GibCursor tmpaftercur_6707 = tmpcur_6699 + 8;
            uint16_t tmptag_6708 = GIB_GET_TAG(tagged_tmpcur_171);
            GibCursor end_from_tagged_indr_3354 = tmpcur_6706 + tmptag_6708;
            GibCursor jump_3356 = tmpcur_6699 + 8;
            unsigned char wildcard_3359 = gib_print_symbol(5710);
            GibCursorGibCursorProd tmp_struct_170 =
                                    _print_PList_v_777(end_from_tagged_indr_3354, tmpcur_6706);
            GibCursor pvrtmp_6709 = tmp_struct_170.field0;
            GibCursor pvrtmp_6710 = tmp_struct_170.field1;

            return (GibCursorGibCursorProd) {end_r_2520, jump_3356};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_173 = *(uintptr_t *) tmpcur_6699;
            GibCursor tmpcur_6711 = GIB_UNTAG(tagged_tmpcur_173);
            GibCursor tmpaftercur_6712 = tmpcur_6699 + 8;
            uint16_t tmptag_6713 = GIB_GET_TAG(tagged_tmpcur_173);
            GibCursor end_from_tagged_indr_3354 = tmpcur_6711 + tmptag_6713;
            unsigned char wildcard_3359 = gib_print_symbol(5709);
            GibCursorGibCursorProd tmp_struct_172 =
                                    _print_PList_v_777(end_from_tagged_indr_3354, tmpcur_6711);
            GibCursor pvrtmp_6714 = tmp_struct_172.field0;
            GibCursor pvrtmp_6715 = tmp_struct_172.field1;

            return (GibCursorGibCursorProd) {pvrtmp_6714, pvrtmp_6715};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6698");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_Maybe_v_785(GibCursor end_r_2523,
                                                                    GibCursor end_r_2524,
                                                                    GibCursor loc_2522,
                                                                    GibCursor arg_1190_1412_1746)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2522 + 18 > end_r_2524) {
        gib_grow_region(&loc_2522, &end_r_2524);
    }

    GibPackedTag tmpval_6717 = *(GibPackedTag *) arg_1190_1412_1746;
    GibCursor tmpcur_6718 = arg_1190_1412_1746 + 1;


  switch_6757:
    ;
    switch (tmpval_6717) {

      case 0:
        {
            GibInt tmpval_6719 = *(GibInt *) tmpcur_6718;
            GibCursor tmpcur_6720 = tmpcur_6718 + sizeof(GibInt);
            GibCursor jump_3197 = tmpcur_6718 + 8;

            *(GibPackedTag *) loc_2522 = 0;

            GibCursor writetag_4709 = loc_2522 + 1;
            GibCursor after_tag_4710 = loc_2522 + 1;

            *(GibInt *) after_tag_4710 = tmpval_6719;

            GibCursor writecur_4714 = after_tag_4710 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2523,
                                                                        end_r_2524,
                                                                        jump_3197,
                                                                        loc_2522,
                                                                        writecur_4714};
            break;
        }

      case 1:
        {
            GibCursor jump_3199 = arg_1190_1412_1746 + 1;

            *(GibPackedTag *) loc_2522 = 1;

            GibCursor writetag_4718 = loc_2522 + 1;
            GibCursor after_tag_4719 = loc_2522 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2523,
                                                                        end_r_2524,
                                                                        jump_3199,
                                                                        loc_2522,
                                                                        after_tag_4719};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_175 = *(uintptr_t *) tmpcur_6718;
            GibCursor tmpcur_6729 = GIB_UNTAG(tagged_tmpcur_175);
            GibCursor tmpaftercur_6730 = tmpcur_6718 + 8;
            uint16_t tmptag_6731 = GIB_GET_TAG(tagged_tmpcur_175);
            GibCursor end_from_tagged_indr_3360 = tmpcur_6729 + tmptag_6731;
            GibCursor jump_3362 = tmpcur_6718 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_174 =
                                                               _copy_Maybe_v_785(end_from_tagged_indr_3360, end_r_2524, loc_2522, tmpcur_6729);
            GibCursor pvrtmp_6732 = tmp_struct_174.field0;
            GibCursor pvrtmp_6733 = tmp_struct_174.field1;
            GibCursor pvrtmp_6734 = tmp_struct_174.field2;
            GibCursor pvrtmp_6735 = tmp_struct_174.field3;
            GibCursor pvrtmp_6736 = tmp_struct_174.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2523,
                                                                        pvrtmp_6733,
                                                                        jump_3362,
                                                                        pvrtmp_6735,
                                                                        pvrtmp_6736};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_177 = *(uintptr_t *) tmpcur_6718;
            GibCursor tmpcur_6743 = GIB_UNTAG(tagged_tmpcur_177);
            GibCursor tmpaftercur_6744 = tmpcur_6718 + 8;
            uint16_t tmptag_6745 = GIB_GET_TAG(tagged_tmpcur_177);
            GibCursor end_from_tagged_indr_3360 = tmpcur_6743 + tmptag_6745;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_176 =
                                                               _copy_Maybe_v_785(end_from_tagged_indr_3360, end_r_2524, loc_2522, tmpcur_6743);
            GibCursor pvrtmp_6746 = tmp_struct_176.field0;
            GibCursor pvrtmp_6747 = tmp_struct_176.field1;
            GibCursor pvrtmp_6748 = tmp_struct_176.field2;
            GibCursor pvrtmp_6749 = tmp_struct_176.field3;
            GibCursor pvrtmp_6750 = tmp_struct_176.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6746,
                                                                        pvrtmp_6747,
                                                                        pvrtmp_6748,
                                                                        pvrtmp_6749,
                                                                        pvrtmp_6750};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6717");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_Maybe_v_785(GibCursor end_r_2527,
                                                                                 GibCursor end_r_2528,
                                                                                 GibCursor loc_2526,
                                                                                 GibCursor arg_1193_1415_1749)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_6758 = *(GibPackedTag *) arg_1193_1415_1749;
    GibCursor tmpcur_6759 = arg_1193_1415_1749 + 1;


  switch_6798:
    ;
    switch (tmpval_6758) {

      case 0:
        {
            GibInt tmpval_6760 = *(GibInt *) tmpcur_6759;
            GibCursor tmpcur_6761 = tmpcur_6759 + sizeof(GibInt);
            GibCursor jump_3201 = tmpcur_6759 + 8;

            *(GibPackedTag *) loc_2526 = 0;

            GibCursor writetag_4737 = loc_2526 + 1;
            GibCursor after_tag_4738 = loc_2526 + 1;

            *(GibInt *) after_tag_4738 = tmpval_6760;

            GibCursor writecur_4742 = after_tag_4738 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2527,
                                                                        end_r_2528,
                                                                        jump_3201,
                                                                        loc_2526,
                                                                        writecur_4742};
            break;
        }

      case 1:
        {
            GibCursor jump_3203 = arg_1193_1415_1749 + 1;

            *(GibPackedTag *) loc_2526 = 1;

            GibCursor writetag_4746 = loc_2526 + 1;
            GibCursor after_tag_4747 = loc_2526 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2527,
                                                                        end_r_2528,
                                                                        jump_3203,
                                                                        loc_2526,
                                                                        after_tag_4747};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_182 = *(uintptr_t *) tmpcur_6759;
            GibCursor tmpcur_6770 = GIB_UNTAG(tagged_tmpcur_182);
            GibCursor tmpaftercur_6771 = tmpcur_6759 + 8;
            uint16_t tmptag_6772 = GIB_GET_TAG(tagged_tmpcur_182);
            GibCursor end_from_tagged_indr_3366 = tmpcur_6770 + tmptag_6772;
            GibCursor jump_3368 = tmpcur_6759 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_181 =
                                                               _copy_without_ptrs_Maybe_v_785(end_from_tagged_indr_3366, end_r_2528, loc_2526, tmpcur_6770);
            GibCursor pvrtmp_6773 = tmp_struct_181.field0;
            GibCursor pvrtmp_6774 = tmp_struct_181.field1;
            GibCursor pvrtmp_6775 = tmp_struct_181.field2;
            GibCursor pvrtmp_6776 = tmp_struct_181.field3;
            GibCursor pvrtmp_6777 = tmp_struct_181.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2527,
                                                                        pvrtmp_6774,
                                                                        jump_3368,
                                                                        pvrtmp_6776,
                                                                        pvrtmp_6777};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_184 = *(uintptr_t *) tmpcur_6759;
            GibCursor tmpcur_6784 = GIB_UNTAG(tagged_tmpcur_184);
            GibCursor tmpaftercur_6785 = tmpcur_6759 + 8;
            uint16_t tmptag_6786 = GIB_GET_TAG(tagged_tmpcur_184);
            GibCursor end_from_tagged_indr_3366 = tmpcur_6784 + tmptag_6786;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_183 =
                                                               _copy_without_ptrs_Maybe_v_785(end_from_tagged_indr_3366, end_r_2528, loc_2526, tmpcur_6784);
            GibCursor pvrtmp_6787 = tmp_struct_183.field0;
            GibCursor pvrtmp_6788 = tmp_struct_183.field1;
            GibCursor pvrtmp_6789 = tmp_struct_183.field2;
            GibCursor pvrtmp_6790 = tmp_struct_183.field3;
            GibCursor pvrtmp_6791 = tmp_struct_183.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6787,
                                                                        pvrtmp_6788,
                                                                        pvrtmp_6789,
                                                                        pvrtmp_6790,
                                                                        pvrtmp_6791};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6758");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_Maybe_v_785(GibCursor end_r_2530,
                                             GibCursor arg_1196_1418_1752)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_6799 = *(GibPackedTag *) arg_1196_1418_1752;
    GibCursor tmpcur_6800 = arg_1196_1418_1752 + 1;


  switch_6813:
    ;
    switch (tmpval_6799) {

      case 0:
        {
            GibInt tmpval_6801 = *(GibInt *) tmpcur_6800;
            GibCursor tmpcur_6802 = tmpcur_6800 + sizeof(GibInt);
            GibCursor jump_3205 = tmpcur_6800 + 8;

            return (GibCursorGibCursorProd) {end_r_2530, jump_3205};
            break;
        }

      case 1:
        {
            GibCursor jump_3207 = arg_1196_1418_1752 + 1;

            return (GibCursorGibCursorProd) {end_r_2530, jump_3207};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_186 = *(uintptr_t *) tmpcur_6800;
            GibCursor tmpcur_6803 = GIB_UNTAG(tagged_tmpcur_186);
            GibCursor tmpaftercur_6804 = tmpcur_6800 + 8;
            uint16_t tmptag_6805 = GIB_GET_TAG(tagged_tmpcur_186);
            GibCursor end_from_tagged_indr_3372 = tmpcur_6803 + tmptag_6805;
            GibCursor jump_3374 = tmpcur_6800 + 8;
            GibCursorGibCursorProd tmp_struct_185 =
                                    _traverse_Maybe_v_785(end_from_tagged_indr_3372, tmpcur_6803);
            GibCursor pvrtmp_6806 = tmp_struct_185.field0;
            GibCursor pvrtmp_6807 = tmp_struct_185.field1;

            return (GibCursorGibCursorProd) {end_r_2530, jump_3374};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_188 = *(uintptr_t *) tmpcur_6800;
            GibCursor tmpcur_6808 = GIB_UNTAG(tagged_tmpcur_188);
            GibCursor tmpaftercur_6809 = tmpcur_6800 + 8;
            uint16_t tmptag_6810 = GIB_GET_TAG(tagged_tmpcur_188);
            GibCursor end_from_tagged_indr_3372 = tmpcur_6808 + tmptag_6810;
            GibCursorGibCursorProd tmp_struct_187 =
                                    _traverse_Maybe_v_785(end_from_tagged_indr_3372, tmpcur_6808);
            GibCursor pvrtmp_6811 = tmp_struct_187.field0;
            GibCursor pvrtmp_6812 = tmp_struct_187.field1;

            return (GibCursorGibCursorProd) {pvrtmp_6811, pvrtmp_6812};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6799");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_Maybe_v_785(GibCursor end_r_2532,
                                          GibCursor arg_1199_1420_1754)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_6814 = *(GibPackedTag *) arg_1199_1420_1754;
    GibCursor tmpcur_6815 = arg_1199_1420_1754 + 1;


  switch_6828:
    ;
    switch (tmpval_6814) {

      case 0:
        {
            GibInt tmpval_6816 = *(GibInt *) tmpcur_6815;
            GibCursor tmpcur_6817 = tmpcur_6815 + sizeof(GibInt);
            GibCursor jump_3209 = tmpcur_6815 + 8;
            unsigned char wildcard_1202_1422_1756 = gib_print_symbol(5706);
            unsigned char wildcard_1205_1423_1757 = gib_print_symbol(5711);
            unsigned char y_1201_1424_1758 = printf("%ld", tmpval_6816);
            unsigned char wildcard_1204_1425_1759 = gib_print_symbol(5711);
            unsigned char y_1201_1426_1760 = gib_print_symbol(5711);
            unsigned char wildcard_1203_1427_1761 = gib_print_symbol(5702);

            return (GibCursorGibCursorProd) {end_r_2532, jump_3209};
            break;
        }

      case 1:
        {
            GibCursor jump_3211 = arg_1199_1420_1754 + 1;
            unsigned char wildcard_1206_1428_1762 = gib_print_symbol(5703);
            unsigned char wildcard_1207_1429_1763 = gib_print_symbol(5702);

            return (GibCursorGibCursorProd) {end_r_2532, jump_3211};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_190 = *(uintptr_t *) tmpcur_6815;
            GibCursor tmpcur_6818 = GIB_UNTAG(tagged_tmpcur_190);
            GibCursor tmpaftercur_6819 = tmpcur_6815 + 8;
            uint16_t tmptag_6820 = GIB_GET_TAG(tagged_tmpcur_190);
            GibCursor end_from_tagged_indr_3378 = tmpcur_6818 + tmptag_6820;
            GibCursor jump_3380 = tmpcur_6815 + 8;
            unsigned char wildcard_3383 = gib_print_symbol(5710);
            GibCursorGibCursorProd tmp_struct_189 =
                                    _print_Maybe_v_785(end_from_tagged_indr_3378, tmpcur_6818);
            GibCursor pvrtmp_6821 = tmp_struct_189.field0;
            GibCursor pvrtmp_6822 = tmp_struct_189.field1;

            return (GibCursorGibCursorProd) {end_r_2532, jump_3380};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_192 = *(uintptr_t *) tmpcur_6815;
            GibCursor tmpcur_6823 = GIB_UNTAG(tagged_tmpcur_192);
            GibCursor tmpaftercur_6824 = tmpcur_6815 + 8;
            uint16_t tmptag_6825 = GIB_GET_TAG(tagged_tmpcur_192);
            GibCursor end_from_tagged_indr_3378 = tmpcur_6823 + tmptag_6825;
            unsigned char wildcard_3383 = gib_print_symbol(5709);
            GibCursorGibCursorProd tmp_struct_191 =
                                    _print_Maybe_v_785(end_from_tagged_indr_3378, tmpcur_6823);
            GibCursor pvrtmp_6826 = tmp_struct_191.field0;
            GibCursor pvrtmp_6827 = tmp_struct_191.field1;

            return (GibCursorGibCursorProd) {pvrtmp_6826, pvrtmp_6827};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6814");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd caseFn_1208(GibCursor end_r_2538,
                                                                                GibCursor end_r_2539,
                                                                                GibCursor end_r_2540,
                                                                                GibCursor end_r_2541,
                                                                                GibCursor end_r_2542,
                                                                                GibCursor loc_2537,
                                                                                GibInt m_141_1209_1430_1764,
                                                                                GibInt n_142_1210_1431_1765,
                                                                                GibCursor xs_143_1211_1432_1766,
                                                                                GibCursor ys_144_1212_1433_1767,
                                                                                GibCursor zs_145_1213_1434_1768,
                                                                                GibCursor xs__147_1214_1435_1769,
                                                                                GibInt x_146_1215_1436_1770)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2537 + 18 > end_r_2542) {
        gib_grow_region(&loc_2537, &end_r_2542);
    }

    GibPackedTag tmpval_6829 = *(GibPackedTag *) xs__147_1214_1435_1769;
    GibCursor tmpcur_6830 = xs__147_1214_1435_1769 + 1;


  switch_7015:
    ;
    switch (tmpval_6829) {

      case 0:
        {
            GibCursorGibBoolProd tmp_struct_193 =
                                  elem_plist_779_1060(end_r_2539, x_146_1215_1436_1770, ys_144_1212_1433_1767);
            GibCursor pvrtmp_6831 = tmp_struct_193.field0;
            GibBool pvrtmp_6832 = tmp_struct_193.field1;

            if (pvrtmp_6832) {
                GibCursor loc_2881 = loc_2537 + 9;

                *(GibPackedTag *) loc_2537 = 1;

                GibCursor writetag_4791 = loc_2537 + 1;
                GibCursor after_tag_4792 = loc_2537 + 1;

                *(GibInt *) after_tag_4792 = x_146_1215_1436_1770;

                GibCursor writecur_4796 = after_tag_4792 + sizeof(GibInt);

                if (loc_2881 + 18 > end_r_2542) {
                    gib_grow_region(&loc_2881, &end_r_2542);
                }
                gib_indirection_barrier(loc_2881, end_r_2542,
                                        zs_145_1213_1434_1768, end_r_2540,
                                        PList_v_775_T);

                GibCursor end_4789 = loc_2881 + 9;

                return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2538,
                                                                                              pvrtmp_6831,
                                                                                              end_r_2540,
                                                                                              end_r_2541,
                                                                                              end_r_2542,
                                                                                              loc_2537,
                                                                                              end_4789};
            } else {
                if (loc_2537 + 18 > end_r_2542) {
                    gib_grow_region(&loc_2537, &end_r_2542);
                }
                gib_indirection_barrier(loc_2537, end_r_2542,
                                        zs_145_1213_1434_1768, end_r_2540,
                                        PList_v_775_T);

                GibCursor end_4801 = loc_2537 + 9;

                return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2538,
                                                                                              pvrtmp_6831,
                                                                                              end_r_2540,
                                                                                              end_r_2541,
                                                                                              end_r_2542,
                                                                                              loc_2537,
                                                                                              end_4801};
            }
            break;
        }

      case 1:
        {
            GibInt tmpval_6843 = *(GibInt *) tmpcur_6830;
            GibCursor tmpcur_6844 = tmpcur_6830 + sizeof(GibInt);
            GibInt m2_150_1439_1775 = m_141_1209_1430_1764 / 2;

            gib_shadowstack_push(rstack, zs_145_1213_1434_1768, end_r_2540, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, ys_144_1212_1433_1767, end_r_2539, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, xs_143_1211_1432_1766, end_r_2538, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(wstack, loc_2537, end_r_2542, Stk,
                                 PList_v_775_T);

            GibChunk region_6845 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_2983 = region_6845.start;
            GibCursor end_r_2983 = region_6845.end;

            frame = gib_shadowstack_pop(wstack);
            loc_2537 = frame->ptr;
            end_r_2542 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            xs_143_1211_1432_1766 = frame->ptr;
            end_r_2538 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1212_1433_1767 = frame->ptr;
            end_r_2539 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1213_1434_1768 = frame->ptr;
            end_r_2540 = frame->endptr;

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_200 =
                                                      take_plist_780(end_r_2538, end_r_2983, r_2983, m2_150_1439_1775, xs_143_1211_1432_1766);
            GibCursor pvrtmp_6846 = tmp_struct_200.field0;
            GibCursor pvrtmp_6847 = tmp_struct_200.field1;
            GibCursor pvrtmp_6848 = tmp_struct_200.field2;
            GibCursor pvrtmp_6849 = tmp_struct_200.field3;

            gib_shadowstack_push(rstack, zs_145_1213_1434_1768, end_r_2540, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, ys_144_1212_1433_1767, end_r_2539, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6848, pvrtmp_6847, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, xs_143_1211_1432_1766, end_r_2538, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(wstack, loc_2537, end_r_2542, Stk,
                                 PList_v_775_T);

            GibChunk region_6854 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_2982 = region_6854.start;
            GibCursor end_r_2982 = region_6854.end;

            frame = gib_shadowstack_pop(wstack);
            loc_2537 = frame->ptr;
            end_r_2542 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            xs_143_1211_1432_1766 = frame->ptr;
            end_r_2538 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6848 = frame->ptr;
            pvrtmp_6847 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1212_1433_1767 = frame->ptr;
            end_r_2539 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1213_1434_1768 = frame->ptr;
            end_r_2540 = frame->endptr;

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_201 =
                                                      drop_plist_781(end_r_2538, end_r_2982, r_2982, m2_150_1439_1775, xs_143_1211_1432_1766);
            GibCursor pvrtmp_6855 = tmp_struct_201.field0;
            GibCursor pvrtmp_6856 = tmp_struct_201.field1;
            GibCursor pvrtmp_6857 = tmp_struct_201.field2;
            GibCursor pvrtmp_6858 = tmp_struct_201.field3;

            gib_shadowstack_push(rstack, zs_145_1213_1434_1768, end_r_2540, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, ys_144_1212_1433_1767, end_r_2539, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6848, pvrtmp_6847, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6857, pvrtmp_6856, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(wstack, loc_2537, end_r_2542, Stk,
                                 PList_v_775_T);

            GibChunk region_6863 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_2981 = region_6863.start;
            GibCursor end_r_2981 = region_6863.end;

            frame = gib_shadowstack_pop(wstack);
            loc_2537 = frame->ptr;
            end_r_2542 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6857 = frame->ptr;
            pvrtmp_6856 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6848 = frame->ptr;
            pvrtmp_6847 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1212_1433_1767 = frame->ptr;
            end_r_2539 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1213_1434_1768 = frame->ptr;
            end_r_2540 = frame->endptr;
            gib_shadowstack_push(rstack, zs_145_1213_1434_1768, end_r_2540, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, ys_144_1212_1433_1767, end_r_2539, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6848, pvrtmp_6847, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6857, pvrtmp_6856, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(wstack, loc_2537, end_r_2542, Stk,
                                 PList_v_775_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_202 =
             algb(pvrtmp_6847, end_r_2539, end_r_2981, r_2981, pvrtmp_6848, ys_144_1212_1433_1767);
            GibCursor pvrtmp_6864 = tmp_struct_202.field0;
            GibCursor pvrtmp_6865 = tmp_struct_202.field1;
            GibCursor pvrtmp_6866 = tmp_struct_202.field2;
            GibCursor pvrtmp_6867 = tmp_struct_202.field3;
            GibCursor pvrtmp_6868 = tmp_struct_202.field4;
            GibCursor pvrtmp_6869 = tmp_struct_202.field5;
            GibCursor pvrtmp_6870 = tmp_struct_202.field6;

            frame = gib_shadowstack_pop(wstack);
            loc_2537 = frame->ptr;
            end_r_2542 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6857 = frame->ptr;
            pvrtmp_6856 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6848 = frame->ptr;
            pvrtmp_6847 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1212_1433_1767 = frame->ptr;
            end_r_2539 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1213_1434_1768 = frame->ptr;
            end_r_2540 = frame->endptr;
            gib_shadowstack_push(rstack, zs_145_1213_1434_1768, end_r_2540, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, ys_144_1212_1433_1767, end_r_2539, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6848, pvrtmp_6847, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6857, pvrtmp_6856, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6869, pvrtmp_6866, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(wstack, loc_2537, end_r_2542, Stk,
                                 PList_v_775_T);

            GibChunk region_6875 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_2980 = region_6875.start;
            GibCursor end_r_2980 = region_6875.end;

            frame = gib_shadowstack_pop(wstack);
            loc_2537 = frame->ptr;
            end_r_2542 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6869 = frame->ptr;
            pvrtmp_6866 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6857 = frame->ptr;
            pvrtmp_6856 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6848 = frame->ptr;
            pvrtmp_6847 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1212_1433_1767 = frame->ptr;
            end_r_2539 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1213_1434_1768 = frame->ptr;
            end_r_2540 = frame->endptr;
            *(GibPackedTag *) r_2980 = 0;

            GibCursor writetag_4815 = r_2980 + 1;
            GibCursor after_tag_4816 = r_2980 + 1;

            gib_shadowstack_push(rstack, zs_145_1213_1434_1768, end_r_2540, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, ys_144_1212_1433_1767, end_r_2539, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6848, pvrtmp_6847, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6857, pvrtmp_6856, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6869, pvrtmp_6866, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, r_2980, end_r_2980, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(wstack, loc_2537, end_r_2542, Stk,
                                 PList_v_775_T);

            GibChunk region_6878 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_2979 = region_6878.start;
            GibCursor end_r_2979 = region_6878.end;

            frame = gib_shadowstack_pop(wstack);
            loc_2537 = frame->ptr;
            end_r_2542 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            r_2980 = frame->ptr;
            end_r_2980 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6869 = frame->ptr;
            pvrtmp_6866 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6857 = frame->ptr;
            pvrtmp_6856 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6848 = frame->ptr;
            pvrtmp_6847 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1212_1433_1767 = frame->ptr;
            end_r_2539 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1213_1434_1768 = frame->ptr;
            end_r_2540 = frame->endptr;
            gib_shadowstack_push(rstack, zs_145_1213_1434_1768, end_r_2540, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, ys_144_1212_1433_1767, end_r_2539, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6848, pvrtmp_6847, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6857, pvrtmp_6856, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6869, pvrtmp_6866, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(wstack, loc_2537, end_r_2542, Stk,
                                 PList_v_775_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_203 =
             reverse_plist_782(pvrtmp_6856, end_r_2980, end_r_2979, r_2979, pvrtmp_6857, r_2980);
            GibCursor pvrtmp_6879 = tmp_struct_203.field0;
            GibCursor pvrtmp_6880 = tmp_struct_203.field1;
            GibCursor pvrtmp_6881 = tmp_struct_203.field2;
            GibCursor pvrtmp_6882 = tmp_struct_203.field3;
            GibCursor pvrtmp_6883 = tmp_struct_203.field4;
            GibCursor pvrtmp_6884 = tmp_struct_203.field5;

            frame = gib_shadowstack_pop(wstack);
            loc_2537 = frame->ptr;
            end_r_2542 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6869 = frame->ptr;
            pvrtmp_6866 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6857 = frame->ptr;
            pvrtmp_6856 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6848 = frame->ptr;
            pvrtmp_6847 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1212_1433_1767 = frame->ptr;
            end_r_2539 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1213_1434_1768 = frame->ptr;
            end_r_2540 = frame->endptr;
            gib_shadowstack_push(rstack, zs_145_1213_1434_1768, end_r_2540, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, ys_144_1212_1433_1767, end_r_2539, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6848, pvrtmp_6847, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6857, pvrtmp_6856, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6869, pvrtmp_6866, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6883, pvrtmp_6881, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(wstack, loc_2537, end_r_2542, Stk,
                                 PList_v_775_T);

            GibChunk region_6889 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_2978 = region_6889.start;
            GibCursor end_r_2978 = region_6889.end;

            frame = gib_shadowstack_pop(wstack);
            loc_2537 = frame->ptr;
            end_r_2542 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6883 = frame->ptr;
            pvrtmp_6881 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6869 = frame->ptr;
            pvrtmp_6866 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6857 = frame->ptr;
            pvrtmp_6856 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6848 = frame->ptr;
            pvrtmp_6847 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1212_1433_1767 = frame->ptr;
            end_r_2539 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1213_1434_1768 = frame->ptr;
            end_r_2540 = frame->endptr;
            *(GibPackedTag *) r_2978 = 0;

            GibCursor writetag_4826 = r_2978 + 1;
            GibCursor after_tag_4827 = r_2978 + 1;

            gib_shadowstack_push(rstack, zs_145_1213_1434_1768, end_r_2540, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, ys_144_1212_1433_1767, end_r_2539, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6848, pvrtmp_6847, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6857, pvrtmp_6856, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6869, pvrtmp_6866, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6883, pvrtmp_6881, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, r_2978, end_r_2978, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(wstack, loc_2537, end_r_2542, Stk,
                                 PList_v_775_T);

            GibChunk region_6892 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_2977 = region_6892.start;
            GibCursor end_r_2977 = region_6892.end;

            frame = gib_shadowstack_pop(wstack);
            loc_2537 = frame->ptr;
            end_r_2542 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            r_2978 = frame->ptr;
            end_r_2978 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6883 = frame->ptr;
            pvrtmp_6881 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6869 = frame->ptr;
            pvrtmp_6866 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6857 = frame->ptr;
            pvrtmp_6856 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6848 = frame->ptr;
            pvrtmp_6847 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1212_1433_1767 = frame->ptr;
            end_r_2539 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1213_1434_1768 = frame->ptr;
            end_r_2540 = frame->endptr;
            gib_shadowstack_push(rstack, zs_145_1213_1434_1768, end_r_2540, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, ys_144_1212_1433_1767, end_r_2539, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6848, pvrtmp_6847, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6857, pvrtmp_6856, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6869, pvrtmp_6866, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6883, pvrtmp_6881, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(wstack, loc_2537, end_r_2542, Stk,
                                 PList_v_775_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_204 =
             reverse_plist_782(end_r_2539, end_r_2978, end_r_2977, r_2977, ys_144_1212_1433_1767, r_2978);
            GibCursor pvrtmp_6893 = tmp_struct_204.field0;
            GibCursor pvrtmp_6894 = tmp_struct_204.field1;
            GibCursor pvrtmp_6895 = tmp_struct_204.field2;
            GibCursor pvrtmp_6896 = tmp_struct_204.field3;
            GibCursor pvrtmp_6897 = tmp_struct_204.field4;
            GibCursor pvrtmp_6898 = tmp_struct_204.field5;

            frame = gib_shadowstack_pop(wstack);
            loc_2537 = frame->ptr;
            end_r_2542 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6883 = frame->ptr;
            pvrtmp_6881 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6869 = frame->ptr;
            pvrtmp_6866 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6857 = frame->ptr;
            pvrtmp_6856 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6848 = frame->ptr;
            pvrtmp_6847 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1212_1433_1767 = frame->ptr;
            end_r_2539 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1213_1434_1768 = frame->ptr;
            end_r_2540 = frame->endptr;
            gib_shadowstack_push(rstack, zs_145_1213_1434_1768, end_r_2540, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, ys_144_1212_1433_1767, end_r_2539, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6848, pvrtmp_6847, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6857, pvrtmp_6856, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6869, pvrtmp_6866, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6883, pvrtmp_6881, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6897, pvrtmp_6895, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(wstack, loc_2537, end_r_2542, Stk,
                                 PList_v_775_T);

            GibChunk region_6903 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_2976 = region_6903.start;
            GibCursor end_r_2976 = region_6903.end;

            frame = gib_shadowstack_pop(wstack);
            loc_2537 = frame->ptr;
            end_r_2542 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6897 = frame->ptr;
            pvrtmp_6895 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6883 = frame->ptr;
            pvrtmp_6881 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6869 = frame->ptr;
            pvrtmp_6866 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6857 = frame->ptr;
            pvrtmp_6856 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6848 = frame->ptr;
            pvrtmp_6847 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1212_1433_1767 = frame->ptr;
            end_r_2539 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1213_1434_1768 = frame->ptr;
            end_r_2540 = frame->endptr;
            gib_shadowstack_push(rstack, zs_145_1213_1434_1768, end_r_2540, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, ys_144_1212_1433_1767, end_r_2539, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6848, pvrtmp_6847, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6857, pvrtmp_6856, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6869, pvrtmp_6866, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(wstack, loc_2537, end_r_2542, Stk,
                                 PList_v_775_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_205 =
             algb(pvrtmp_6881, pvrtmp_6895, end_r_2976, r_2976, pvrtmp_6883, pvrtmp_6897);
            GibCursor pvrtmp_6904 = tmp_struct_205.field0;
            GibCursor pvrtmp_6905 = tmp_struct_205.field1;
            GibCursor pvrtmp_6906 = tmp_struct_205.field2;
            GibCursor pvrtmp_6907 = tmp_struct_205.field3;
            GibCursor pvrtmp_6908 = tmp_struct_205.field4;
            GibCursor pvrtmp_6909 = tmp_struct_205.field5;
            GibCursor pvrtmp_6910 = tmp_struct_205.field6;

            frame = gib_shadowstack_pop(wstack);
            loc_2537 = frame->ptr;
            end_r_2542 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6869 = frame->ptr;
            pvrtmp_6866 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6857 = frame->ptr;
            pvrtmp_6856 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6848 = frame->ptr;
            pvrtmp_6847 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1212_1433_1767 = frame->ptr;
            end_r_2539 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1213_1434_1768 = frame->ptr;
            end_r_2540 = frame->endptr;
            gib_shadowstack_push(rstack, zs_145_1213_1434_1768, end_r_2540, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, ys_144_1212_1433_1767, end_r_2539, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6848, pvrtmp_6847, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6857, pvrtmp_6856, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6869, pvrtmp_6866, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6909, pvrtmp_6906, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(wstack, loc_2537, end_r_2542, Stk,
                                 PList_v_775_T);

            GibChunk region_6915 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_2975 = region_6915.start;
            GibCursor end_r_2975 = region_6915.end;

            frame = gib_shadowstack_pop(wstack);
            loc_2537 = frame->ptr;
            end_r_2542 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6909 = frame->ptr;
            pvrtmp_6906 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6869 = frame->ptr;
            pvrtmp_6866 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6857 = frame->ptr;
            pvrtmp_6856 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6848 = frame->ptr;
            pvrtmp_6847 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1212_1433_1767 = frame->ptr;
            end_r_2539 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1213_1434_1768 = frame->ptr;
            end_r_2540 = frame->endptr;
            *(GibPackedTag *) r_2975 = 0;

            GibCursor writetag_4841 = r_2975 + 1;
            GibCursor after_tag_4842 = r_2975 + 1;

            gib_shadowstack_push(rstack, zs_145_1213_1434_1768, end_r_2540, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, ys_144_1212_1433_1767, end_r_2539, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6848, pvrtmp_6847, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6857, pvrtmp_6856, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6869, pvrtmp_6866, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6909, pvrtmp_6906, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, r_2975, end_r_2975, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(wstack, loc_2537, end_r_2542, Stk,
                                 PList_v_775_T);

            GibChunk region_6918 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_2974 = region_6918.start;
            GibCursor end_r_2974 = region_6918.end;

            frame = gib_shadowstack_pop(wstack);
            loc_2537 = frame->ptr;
            end_r_2542 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            r_2975 = frame->ptr;
            end_r_2975 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6909 = frame->ptr;
            pvrtmp_6906 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6869 = frame->ptr;
            pvrtmp_6866 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6857 = frame->ptr;
            pvrtmp_6856 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6848 = frame->ptr;
            pvrtmp_6847 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1212_1433_1767 = frame->ptr;
            end_r_2539 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1213_1434_1768 = frame->ptr;
            end_r_2540 = frame->endptr;
            gib_shadowstack_push(rstack, zs_145_1213_1434_1768, end_r_2540, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, ys_144_1212_1433_1767, end_r_2539, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6848, pvrtmp_6847, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6857, pvrtmp_6856, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6869, pvrtmp_6866, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(wstack, loc_2537, end_r_2542, Stk,
                                 PList_v_775_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_206 =
             reverse_plist_782(pvrtmp_6906, end_r_2975, end_r_2974, r_2974, pvrtmp_6909, r_2975);
            GibCursor pvrtmp_6919 = tmp_struct_206.field0;
            GibCursor pvrtmp_6920 = tmp_struct_206.field1;
            GibCursor pvrtmp_6921 = tmp_struct_206.field2;
            GibCursor pvrtmp_6922 = tmp_struct_206.field3;
            GibCursor pvrtmp_6923 = tmp_struct_206.field4;
            GibCursor pvrtmp_6924 = tmp_struct_206.field5;

            frame = gib_shadowstack_pop(wstack);
            loc_2537 = frame->ptr;
            end_r_2542 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6869 = frame->ptr;
            pvrtmp_6866 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6857 = frame->ptr;
            pvrtmp_6856 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6848 = frame->ptr;
            pvrtmp_6847 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1212_1433_1767 = frame->ptr;
            end_r_2539 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1213_1434_1768 = frame->ptr;
            end_r_2540 = frame->endptr;

            GibInt fltAppE_1523_1786 = 0 - 1;

            gib_shadowstack_push(rstack, zs_145_1213_1434_1768, end_r_2540, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, ys_144_1212_1433_1767, end_r_2539, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6848, pvrtmp_6847, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6857, pvrtmp_6856, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6869, pvrtmp_6866, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6923, pvrtmp_6921, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(wstack, loc_2537, end_r_2542, Stk,
                                 PList_v_775_T);

            GibChunk region_6929 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_2973 = region_6929.start;
            GibCursor end_r_2973 = region_6929.end;

            frame = gib_shadowstack_pop(wstack);
            loc_2537 = frame->ptr;
            end_r_2542 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6923 = frame->ptr;
            pvrtmp_6921 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6869 = frame->ptr;
            pvrtmp_6866 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6857 = frame->ptr;
            pvrtmp_6856 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6848 = frame->ptr;
            pvrtmp_6847 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1212_1433_1767 = frame->ptr;
            end_r_2539 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1213_1434_1768 = frame->ptr;
            end_r_2540 = frame->endptr;

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_207 =
                                                               zip_plist_783(pvrtmp_6866, pvrtmp_6921, end_r_2973, r_2973, pvrtmp_6869, pvrtmp_6923);
            GibCursor pvrtmp_6930 = tmp_struct_207.field0;
            GibCursor pvrtmp_6931 = tmp_struct_207.field1;
            GibCursor pvrtmp_6932 = tmp_struct_207.field2;
            GibCursor pvrtmp_6933 = tmp_struct_207.field3;
            GibCursor pvrtmp_6934 = tmp_struct_207.field4;
            GibCursorGibCursorGibIntProd tmp_struct_208 =
                                          findk(pvrtmp_6932, 0, 0, fltAppE_1523_1786, pvrtmp_6933);
            GibCursor pvrtmp_6939 = tmp_struct_208.field0;
            GibCursor pvrtmp_6940 = tmp_struct_208.field1;
            GibInt pvrtmp_6941 = tmp_struct_208.field2;
            GibInt fltAppE_1525_1789 = m_141_1209_1430_1764 - m2_150_1439_1775;
            GibInt fltAppE_1526_1790 = n_142_1210_1431_1765 - pvrtmp_6941;

            gib_shadowstack_push(rstack, zs_145_1213_1434_1768, end_r_2540, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, ys_144_1212_1433_1767, end_r_2539, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6848, pvrtmp_6847, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6857, pvrtmp_6856, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(wstack, loc_2537, end_r_2542, Stk,
                                 PList_v_775_T);

            GibChunk region_6942 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_2972 = region_6942.start;
            GibCursor end_r_2972 = region_6942.end;

            frame = gib_shadowstack_pop(wstack);
            loc_2537 = frame->ptr;
            end_r_2542 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6857 = frame->ptr;
            pvrtmp_6856 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6848 = frame->ptr;
            pvrtmp_6847 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1212_1433_1767 = frame->ptr;
            end_r_2539 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1213_1434_1768 = frame->ptr;
            end_r_2540 = frame->endptr;

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_209 =
                                                      drop_plist_781(end_r_2539, end_r_2972, r_2972, pvrtmp_6941, ys_144_1212_1433_1767);
            GibCursor pvrtmp_6943 = tmp_struct_209.field0;
            GibCursor pvrtmp_6944 = tmp_struct_209.field1;
            GibCursor pvrtmp_6945 = tmp_struct_209.field2;
            GibCursor pvrtmp_6946 = tmp_struct_209.field3;

            gib_shadowstack_push(rstack, zs_145_1213_1434_1768, end_r_2540, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, ys_144_1212_1433_1767, end_r_2539, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6848, pvrtmp_6847, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6857, pvrtmp_6856, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6945, pvrtmp_6944, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(wstack, loc_2537, end_r_2542, Stk,
                                 PList_v_775_T);

            GibChunk region_6951 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_2971 = region_6951.start;
            GibCursor end_r_2971 = region_6951.end;

            frame = gib_shadowstack_pop(wstack);
            loc_2537 = frame->ptr;
            end_r_2542 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6945 = frame->ptr;
            pvrtmp_6944 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6857 = frame->ptr;
            pvrtmp_6856 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6848 = frame->ptr;
            pvrtmp_6847 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1212_1433_1767 = frame->ptr;
            end_r_2539 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            zs_145_1213_1434_1768 = frame->ptr;
            end_r_2540 = frame->endptr;
            gib_shadowstack_push(rstack, ys_144_1212_1433_1767, end_r_2539, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6848, pvrtmp_6847, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(wstack, loc_2537, end_r_2542, Stk,
                                 PList_v_775_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_210 =
             algc(pvrtmp_6856, pvrtmp_6944, end_r_2540, end_r_2971, r_2971, fltAppE_1525_1789, fltAppE_1526_1790, pvrtmp_6857, pvrtmp_6945, zs_145_1213_1434_1768);
            GibCursor pvrtmp_6952 = tmp_struct_210.field0;
            GibCursor pvrtmp_6953 = tmp_struct_210.field1;
            GibCursor pvrtmp_6954 = tmp_struct_210.field2;
            GibCursor pvrtmp_6955 = tmp_struct_210.field3;
            GibCursor pvrtmp_6956 = tmp_struct_210.field4;
            GibCursor pvrtmp_6957 = tmp_struct_210.field5;

            frame = gib_shadowstack_pop(wstack);
            loc_2537 = frame->ptr;
            end_r_2542 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6848 = frame->ptr;
            pvrtmp_6847 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1212_1433_1767 = frame->ptr;
            end_r_2539 = frame->endptr;
            gib_shadowstack_push(rstack, ys_144_1212_1433_1767, end_r_2539, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6848, pvrtmp_6847, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(rstack, pvrtmp_6956, pvrtmp_6955, Stk,
                                 PList_v_775_T);
            gib_shadowstack_push(wstack, loc_2537, end_r_2542, Stk,
                                 PList_v_775_T);

            GibChunk region_6962 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_2970 = region_6962.start;
            GibCursor end_r_2970 = region_6962.end;

            frame = gib_shadowstack_pop(wstack);
            loc_2537 = frame->ptr;
            end_r_2542 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6956 = frame->ptr;
            pvrtmp_6955 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_6848 = frame->ptr;
            pvrtmp_6847 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_144_1212_1433_1767 = frame->ptr;
            end_r_2539 = frame->endptr;

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_211 =
                                                      take_plist_780(end_r_2539, end_r_2970, r_2970, pvrtmp_6941, ys_144_1212_1433_1767);
            GibCursor pvrtmp_6963 = tmp_struct_211.field0;
            GibCursor pvrtmp_6964 = tmp_struct_211.field1;
            GibCursor pvrtmp_6965 = tmp_struct_211.field2;
            GibCursor pvrtmp_6966 = tmp_struct_211.field3;
            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_212 =
             algc(pvrtmp_6847, pvrtmp_6964, pvrtmp_6955, end_r_2542, loc_2537, m2_150_1439_1775, pvrtmp_6941, pvrtmp_6848, pvrtmp_6965, pvrtmp_6956);
            GibCursor pvrtmp_6971 = tmp_struct_212.field0;
            GibCursor pvrtmp_6972 = tmp_struct_212.field1;
            GibCursor pvrtmp_6973 = tmp_struct_212.field2;
            GibCursor pvrtmp_6974 = tmp_struct_212.field3;
            GibCursor pvrtmp_6975 = tmp_struct_212.field4;
            GibCursor pvrtmp_6976 = tmp_struct_212.field5;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6855,
                                                                                          pvrtmp_6963,
                                                                                          pvrtmp_6954,
                                                                                          end_r_2541,
                                                                                          pvrtmp_6974,
                                                                                          pvrtmp_6975,
                                                                                          pvrtmp_6976};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_214 = *(uintptr_t *) tmpcur_6830;
            GibCursor tmpcur_6983 = GIB_UNTAG(tagged_tmpcur_214);
            GibCursor tmpaftercur_6984 = tmpcur_6830 + 8;
            uint16_t tmptag_6985 = GIB_GET_TAG(tagged_tmpcur_214);
            GibCursor end_from_tagged_indr_3384 = tmpcur_6983 + tmptag_6985;
            GibCursor jump_3386 = tmpcur_6830 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_213 =
             caseFn_1208(end_r_2538, end_r_2539, end_r_2540, end_from_tagged_indr_3384, end_r_2542, loc_2537, m_141_1209_1430_1764, n_142_1210_1431_1765, xs_143_1211_1432_1766, ys_144_1212_1433_1767, zs_145_1213_1434_1768, tmpcur_6983, x_146_1215_1436_1770);
            GibCursor pvrtmp_6986 = tmp_struct_213.field0;
            GibCursor pvrtmp_6987 = tmp_struct_213.field1;
            GibCursor pvrtmp_6988 = tmp_struct_213.field2;
            GibCursor pvrtmp_6989 = tmp_struct_213.field3;
            GibCursor pvrtmp_6990 = tmp_struct_213.field4;
            GibCursor pvrtmp_6991 = tmp_struct_213.field5;
            GibCursor pvrtmp_6992 = tmp_struct_213.field6;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_6986,
                                                                                          pvrtmp_6987,
                                                                                          pvrtmp_6988,
                                                                                          end_r_2541,
                                                                                          pvrtmp_6990,
                                                                                          pvrtmp_6991,
                                                                                          pvrtmp_6992};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_216 = *(uintptr_t *) tmpcur_6830;
            GibCursor tmpcur_6999 = GIB_UNTAG(tagged_tmpcur_216);
            GibCursor tmpaftercur_7000 = tmpcur_6830 + 8;
            uint16_t tmptag_7001 = GIB_GET_TAG(tagged_tmpcur_216);
            GibCursor end_from_tagged_indr_3384 = tmpcur_6999 + tmptag_7001;
            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_215 =
             caseFn_1208(end_r_2538, end_r_2539, end_r_2540, end_from_tagged_indr_3384, end_r_2542, loc_2537, m_141_1209_1430_1764, n_142_1210_1431_1765, xs_143_1211_1432_1766, ys_144_1212_1433_1767, zs_145_1213_1434_1768, tmpcur_6999, x_146_1215_1436_1770);
            GibCursor pvrtmp_7002 = tmp_struct_215.field0;
            GibCursor pvrtmp_7003 = tmp_struct_215.field1;
            GibCursor pvrtmp_7004 = tmp_struct_215.field2;
            GibCursor pvrtmp_7005 = tmp_struct_215.field3;
            GibCursor pvrtmp_7006 = tmp_struct_215.field4;
            GibCursor pvrtmp_7007 = tmp_struct_215.field5;
            GibCursor pvrtmp_7008 = tmp_struct_215.field6;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_7002,
                                                                                          pvrtmp_7003,
                                                                                          pvrtmp_7004,
                                                                                          pvrtmp_7005,
                                                                                          pvrtmp_7006,
                                                                                          pvrtmp_7007,
                                                                                          pvrtmp_7008};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6829");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd caseFn_1216(GibCursor end_r_2547,
                                                                       GibCursor end_r_2548,
                                                                       GibCursor end_r_2549,
                                                                       GibCursor end_r_2550,
                                                                       GibCursor loc_2546,
                                                                       GibInt m_141_1217_1450_1795,
                                                                       GibInt n_142_1218_1451_1796,
                                                                       GibCursor xs_143_1219_1452_1797,
                                                                       GibCursor ys_144_1220_1453_1798,
                                                                       GibCursor zs_145_1221_1454_1799)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2546 + 18 > end_r_2550) {
        gib_grow_region(&loc_2546, &end_r_2550);
    }

    GibPackedTag tmpval_7016 = *(GibPackedTag *) xs_143_1219_1452_1797;
    GibCursor tmpcur_7017 = xs_143_1219_1452_1797 + 1;


  switch_7067:
    ;
    switch (tmpval_7016) {

      case 0:
        {
            *(GibPackedTag *) loc_2546 = 0;

            GibCursor writetag_4891 = loc_2546 + 1;
            GibCursor after_tag_4892 = loc_2546 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2547,
                                                                                 end_r_2548,
                                                                                 end_r_2549,
                                                                                 end_r_2550,
                                                                                 loc_2546,
                                                                                 after_tag_4892};
            break;
        }

      case 1:
        {
            GibInt tmpval_7022 = *(GibInt *) tmpcur_7017;
            GibCursor tmpcur_7023 = tmpcur_7017 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_220 =
             caseFn_1208(end_r_2547, end_r_2548, end_r_2549, end_r_2547, end_r_2550, loc_2546, m_141_1217_1450_1795, n_142_1218_1451_1796, xs_143_1219_1452_1797, ys_144_1220_1453_1798, zs_145_1221_1454_1799, tmpcur_7023, tmpval_7022);
            GibCursor pvrtmp_7024 = tmp_struct_220.field0;
            GibCursor pvrtmp_7025 = tmp_struct_220.field1;
            GibCursor pvrtmp_7026 = tmp_struct_220.field2;
            GibCursor pvrtmp_7027 = tmp_struct_220.field3;
            GibCursor pvrtmp_7028 = tmp_struct_220.field4;
            GibCursor pvrtmp_7029 = tmp_struct_220.field5;
            GibCursor pvrtmp_7030 = tmp_struct_220.field6;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_7027,
                                                                                 pvrtmp_7025,
                                                                                 pvrtmp_7026,
                                                                                 pvrtmp_7028,
                                                                                 pvrtmp_7029,
                                                                                 pvrtmp_7030};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_222 = *(uintptr_t *) tmpcur_7017;
            GibCursor tmpcur_7037 = GIB_UNTAG(tagged_tmpcur_222);
            GibCursor tmpaftercur_7038 = tmpcur_7017 + 8;
            uint16_t tmptag_7039 = GIB_GET_TAG(tagged_tmpcur_222);
            GibCursor end_from_tagged_indr_3389 = tmpcur_7037 + tmptag_7039;
            GibCursor jump_3391 = tmpcur_7017 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_221 =
             caseFn_1216(end_from_tagged_indr_3389, end_r_2548, end_r_2549, end_r_2550, loc_2546, m_141_1217_1450_1795, n_142_1218_1451_1796, tmpcur_7037, ys_144_1220_1453_1798, zs_145_1221_1454_1799);
            GibCursor pvrtmp_7040 = tmp_struct_221.field0;
            GibCursor pvrtmp_7041 = tmp_struct_221.field1;
            GibCursor pvrtmp_7042 = tmp_struct_221.field2;
            GibCursor pvrtmp_7043 = tmp_struct_221.field3;
            GibCursor pvrtmp_7044 = tmp_struct_221.field4;
            GibCursor pvrtmp_7045 = tmp_struct_221.field5;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2547,
                                                                                 pvrtmp_7041,
                                                                                 pvrtmp_7042,
                                                                                 pvrtmp_7043,
                                                                                 pvrtmp_7044,
                                                                                 pvrtmp_7045};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_224 = *(uintptr_t *) tmpcur_7017;
            GibCursor tmpcur_7052 = GIB_UNTAG(tagged_tmpcur_224);
            GibCursor tmpaftercur_7053 = tmpcur_7017 + 8;
            uint16_t tmptag_7054 = GIB_GET_TAG(tagged_tmpcur_224);
            GibCursor end_from_tagged_indr_3389 = tmpcur_7052 + tmptag_7054;
            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_223 =
             caseFn_1216(end_from_tagged_indr_3389, end_r_2548, end_r_2549, end_r_2550, loc_2546, m_141_1217_1450_1795, n_142_1218_1451_1796, tmpcur_7052, ys_144_1220_1453_1798, zs_145_1221_1454_1799);
            GibCursor pvrtmp_7055 = tmp_struct_223.field0;
            GibCursor pvrtmp_7056 = tmp_struct_223.field1;
            GibCursor pvrtmp_7057 = tmp_struct_223.field2;
            GibCursor pvrtmp_7058 = tmp_struct_223.field3;
            GibCursor pvrtmp_7059 = tmp_struct_223.field4;
            GibCursor pvrtmp_7060 = tmp_struct_223.field5;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_7055,
                                                                                 pvrtmp_7056,
                                                                                 pvrtmp_7057,
                                                                                 pvrtmp_7058,
                                                                                 pvrtmp_7059,
                                                                                 pvrtmp_7060};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7016");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd caseFn_1222(GibCursor end_r_2554,
                                                              GibCursor end_r_2555,
                                                              GibCursor end_r_2556,
                                                              GibCursor loc_2553,
                                                              GibCursor bs_214_1223_1457_1802,
                                                              GibInt z_217_1224_1458_1803,
                                                              GibCursor zs_218_1225_1459_1804)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2553 + 26 > end_r_2556) {
        gib_grow_region(&loc_2553, &end_r_2556);
    }

    GibPackedTag tmpval_7068 = *(GibPackedTag *) bs_214_1223_1457_1802;
    GibCursor tmpcur_7069 = bs_214_1223_1457_1802 + 1;


  switch_7117:
    ;
    switch (tmpval_7068) {

      case 0:
        {
            *(GibPackedTag *) loc_2553 = 0;

            GibCursor writetag_4921 = loc_2553 + 1;
            GibCursor after_tag_4922 = loc_2553 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2554,
                                                                        end_r_2555,
                                                                        end_r_2556,
                                                                        loc_2553,
                                                                        after_tag_4922};
            break;
        }

      case 1:
        {
            GibInt tmpval_7074 = *(GibInt *) tmpcur_7069;
            GibCursor tmpcur_7075 = tmpcur_7069 + sizeof(GibInt);
            GibCursor loc_3011 = loc_2553 + 17;

            *(GibPackedTag *) loc_2553 = 1;

            GibCursor writetag_4934 = loc_2553 + 1;
            GibCursor after_tag_4935 = loc_2553 + 1;

            *(GibInt *) after_tag_4935 = z_217_1224_1458_1803;

            GibCursor writecur_4939 = after_tag_4935 + sizeof(GibInt);

            *(GibInt *) writecur_4939 = tmpval_7074;

            GibCursor writecur_4940 = writecur_4939 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_228 =
                                                               zip_plist_783(end_r_2555, end_r_2554, end_r_2556, loc_3011, zs_218_1225_1459_1804, tmpcur_7075);
            GibCursor pvrtmp_7076 = tmp_struct_228.field0;
            GibCursor pvrtmp_7077 = tmp_struct_228.field1;
            GibCursor pvrtmp_7078 = tmp_struct_228.field2;
            GibCursor pvrtmp_7079 = tmp_struct_228.field3;
            GibCursor pvrtmp_7080 = tmp_struct_228.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_7077,
                                                                        pvrtmp_7076,
                                                                        pvrtmp_7078,
                                                                        loc_2553,
                                                                        pvrtmp_7080};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_230 = *(uintptr_t *) tmpcur_7069;
            GibCursor tmpcur_7089 = GIB_UNTAG(tagged_tmpcur_230);
            GibCursor tmpaftercur_7090 = tmpcur_7069 + 8;
            uint16_t tmptag_7091 = GIB_GET_TAG(tagged_tmpcur_230);
            GibCursor end_from_tagged_indr_3394 = tmpcur_7089 + tmptag_7091;
            GibCursor jump_3396 = tmpcur_7069 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_229 =
                                                               caseFn_1222(end_from_tagged_indr_3394, end_r_2555, end_r_2556, loc_2553, tmpcur_7089, z_217_1224_1458_1803, zs_218_1225_1459_1804);
            GibCursor pvrtmp_7092 = tmp_struct_229.field0;
            GibCursor pvrtmp_7093 = tmp_struct_229.field1;
            GibCursor pvrtmp_7094 = tmp_struct_229.field2;
            GibCursor pvrtmp_7095 = tmp_struct_229.field3;
            GibCursor pvrtmp_7096 = tmp_struct_229.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2554,
                                                                        pvrtmp_7093,
                                                                        pvrtmp_7094,
                                                                        pvrtmp_7095,
                                                                        pvrtmp_7096};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_232 = *(uintptr_t *) tmpcur_7069;
            GibCursor tmpcur_7103 = GIB_UNTAG(tagged_tmpcur_232);
            GibCursor tmpaftercur_7104 = tmpcur_7069 + 8;
            uint16_t tmptag_7105 = GIB_GET_TAG(tagged_tmpcur_232);
            GibCursor end_from_tagged_indr_3394 = tmpcur_7103 + tmptag_7105;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_231 =
                                                               caseFn_1222(end_from_tagged_indr_3394, end_r_2555, end_r_2556, loc_2553, tmpcur_7103, z_217_1224_1458_1803, zs_218_1225_1459_1804);
            GibCursor pvrtmp_7106 = tmp_struct_231.field0;
            GibCursor pvrtmp_7107 = tmp_struct_231.field1;
            GibCursor pvrtmp_7108 = tmp_struct_231.field2;
            GibCursor pvrtmp_7109 = tmp_struct_231.field3;
            GibCursor pvrtmp_7110 = tmp_struct_231.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_7106,
                                                                        pvrtmp_7107,
                                                                        pvrtmp_7108,
                                                                        pvrtmp_7109,
                                                                        pvrtmp_7110};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7068");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd caseFn_1226(GibCursor end_r_2559,
                                                     GibCursor end_r_2560,
                                                     GibCursor loc_2558,
                                                     GibInt n_203_1227_1462_1808,
                                                     GibCursor a_204_1228_1463_1809)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2558 + 18 > end_r_2560) {
        gib_grow_region(&loc_2558, &end_r_2560);
    }

    GibPackedTag tmpval_7118 = *(GibPackedTag *) a_204_1228_1463_1809;
    GibCursor tmpcur_7119 = a_204_1228_1463_1809 + 1;


  switch_7164:
    ;
    switch (tmpval_7118) {

      case 0:
        {
            *(GibPackedTag *) loc_2558 = 0;

            GibCursor writetag_4957 = loc_2558 + 1;
            GibCursor after_tag_4958 = loc_2558 + 1;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_2559,
                                                               end_r_2560,
                                                               loc_2558,
                                                               after_tag_4958};
            break;
        }

      case 1:
        {
            GibInt tmpval_7124 = *(GibInt *) tmpcur_7119;
            GibCursor tmpcur_7125 = tmpcur_7119 + sizeof(GibInt);
            GibInt fltAppE_1531_1812 = n_203_1227_1462_1808 - 1;
            GibCursor loc_3026 = loc_2558 + 9;

            *(GibPackedTag *) loc_2558 = 1;

            GibCursor writetag_4969 = loc_2558 + 1;
            GibCursor after_tag_4970 = loc_2558 + 1;

            *(GibInt *) after_tag_4970 = tmpval_7124;

            GibCursor writecur_4974 = after_tag_4970 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_236 =
                                                      take_plist_780(end_r_2559, end_r_2560, loc_3026, fltAppE_1531_1812, tmpcur_7125);
            GibCursor pvrtmp_7126 = tmp_struct_236.field0;
            GibCursor pvrtmp_7127 = tmp_struct_236.field1;
            GibCursor pvrtmp_7128 = tmp_struct_236.field2;
            GibCursor pvrtmp_7129 = tmp_struct_236.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_7126,
                                                               pvrtmp_7127,
                                                               loc_2558,
                                                               pvrtmp_7129};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_238 = *(uintptr_t *) tmpcur_7119;
            GibCursor tmpcur_7138 = GIB_UNTAG(tagged_tmpcur_238);
            GibCursor tmpaftercur_7139 = tmpcur_7119 + 8;
            uint16_t tmptag_7140 = GIB_GET_TAG(tagged_tmpcur_238);
            GibCursor end_from_tagged_indr_3399 = tmpcur_7138 + tmptag_7140;
            GibCursor jump_3401 = tmpcur_7119 + 8;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_237 =
                                                      caseFn_1226(end_from_tagged_indr_3399, end_r_2560, loc_2558, n_203_1227_1462_1808, tmpcur_7138);
            GibCursor pvrtmp_7141 = tmp_struct_237.field0;
            GibCursor pvrtmp_7142 = tmp_struct_237.field1;
            GibCursor pvrtmp_7143 = tmp_struct_237.field2;
            GibCursor pvrtmp_7144 = tmp_struct_237.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_2559,
                                                               pvrtmp_7142,
                                                               pvrtmp_7143,
                                                               pvrtmp_7144};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_240 = *(uintptr_t *) tmpcur_7119;
            GibCursor tmpcur_7151 = GIB_UNTAG(tagged_tmpcur_240);
            GibCursor tmpaftercur_7152 = tmpcur_7119 + 8;
            uint16_t tmptag_7153 = GIB_GET_TAG(tagged_tmpcur_240);
            GibCursor end_from_tagged_indr_3399 = tmpcur_7151 + tmptag_7153;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_239 =
                                                      caseFn_1226(end_from_tagged_indr_3399, end_r_2560, loc_2558, n_203_1227_1462_1808, tmpcur_7151);
            GibCursor pvrtmp_7154 = tmp_struct_239.field0;
            GibCursor pvrtmp_7155 = tmp_struct_239.field1;
            GibCursor pvrtmp_7156 = tmp_struct_239.field2;
            GibCursor pvrtmp_7157 = tmp_struct_239.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_7154,
                                                               pvrtmp_7155,
                                                               pvrtmp_7156,
                                                               pvrtmp_7157};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7118");
            exit(1);
        }
    }
}
int main(int argc, char **argv)
{
    int init_252 = gib_init(argc, argv);

    info_table_initialize();
    symbol_table_initialize();

    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibInt n_101_1229_1532 = gib_get_size_param();
    GibBool fltPrm_1472_1533 = n_101_1229_1532 < 1;
    GibBool fltPrm_1473_1534 = n_101_1229_1532 == 1;
    GibBool fltIf_1471_1535 = fltPrm_1472_1533 || fltPrm_1473_1534;

    if (fltIf_1471_1535) {
        GibIntGibIntGibIntGibIntGibIntGibIntProd tmp_struct_244 =  test_opts();
        GibInt pvrtmp_5712 = tmp_struct_244.field0;
        GibInt pvrtmp_5713 = tmp_struct_244.field1;
        GibInt pvrtmp_5714 = tmp_struct_244.field2;
        GibInt pvrtmp_5715 = tmp_struct_244.field3;
        GibInt pvrtmp_5716 = tmp_struct_244.field4;
        GibInt pvrtmp_5717 = tmp_struct_244.field5;
        GibIntGibIntGibIntProd tmp_struct_245 =  test_opts_answer();
        GibInt pvrtmp_5718 = tmp_struct_245.field0;
        GibInt pvrtmp_5719 = tmp_struct_245.field1;
        GibInt pvrtmp_5720 = tmp_struct_245.field2;
        GibBool tailapp_3236 =
                 bench_lcss((GibIntGibIntGibIntGibIntGibIntGibIntProd) {pvrtmp_5712, pvrtmp_5713, pvrtmp_5714, pvrtmp_5715, pvrtmp_5716, pvrtmp_5717}, (GibIntGibIntGibIntProd) {pvrtmp_5718, pvrtmp_5719, pvrtmp_5720});

        if (tailapp_3236) {
            printf("#t");
            printf("\n");
            // return 0;
        } else {
            printf("#f");
            printf("\n");
            // return 0;
        }
    } else {
        GibBool fltIf_1476_1538 = n_101_1229_1532 == 2;

        if (fltIf_1476_1538) {
            GibIntGibIntGibIntGibIntGibIntGibIntProd tmp_struct_246 =
                                                      fast_opts();
            GibInt pvrtmp_5730 = tmp_struct_246.field0;
            GibInt pvrtmp_5731 = tmp_struct_246.field1;
            GibInt pvrtmp_5732 = tmp_struct_246.field2;
            GibInt pvrtmp_5733 = tmp_struct_246.field3;
            GibInt pvrtmp_5734 = tmp_struct_246.field4;
            GibInt pvrtmp_5735 = tmp_struct_246.field5;
            GibIntGibIntGibIntProd tmp_struct_247 =  fast_opts_answer();
            GibInt pvrtmp_5736 = tmp_struct_247.field0;
            GibInt pvrtmp_5737 = tmp_struct_247.field1;
            GibInt pvrtmp_5738 = tmp_struct_247.field2;
            GibBool tailapp_3237 =
                     bench_lcss((GibIntGibIntGibIntGibIntGibIntGibIntProd) {pvrtmp_5730, pvrtmp_5731, pvrtmp_5732, pvrtmp_5733, pvrtmp_5734, pvrtmp_5735}, (GibIntGibIntGibIntProd) {pvrtmp_5736, pvrtmp_5737, pvrtmp_5738});

            if (tailapp_3237) {
                printf("#t");
                printf("\n");
                // return 0;
            } else {
                printf("#f");
                printf("\n");
                // return 0;
            }
        } else {
            GibBool fltIf_1479_1541 = n_101_1229_1532 == 3;

            if (fltIf_1479_1541) {
                GibIntGibIntGibIntGibIntGibIntGibIntProd tmp_struct_248 =
                                                          norm_opts();
                GibInt pvrtmp_5748 = tmp_struct_248.field0;
                GibInt pvrtmp_5749 = tmp_struct_248.field1;
                GibInt pvrtmp_5750 = tmp_struct_248.field2;
                GibInt pvrtmp_5751 = tmp_struct_248.field3;
                GibInt pvrtmp_5752 = tmp_struct_248.field4;
                GibInt pvrtmp_5753 = tmp_struct_248.field5;
                GibIntGibIntGibIntProd tmp_struct_249 =  norm_opts_answer();
                GibInt pvrtmp_5754 = tmp_struct_249.field0;
                GibInt pvrtmp_5755 = tmp_struct_249.field1;
                GibInt pvrtmp_5756 = tmp_struct_249.field2;
                GibBool tailapp_3238 =
                         bench_lcss((GibIntGibIntGibIntGibIntGibIntGibIntProd) {pvrtmp_5748, pvrtmp_5749, pvrtmp_5750, pvrtmp_5751, pvrtmp_5752, pvrtmp_5753}, (GibIntGibIntGibIntProd) {pvrtmp_5754, pvrtmp_5755, pvrtmp_5756});

                if (tailapp_3238) {
                    printf("#t");
                    printf("\n");
                    // return 0;
                } else {
                    printf("#f");
                    printf("\n");
                    // return 0;
                }
            } else {
                GibIntGibIntGibIntGibIntGibIntGibIntProd tmp_struct_250 =
                                                          slow_opts();
                GibInt pvrtmp_5766 = tmp_struct_250.field0;
                GibInt pvrtmp_5767 = tmp_struct_250.field1;
                GibInt pvrtmp_5768 = tmp_struct_250.field2;
                GibInt pvrtmp_5769 = tmp_struct_250.field3;
                GibInt pvrtmp_5770 = tmp_struct_250.field4;
                GibInt pvrtmp_5771 = tmp_struct_250.field5;
                GibIntGibIntGibIntProd tmp_struct_251 =  slow_opts_answer();
                GibInt pvrtmp_5772 = tmp_struct_251.field0;
                GibInt pvrtmp_5773 = tmp_struct_251.field1;
                GibInt pvrtmp_5774 = tmp_struct_251.field2;
                GibBool tailapp_3239 =
                         bench_lcss((GibIntGibIntGibIntGibIntGibIntGibIntProd) {pvrtmp_5766, pvrtmp_5767, pvrtmp_5768, pvrtmp_5769, pvrtmp_5770, pvrtmp_5771}, (GibIntGibIntGibIntProd) {pvrtmp_5772, pvrtmp_5773, pvrtmp_5774});

                if (tailapp_3239) {
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

    int exit_253 = gib_exit();

    return exit_253;
}
