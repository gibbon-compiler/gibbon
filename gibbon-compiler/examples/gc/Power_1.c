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
typedef struct GibFloatProd_struct {
            GibFloat field0;
        } GibFloatProd;
typedef struct GibFloatGibCursorProd_struct {
            GibFloat field0;
            GibCursor field1;
        } GibFloatGibCursorProd;
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
unsigned char bench_psc();
unsigned char bench_psb();
unsigned char bench_ts();
GibCursorGibCursorGibCursorProd expx_ans(GibCursor end_r_2981,
                                         GibCursor loc_2980);
GibCursorGibCursorGibCursorProd sinx_ans(GibCursor end_r_2983,
                                         GibCursor loc_2982);
GibCursorGibCursorGibCursorProd cosx_ans(GibCursor end_r_2985,
                                         GibCursor loc_2984);
GibCursorGibCursorGibCursorProd ansb(GibCursor end_r_2987, GibCursor loc_2986);
GibCursorGibCursorGibCursorProd ansc(GibCursor end_r_2989, GibCursor loc_2988);
GibCursorGibCursorGibCursorProd ansd(GibCursor end_r_2991, GibCursor loc_2990);
GibCursorGibCursorGibCursorProd psB(GibCursor end_r_2993, GibCursor loc_2992,
                                    GibInt n_242_856_1365);
GibCursorGibCursorGibCursorProd psC(GibCursor end_r_2995, GibCursor loc_2994,
                                    GibInt n_243_857_1375);
GibCursorGibCursorGibCursorGibCursorGibCursorProd toList(GibCursor end_r_2998,
                                                         GibCursor end_r_2999,
                                                         GibCursor loc_2997,
                                                         GibCursor ps_244_858_1389);
GibCursorGibCursorGibBoolProd equal(GibCursor end_r_3002, GibCursor end_r_3003,
                                    GibCursor as_247_861_1393,
                                    GibCursor bs_248_862_1394);
GibCursorGibCursorGibCursorProd expx(GibCursor end_r_3005, GibCursor loc_3004,
                                     GibInt n_258_865_1397);
GibCursorGibCursorGibCursorProd sinx(GibCursor end_r_3007, GibCursor loc_3006,
                                     GibInt n_259_866_1403);
GibCursorGibCursorGibCursorProd cosx(GibCursor end_r_3009, GibCursor loc_3008,
                                     GibInt n_260_867_1407);
GibCursorGibCursorGibCursorGibCursorProd psSqrt(GibCursor end_r_3012,
                                                GibCursor end_r_3013,
                                                GibCursor loc_3011,
                                                GibInt n_261_868_1414,
                                                GibCursor a_262_869_1415);
GibCursorGibCursorGibCursorGibCursorProd getQs(GibCursor end_r_3016,
                                               GibCursor end_r_3017,
                                               GibCursor loc_3015,
                                               GibInt n_267_872_1419,
                                               GibCursor fs_268_873_1420);
GibCursorGibCursorGibCursorGibCursorGibCursorProd integral(GibCursor end_r_3020,
                                                           GibCursor end_r_3021,
                                                           GibCursor loc_3019,
                                                           GibCursor fs_269_874_1431);
GibCursorGibCursorGibCursorGibCursorGibCursorProd int1(GibCursor end_r_3024,
                                                       GibCursor end_r_3025,
                                                       GibCursor loc_3023,
                                                       GibCursor a_270_875_1433,
                                                       GibInt n_271_876_1434);
GibCursorGibCursorGibCursorGibCursorGibCursorProd deriv(GibCursor end_r_3028,
                                                        GibCursor end_r_3029,
                                                        GibCursor loc_3027,
                                                        GibCursor a_274_879_1441);
GibCursorGibCursorGibCursorGibCursorGibCursorProd deriv1(GibCursor end_r_3032,
                                                         GibCursor end_r_3033,
                                                         GibCursor loc_3031,
                                                         GibCursor a_277_882_1444,
                                                         GibInt n_278_883_1445);
GibCursorGibCursorGibCursorGibCursorProd revert(GibCursor end_r_3036,
                                                GibCursor end_r_3037,
                                                GibCursor loc_3035,
                                                GibInt n_281_886_1452,
                                                GibCursor a_282_887_1453);
GibCursorGibCursorGibCursorGibCursorProd getRs(GibCursor end_r_3040,
                                               GibCursor end_r_3041,
                                               GibCursor loc_3039,
                                               GibInt n_287_890_1457,
                                               GibCursor fs_288_891_1458);
GibCursorGibCursorGibCursorGibCursorGibCursorProd compose(GibCursor end_r_3045,
                                                          GibCursor end_r_3046,
                                                          GibCursor end_r_3047,
                                                          GibCursor loc_3044,
                                                          GibCursor a_289_892_1466,
                                                          GibCursor b_290_893_1467);
GibCursorGibCursorGibCursorProd list(GibCursor end_r_3049, GibCursor loc_3048,
                                     GibInt n_295_896_1470);
GibCursorGibCursorGibCursorProd ts(GibCursor end_r_3051, GibCursor loc_3050,
                                   GibInt n_296_897_1474);
GibCursorGibCursorGibCursorGibCursorProd takePs(GibCursor end_r_3054,
                                                GibCursor end_r_3055,
                                                GibCursor loc_3053,
                                                GibInt n_297_898_1483,
                                                GibCursor fs_298_899_1484);
GibCursorGibCursorGibCursorGibCursorGibCursorProd psDiv(GibCursor end_r_3059,
                                                        GibCursor end_r_3060,
                                                        GibCursor end_r_3061,
                                                        GibCursor loc_3058,
                                                        GibInt n_301_900_1486,
                                                        GibCursor a_302_901_1487,
                                                        GibCursor b_303_902_1488);
GibCursorGibCursorGibCursorGibCursorGibCursorProd psMult(GibCursor end_r_3065,
                                                         GibCursor end_r_3066,
                                                         GibCursor end_r_3067,
                                                         GibCursor loc_3064,
                                                         GibCursor a_311_903_1490,
                                                         GibCursor b_312_904_1491);
GibCursorGibCursorGibCursorGibCursorGibCursorProd psAdd(GibCursor end_r_3071,
                                                        GibCursor end_r_3072,
                                                        GibCursor end_r_3073,
                                                        GibCursor loc_3070,
                                                        GibCursor a_317_907_1494,
                                                        GibCursor b_318_908_1495);
GibCursorGibCursorGibCursorGibCursorGibCursorProd psNeg(GibCursor end_r_3076,
                                                        GibCursor end_r_3077,
                                                        GibCursor loc_3075,
                                                        GibCursor a_323_911_1498);
GibCursorGibCursorGibCursorProd psX(GibCursor end_r_3079, GibCursor loc_3078);
GibCursorGibCursorGibCursorGibCursorGibCursorProd dot(GibCursor end_r_3082,
                                                      GibCursor end_r_3083,
                                                      GibCursor loc_3081,
                                                      GibFloat c_326_914_1505,
                                                      GibCursor b_327_915_1506);
GibCursorGibCursorGibCursorProd pone(GibCursor end_r_3085, GibCursor loc_3084);
GibCursorGibCursorGibIntProd size(GibCursor end_r_3087,
                                  GibCursor ls_330_918_1512);
unsigned char print_check(GibBool b_333_921_1516);
unsigned char print_space(unsigned char wildcard__20_336_924_1519);
unsigned char print_newline(unsigned char wildcard__18_337_925_1520);
GibInt compare_int(GibInt r1_338_926_1521, GibInt r2_339_927_1522);
GibInt compare_float(GibFloat r1_340_928_1525, GibFloat r2_341_929_1526);
GibFloat float_abs(GibFloat f_342_930_1529);
GibFloat minFloat(GibFloat a_343_931_1532, GibFloat b_344_932_1533);
GibFloat maxFloat(GibFloat a_345_933_1535, GibFloat b_346_934_1536);
GibInt minInt(GibInt a_347_935_1538, GibInt b_348_936_1539);
GibInt maxInt(GibInt a_349_937_1541, GibInt b_350_938_1542);
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_Ps(GibCursor end_r_3090,
                                                           GibCursor end_r_3091,
                                                           GibCursor loc_3089,
                                                           GibCursor arg_743_939_1544);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_Ps(GibCursor end_r_3094, GibCursor end_r_3095,
                      GibCursor loc_3093, GibCursor arg_748_944_1549);
GibCursorGibCursorProd _traverse_Ps(GibCursor end_r_3097,
                                    GibCursor arg_753_949_1554);
GibCursorGibCursorProd _print_Ps(GibCursor end_r_3099,
                                 GibCursor arg_758_953_1558);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_PList1(GibCursor end_r_3102, GibCursor end_r_3103, GibCursor loc_3101,
             GibCursor arg_773_970_1575);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_PList1(GibCursor end_r_3106, GibCursor end_r_3107,
                          GibCursor loc_3105, GibCursor arg_778_975_1580);
GibCursorGibCursorProd _traverse_PList1(GibCursor end_r_3109,
                                        GibCursor arg_783_980_1585);
GibCursorGibCursorProd _print_PList1(GibCursor end_r_3111,
                                     GibCursor arg_788_984_1589);
GibCursorGibBoolProd caseFn_803(GibCursor end_r_3113,
                                GibCursor bs_248_804_1001_1606);
GibCursorGibBoolProd caseFn_805(GibCursor end_r_3115,
                                GibCursor bs_248_806_1004_1609);
GibCursorGibCursorGibBoolProd caseFn_807(GibCursor end_r_3118,
                                         GibCursor end_r_3119,
                                         GibCursor bs_248_808_1007_1612,
                                         GibFloat a_253_809_1008_1613,
                                         GibCursor as__254_810_1009_1614);
GibCursorGibCursorGibCursorGibCursorProd caseFn_811(GibCursor end_r_3122,
                                                    GibCursor end_r_3123,
                                                    GibCursor loc_3121,
                                                    GibInt n_261_812_1013_1623,
                                                    GibCursor fs_264_813_1014_1624);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
caseFn_814(GibCursor end_r_3126, GibCursor end_r_3127, GibCursor loc_3125,
           GibFloat f_283_815_1017_1630, GibCursor fs__286_816_1018_1631,
           GibFloat f__285_817_1019_1632);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
caseFn_818(GibCursor end_r_3130, GibCursor end_r_3131, GibCursor loc_3129,
           GibFloat f_283_819_1020_1638, GibCursor fs_284_820_1021_1639);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
caseFn_821(GibCursor end_r_3135, GibCursor end_r_3136, GibCursor end_r_3137,
           GibCursor loc_3134, GibCursor b_290_822_1024_1642,
           GibFloat f_291_823_1025_1643, GibCursor fs_292_824_1026_1644);
GibCursorGibCursorGibCursorGibCursorProd caseFn_825(GibCursor end_r_3140,
                                                    GibCursor end_r_3141,
                                                    GibCursor loc_3139,
                                                    GibInt n_297_826_1029_1656,
                                                    GibCursor fs_298_827_1030_1657);
GibCursorGibCursorGibCursorGibCursorProd caseFn_828(GibCursor end_r_3144,
                                                    GibCursor end_r_3145,
                                                    GibCursor loc_3143,
                                                    GibInt n_301_829_1033_1662,
                                                    GibCursor b_303_830_1034_1663);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
caseFn_831(GibCursor end_r_3149, GibCursor end_r_3150, GibCursor end_r_3151,
           GibCursor loc_3148, GibInt n_301_832_1037_1668,
           GibCursor b_303_833_1038_1669, GibFloat f_306_834_1039_1670,
           GibCursor fs_307_835_1040_1671);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
caseFn_836(GibCursor end_r_3155, GibCursor end_r_3156, GibCursor end_r_3157,
           GibCursor loc_3154, GibInt n_301_837_1044_1683,
           GibCursor a_302_838_1045_1684, GibCursor b_303_839_1046_1685);
static inline
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
caseFn_840(GibCursor end_r_3161, GibCursor end_r_3162, GibCursor end_r_3163,
           GibCursor loc_3160, GibCursor b_312_841_1049_1688,
           GibFloat f_313_842_1050_1689, GibCursor fs_314_843_1051_1690);
static inline
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
caseFn_844(GibCursor end_r_3168, GibCursor end_r_3169, GibCursor end_r_3170,
           GibCursor end_r_3171, GibCursor loc_3167,
           GibCursor a_317_845_1054_1701, GibCursor b_318_846_1055_1702,
           GibFloat f_319_847_1056_1703, GibCursor fs_320_848_1057_1704);
typedef enum {
            GibInt_T,
            GibFloat_T,
            GibSym_T,
            GibBool_T,
            GibVector_T,
            GibList_T,
            GibCursor_T,
            PList1_T,
            Ps_T,
        } GibDatatype;
void info_table_initialize(void)
{
    int error = gib_info_table_initialize(9);

    if (error < 0) {
        fprintf(stderr, "Couldn't initialize info table, errorno=%d", error);
        exit(1);
    }

    GibDatatype field_tys[2];

    field_tys[0] = PList1_T;
    error = gib_info_table_insert_packed_dcon(PList1_T, 1, 4, 0, 1, 1,
                                              field_tys, 1);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, PList1_T, 1);
        exit(1);
    }
    error = gib_info_table_insert_packed_dcon(PList1_T, 2, 0, 0, 0, 0,
                                              field_tys, 0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, PList1_T, 2);
        exit(1);
    }
    error = gib_info_table_insert_packed_dcon(PList1_T, 0, 0, 0, 0, 0,
                                              field_tys, 0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, PList1_T, 0);
        exit(1);
    }
    error = gib_info_table_insert_packed_dcon(Ps_T, 2, 0, 0, 0, 0, field_tys,
                                              0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, Ps_T, 2);
        exit(1);
    }
    field_tys[0] = Ps_T;
    error = gib_info_table_insert_packed_dcon(Ps_T, 1, 4, 0, 1, 1, field_tys,
                                              1);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, Ps_T, 1);
        exit(1);
    }
    error = gib_info_table_insert_packed_dcon(Ps_T, 0, 0, 0, 0, 0, field_tys,
                                              0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, Ps_T, 0);
        exit(1);
    }
    gib_info_table_finalize();
}
void symbol_table_initialize(void)
{
    gib_add_symbol(9420,
                   "benchrunner: select benchmark to run with --bench-prog\n");
    gib_add_symbol(9421, "OK\n");
    gib_add_symbol(9422, "Err\n");
    gib_add_symbol(9423, ")");
    gib_add_symbol(9424, "(Pz");
    gib_add_symbol(9425, "(OpP");
    gib_add_symbol(9426, "(Nil1");
    gib_add_symbol(9427, "(ErrorL");
    gib_add_symbol(9428, "(Error");
    gib_add_symbol(9429, "(Cons1");
    gib_add_symbol(9430, " ->r ");
    gib_add_symbol(9431, " ->i ");
    gib_add_symbol(9432, " ");
    gib_add_symbol(9433, "\n");
}
unsigned char bench_psc()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibChunk region_9434 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_3183 = region_9434.start;
    GibCursor end_r_3183 = region_9434.end;
    GibCursor pvrtmp_9444;
    GibCursor pvrtmp_9445;
    GibCursor pvrtmp_9446;
    GibVector *times_4 = gib_vector_alloc(gib_get_iters_param(),
                                          sizeof(double));
    struct timespec begin_pvrtmp_9444;
    struct timespec end_pvrtmp_9444;

    GibGcStateSnapshot *snapshot = gib_gc_init_state(1);

    for (long long iters_pvrtmp_9444 = 0; iters_pvrtmp_9444 <
         gib_get_iters_param(); iters_pvrtmp_9444++) {
        if (iters_pvrtmp_9444 != gib_get_iters_param() - 1) {
            gib_gc_save_state(snapshot, 1, region_9434.end);
            gib_list_bumpalloc_save_state();
            gib_ptr_bumpalloc_save_state();
        }
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_9444);

        GibCursorGibCursorGibCursorProd tmp_struct_0 =
                                         psC(end_r_3183, r_3183, 5);
        GibCursor pvrtmp_9435 = tmp_struct_0.field0;
        GibCursor pvrtmp_9436 = tmp_struct_0.field1;
        GibCursor pvrtmp_9437 = tmp_struct_0.field2;

        pvrtmp_9444 = pvrtmp_9435;
        pvrtmp_9445 = pvrtmp_9436;
        pvrtmp_9446 = pvrtmp_9437;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_9444);
        if (iters_pvrtmp_9444 != gib_get_iters_param() - 1) {
            gib_gc_restore_state(snapshot);
            gib_list_bumpalloc_restore_state();
            gib_ptr_bumpalloc_restore_state();
        }

        double itertime_1 = gib_difftimespecs(&begin_pvrtmp_9444,
                                              &end_pvrtmp_9444);

        printf("itertime: %lf\n", itertime_1);
        gib_vector_inplace_update(times_4, iters_pvrtmp_9444, &itertime_1);
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
    gib_shadowstack_push(rstack, pvrtmp_9445, end_r_3183, Stk, Ps_T);

    GibChunk region_9454 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_3182 = region_9454.start;
    GibCursor end_r_3182 = region_9454.end;

    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9445 = frame->ptr;
    end_r_3183 = frame->endptr;

    GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_6 =
                                                       toList(end_r_3183, end_r_3182, r_3182, pvrtmp_9445);
    GibCursor pvrtmp_9455 = tmp_struct_6.field0;
    GibCursor pvrtmp_9456 = tmp_struct_6.field1;
    GibCursor pvrtmp_9457 = tmp_struct_6.field2;
    GibCursor pvrtmp_9458 = tmp_struct_6.field3;
    GibCursor pvrtmp_9459 = tmp_struct_6.field4;
    GibCursorGibCursorGibIntProd tmp_struct_7 =  size(pvrtmp_9456, pvrtmp_9458);
    GibCursor pvrtmp_9464 = tmp_struct_7.field0;
    GibCursor pvrtmp_9465 = tmp_struct_7.field1;
    GibInt pvrtmp_9466 = tmp_struct_7.field2;
    GibBool fltAppE_1064_1286 = pvrtmp_9466 == 5;
    unsigned char tailapp_4314 =  print_check(fltAppE_1064_1286);

    return tailapp_4314;
}
unsigned char bench_psb()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibChunk region_9467 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_3195 = region_9467.start;
    GibCursor end_r_3195 = region_9467.end;
    GibCursor pvrtmp_9477;
    GibCursor pvrtmp_9478;
    GibCursor pvrtmp_9479;
    GibVector *times_12 = gib_vector_alloc(gib_get_iters_param(),
                                           sizeof(double));
    struct timespec begin_pvrtmp_9477;
    struct timespec end_pvrtmp_9477;

    GibGcStateSnapshot *snapshot = gib_gc_init_state(1);

    for (long long iters_pvrtmp_9477 = 0; iters_pvrtmp_9477 <
         gib_get_iters_param(); iters_pvrtmp_9477++) {
        if (iters_pvrtmp_9477 != gib_get_iters_param() - 1) {
            gib_gc_save_state(snapshot, 1, region_9467.end);
            gib_list_bumpalloc_save_state();
            gib_ptr_bumpalloc_save_state();
        }
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_9477);

        GibCursorGibCursorGibCursorProd tmp_struct_8 =
                                         psB(end_r_3195, r_3195, 90);
        GibCursor pvrtmp_9468 = tmp_struct_8.field0;
        GibCursor pvrtmp_9469 = tmp_struct_8.field1;
        GibCursor pvrtmp_9470 = tmp_struct_8.field2;

        pvrtmp_9477 = pvrtmp_9468;
        pvrtmp_9478 = pvrtmp_9469;
        pvrtmp_9479 = pvrtmp_9470;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_9477);
        if (iters_pvrtmp_9477 != gib_get_iters_param() - 1) {
            gib_gc_restore_state(snapshot);
            gib_list_bumpalloc_restore_state();
            gib_ptr_bumpalloc_restore_state();
        }

        double itertime_9 = gib_difftimespecs(&begin_pvrtmp_9477,
                                              &end_pvrtmp_9477);

        printf("itertime: %lf\n", itertime_9);
        gib_vector_inplace_update(times_12, iters_pvrtmp_9477, &itertime_9);
    }
    gib_vector_inplace_sort(times_12, gib_compare_doubles);

    double *tmp_13 = (double *) gib_vector_nth(times_12, gib_get_iters_param() /
                                               2);
    double selftimed_11 = *tmp_13;
    double batchtime_10 = gib_sum_timing_array(times_12);

    gib_print_timing_array(times_12);
    gib_vector_free(times_12);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_10);
    printf("SELFTIMED: %e\n", selftimed_11);
    gib_shadowstack_push(rstack, pvrtmp_9478, end_r_3195, Stk, Ps_T);

    GibChunk region_9487 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_3194 = region_9487.start;
    GibCursor end_r_3194 = region_9487.end;

    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9478 = frame->ptr;
    end_r_3195 = frame->endptr;

    GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_14 =
                                                       toList(end_r_3195, end_r_3194, r_3194, pvrtmp_9478);
    GibCursor pvrtmp_9488 = tmp_struct_14.field0;
    GibCursor pvrtmp_9489 = tmp_struct_14.field1;
    GibCursor pvrtmp_9490 = tmp_struct_14.field2;
    GibCursor pvrtmp_9491 = tmp_struct_14.field3;
    GibCursor pvrtmp_9492 = tmp_struct_14.field4;
    GibCursorGibCursorGibIntProd tmp_struct_15 =
                                  size(pvrtmp_9489, pvrtmp_9491);
    GibCursor pvrtmp_9497 = tmp_struct_15.field0;
    GibCursor pvrtmp_9498 = tmp_struct_15.field1;
    GibInt pvrtmp_9499 = tmp_struct_15.field2;
    GibBool fltAppE_1066_1290 = pvrtmp_9499 == 90;
    unsigned char tailapp_4318 =  print_check(fltAppE_1066_1290);

    return tailapp_4318;
}
unsigned char bench_ts()
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibChunk region_9500 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_3207 = region_9500.start;
    GibCursor end_r_3207 = region_9500.end;
    GibCursor pvrtmp_9510;
    GibCursor pvrtmp_9511;
    GibCursor pvrtmp_9512;
    GibVector *times_20 = gib_vector_alloc(gib_get_iters_param(),
                                           sizeof(double));
    struct timespec begin_pvrtmp_9510;
    struct timespec end_pvrtmp_9510;

    GibGcStateSnapshot *snapshot = gib_gc_init_state(1);

    for (long long iters_pvrtmp_9510 = 0; iters_pvrtmp_9510 <
         gib_get_iters_param(); iters_pvrtmp_9510++) {
        if (iters_pvrtmp_9510 != gib_get_iters_param() - 1) {
            gib_gc_save_state(snapshot, 1, region_9500.end);
            gib_list_bumpalloc_save_state();
            gib_ptr_bumpalloc_save_state();
        }
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_9510);

        GibCursorGibCursorGibCursorProd tmp_struct_16 =
                                         ts(end_r_3207, r_3207, 20);
        GibCursor pvrtmp_9501 = tmp_struct_16.field0;
        GibCursor pvrtmp_9502 = tmp_struct_16.field1;
        GibCursor pvrtmp_9503 = tmp_struct_16.field2;

        pvrtmp_9510 = pvrtmp_9501;
        pvrtmp_9511 = pvrtmp_9502;
        pvrtmp_9512 = pvrtmp_9503;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_9510);
        if (iters_pvrtmp_9510 != gib_get_iters_param() - 1) {
            gib_gc_restore_state(snapshot);
            gib_list_bumpalloc_restore_state();
            gib_ptr_bumpalloc_restore_state();
        }

        double itertime_17 = gib_difftimespecs(&begin_pvrtmp_9510,
                                               &end_pvrtmp_9510);

        printf("itertime: %lf\n", itertime_17);
        gib_vector_inplace_update(times_20, iters_pvrtmp_9510, &itertime_17);
    }
    gib_vector_inplace_sort(times_20, gib_compare_doubles);

    double *tmp_21 = (double *) gib_vector_nth(times_20, gib_get_iters_param() /
                                               2);
    double selftimed_19 = *tmp_21;
    double batchtime_18 = gib_sum_timing_array(times_20);

    gib_print_timing_array(times_20);
    gib_vector_free(times_20);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_18);
    printf("SELFTIMED: %e\n", selftimed_19);
    gib_shadowstack_push(rstack, pvrtmp_9511, end_r_3207, Stk, Ps_T);

    GibChunk region_9520 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_3206 = region_9520.start;
    GibCursor end_r_3206 = region_9520.end;

    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9511 = frame->ptr;
    end_r_3207 = frame->endptr;

    GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_22 =
                                                       toList(end_r_3207, end_r_3206, r_3206, pvrtmp_9511);
    GibCursor pvrtmp_9521 = tmp_struct_22.field0;
    GibCursor pvrtmp_9522 = tmp_struct_22.field1;
    GibCursor pvrtmp_9523 = tmp_struct_22.field2;
    GibCursor pvrtmp_9524 = tmp_struct_22.field3;
    GibCursor pvrtmp_9525 = tmp_struct_22.field4;
    GibCursorGibCursorGibIntProd tmp_struct_23 =
                                  size(pvrtmp_9522, pvrtmp_9524);
    GibCursor pvrtmp_9530 = tmp_struct_23.field0;
    GibCursor pvrtmp_9531 = tmp_struct_23.field1;
    GibInt pvrtmp_9532 = tmp_struct_23.field2;
    GibBool fltAppE_1068_1294 = pvrtmp_9532 == 20;
    unsigned char tailapp_4322 =  print_check(fltAppE_1068_1294);

    return tailapp_4322;
}
GibCursorGibCursorGibCursorProd expx_ans(GibCursor end_r_2981,
                                         GibCursor loc_2980)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2980 + 18 > end_r_2981) {
        gib_grow_region(&loc_2980, &end_r_2981);
    }

    GibFloat fltPkd_1071_1295 = 1.0 / 2.0;
    GibFloat fltPkd_1073_1296 = 1.0 / 6.0;
    GibFloat fltPkd_1075_1297 = 1.0 / 24.0;
    GibFloat fltPkd_1077_1298 = 1.0 / 120.0;
    GibFloat fltPkd_1079_1299 = 1.0 / 720.0;
    GibFloat fltPkd_1081_1300 = 1.0 / 5040.0;
    GibFloat fltPkd_1083_1301 = 1.0 / 40320.0;
    GibCursor loc_3257 = loc_2980 + 5;
    GibCursor loc_3254 = loc_2980 + 10;
    GibCursor loc_3248 = loc_2980 + 15;
    GibCursor loc_3242 = loc_2980 + 20;
    GibCursor loc_3236 = loc_2980 + 25;
    GibCursor loc_3230 = loc_2980 + 30;
    GibCursor loc_3224 = loc_2980 + 35;
    GibCursor loc_3218 = loc_2980 + 40;
    GibCursor loc_3212 = loc_2980 + 45;

    *(GibPackedTag *) loc_2980 = 1;

    GibCursor writetag_6145 = loc_2980 + 1;
    GibCursor after_tag_6146 = loc_2980 + 1;

    *(GibFloat *) after_tag_6146 = 1.0;

    GibCursor writecur_6150 = after_tag_6146 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3212 = 0;

    GibCursor writetag_6066 = loc_3212 + 1;
    GibCursor after_tag_6067 = loc_3212 + 1;

    *(GibPackedTag *) loc_3218 = 1;

    GibCursor writetag_6073 = loc_3218 + 1;
    GibCursor after_tag_6074 = loc_3218 + 1;

    *(GibFloat *) after_tag_6074 = fltPkd_1083_1301;

    GibCursor writecur_6078 = after_tag_6074 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3224 = 1;

    GibCursor writetag_6082 = loc_3224 + 1;
    GibCursor after_tag_6083 = loc_3224 + 1;

    *(GibFloat *) after_tag_6083 = fltPkd_1081_1300;

    GibCursor writecur_6087 = after_tag_6083 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3230 = 1;

    GibCursor writetag_6091 = loc_3230 + 1;
    GibCursor after_tag_6092 = loc_3230 + 1;

    *(GibFloat *) after_tag_6092 = fltPkd_1079_1299;

    GibCursor writecur_6096 = after_tag_6092 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3236 = 1;

    GibCursor writetag_6100 = loc_3236 + 1;
    GibCursor after_tag_6101 = loc_3236 + 1;

    *(GibFloat *) after_tag_6101 = fltPkd_1077_1298;

    GibCursor writecur_6105 = after_tag_6101 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3242 = 1;

    GibCursor writetag_6109 = loc_3242 + 1;
    GibCursor after_tag_6110 = loc_3242 + 1;

    *(GibFloat *) after_tag_6110 = fltPkd_1075_1297;

    GibCursor writecur_6114 = after_tag_6110 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3248 = 1;

    GibCursor writetag_6118 = loc_3248 + 1;
    GibCursor after_tag_6119 = loc_3248 + 1;

    *(GibFloat *) after_tag_6119 = fltPkd_1073_1296;

    GibCursor writecur_6123 = after_tag_6119 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3254 = 1;

    GibCursor writetag_6127 = loc_3254 + 1;
    GibCursor after_tag_6128 = loc_3254 + 1;

    *(GibFloat *) after_tag_6128 = fltPkd_1071_1295;

    GibCursor writecur_6132 = after_tag_6128 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3257 = 1;

    GibCursor writetag_6136 = loc_3257 + 1;
    GibCursor after_tag_6137 = loc_3257 + 1;

    *(GibFloat *) after_tag_6137 = 1.0;

    GibCursor writecur_6141 = after_tag_6137 + sizeof(GibFloat);

    return (GibCursorGibCursorGibCursorProd) {end_r_2981, loc_2980,
                                              after_tag_6067};
}
GibCursorGibCursorGibCursorProd sinx_ans(GibCursor end_r_2983,
                                         GibCursor loc_2982)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2982 + 18 > end_r_2983) {
        gib_grow_region(&loc_2982, &end_r_2983);
    }

    GibFloat fltPrm_1089_1311 = 0.0 - 1.0;
    GibFloat fltPkd_1088_1312 = fltPrm_1089_1311 / 6.0;
    GibFloat fltPkd_1092_1313 = 1.0 / 120.0;
    GibFloat fltPrm_1096_1314 = 0.0 - 1.0;
    GibFloat fltPkd_1095_1315 = fltPrm_1096_1314 / 5040.0;
    GibFloat fltPkd_1099_1316 = 1.0 / 362880.0;
    GibCursor loc_3310 = loc_2982 + 5;
    GibCursor loc_3307 = loc_2982 + 10;
    GibCursor loc_3303 = loc_2982 + 15;
    GibCursor loc_3297 = loc_2982 + 20;
    GibCursor loc_3293 = loc_2982 + 25;
    GibCursor loc_3287 = loc_2982 + 30;
    GibCursor loc_3283 = loc_2982 + 35;
    GibCursor loc_3277 = loc_2982 + 40;
    GibCursor loc_3273 = loc_2982 + 45;
    GibCursor loc_3267 = loc_2982 + 50;
    GibCursor loc_3263 = loc_2982 + 55;

    *(GibPackedTag *) loc_2982 = 1;

    GibCursor writetag_6251 = loc_2982 + 1;
    GibCursor after_tag_6252 = loc_2982 + 1;

    *(GibFloat *) after_tag_6252 = 0.0;

    GibCursor writecur_6256 = after_tag_6252 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3263 = 0;

    GibCursor writetag_6154 = loc_3263 + 1;
    GibCursor after_tag_6155 = loc_3263 + 1;

    *(GibPackedTag *) loc_3267 = 1;

    GibCursor writetag_6161 = loc_3267 + 1;
    GibCursor after_tag_6162 = loc_3267 + 1;

    *(GibFloat *) after_tag_6162 = 0.0;

    GibCursor writecur_6166 = after_tag_6162 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3273 = 1;

    GibCursor writetag_6170 = loc_3273 + 1;
    GibCursor after_tag_6171 = loc_3273 + 1;

    *(GibFloat *) after_tag_6171 = fltPkd_1099_1316;

    GibCursor writecur_6175 = after_tag_6171 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3277 = 1;

    GibCursor writetag_6179 = loc_3277 + 1;
    GibCursor after_tag_6180 = loc_3277 + 1;

    *(GibFloat *) after_tag_6180 = 0.0;

    GibCursor writecur_6184 = after_tag_6180 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3283 = 1;

    GibCursor writetag_6188 = loc_3283 + 1;
    GibCursor after_tag_6189 = loc_3283 + 1;

    *(GibFloat *) after_tag_6189 = fltPkd_1095_1315;

    GibCursor writecur_6193 = after_tag_6189 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3287 = 1;

    GibCursor writetag_6197 = loc_3287 + 1;
    GibCursor after_tag_6198 = loc_3287 + 1;

    *(GibFloat *) after_tag_6198 = 0.0;

    GibCursor writecur_6202 = after_tag_6198 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3293 = 1;

    GibCursor writetag_6206 = loc_3293 + 1;
    GibCursor after_tag_6207 = loc_3293 + 1;

    *(GibFloat *) after_tag_6207 = fltPkd_1092_1313;

    GibCursor writecur_6211 = after_tag_6207 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3297 = 1;

    GibCursor writetag_6215 = loc_3297 + 1;
    GibCursor after_tag_6216 = loc_3297 + 1;

    *(GibFloat *) after_tag_6216 = 0.0;

    GibCursor writecur_6220 = after_tag_6216 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3303 = 1;

    GibCursor writetag_6224 = loc_3303 + 1;
    GibCursor after_tag_6225 = loc_3303 + 1;

    *(GibFloat *) after_tag_6225 = fltPkd_1088_1312;

    GibCursor writecur_6229 = after_tag_6225 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3307 = 1;

    GibCursor writetag_6233 = loc_3307 + 1;
    GibCursor after_tag_6234 = loc_3307 + 1;

    *(GibFloat *) after_tag_6234 = 0.0;

    GibCursor writecur_6238 = after_tag_6234 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3310 = 1;

    GibCursor writetag_6242 = loc_3310 + 1;
    GibCursor after_tag_6243 = loc_3310 + 1;

    *(GibFloat *) after_tag_6243 = 1.0;

    GibCursor writecur_6247 = after_tag_6243 + sizeof(GibFloat);

    return (GibCursorGibCursorGibCursorProd) {end_r_2983, loc_2982,
                                              after_tag_6155};
}
GibCursorGibCursorGibCursorProd cosx_ans(GibCursor end_r_2985,
                                         GibCursor loc_2984)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2984 + 18 > end_r_2985) {
        gib_grow_region(&loc_2984, &end_r_2985);
    }

    GibFloat fltPrm_1105_1328 = 0.0 - 1.0;
    GibFloat fltPkd_1104_1329 = fltPrm_1105_1328 / 2.0;
    GibFloat fltPkd_1108_1330 = 1.0 / 24.0;
    GibFloat fltPrm_1112_1331 = 0.0 - 1.0;
    GibFloat fltPkd_1111_1332 = fltPrm_1112_1331 / 720.0;
    GibFloat fltPkd_1115_1333 = 1.0 / 40320.0;
    GibCursor loc_3355 = loc_2984 + 5;
    GibCursor loc_3352 = loc_2984 + 10;
    GibCursor loc_3346 = loc_2984 + 15;
    GibCursor loc_3342 = loc_2984 + 20;
    GibCursor loc_3336 = loc_2984 + 25;
    GibCursor loc_3332 = loc_2984 + 30;
    GibCursor loc_3326 = loc_2984 + 35;
    GibCursor loc_3322 = loc_2984 + 40;
    GibCursor loc_3316 = loc_2984 + 45;

    *(GibPackedTag *) loc_2984 = 1;

    GibCursor writetag_6339 = loc_2984 + 1;
    GibCursor after_tag_6340 = loc_2984 + 1;

    *(GibFloat *) after_tag_6340 = 1.0;

    GibCursor writecur_6344 = after_tag_6340 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3316 = 0;

    GibCursor writetag_6260 = loc_3316 + 1;
    GibCursor after_tag_6261 = loc_3316 + 1;

    *(GibPackedTag *) loc_3322 = 1;

    GibCursor writetag_6267 = loc_3322 + 1;
    GibCursor after_tag_6268 = loc_3322 + 1;

    *(GibFloat *) after_tag_6268 = fltPkd_1115_1333;

    GibCursor writecur_6272 = after_tag_6268 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3326 = 1;

    GibCursor writetag_6276 = loc_3326 + 1;
    GibCursor after_tag_6277 = loc_3326 + 1;

    *(GibFloat *) after_tag_6277 = 0.0;

    GibCursor writecur_6281 = after_tag_6277 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3332 = 1;

    GibCursor writetag_6285 = loc_3332 + 1;
    GibCursor after_tag_6286 = loc_3332 + 1;

    *(GibFloat *) after_tag_6286 = fltPkd_1111_1332;

    GibCursor writecur_6290 = after_tag_6286 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3336 = 1;

    GibCursor writetag_6294 = loc_3336 + 1;
    GibCursor after_tag_6295 = loc_3336 + 1;

    *(GibFloat *) after_tag_6295 = 0.0;

    GibCursor writecur_6299 = after_tag_6295 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3342 = 1;

    GibCursor writetag_6303 = loc_3342 + 1;
    GibCursor after_tag_6304 = loc_3342 + 1;

    *(GibFloat *) after_tag_6304 = fltPkd_1108_1330;

    GibCursor writecur_6308 = after_tag_6304 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3346 = 1;

    GibCursor writetag_6312 = loc_3346 + 1;
    GibCursor after_tag_6313 = loc_3346 + 1;

    *(GibFloat *) after_tag_6313 = 0.0;

    GibCursor writecur_6317 = after_tag_6313 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3352 = 1;

    GibCursor writetag_6321 = loc_3352 + 1;
    GibCursor after_tag_6322 = loc_3352 + 1;

    *(GibFloat *) after_tag_6322 = fltPkd_1104_1329;

    GibCursor writecur_6326 = after_tag_6322 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3355 = 1;

    GibCursor writetag_6330 = loc_3355 + 1;
    GibCursor after_tag_6331 = loc_3355 + 1;

    *(GibFloat *) after_tag_6331 = 0.0;

    GibCursor writecur_6335 = after_tag_6331 + sizeof(GibFloat);

    return (GibCursorGibCursorGibCursorProd) {end_r_2985, loc_2984,
                                              after_tag_6261};
}
GibCursorGibCursorGibCursorProd ansb(GibCursor end_r_2987, GibCursor loc_2986)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2986 + 18 > end_r_2987) {
        gib_grow_region(&loc_2986, &end_r_2987);
    }

    GibCursor loc_3376 = loc_2986 + 5;
    GibCursor loc_3373 = loc_2986 + 10;
    GibCursor loc_3369 = loc_2986 + 15;
    GibCursor loc_3365 = loc_2986 + 20;
    GibCursor loc_3361 = loc_2986 + 25;

    *(GibPackedTag *) loc_2986 = 1;

    GibCursor writetag_6391 = loc_2986 + 1;
    GibCursor after_tag_6392 = loc_2986 + 1;

    *(GibFloat *) after_tag_6392 = 0.0;

    GibCursor writecur_6396 = after_tag_6392 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3361 = 0;

    GibCursor writetag_6348 = loc_3361 + 1;
    GibCursor after_tag_6349 = loc_3361 + 1;

    *(GibPackedTag *) loc_3365 = 1;

    GibCursor writetag_6355 = loc_3365 + 1;
    GibCursor after_tag_6356 = loc_3365 + 1;

    *(GibFloat *) after_tag_6356 = 0.0;

    GibCursor writecur_6360 = after_tag_6356 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3369 = 1;

    GibCursor writetag_6364 = loc_3369 + 1;
    GibCursor after_tag_6365 = loc_3369 + 1;

    *(GibFloat *) after_tag_6365 = 0.0;

    GibCursor writecur_6369 = after_tag_6365 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3373 = 1;

    GibCursor writetag_6373 = loc_3373 + 1;
    GibCursor after_tag_6374 = loc_3373 + 1;

    *(GibFloat *) after_tag_6374 = 0.0;

    GibCursor writecur_6378 = after_tag_6374 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3376 = 1;

    GibCursor writetag_6382 = loc_3376 + 1;
    GibCursor after_tag_6383 = loc_3376 + 1;

    *(GibFloat *) after_tag_6383 = 0.0;

    GibCursor writecur_6387 = after_tag_6383 + sizeof(GibFloat);

    return (GibCursorGibCursorGibCursorProd) {end_r_2987, loc_2986,
                                              after_tag_6349};
}
GibCursorGibCursorGibCursorProd ansc(GibCursor end_r_2989, GibCursor loc_2988)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2988 + 18 > end_r_2989) {
        gib_grow_region(&loc_2988, &end_r_2989);
    }

    GibCursor loc_3397 = loc_2988 + 5;
    GibCursor loc_3394 = loc_2988 + 10;
    GibCursor loc_3390 = loc_2988 + 15;
    GibCursor loc_3386 = loc_2988 + 20;
    GibCursor loc_3382 = loc_2988 + 25;

    *(GibPackedTag *) loc_2988 = 1;

    GibCursor writetag_6443 = loc_2988 + 1;
    GibCursor after_tag_6444 = loc_2988 + 1;

    *(GibFloat *) after_tag_6444 = 0.0;

    GibCursor writecur_6448 = after_tag_6444 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3382 = 0;

    GibCursor writetag_6400 = loc_3382 + 1;
    GibCursor after_tag_6401 = loc_3382 + 1;

    *(GibPackedTag *) loc_3386 = 1;

    GibCursor writetag_6407 = loc_3386 + 1;
    GibCursor after_tag_6408 = loc_3386 + 1;

    *(GibFloat *) after_tag_6408 = 0.0;

    GibCursor writecur_6412 = after_tag_6408 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3390 = 1;

    GibCursor writetag_6416 = loc_3390 + 1;
    GibCursor after_tag_6417 = loc_3390 + 1;

    *(GibFloat *) after_tag_6417 = 0.0;

    GibCursor writecur_6421 = after_tag_6417 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3394 = 1;

    GibCursor writetag_6425 = loc_3394 + 1;
    GibCursor after_tag_6426 = loc_3394 + 1;

    *(GibFloat *) after_tag_6426 = 0.0;

    GibCursor writecur_6430 = after_tag_6426 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3397 = 1;

    GibCursor writetag_6434 = loc_3397 + 1;
    GibCursor after_tag_6435 = loc_3397 + 1;

    *(GibFloat *) after_tag_6435 = 0.0;

    GibCursor writecur_6439 = after_tag_6435 + sizeof(GibFloat);

    return (GibCursorGibCursorGibCursorProd) {end_r_2989, loc_2988,
                                              after_tag_6401};
}
GibCursorGibCursorGibCursorProd ansd(GibCursor end_r_2991, GibCursor loc_2990)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2990 + 18 > end_r_2991) {
        gib_grow_region(&loc_2990, &end_r_2991);
    }

    GibCursor loc_3446 = loc_2990 + 5;
    GibCursor loc_3443 = loc_2990 + 10;
    GibCursor loc_3439 = loc_2990 + 15;
    GibCursor loc_3435 = loc_2990 + 20;
    GibCursor loc_3431 = loc_2990 + 25;
    GibCursor loc_3427 = loc_2990 + 30;
    GibCursor loc_3423 = loc_2990 + 35;
    GibCursor loc_3419 = loc_2990 + 40;
    GibCursor loc_3415 = loc_2990 + 45;
    GibCursor loc_3411 = loc_2990 + 50;
    GibCursor loc_3407 = loc_2990 + 55;
    GibCursor loc_3403 = loc_2990 + 60;

    *(GibPackedTag *) loc_2990 = 1;

    GibCursor writetag_6558 = loc_2990 + 1;
    GibCursor after_tag_6559 = loc_2990 + 1;

    *(GibFloat *) after_tag_6559 = 1.0;

    GibCursor writecur_6563 = after_tag_6559 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3403 = 0;

    GibCursor writetag_6452 = loc_3403 + 1;
    GibCursor after_tag_6453 = loc_3403 + 1;

    *(GibPackedTag *) loc_3407 = 1;

    GibCursor writetag_6459 = loc_3407 + 1;
    GibCursor after_tag_6460 = loc_3407 + 1;

    *(GibFloat *) after_tag_6460 = 58786.0;

    GibCursor writecur_6464 = after_tag_6460 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3411 = 1;

    GibCursor writetag_6468 = loc_3411 + 1;
    GibCursor after_tag_6469 = loc_3411 + 1;

    *(GibFloat *) after_tag_6469 = 16796.0;

    GibCursor writecur_6473 = after_tag_6469 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3415 = 1;

    GibCursor writetag_6477 = loc_3415 + 1;
    GibCursor after_tag_6478 = loc_3415 + 1;

    *(GibFloat *) after_tag_6478 = 4862.0;

    GibCursor writecur_6482 = after_tag_6478 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3419 = 1;

    GibCursor writetag_6486 = loc_3419 + 1;
    GibCursor after_tag_6487 = loc_3419 + 1;

    *(GibFloat *) after_tag_6487 = 1430.0;

    GibCursor writecur_6491 = after_tag_6487 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3423 = 1;

    GibCursor writetag_6495 = loc_3423 + 1;
    GibCursor after_tag_6496 = loc_3423 + 1;

    *(GibFloat *) after_tag_6496 = 429.0;

    GibCursor writecur_6500 = after_tag_6496 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3427 = 1;

    GibCursor writetag_6504 = loc_3427 + 1;
    GibCursor after_tag_6505 = loc_3427 + 1;

    *(GibFloat *) after_tag_6505 = 132.0;

    GibCursor writecur_6509 = after_tag_6505 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3431 = 1;

    GibCursor writetag_6513 = loc_3431 + 1;
    GibCursor after_tag_6514 = loc_3431 + 1;

    *(GibFloat *) after_tag_6514 = 42.0;

    GibCursor writecur_6518 = after_tag_6514 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3435 = 1;

    GibCursor writetag_6522 = loc_3435 + 1;
    GibCursor after_tag_6523 = loc_3435 + 1;

    *(GibFloat *) after_tag_6523 = 14.0;

    GibCursor writecur_6527 = after_tag_6523 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3439 = 1;

    GibCursor writetag_6531 = loc_3439 + 1;
    GibCursor after_tag_6532 = loc_3439 + 1;

    *(GibFloat *) after_tag_6532 = 5.0;

    GibCursor writecur_6536 = after_tag_6532 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3443 = 1;

    GibCursor writetag_6540 = loc_3443 + 1;
    GibCursor after_tag_6541 = loc_3443 + 1;

    *(GibFloat *) after_tag_6541 = 2.0;

    GibCursor writecur_6545 = after_tag_6541 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3446 = 1;

    GibCursor writetag_6549 = loc_3446 + 1;
    GibCursor after_tag_6550 = loc_3446 + 1;

    *(GibFloat *) after_tag_6550 = 1.0;

    GibCursor writecur_6554 = after_tag_6550 + sizeof(GibFloat);

    return (GibCursorGibCursorGibCursorProd) {end_r_2991, loc_2990,
                                              after_tag_6453};
}
GibCursorGibCursorGibCursorProd psB(GibCursor end_r_2993, GibCursor loc_2992,
                                    GibInt n_242_856_1365)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2992 + 18 > end_r_2993) {
        gib_grow_region(&loc_2992, &end_r_2993);
    }
    gib_shadowstack_push(wstack, loc_2992, end_r_2993, Stk, Ps_T);

    GibChunk region_9659 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_3494 = region_9659.start;
    GibCursor end_r_3494 = region_9659.end;

    frame = gib_shadowstack_pop(wstack);
    loc_2992 = frame->ptr;
    end_r_2993 = frame->endptr;
    gib_shadowstack_push(wstack, loc_2992, end_r_2993, Stk, Ps_T);

    GibCursorGibCursorGibCursorProd tmp_struct_42 =
                                     sinx(end_r_3494, r_3494, n_242_856_1365);
    GibCursor pvrtmp_9660 = tmp_struct_42.field0;
    GibCursor pvrtmp_9661 = tmp_struct_42.field1;
    GibCursor pvrtmp_9662 = tmp_struct_42.field2;

    frame = gib_shadowstack_pop(wstack);
    loc_2992 = frame->ptr;
    end_r_2993 = frame->endptr;
    gib_shadowstack_push(rstack, pvrtmp_9661, pvrtmp_9660, Stk, Ps_T);
    gib_shadowstack_push(wstack, loc_2992, end_r_2993, Stk, Ps_T);

    GibChunk region_9667 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_3493 = region_9667.start;
    GibCursor end_r_3493 = region_9667.end;

    frame = gib_shadowstack_pop(wstack);
    loc_2992 = frame->ptr;
    end_r_2993 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9661 = frame->ptr;
    pvrtmp_9660 = frame->endptr;

    GibCursorGibCursorGibCursorProd tmp_struct_43 =  pone(end_r_3493, r_3493);
    GibCursor pvrtmp_9668 = tmp_struct_43.field0;
    GibCursor pvrtmp_9669 = tmp_struct_43.field1;
    GibCursor pvrtmp_9670 = tmp_struct_43.field2;

    gib_shadowstack_push(rstack, pvrtmp_9661, pvrtmp_9660, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9669, pvrtmp_9668, Stk, Ps_T);
    gib_shadowstack_push(wstack, loc_2992, end_r_2993, Stk, Ps_T);

    GibChunk region_9675 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_3492 = region_9675.start;
    GibCursor end_r_3492 = region_9675.end;

    frame = gib_shadowstack_pop(wstack);
    loc_2992 = frame->ptr;
    end_r_2993 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9669 = frame->ptr;
    pvrtmp_9668 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9661 = frame->ptr;
    pvrtmp_9660 = frame->endptr;
    gib_shadowstack_push(rstack, pvrtmp_9661, pvrtmp_9660, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9669, pvrtmp_9668, Stk, Ps_T);
    gib_shadowstack_push(wstack, loc_2992, end_r_2993, Stk, Ps_T);

    GibCursorGibCursorGibCursorProd tmp_struct_44 =
                                     cosx(end_r_3492, r_3492, n_242_856_1365);
    GibCursor pvrtmp_9676 = tmp_struct_44.field0;
    GibCursor pvrtmp_9677 = tmp_struct_44.field1;
    GibCursor pvrtmp_9678 = tmp_struct_44.field2;

    frame = gib_shadowstack_pop(wstack);
    loc_2992 = frame->ptr;
    end_r_2993 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9669 = frame->ptr;
    pvrtmp_9668 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9661 = frame->ptr;
    pvrtmp_9660 = frame->endptr;
    gib_shadowstack_push(rstack, pvrtmp_9661, pvrtmp_9660, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9669, pvrtmp_9668, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9677, pvrtmp_9676, Stk, Ps_T);
    gib_shadowstack_push(wstack, loc_2992, end_r_2993, Stk, Ps_T);

    GibChunk region_9683 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_3491 = region_9683.start;
    GibCursor end_r_3491 = region_9683.end;

    frame = gib_shadowstack_pop(wstack);
    loc_2992 = frame->ptr;
    end_r_2993 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9677 = frame->ptr;
    pvrtmp_9676 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9669 = frame->ptr;
    pvrtmp_9668 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9661 = frame->ptr;
    pvrtmp_9660 = frame->endptr;
    gib_shadowstack_push(rstack, pvrtmp_9661, pvrtmp_9660, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9669, pvrtmp_9668, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9677, pvrtmp_9676, Stk, Ps_T);
    gib_shadowstack_push(wstack, loc_2992, end_r_2993, Stk, Ps_T);

    GibCursorGibCursorGibCursorProd tmp_struct_45 =
                                     cosx(end_r_3491, r_3491, n_242_856_1365);
    GibCursor pvrtmp_9684 = tmp_struct_45.field0;
    GibCursor pvrtmp_9685 = tmp_struct_45.field1;
    GibCursor pvrtmp_9686 = tmp_struct_45.field2;

    frame = gib_shadowstack_pop(wstack);
    loc_2992 = frame->ptr;
    end_r_2993 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9677 = frame->ptr;
    pvrtmp_9676 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9669 = frame->ptr;
    pvrtmp_9668 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9661 = frame->ptr;
    pvrtmp_9660 = frame->endptr;
    gib_shadowstack_push(rstack, pvrtmp_9661, pvrtmp_9660, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9669, pvrtmp_9668, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9677, pvrtmp_9676, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9685, pvrtmp_9684, Stk, Ps_T);
    gib_shadowstack_push(wstack, loc_2992, end_r_2993, Stk, Ps_T);

    GibChunk region_9691 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_3490 = region_9691.start;
    GibCursor end_r_3490 = region_9691.end;

    frame = gib_shadowstack_pop(wstack);
    loc_2992 = frame->ptr;
    end_r_2993 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9685 = frame->ptr;
    pvrtmp_9684 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9677 = frame->ptr;
    pvrtmp_9676 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9669 = frame->ptr;
    pvrtmp_9668 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9661 = frame->ptr;
    pvrtmp_9660 = frame->endptr;
    gib_shadowstack_push(rstack, pvrtmp_9661, pvrtmp_9660, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9669, pvrtmp_9668, Stk, Ps_T);
    gib_shadowstack_push(wstack, loc_2992, end_r_2993, Stk, Ps_T);

    GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_46 =
                                                       psMult(pvrtmp_9676, pvrtmp_9684, end_r_3490, r_3490, pvrtmp_9677, pvrtmp_9685);
    GibCursor pvrtmp_9692 = tmp_struct_46.field0;
    GibCursor pvrtmp_9693 = tmp_struct_46.field1;
    GibCursor pvrtmp_9694 = tmp_struct_46.field2;
    GibCursor pvrtmp_9695 = tmp_struct_46.field3;
    GibCursor pvrtmp_9696 = tmp_struct_46.field4;

    frame = gib_shadowstack_pop(wstack);
    loc_2992 = frame->ptr;
    end_r_2993 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9669 = frame->ptr;
    pvrtmp_9668 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9661 = frame->ptr;
    pvrtmp_9660 = frame->endptr;
    gib_shadowstack_push(rstack, pvrtmp_9661, pvrtmp_9660, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9669, pvrtmp_9668, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9695, pvrtmp_9694, Stk, Ps_T);
    gib_shadowstack_push(wstack, loc_2992, end_r_2993, Stk, Ps_T);

    GibChunk region_9701 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_3489 = region_9701.start;
    GibCursor end_r_3489 = region_9701.end;

    frame = gib_shadowstack_pop(wstack);
    loc_2992 = frame->ptr;
    end_r_2993 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9695 = frame->ptr;
    pvrtmp_9694 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9669 = frame->ptr;
    pvrtmp_9668 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9661 = frame->ptr;
    pvrtmp_9660 = frame->endptr;

    GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_47 =
                                                       psNeg(pvrtmp_9694, end_r_3489, r_3489, pvrtmp_9695);
    GibCursor pvrtmp_9702 = tmp_struct_47.field0;
    GibCursor pvrtmp_9703 = tmp_struct_47.field1;
    GibCursor pvrtmp_9704 = tmp_struct_47.field2;
    GibCursor pvrtmp_9705 = tmp_struct_47.field3;
    GibCursor pvrtmp_9706 = tmp_struct_47.field4;

    gib_shadowstack_push(rstack, pvrtmp_9661, pvrtmp_9660, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9669, pvrtmp_9668, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9705, pvrtmp_9703, Stk, Ps_T);
    gib_shadowstack_push(wstack, loc_2992, end_r_2993, Stk, Ps_T);

    GibChunk region_9711 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_3488 = region_9711.start;
    GibCursor end_r_3488 = region_9711.end;

    frame = gib_shadowstack_pop(wstack);
    loc_2992 = frame->ptr;
    end_r_2993 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9705 = frame->ptr;
    pvrtmp_9703 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9669 = frame->ptr;
    pvrtmp_9668 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9661 = frame->ptr;
    pvrtmp_9660 = frame->endptr;

    GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_48 =
                                                       psAdd(pvrtmp_9668, pvrtmp_9703, end_r_3488, r_3488, pvrtmp_9669, pvrtmp_9705);
    GibCursor pvrtmp_9712 = tmp_struct_48.field0;
    GibCursor pvrtmp_9713 = tmp_struct_48.field1;
    GibCursor pvrtmp_9714 = tmp_struct_48.field2;
    GibCursor pvrtmp_9715 = tmp_struct_48.field3;
    GibCursor pvrtmp_9716 = tmp_struct_48.field4;

    gib_shadowstack_push(rstack, pvrtmp_9661, pvrtmp_9660, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9715, pvrtmp_9714, Stk, Ps_T);
    gib_shadowstack_push(wstack, loc_2992, end_r_2993, Stk, Ps_T);

    GibChunk region_9721 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_3487 = region_9721.start;
    GibCursor end_r_3487 = region_9721.end;

    frame = gib_shadowstack_pop(wstack);
    loc_2992 = frame->ptr;
    end_r_2993 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9715 = frame->ptr;
    pvrtmp_9714 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9661 = frame->ptr;
    pvrtmp_9660 = frame->endptr;
    gib_shadowstack_push(rstack, pvrtmp_9661, pvrtmp_9660, Stk, Ps_T);
    gib_shadowstack_push(wstack, loc_2992, end_r_2993, Stk, Ps_T);

    GibCursorGibCursorGibCursorGibCursorProd tmp_struct_49 =
                                              psSqrt(pvrtmp_9714, end_r_3487, r_3487, n_242_856_1365, pvrtmp_9715);
    GibCursor pvrtmp_9722 = tmp_struct_49.field0;
    GibCursor pvrtmp_9723 = tmp_struct_49.field1;
    GibCursor pvrtmp_9724 = tmp_struct_49.field2;
    GibCursor pvrtmp_9725 = tmp_struct_49.field3;

    frame = gib_shadowstack_pop(wstack);
    loc_2992 = frame->ptr;
    end_r_2993 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9661 = frame->ptr;
    pvrtmp_9660 = frame->endptr;
    gib_shadowstack_push(rstack, pvrtmp_9661, pvrtmp_9660, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9724, pvrtmp_9723, Stk, Ps_T);
    gib_shadowstack_push(wstack, loc_2992, end_r_2993, Stk, Ps_T);

    GibChunk region_9730 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_3486 = region_9730.start;
    GibCursor end_r_3486 = region_9730.end;

    frame = gib_shadowstack_pop(wstack);
    loc_2992 = frame->ptr;
    end_r_2993 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9724 = frame->ptr;
    pvrtmp_9723 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9661 = frame->ptr;
    pvrtmp_9660 = frame->endptr;

    GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_50 =
                                                       psNeg(pvrtmp_9723, end_r_3486, r_3486, pvrtmp_9724);
    GibCursor pvrtmp_9731 = tmp_struct_50.field0;
    GibCursor pvrtmp_9732 = tmp_struct_50.field1;
    GibCursor pvrtmp_9733 = tmp_struct_50.field2;
    GibCursor pvrtmp_9734 = tmp_struct_50.field3;
    GibCursor pvrtmp_9735 = tmp_struct_50.field4;
    GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_51 =
                                                       psAdd(pvrtmp_9660, pvrtmp_9732, end_r_2993, loc_2992, pvrtmp_9661, pvrtmp_9734);
    GibCursor pvrtmp_9740 = tmp_struct_51.field0;
    GibCursor pvrtmp_9741 = tmp_struct_51.field1;
    GibCursor pvrtmp_9742 = tmp_struct_51.field2;
    GibCursor pvrtmp_9743 = tmp_struct_51.field3;
    GibCursor pvrtmp_9744 = tmp_struct_51.field4;

    return (GibCursorGibCursorGibCursorProd) {pvrtmp_9742, pvrtmp_9743,
                                              pvrtmp_9744};
}
GibCursorGibCursorGibCursorProd psC(GibCursor end_r_2995, GibCursor loc_2994,
                                    GibInt n_243_857_1375)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2994 + 18 > end_r_2995) {
        gib_grow_region(&loc_2994, &end_r_2995);
    }
    gib_shadowstack_push(wstack, loc_2994, end_r_2995, Stk, Ps_T);

    GibChunk region_9751 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_3561 = region_9751.start;
    GibCursor end_r_3561 = region_9751.end;

    frame = gib_shadowstack_pop(wstack);
    loc_2994 = frame->ptr;
    end_r_2995 = frame->endptr;
    gib_shadowstack_push(wstack, loc_2994, end_r_2995, Stk, Ps_T);

    GibCursorGibCursorGibCursorProd tmp_struct_55 =
                                     sinx(end_r_3561, r_3561, n_243_857_1375);
    GibCursor pvrtmp_9752 = tmp_struct_55.field0;
    GibCursor pvrtmp_9753 = tmp_struct_55.field1;
    GibCursor pvrtmp_9754 = tmp_struct_55.field2;

    frame = gib_shadowstack_pop(wstack);
    loc_2994 = frame->ptr;
    end_r_2995 = frame->endptr;
    gib_shadowstack_push(rstack, pvrtmp_9753, pvrtmp_9752, Stk, Ps_T);
    gib_shadowstack_push(wstack, loc_2994, end_r_2995, Stk, Ps_T);

    GibChunk region_9759 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_3560 = region_9759.start;
    GibCursor end_r_3560 = region_9759.end;

    frame = gib_shadowstack_pop(wstack);
    loc_2994 = frame->ptr;
    end_r_2995 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9753 = frame->ptr;
    pvrtmp_9752 = frame->endptr;
    gib_shadowstack_push(rstack, pvrtmp_9753, pvrtmp_9752, Stk, Ps_T);
    gib_shadowstack_push(wstack, loc_2994, end_r_2995, Stk, Ps_T);

    GibCursorGibCursorGibCursorProd tmp_struct_56 =
                                     cosx(end_r_3560, r_3560, n_243_857_1375);
    GibCursor pvrtmp_9760 = tmp_struct_56.field0;
    GibCursor pvrtmp_9761 = tmp_struct_56.field1;
    GibCursor pvrtmp_9762 = tmp_struct_56.field2;

    frame = gib_shadowstack_pop(wstack);
    loc_2994 = frame->ptr;
    end_r_2995 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9753 = frame->ptr;
    pvrtmp_9752 = frame->endptr;
    gib_shadowstack_push(rstack, pvrtmp_9753, pvrtmp_9752, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9761, pvrtmp_9760, Stk, Ps_T);
    gib_shadowstack_push(wstack, loc_2994, end_r_2995, Stk, Ps_T);

    GibChunk region_9767 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_3559 = region_9767.start;
    GibCursor end_r_3559 = region_9767.end;

    frame = gib_shadowstack_pop(wstack);
    loc_2994 = frame->ptr;
    end_r_2995 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9761 = frame->ptr;
    pvrtmp_9760 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9753 = frame->ptr;
    pvrtmp_9752 = frame->endptr;
    gib_shadowstack_push(wstack, loc_2994, end_r_2995, Stk, Ps_T);

    GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_57 =
                                                       psDiv(pvrtmp_9752, pvrtmp_9760, end_r_3559, r_3559, n_243_857_1375, pvrtmp_9753, pvrtmp_9761);
    GibCursor pvrtmp_9768 = tmp_struct_57.field0;
    GibCursor pvrtmp_9769 = tmp_struct_57.field1;
    GibCursor pvrtmp_9770 = tmp_struct_57.field2;
    GibCursor pvrtmp_9771 = tmp_struct_57.field3;
    GibCursor pvrtmp_9772 = tmp_struct_57.field4;

    frame = gib_shadowstack_pop(wstack);
    loc_2994 = frame->ptr;
    end_r_2995 = frame->endptr;
    gib_shadowstack_push(rstack, pvrtmp_9771, pvrtmp_9770, Stk, Ps_T);
    gib_shadowstack_push(wstack, loc_2994, end_r_2995, Stk, Ps_T);

    GibChunk region_9777 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_3558 = region_9777.start;
    GibCursor end_r_3558 = region_9777.end;

    frame = gib_shadowstack_pop(wstack);
    loc_2994 = frame->ptr;
    end_r_2995 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9771 = frame->ptr;
    pvrtmp_9770 = frame->endptr;

    GibCursorGibCursorGibCursorProd tmp_struct_58 =  pone(end_r_3558, r_3558);
    GibCursor pvrtmp_9778 = tmp_struct_58.field0;
    GibCursor pvrtmp_9779 = tmp_struct_58.field1;
    GibCursor pvrtmp_9780 = tmp_struct_58.field2;

    gib_shadowstack_push(rstack, pvrtmp_9771, pvrtmp_9770, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9779, pvrtmp_9778, Stk, Ps_T);
    gib_shadowstack_push(wstack, loc_2994, end_r_2995, Stk, Ps_T);

    GibChunk region_9785 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_3557 = region_9785.start;
    GibCursor end_r_3557 = region_9785.end;

    frame = gib_shadowstack_pop(wstack);
    loc_2994 = frame->ptr;
    end_r_2995 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9779 = frame->ptr;
    pvrtmp_9778 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9771 = frame->ptr;
    pvrtmp_9770 = frame->endptr;

    GibCursorGibCursorGibCursorProd tmp_struct_59 =  pone(end_r_3557, r_3557);
    GibCursor pvrtmp_9786 = tmp_struct_59.field0;
    GibCursor pvrtmp_9787 = tmp_struct_59.field1;
    GibCursor pvrtmp_9788 = tmp_struct_59.field2;

    gib_shadowstack_push(rstack, pvrtmp_9771, pvrtmp_9770, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9779, pvrtmp_9778, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9787, pvrtmp_9786, Stk, Ps_T);
    gib_shadowstack_push(wstack, loc_2994, end_r_2995, Stk, Ps_T);

    GibChunk region_9793 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_3556 = region_9793.start;
    GibCursor end_r_3556 = region_9793.end;

    frame = gib_shadowstack_pop(wstack);
    loc_2994 = frame->ptr;
    end_r_2995 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9787 = frame->ptr;
    pvrtmp_9786 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9779 = frame->ptr;
    pvrtmp_9778 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9771 = frame->ptr;
    pvrtmp_9770 = frame->endptr;

    GibCursorGibCursorGibCursorProd tmp_struct_60 =  psX(end_r_3556, r_3556);
    GibCursor pvrtmp_9794 = tmp_struct_60.field0;
    GibCursor pvrtmp_9795 = tmp_struct_60.field1;
    GibCursor pvrtmp_9796 = tmp_struct_60.field2;

    gib_shadowstack_push(rstack, pvrtmp_9771, pvrtmp_9770, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9779, pvrtmp_9778, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9787, pvrtmp_9786, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9795, pvrtmp_9794, Stk, Ps_T);
    gib_shadowstack_push(wstack, loc_2994, end_r_2995, Stk, Ps_T);

    GibChunk region_9801 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_3555 = region_9801.start;
    GibCursor end_r_3555 = region_9801.end;

    frame = gib_shadowstack_pop(wstack);
    loc_2994 = frame->ptr;
    end_r_2995 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9795 = frame->ptr;
    pvrtmp_9794 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9787 = frame->ptr;
    pvrtmp_9786 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9779 = frame->ptr;
    pvrtmp_9778 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9771 = frame->ptr;
    pvrtmp_9770 = frame->endptr;

    GibCursorGibCursorGibCursorProd tmp_struct_61 =  psX(end_r_3555, r_3555);
    GibCursor pvrtmp_9802 = tmp_struct_61.field0;
    GibCursor pvrtmp_9803 = tmp_struct_61.field1;
    GibCursor pvrtmp_9804 = tmp_struct_61.field2;

    gib_shadowstack_push(rstack, pvrtmp_9771, pvrtmp_9770, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9779, pvrtmp_9778, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9787, pvrtmp_9786, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9795, pvrtmp_9794, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9803, pvrtmp_9802, Stk, Ps_T);
    gib_shadowstack_push(wstack, loc_2994, end_r_2995, Stk, Ps_T);

    GibChunk region_9809 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_3554 = region_9809.start;
    GibCursor end_r_3554 = region_9809.end;

    frame = gib_shadowstack_pop(wstack);
    loc_2994 = frame->ptr;
    end_r_2995 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9803 = frame->ptr;
    pvrtmp_9802 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9795 = frame->ptr;
    pvrtmp_9794 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9787 = frame->ptr;
    pvrtmp_9786 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9779 = frame->ptr;
    pvrtmp_9778 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9771 = frame->ptr;
    pvrtmp_9770 = frame->endptr;
    gib_shadowstack_push(rstack, pvrtmp_9771, pvrtmp_9770, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9779, pvrtmp_9778, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9787, pvrtmp_9786, Stk, Ps_T);
    gib_shadowstack_push(wstack, loc_2994, end_r_2995, Stk, Ps_T);

    GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_62 =
                                                       psMult(pvrtmp_9794, pvrtmp_9802, end_r_3554, r_3554, pvrtmp_9795, pvrtmp_9803);
    GibCursor pvrtmp_9810 = tmp_struct_62.field0;
    GibCursor pvrtmp_9811 = tmp_struct_62.field1;
    GibCursor pvrtmp_9812 = tmp_struct_62.field2;
    GibCursor pvrtmp_9813 = tmp_struct_62.field3;
    GibCursor pvrtmp_9814 = tmp_struct_62.field4;

    frame = gib_shadowstack_pop(wstack);
    loc_2994 = frame->ptr;
    end_r_2995 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9787 = frame->ptr;
    pvrtmp_9786 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9779 = frame->ptr;
    pvrtmp_9778 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9771 = frame->ptr;
    pvrtmp_9770 = frame->endptr;
    gib_shadowstack_push(rstack, pvrtmp_9771, pvrtmp_9770, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9779, pvrtmp_9778, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9787, pvrtmp_9786, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9813, pvrtmp_9812, Stk, Ps_T);
    gib_shadowstack_push(wstack, loc_2994, end_r_2995, Stk, Ps_T);

    GibChunk region_9819 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_3553 = region_9819.start;
    GibCursor end_r_3553 = region_9819.end;

    frame = gib_shadowstack_pop(wstack);
    loc_2994 = frame->ptr;
    end_r_2995 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9813 = frame->ptr;
    pvrtmp_9812 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9787 = frame->ptr;
    pvrtmp_9786 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9779 = frame->ptr;
    pvrtmp_9778 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9771 = frame->ptr;
    pvrtmp_9770 = frame->endptr;

    GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_63 =
                                                       psAdd(pvrtmp_9786, pvrtmp_9812, end_r_3553, r_3553, pvrtmp_9787, pvrtmp_9813);
    GibCursor pvrtmp_9820 = tmp_struct_63.field0;
    GibCursor pvrtmp_9821 = tmp_struct_63.field1;
    GibCursor pvrtmp_9822 = tmp_struct_63.field2;
    GibCursor pvrtmp_9823 = tmp_struct_63.field3;
    GibCursor pvrtmp_9824 = tmp_struct_63.field4;

    gib_shadowstack_push(rstack, pvrtmp_9771, pvrtmp_9770, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9779, pvrtmp_9778, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9823, pvrtmp_9822, Stk, Ps_T);
    gib_shadowstack_push(wstack, loc_2994, end_r_2995, Stk, Ps_T);

    GibChunk region_9829 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_3552 = region_9829.start;
    GibCursor end_r_3552 = region_9829.end;

    frame = gib_shadowstack_pop(wstack);
    loc_2994 = frame->ptr;
    end_r_2995 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9823 = frame->ptr;
    pvrtmp_9822 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9779 = frame->ptr;
    pvrtmp_9778 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9771 = frame->ptr;
    pvrtmp_9770 = frame->endptr;
    gib_shadowstack_push(rstack, pvrtmp_9771, pvrtmp_9770, Stk, Ps_T);
    gib_shadowstack_push(wstack, loc_2994, end_r_2995, Stk, Ps_T);

    GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_64 =
                                                       psDiv(pvrtmp_9778, pvrtmp_9822, end_r_3552, r_3552, n_243_857_1375, pvrtmp_9779, pvrtmp_9823);
    GibCursor pvrtmp_9830 = tmp_struct_64.field0;
    GibCursor pvrtmp_9831 = tmp_struct_64.field1;
    GibCursor pvrtmp_9832 = tmp_struct_64.field2;
    GibCursor pvrtmp_9833 = tmp_struct_64.field3;
    GibCursor pvrtmp_9834 = tmp_struct_64.field4;

    frame = gib_shadowstack_pop(wstack);
    loc_2994 = frame->ptr;
    end_r_2995 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9771 = frame->ptr;
    pvrtmp_9770 = frame->endptr;
    gib_shadowstack_push(rstack, pvrtmp_9771, pvrtmp_9770, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9833, pvrtmp_9832, Stk, Ps_T);
    gib_shadowstack_push(wstack, loc_2994, end_r_2995, Stk, Ps_T);

    GibChunk region_9839 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_3551 = region_9839.start;
    GibCursor end_r_3551 = region_9839.end;

    frame = gib_shadowstack_pop(wstack);
    loc_2994 = frame->ptr;
    end_r_2995 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9833 = frame->ptr;
    pvrtmp_9832 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9771 = frame->ptr;
    pvrtmp_9770 = frame->endptr;

    GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_65 =
                                                       integral(pvrtmp_9832, end_r_3551, r_3551, pvrtmp_9833);
    GibCursor pvrtmp_9840 = tmp_struct_65.field0;
    GibCursor pvrtmp_9841 = tmp_struct_65.field1;
    GibCursor pvrtmp_9842 = tmp_struct_65.field2;
    GibCursor pvrtmp_9843 = tmp_struct_65.field3;
    GibCursor pvrtmp_9844 = tmp_struct_65.field4;

    gib_shadowstack_push(rstack, pvrtmp_9771, pvrtmp_9770, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9843, pvrtmp_9841, Stk, Ps_T);
    gib_shadowstack_push(wstack, loc_2994, end_r_2995, Stk, Ps_T);

    GibChunk region_9849 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_3550 = region_9849.start;
    GibCursor end_r_3550 = region_9849.end;

    frame = gib_shadowstack_pop(wstack);
    loc_2994 = frame->ptr;
    end_r_2995 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9843 = frame->ptr;
    pvrtmp_9841 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9771 = frame->ptr;
    pvrtmp_9770 = frame->endptr;
    gib_shadowstack_push(rstack, pvrtmp_9771, pvrtmp_9770, Stk, Ps_T);
    gib_shadowstack_push(wstack, loc_2994, end_r_2995, Stk, Ps_T);

    GibCursorGibCursorGibCursorGibCursorProd tmp_struct_66 =
                                              revert(pvrtmp_9841, end_r_3550, r_3550, n_243_857_1375, pvrtmp_9843);
    GibCursor pvrtmp_9850 = tmp_struct_66.field0;
    GibCursor pvrtmp_9851 = tmp_struct_66.field1;
    GibCursor pvrtmp_9852 = tmp_struct_66.field2;
    GibCursor pvrtmp_9853 = tmp_struct_66.field3;

    frame = gib_shadowstack_pop(wstack);
    loc_2994 = frame->ptr;
    end_r_2995 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9771 = frame->ptr;
    pvrtmp_9770 = frame->endptr;
    gib_shadowstack_push(rstack, pvrtmp_9771, pvrtmp_9770, Stk, Ps_T);
    gib_shadowstack_push(rstack, pvrtmp_9852, pvrtmp_9851, Stk, Ps_T);
    gib_shadowstack_push(wstack, loc_2994, end_r_2995, Stk, Ps_T);

    GibChunk region_9858 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_3549 = region_9858.start;
    GibCursor end_r_3549 = region_9858.end;

    frame = gib_shadowstack_pop(wstack);
    loc_2994 = frame->ptr;
    end_r_2995 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9852 = frame->ptr;
    pvrtmp_9851 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    pvrtmp_9771 = frame->ptr;
    pvrtmp_9770 = frame->endptr;

    GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_67 =
                                                       psNeg(pvrtmp_9851, end_r_3549, r_3549, pvrtmp_9852);
    GibCursor pvrtmp_9859 = tmp_struct_67.field0;
    GibCursor pvrtmp_9860 = tmp_struct_67.field1;
    GibCursor pvrtmp_9861 = tmp_struct_67.field2;
    GibCursor pvrtmp_9862 = tmp_struct_67.field3;
    GibCursor pvrtmp_9863 = tmp_struct_67.field4;
    GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_68 =
                                                       psAdd(pvrtmp_9770, pvrtmp_9860, end_r_2995, loc_2994, pvrtmp_9771, pvrtmp_9862);
    GibCursor pvrtmp_9868 = tmp_struct_68.field0;
    GibCursor pvrtmp_9869 = tmp_struct_68.field1;
    GibCursor pvrtmp_9870 = tmp_struct_68.field2;
    GibCursor pvrtmp_9871 = tmp_struct_68.field3;
    GibCursor pvrtmp_9872 = tmp_struct_68.field4;

    return (GibCursorGibCursorGibCursorProd) {pvrtmp_9870, pvrtmp_9871,
                                              pvrtmp_9872};
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd toList(GibCursor end_r_2998,
                                                         GibCursor end_r_2999,
                                                         GibCursor loc_2997,
                                                         GibCursor ps_244_858_1389)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_2997 + 18 > end_r_2999) {
        gib_grow_region(&loc_2997, &end_r_2999);
    }

    GibPackedTag tmpval_9879 = *(GibPackedTag *) ps_244_858_1389;
    GibCursor tmpcur_9880 = ps_244_858_1389 + 1;


  switch_9928:
    ;
    switch (tmpval_9879) {

      case 0:
        {
            GibCursor jump_4335 = ps_244_858_1389 + 1;

            *(GibPackedTag *) loc_2997 = 0;

            GibCursor writetag_6638 = loc_2997 + 1;
            GibCursor after_tag_6639 = loc_2997 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2998,
                                                                        end_r_2999,
                                                                        jump_4335,
                                                                        loc_2997,
                                                                        after_tag_6639};
            break;
        }

      case 1:
        {
            GibFloat tmpval_9885 = *(GibFloat *) tmpcur_9880;
            GibCursor tmpcur_9886 = tmpcur_9880 + sizeof(GibFloat);
            GibCursor loc_3571 = loc_2997 + 5;

            *(GibPackedTag *) loc_2997 = 1;

            GibCursor writetag_6650 = loc_2997 + 1;
            GibCursor after_tag_6651 = loc_2997 + 1;

            *(GibFloat *) after_tag_6651 = tmpval_9885;

            GibCursor writecur_6655 = after_tag_6651 + sizeof(GibFloat);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_72 =
                                                               toList(end_r_2998, end_r_2999, loc_3571, tmpcur_9886);
            GibCursor pvrtmp_9887 = tmp_struct_72.field0;
            GibCursor pvrtmp_9888 = tmp_struct_72.field1;
            GibCursor pvrtmp_9889 = tmp_struct_72.field2;
            GibCursor pvrtmp_9890 = tmp_struct_72.field3;
            GibCursor pvrtmp_9891 = tmp_struct_72.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_9887,
                                                                        pvrtmp_9888,
                                                                        pvrtmp_9889,
                                                                        loc_2997,
                                                                        pvrtmp_9891};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_74 = *(uintptr_t *) tmpcur_9880;
            GibCursor tmpcur_9900 = GIB_UNTAG(tagged_tmpcur_74);
            GibCursor tmpaftercur_9901 = tmpcur_9880 + 8;
            uint16_t tmptag_9902 = GIB_GET_TAG(tagged_tmpcur_74);
            GibCursor end_from_tagged_indr_4599 = tmpcur_9900 + tmptag_9902;
            GibCursor jump_4601 = tmpcur_9880 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_73 =
                                                               toList(end_from_tagged_indr_4599, end_r_2999, loc_2997, tmpcur_9900);
            GibCursor pvrtmp_9903 = tmp_struct_73.field0;
            GibCursor pvrtmp_9904 = tmp_struct_73.field1;
            GibCursor pvrtmp_9905 = tmp_struct_73.field2;
            GibCursor pvrtmp_9906 = tmp_struct_73.field3;
            GibCursor pvrtmp_9907 = tmp_struct_73.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_2998,
                                                                        pvrtmp_9904,
                                                                        jump_4601,
                                                                        pvrtmp_9906,
                                                                        pvrtmp_9907};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_76 = *(uintptr_t *) tmpcur_9880;
            GibCursor tmpcur_9914 = GIB_UNTAG(tagged_tmpcur_76);
            GibCursor tmpaftercur_9915 = tmpcur_9880 + 8;
            uint16_t tmptag_9916 = GIB_GET_TAG(tagged_tmpcur_76);
            GibCursor end_from_tagged_indr_4599 = tmpcur_9914 + tmptag_9916;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_75 =
                                                               toList(end_from_tagged_indr_4599, end_r_2999, loc_2997, tmpcur_9914);
            GibCursor pvrtmp_9917 = tmp_struct_75.field0;
            GibCursor pvrtmp_9918 = tmp_struct_75.field1;
            GibCursor pvrtmp_9919 = tmp_struct_75.field2;
            GibCursor pvrtmp_9920 = tmp_struct_75.field3;
            GibCursor pvrtmp_9921 = tmp_struct_75.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_9917,
                                                                        pvrtmp_9918,
                                                                        pvrtmp_9919,
                                                                        pvrtmp_9920,
                                                                        pvrtmp_9921};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_9879");
            exit(1);
        }
    }
}
GibCursorGibCursorGibBoolProd equal(GibCursor end_r_3002, GibCursor end_r_3003,
                                    GibCursor as_247_861_1393,
                                    GibCursor bs_248_862_1394)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_9929 = *(GibPackedTag *) as_247_861_1393;
    GibCursor tmpcur_9930 = as_247_861_1393 + 1;


  switch_9952:
    ;
    switch (tmpval_9929) {

      case 2:
        {
            GibCursorGibBoolProd tmp_struct_80 =
                                  caseFn_803(end_r_3003, bs_248_862_1394);
            GibCursor pvrtmp_9931 = tmp_struct_80.field0;
            GibBool pvrtmp_9932 = tmp_struct_80.field1;

            return (GibCursorGibCursorGibBoolProd) {end_r_3002, pvrtmp_9931,
                                                    pvrtmp_9932};
            break;
        }

      case 0:
        {
            GibCursorGibBoolProd tmp_struct_81 =
                                  caseFn_805(end_r_3003, bs_248_862_1394);
            GibCursor pvrtmp_9933 = tmp_struct_81.field0;
            GibBool pvrtmp_9934 = tmp_struct_81.field1;

            return (GibCursorGibCursorGibBoolProd) {end_r_3002, pvrtmp_9933,
                                                    pvrtmp_9934};
            break;
        }

      case 1:
        {
            GibFloat tmpval_9935 = *(GibFloat *) tmpcur_9930;
            GibCursor tmpcur_9936 = tmpcur_9930 + sizeof(GibFloat);
            GibCursorGibCursorGibBoolProd tmp_struct_82 =
                                           caseFn_807(end_r_3003, end_r_3002, bs_248_862_1394, tmpval_9935, tmpcur_9936);
            GibCursor pvrtmp_9937 = tmp_struct_82.field0;
            GibCursor pvrtmp_9938 = tmp_struct_82.field1;
            GibBool pvrtmp_9939 = tmp_struct_82.field2;

            return (GibCursorGibCursorGibBoolProd) {pvrtmp_9938, pvrtmp_9937,
                                                    pvrtmp_9939};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_84 = *(uintptr_t *) tmpcur_9930;
            GibCursor tmpcur_9940 = GIB_UNTAG(tagged_tmpcur_84);
            GibCursor tmpaftercur_9941 = tmpcur_9930 + 8;
            uint16_t tmptag_9942 = GIB_GET_TAG(tagged_tmpcur_84);
            GibCursor end_from_tagged_indr_4605 = tmpcur_9940 + tmptag_9942;
            GibCursor jump_4607 = tmpcur_9930 + 8;
            GibCursorGibCursorGibBoolProd tmp_struct_83 =
                                           equal(end_from_tagged_indr_4605, end_r_3003, tmpcur_9940, bs_248_862_1394);
            GibCursor pvrtmp_9943 = tmp_struct_83.field0;
            GibCursor pvrtmp_9944 = tmp_struct_83.field1;
            GibBool pvrtmp_9945 = tmp_struct_83.field2;

            return (GibCursorGibCursorGibBoolProd) {end_r_3002, pvrtmp_9944,
                                                    pvrtmp_9945};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_86 = *(uintptr_t *) tmpcur_9930;
            GibCursor tmpcur_9946 = GIB_UNTAG(tagged_tmpcur_86);
            GibCursor tmpaftercur_9947 = tmpcur_9930 + 8;
            uint16_t tmptag_9948 = GIB_GET_TAG(tagged_tmpcur_86);
            GibCursor end_from_tagged_indr_4605 = tmpcur_9946 + tmptag_9948;
            GibCursorGibCursorGibBoolProd tmp_struct_85 =
                                           equal(end_from_tagged_indr_4605, end_r_3003, tmpcur_9946, bs_248_862_1394);
            GibCursor pvrtmp_9949 = tmp_struct_85.field0;
            GibCursor pvrtmp_9950 = tmp_struct_85.field1;
            GibBool pvrtmp_9951 = tmp_struct_85.field2;

            return (GibCursorGibCursorGibBoolProd) {pvrtmp_9949, pvrtmp_9950,
                                                    pvrtmp_9951};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_9929");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorProd expx(GibCursor end_r_3005, GibCursor loc_3004,
                                     GibInt n_258_865_1397)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_3004 + 18 > end_r_3005) {
        gib_grow_region(&loc_3004, &end_r_3005);
    }

    GibBool fltIf_1162_1398 = n_258_865_1397 == 0;

    if (fltIf_1162_1398) {
        *(GibPackedTag *) loc_3004 = 0;

        GibCursor writetag_6690 = loc_3004 + 1;
        GibCursor after_tag_6691 = loc_3004 + 1;

        return (GibCursorGibCursorGibCursorProd) {end_r_3005, loc_3004,
                                                  after_tag_6691};
    } else {
        gib_shadowstack_push(wstack, loc_3004, end_r_3005, Stk, Ps_T);

        GibChunk region_9957 = gib_alloc_region(gib_get_inf_init_chunk_size());
        GibCursor r_3604 = region_9957.start;
        GibCursor end_r_3604 = region_9957.end;

        frame = gib_shadowstack_pop(wstack);
        loc_3004 = frame->ptr;
        end_r_3005 = frame->endptr;

        GibCursorGibCursorGibCursorProd tmp_struct_87 =
                                         pone(end_r_3604, r_3604);
        GibCursor pvrtmp_9958 = tmp_struct_87.field0;
        GibCursor pvrtmp_9959 = tmp_struct_87.field1;
        GibCursor pvrtmp_9960 = tmp_struct_87.field2;
        GibInt fltAppE_1166_1400 = n_258_865_1397 - 1;

        gib_shadowstack_push(rstack, pvrtmp_9959, pvrtmp_9958, Stk, Ps_T);
        gib_shadowstack_push(wstack, loc_3004, end_r_3005, Stk, Ps_T);

        GibChunk region_9965 = gib_alloc_region(gib_get_inf_init_chunk_size());
        GibCursor r_3603 = region_9965.start;
        GibCursor end_r_3603 = region_9965.end;

        frame = gib_shadowstack_pop(wstack);
        loc_3004 = frame->ptr;
        end_r_3005 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        pvrtmp_9959 = frame->ptr;
        pvrtmp_9958 = frame->endptr;
        gib_shadowstack_push(rstack, pvrtmp_9959, pvrtmp_9958, Stk, Ps_T);
        gib_shadowstack_push(wstack, loc_3004, end_r_3005, Stk, Ps_T);

        GibCursorGibCursorGibCursorProd tmp_struct_88 =
                                         expx(end_r_3603, r_3603, fltAppE_1166_1400);
        GibCursor pvrtmp_9966 = tmp_struct_88.field0;
        GibCursor pvrtmp_9967 = tmp_struct_88.field1;
        GibCursor pvrtmp_9968 = tmp_struct_88.field2;

        frame = gib_shadowstack_pop(wstack);
        loc_3004 = frame->ptr;
        end_r_3005 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        pvrtmp_9959 = frame->ptr;
        pvrtmp_9958 = frame->endptr;
        gib_shadowstack_push(rstack, pvrtmp_9959, pvrtmp_9958, Stk, Ps_T);
        gib_shadowstack_push(rstack, pvrtmp_9967, pvrtmp_9966, Stk, Ps_T);
        gib_shadowstack_push(wstack, loc_3004, end_r_3005, Stk, Ps_T);

        GibChunk region_9973 = gib_alloc_region(gib_get_inf_init_chunk_size());
        GibCursor r_3602 = region_9973.start;
        GibCursor end_r_3602 = region_9973.end;

        frame = gib_shadowstack_pop(wstack);
        loc_3004 = frame->ptr;
        end_r_3005 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        pvrtmp_9967 = frame->ptr;
        pvrtmp_9966 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        pvrtmp_9959 = frame->ptr;
        pvrtmp_9958 = frame->endptr;

        GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_89 =
                                                           integral(pvrtmp_9966, end_r_3602, r_3602, pvrtmp_9967);
        GibCursor pvrtmp_9974 = tmp_struct_89.field0;
        GibCursor pvrtmp_9975 = tmp_struct_89.field1;
        GibCursor pvrtmp_9976 = tmp_struct_89.field2;
        GibCursor pvrtmp_9977 = tmp_struct_89.field3;
        GibCursor pvrtmp_9978 = tmp_struct_89.field4;
        GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_90 =
                                                           psAdd(pvrtmp_9958, pvrtmp_9975, end_r_3005, loc_3004, pvrtmp_9959, pvrtmp_9977);
        GibCursor pvrtmp_9983 = tmp_struct_90.field0;
        GibCursor pvrtmp_9984 = tmp_struct_90.field1;
        GibCursor pvrtmp_9985 = tmp_struct_90.field2;
        GibCursor pvrtmp_9986 = tmp_struct_90.field3;
        GibCursor pvrtmp_9987 = tmp_struct_90.field4;

        return (GibCursorGibCursorGibCursorProd) {pvrtmp_9985, pvrtmp_9986,
                                                  pvrtmp_9987};
    }
}
GibCursorGibCursorGibCursorProd sinx(GibCursor end_r_3007, GibCursor loc_3006,
                                     GibInt n_259_866_1403)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_3006 + 18 > end_r_3007) {
        gib_grow_region(&loc_3006, &end_r_3007);
    }

    GibBool fltIf_1167_1404 = n_259_866_1403 == 0;

    if (fltIf_1167_1404) {
        *(GibPackedTag *) loc_3006 = 0;

        GibCursor writetag_6708 = loc_3006 + 1;
        GibCursor after_tag_6709 = loc_3006 + 1;

        return (GibCursorGibCursorGibCursorProd) {end_r_3007, loc_3006,
                                                  after_tag_6709};
    } else {
        GibInt fltAppE_1169_1405 = n_259_866_1403 - 1;

        gib_shadowstack_push(wstack, loc_3006, end_r_3007, Stk, Ps_T);

        GibChunk region_9998 = gib_alloc_region(gib_get_inf_init_chunk_size());
        GibCursor r_3612 = region_9998.start;
        GibCursor end_r_3612 = region_9998.end;

        frame = gib_shadowstack_pop(wstack);
        loc_3006 = frame->ptr;
        end_r_3007 = frame->endptr;
        gib_shadowstack_push(wstack, loc_3006, end_r_3007, Stk, Ps_T);

        GibCursorGibCursorGibCursorProd tmp_struct_94 =
                                         cosx(end_r_3612, r_3612, fltAppE_1169_1405);
        GibCursor pvrtmp_9999 = tmp_struct_94.field0;
        GibCursor pvrtmp_10000 = tmp_struct_94.field1;
        GibCursor pvrtmp_10001 = tmp_struct_94.field2;

        frame = gib_shadowstack_pop(wstack);
        loc_3006 = frame->ptr;
        end_r_3007 = frame->endptr;

        GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_95 =
                                                           integral(pvrtmp_9999, end_r_3007, loc_3006, pvrtmp_10000);
        GibCursor pvrtmp_10006 = tmp_struct_95.field0;
        GibCursor pvrtmp_10007 = tmp_struct_95.field1;
        GibCursor pvrtmp_10008 = tmp_struct_95.field2;
        GibCursor pvrtmp_10009 = tmp_struct_95.field3;
        GibCursor pvrtmp_10010 = tmp_struct_95.field4;

        return (GibCursorGibCursorGibCursorProd) {pvrtmp_10007, pvrtmp_10009,
                                                  pvrtmp_10010};
    }
}
GibCursorGibCursorGibCursorProd cosx(GibCursor end_r_3009, GibCursor loc_3008,
                                     GibInt n_260_867_1407)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_3008 + 18 > end_r_3009) {
        gib_grow_region(&loc_3008, &end_r_3009);
    }

    GibBool fltIf_1170_1408 = n_260_867_1407 == 0;

    if (fltIf_1170_1408) {
        *(GibPackedTag *) loc_3008 = 0;

        GibCursor writetag_6720 = loc_3008 + 1;
        GibCursor after_tag_6721 = loc_3008 + 1;

        return (GibCursorGibCursorGibCursorProd) {end_r_3009, loc_3008,
                                                  after_tag_6721};
    } else {
        gib_shadowstack_push(wstack, loc_3008, end_r_3009, Stk, Ps_T);

        GibChunk region_10021 = gib_alloc_region(gib_get_inf_init_chunk_size());
        GibCursor r_3635 = region_10021.start;
        GibCursor end_r_3635 = region_10021.end;

        frame = gib_shadowstack_pop(wstack);
        loc_3008 = frame->ptr;
        end_r_3009 = frame->endptr;

        GibCursorGibCursorGibCursorProd tmp_struct_99 =
                                         pone(end_r_3635, r_3635);
        GibCursor pvrtmp_10022 = tmp_struct_99.field0;
        GibCursor pvrtmp_10023 = tmp_struct_99.field1;
        GibCursor pvrtmp_10024 = tmp_struct_99.field2;
        GibInt fltAppE_1175_1410 = n_260_867_1407 - 1;

        gib_shadowstack_push(rstack, pvrtmp_10023, pvrtmp_10022, Stk, Ps_T);
        gib_shadowstack_push(wstack, loc_3008, end_r_3009, Stk, Ps_T);

        GibChunk region_10029 = gib_alloc_region(gib_get_inf_init_chunk_size());
        GibCursor r_3634 = region_10029.start;
        GibCursor end_r_3634 = region_10029.end;

        frame = gib_shadowstack_pop(wstack);
        loc_3008 = frame->ptr;
        end_r_3009 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        pvrtmp_10023 = frame->ptr;
        pvrtmp_10022 = frame->endptr;
        gib_shadowstack_push(rstack, pvrtmp_10023, pvrtmp_10022, Stk, Ps_T);
        gib_shadowstack_push(wstack, loc_3008, end_r_3009, Stk, Ps_T);

        GibCursorGibCursorGibCursorProd tmp_struct_100 =
                                         sinx(end_r_3634, r_3634, fltAppE_1175_1410);
        GibCursor pvrtmp_10030 = tmp_struct_100.field0;
        GibCursor pvrtmp_10031 = tmp_struct_100.field1;
        GibCursor pvrtmp_10032 = tmp_struct_100.field2;

        frame = gib_shadowstack_pop(wstack);
        loc_3008 = frame->ptr;
        end_r_3009 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        pvrtmp_10023 = frame->ptr;
        pvrtmp_10022 = frame->endptr;
        gib_shadowstack_push(rstack, pvrtmp_10023, pvrtmp_10022, Stk, Ps_T);
        gib_shadowstack_push(rstack, pvrtmp_10031, pvrtmp_10030, Stk, Ps_T);
        gib_shadowstack_push(wstack, loc_3008, end_r_3009, Stk, Ps_T);

        GibChunk region_10037 = gib_alloc_region(gib_get_inf_init_chunk_size());
        GibCursor r_3633 = region_10037.start;
        GibCursor end_r_3633 = region_10037.end;

        frame = gib_shadowstack_pop(wstack);
        loc_3008 = frame->ptr;
        end_r_3009 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        pvrtmp_10031 = frame->ptr;
        pvrtmp_10030 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        pvrtmp_10023 = frame->ptr;
        pvrtmp_10022 = frame->endptr;

        GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_101 =
                                                           integral(pvrtmp_10030, end_r_3633, r_3633, pvrtmp_10031);
        GibCursor pvrtmp_10038 = tmp_struct_101.field0;
        GibCursor pvrtmp_10039 = tmp_struct_101.field1;
        GibCursor pvrtmp_10040 = tmp_struct_101.field2;
        GibCursor pvrtmp_10041 = tmp_struct_101.field3;
        GibCursor pvrtmp_10042 = tmp_struct_101.field4;

        gib_shadowstack_push(rstack, pvrtmp_10023, pvrtmp_10022, Stk, Ps_T);
        gib_shadowstack_push(rstack, pvrtmp_10041, pvrtmp_10039, Stk, Ps_T);
        gib_shadowstack_push(wstack, loc_3008, end_r_3009, Stk, Ps_T);

        GibChunk region_10047 = gib_alloc_region(gib_get_inf_init_chunk_size());
        GibCursor r_3632 = region_10047.start;
        GibCursor end_r_3632 = region_10047.end;

        frame = gib_shadowstack_pop(wstack);
        loc_3008 = frame->ptr;
        end_r_3009 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        pvrtmp_10041 = frame->ptr;
        pvrtmp_10039 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        pvrtmp_10023 = frame->ptr;
        pvrtmp_10022 = frame->endptr;

        GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_102 =
                                                           psNeg(pvrtmp_10039, end_r_3632, r_3632, pvrtmp_10041);
        GibCursor pvrtmp_10048 = tmp_struct_102.field0;
        GibCursor pvrtmp_10049 = tmp_struct_102.field1;
        GibCursor pvrtmp_10050 = tmp_struct_102.field2;
        GibCursor pvrtmp_10051 = tmp_struct_102.field3;
        GibCursor pvrtmp_10052 = tmp_struct_102.field4;
        GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_103 =
                                                           psAdd(pvrtmp_10022, pvrtmp_10049, end_r_3009, loc_3008, pvrtmp_10023, pvrtmp_10051);
        GibCursor pvrtmp_10057 = tmp_struct_103.field0;
        GibCursor pvrtmp_10058 = tmp_struct_103.field1;
        GibCursor pvrtmp_10059 = tmp_struct_103.field2;
        GibCursor pvrtmp_10060 = tmp_struct_103.field3;
        GibCursor pvrtmp_10061 = tmp_struct_103.field4;

        return (GibCursorGibCursorGibCursorProd) {pvrtmp_10059, pvrtmp_10060,
                                                  pvrtmp_10061};
    }
}
GibCursorGibCursorGibCursorGibCursorProd psSqrt(GibCursor end_r_3012,
                                                GibCursor end_r_3013,
                                                GibCursor loc_3011,
                                                GibInt n_261_868_1414,
                                                GibCursor a_262_869_1415)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_3011 + 18 > end_r_3013) {
        gib_grow_region(&loc_3011, &end_r_3013);
    }

    GibPackedTag tmpval_10068 = *(GibPackedTag *) a_262_869_1415;
    GibCursor tmpcur_10069 = a_262_869_1415 + 1;


  switch_10126:
    ;
    switch (tmpval_10068) {

      case 0:
        {
            *(GibPackedTag *) loc_3011 = 0;

            GibCursor writetag_6742 = loc_3011 + 1;
            GibCursor after_tag_6743 = loc_3011 + 1;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_3012,
                                                               end_r_3013,
                                                               loc_3011,
                                                               after_tag_6743};
            break;
        }

      case 1:
        {
            GibFloat tmpval_10074 = *(GibFloat *) tmpcur_10069;
            GibCursor tmpcur_10075 = tmpcur_10069 + sizeof(GibFloat);
            GibBool fltIf_1176_1418 = tmpval_10074 == 1.0;

            if (fltIf_1176_1418) {
                GibCursorGibCursorGibCursorGibCursorProd tmp_struct_107 =
                                                          getQs(end_r_3012, end_r_3013, loc_3011, n_261_868_1414, tmpcur_10075);
                GibCursor pvrtmp_10076 = tmp_struct_107.field0;
                GibCursor pvrtmp_10077 = tmp_struct_107.field1;
                GibCursor pvrtmp_10078 = tmp_struct_107.field2;
                GibCursor pvrtmp_10079 = tmp_struct_107.field3;

                return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_10076,
                                                                   pvrtmp_10077,
                                                                   pvrtmp_10078,
                                                                   pvrtmp_10079};
            } else {
                GibCursorGibCursorGibCursorGibCursorProd tmp_struct_108 =
                                                          caseFn_811(end_r_3012, end_r_3013, loc_3011, n_261_868_1414, tmpcur_10075);
                GibCursor pvrtmp_10086 = tmp_struct_108.field0;
                GibCursor pvrtmp_10087 = tmp_struct_108.field1;
                GibCursor pvrtmp_10088 = tmp_struct_108.field2;
                GibCursor pvrtmp_10089 = tmp_struct_108.field3;

                return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_10086,
                                                                   pvrtmp_10087,
                                                                   pvrtmp_10088,
                                                                   pvrtmp_10089};
            }
            break;
        }

      case 2:
        {
            *(GibPackedTag *) loc_3011 = 2;

            GibCursor writetag_6758 = loc_3011 + 1;
            GibCursor after_tag_6759 = loc_3011 + 1;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_3012,
                                                               end_r_3013,
                                                               loc_3011,
                                                               after_tag_6759};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_110 = *(uintptr_t *) tmpcur_10069;
            GibCursor tmpcur_10100 = GIB_UNTAG(tagged_tmpcur_110);
            GibCursor tmpaftercur_10101 = tmpcur_10069 + 8;
            uint16_t tmptag_10102 = GIB_GET_TAG(tagged_tmpcur_110);
            GibCursor end_from_tagged_indr_4610 = tmpcur_10100 + tmptag_10102;
            GibCursor jump_4612 = tmpcur_10069 + 8;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_109 =
                                                      psSqrt(end_from_tagged_indr_4610, end_r_3013, loc_3011, n_261_868_1414, tmpcur_10100);
            GibCursor pvrtmp_10103 = tmp_struct_109.field0;
            GibCursor pvrtmp_10104 = tmp_struct_109.field1;
            GibCursor pvrtmp_10105 = tmp_struct_109.field2;
            GibCursor pvrtmp_10106 = tmp_struct_109.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_3012,
                                                               pvrtmp_10104,
                                                               pvrtmp_10105,
                                                               pvrtmp_10106};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_112 = *(uintptr_t *) tmpcur_10069;
            GibCursor tmpcur_10113 = GIB_UNTAG(tagged_tmpcur_112);
            GibCursor tmpaftercur_10114 = tmpcur_10069 + 8;
            uint16_t tmptag_10115 = GIB_GET_TAG(tagged_tmpcur_112);
            GibCursor end_from_tagged_indr_4610 = tmpcur_10113 + tmptag_10115;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_111 =
                                                      psSqrt(end_from_tagged_indr_4610, end_r_3013, loc_3011, n_261_868_1414, tmpcur_10113);
            GibCursor pvrtmp_10116 = tmp_struct_111.field0;
            GibCursor pvrtmp_10117 = tmp_struct_111.field1;
            GibCursor pvrtmp_10118 = tmp_struct_111.field2;
            GibCursor pvrtmp_10119 = tmp_struct_111.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_10116,
                                                               pvrtmp_10117,
                                                               pvrtmp_10118,
                                                               pvrtmp_10119};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_10068");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd getQs(GibCursor end_r_3016,
                                               GibCursor end_r_3017,
                                               GibCursor loc_3015,
                                               GibInt n_267_872_1419,
                                               GibCursor fs_268_873_1420)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_3015 + 18 > end_r_3017) {
        gib_grow_region(&loc_3015, &end_r_3017);
    }

    GibBool fltIf_1177_1421 = n_267_872_1419 <= 0;

    if (fltIf_1177_1421) {
        *(GibPackedTag *) loc_3015 = 0;

        GibCursor writetag_6775 = loc_3015 + 1;
        GibCursor after_tag_6776 = loc_3015 + 1;

        return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_3016,
                                                           end_r_3017, loc_3015,
                                                           after_tag_6776};
    } else {
        gib_shadowstack_push(rstack, fs_268_873_1420, end_r_3016, Stk, Ps_T);
        gib_shadowstack_push(wstack, loc_3015, end_r_3017, Stk, Ps_T);

        GibChunk region_10131 = gib_alloc_region(gib_get_inf_init_chunk_size());
        GibCursor r_3692 = region_10131.start;
        GibCursor end_r_3692 = region_10131.end;

        frame = gib_shadowstack_pop(wstack);
        loc_3015 = frame->ptr;
        end_r_3017 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        fs_268_873_1420 = frame->ptr;
        end_r_3016 = frame->endptr;

        GibCursorGibCursorGibCursorProd tmp_struct_116 =
                                         pone(end_r_3692, r_3692);
        GibCursor pvrtmp_10132 = tmp_struct_116.field0;
        GibCursor pvrtmp_10133 = tmp_struct_116.field1;
        GibCursor pvrtmp_10134 = tmp_struct_116.field2;
        GibInt fltAppE_1181_1423 = n_267_872_1419 - 1;

        gib_shadowstack_push(rstack, pvrtmp_10133, pvrtmp_10132, Stk, Ps_T);
        gib_shadowstack_push(rstack, fs_268_873_1420, end_r_3016, Stk, Ps_T);
        gib_shadowstack_push(wstack, loc_3015, end_r_3017, Stk, Ps_T);

        GibChunk region_10139 = gib_alloc_region(gib_get_inf_init_chunk_size());
        GibCursor r_3691 = region_10139.start;
        GibCursor end_r_3691 = region_10139.end;

        frame = gib_shadowstack_pop(wstack);
        loc_3015 = frame->ptr;
        end_r_3017 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        fs_268_873_1420 = frame->ptr;
        end_r_3016 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        pvrtmp_10133 = frame->ptr;
        pvrtmp_10132 = frame->endptr;

        GibCursor loc_3654 = r_3691 + 5;

        *(GibPackedTag *) r_3691 = 1;

        GibCursor writetag_6787 = r_3691 + 1;
        GibCursor after_tag_6788 = r_3691 + 1;

        *(GibFloat *) after_tag_6788 = 1.0;

        GibCursor writecur_6792 = after_tag_6788 + sizeof(GibFloat);

        // if (loc_3654 + 18 > end_r_3691) {
        //     gib_grow_region(&loc_3654, &end_r_3691);
        // }
        gib_indirection_barrier(loc_3654, end_r_3691, fs_268_873_1420,
                                end_r_3016, Ps_T);

        GibCursor end_6785 = loc_3654 + 9;

        gib_shadowstack_push(rstack, pvrtmp_10133, pvrtmp_10132, Stk, Ps_T);
        gib_shadowstack_push(rstack, r_3691, end_r_3691, Stk, Ps_T);
        gib_shadowstack_push(rstack, fs_268_873_1420, end_r_3016, Stk, Ps_T);
        gib_shadowstack_push(wstack, loc_3015, end_r_3017, Stk, Ps_T);

        GibChunk region_10144 = gib_alloc_region(gib_get_inf_init_chunk_size());
        GibCursor r_3690 = region_10144.start;
        GibCursor end_r_3690 = region_10144.end;

        frame = gib_shadowstack_pop(wstack);
        loc_3015 = frame->ptr;
        end_r_3017 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        fs_268_873_1420 = frame->ptr;
        end_r_3016 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        r_3691 = frame->ptr;
        end_r_3691 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        pvrtmp_10133 = frame->ptr;
        pvrtmp_10132 = frame->endptr;

        GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_117 =
                                                           deriv(end_r_3691, end_r_3690, r_3690, r_3691);
        GibCursor pvrtmp_10145 = tmp_struct_117.field0;
        GibCursor pvrtmp_10146 = tmp_struct_117.field1;
        GibCursor pvrtmp_10147 = tmp_struct_117.field2;
        GibCursor pvrtmp_10148 = tmp_struct_117.field3;
        GibCursor pvrtmp_10149 = tmp_struct_117.field4;
        GibInt fltAppE_1186_1426 = n_267_872_1419 - 1;

        gib_shadowstack_push(rstack, pvrtmp_10133, pvrtmp_10132, Stk, Ps_T);
        gib_shadowstack_push(rstack, pvrtmp_10148, pvrtmp_10146, Stk, Ps_T);
        gib_shadowstack_push(rstack, fs_268_873_1420, end_r_3016, Stk, Ps_T);
        gib_shadowstack_push(wstack, loc_3015, end_r_3017, Stk, Ps_T);

        GibChunk region_10154 = gib_alloc_region(gib_get_inf_init_chunk_size());
        GibCursor r_3689 = region_10154.start;
        GibCursor end_r_3689 = region_10154.end;

        frame = gib_shadowstack_pop(wstack);
        loc_3015 = frame->ptr;
        end_r_3017 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        fs_268_873_1420 = frame->ptr;
        end_r_3016 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        pvrtmp_10148 = frame->ptr;
        pvrtmp_10146 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        pvrtmp_10133 = frame->ptr;
        pvrtmp_10132 = frame->endptr;
        gib_shadowstack_push(rstack, pvrtmp_10133, pvrtmp_10132, Stk, Ps_T);
        gib_shadowstack_push(rstack, pvrtmp_10148, pvrtmp_10146, Stk, Ps_T);
        gib_shadowstack_push(wstack, loc_3015, end_r_3017, Stk, Ps_T);

        GibCursorGibCursorGibCursorGibCursorProd tmp_struct_118 =
                                                  getQs(end_r_3016, end_r_3689, r_3689, fltAppE_1186_1426, fs_268_873_1420);
        GibCursor pvrtmp_10155 = tmp_struct_118.field0;
        GibCursor pvrtmp_10156 = tmp_struct_118.field1;
        GibCursor pvrtmp_10157 = tmp_struct_118.field2;
        GibCursor pvrtmp_10158 = tmp_struct_118.field3;

        frame = gib_shadowstack_pop(wstack);
        loc_3015 = frame->ptr;
        end_r_3017 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        pvrtmp_10148 = frame->ptr;
        pvrtmp_10146 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        pvrtmp_10133 = frame->ptr;
        pvrtmp_10132 = frame->endptr;
        gib_shadowstack_push(rstack, pvrtmp_10133, pvrtmp_10132, Stk, Ps_T);
        gib_shadowstack_push(rstack, pvrtmp_10148, pvrtmp_10146, Stk, Ps_T);
        gib_shadowstack_push(rstack, pvrtmp_10157, pvrtmp_10156, Stk, Ps_T);
        gib_shadowstack_push(wstack, loc_3015, end_r_3017, Stk, Ps_T);

        GibChunk region_10163 = gib_alloc_region(gib_get_inf_init_chunk_size());
        GibCursor r_3688 = region_10163.start;
        GibCursor end_r_3688 = region_10163.end;

        frame = gib_shadowstack_pop(wstack);
        loc_3015 = frame->ptr;
        end_r_3017 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        pvrtmp_10157 = frame->ptr;
        pvrtmp_10156 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        pvrtmp_10148 = frame->ptr;
        pvrtmp_10146 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        pvrtmp_10133 = frame->ptr;
        pvrtmp_10132 = frame->endptr;

        GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_119 =
                                                           dot(pvrtmp_10156, end_r_3688, r_3688, 2.0, pvrtmp_10157);
        GibCursor pvrtmp_10164 = tmp_struct_119.field0;
        GibCursor pvrtmp_10165 = tmp_struct_119.field1;
        GibCursor pvrtmp_10166 = tmp_struct_119.field2;
        GibCursor pvrtmp_10167 = tmp_struct_119.field3;
        GibCursor pvrtmp_10168 = tmp_struct_119.field4;

        gib_shadowstack_push(rstack, pvrtmp_10133, pvrtmp_10132, Stk, Ps_T);
        gib_shadowstack_push(rstack, pvrtmp_10148, pvrtmp_10146, Stk, Ps_T);
        gib_shadowstack_push(rstack, pvrtmp_10167, pvrtmp_10165, Stk, Ps_T);
        gib_shadowstack_push(wstack, loc_3015, end_r_3017, Stk, Ps_T);

        GibChunk region_10173 = gib_alloc_region(gib_get_inf_init_chunk_size());
        GibCursor r_3687 = region_10173.start;
        GibCursor end_r_3687 = region_10173.end;

        frame = gib_shadowstack_pop(wstack);
        loc_3015 = frame->ptr;
        end_r_3017 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        pvrtmp_10167 = frame->ptr;
        pvrtmp_10165 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        pvrtmp_10148 = frame->ptr;
        pvrtmp_10146 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        pvrtmp_10133 = frame->ptr;
        pvrtmp_10132 = frame->endptr;
        gib_shadowstack_push(rstack, pvrtmp_10133, pvrtmp_10132, Stk, Ps_T);
        gib_shadowstack_push(wstack, loc_3015, end_r_3017, Stk, Ps_T);

        GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_120 =
                                                           psDiv(pvrtmp_10146, pvrtmp_10165, end_r_3687, r_3687, fltAppE_1181_1423, pvrtmp_10148, pvrtmp_10167);
        GibCursor pvrtmp_10174 = tmp_struct_120.field0;
        GibCursor pvrtmp_10175 = tmp_struct_120.field1;
        GibCursor pvrtmp_10176 = tmp_struct_120.field2;
        GibCursor pvrtmp_10177 = tmp_struct_120.field3;
        GibCursor pvrtmp_10178 = tmp_struct_120.field4;

        frame = gib_shadowstack_pop(wstack);
        loc_3015 = frame->ptr;
        end_r_3017 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        pvrtmp_10133 = frame->ptr;
        pvrtmp_10132 = frame->endptr;
        gib_shadowstack_push(rstack, pvrtmp_10133, pvrtmp_10132, Stk, Ps_T);
        gib_shadowstack_push(rstack, pvrtmp_10177, pvrtmp_10176, Stk, Ps_T);
        gib_shadowstack_push(wstack, loc_3015, end_r_3017, Stk, Ps_T);

        GibChunk region_10183 = gib_alloc_region(gib_get_inf_init_chunk_size());
        GibCursor r_3686 = region_10183.start;
        GibCursor end_r_3686 = region_10183.end;

        frame = gib_shadowstack_pop(wstack);
        loc_3015 = frame->ptr;
        end_r_3017 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        pvrtmp_10177 = frame->ptr;
        pvrtmp_10176 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        pvrtmp_10133 = frame->ptr;
        pvrtmp_10132 = frame->endptr;

        GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_121 =
                                                           integral(pvrtmp_10176, end_r_3686, r_3686, pvrtmp_10177);
        GibCursor pvrtmp_10184 = tmp_struct_121.field0;
        GibCursor pvrtmp_10185 = tmp_struct_121.field1;
        GibCursor pvrtmp_10186 = tmp_struct_121.field2;
        GibCursor pvrtmp_10187 = tmp_struct_121.field3;
        GibCursor pvrtmp_10188 = tmp_struct_121.field4;
        GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_122 =
                                                           psAdd(pvrtmp_10132, pvrtmp_10185, end_r_3017, loc_3015, pvrtmp_10133, pvrtmp_10187);
        GibCursor pvrtmp_10193 = tmp_struct_122.field0;
        GibCursor pvrtmp_10194 = tmp_struct_122.field1;
        GibCursor pvrtmp_10195 = tmp_struct_122.field2;
        GibCursor pvrtmp_10196 = tmp_struct_122.field3;
        GibCursor pvrtmp_10197 = tmp_struct_122.field4;

        return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_10155,
                                                           pvrtmp_10195,
                                                           pvrtmp_10196,
                                                           pvrtmp_10197};
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd integral(GibCursor end_r_3020,
                                                           GibCursor end_r_3021,
                                                           GibCursor loc_3019,
                                                           GibCursor fs_269_874_1431)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_3019 + 18 > end_r_3021) {
        gib_grow_region(&loc_3019, &end_r_3021);
    }

    GibCursor loc_3697 = loc_3019 + 5;

    *(GibPackedTag *) loc_3019 = 1;

    GibCursor writetag_6819 = loc_3019 + 1;
    GibCursor after_tag_6820 = loc_3019 + 1;

    *(GibFloat *) after_tag_6820 = 0.0;

    GibCursor writecur_6824 = after_tag_6820 + sizeof(GibFloat);
    GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_129 =
                                                       int1(end_r_3020, end_r_3021, loc_3697, fs_269_874_1431, 1);
    GibCursor pvrtmp_10204 = tmp_struct_129.field0;
    GibCursor pvrtmp_10205 = tmp_struct_129.field1;
    GibCursor pvrtmp_10206 = tmp_struct_129.field2;
    GibCursor pvrtmp_10207 = tmp_struct_129.field3;
    GibCursor pvrtmp_10208 = tmp_struct_129.field4;

    return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_10204,
                                                                pvrtmp_10205,
                                                                pvrtmp_10206,
                                                                loc_3019,
                                                                pvrtmp_10208};
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd int1(GibCursor end_r_3024,
                                                       GibCursor end_r_3025,
                                                       GibCursor loc_3023,
                                                       GibCursor a_270_875_1433,
                                                       GibInt n_271_876_1434)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_3023 + 18 > end_r_3025) {
        gib_grow_region(&loc_3023, &end_r_3025);
    }

    GibPackedTag tmpval_10217 = *(GibPackedTag *) a_270_875_1433;
    GibCursor tmpcur_10218 = a_270_875_1433 + 1;


  switch_10270:
    ;
    switch (tmpval_10217) {

      case 0:
        {
            GibCursor jump_4370 = a_270_875_1433 + 1;

            *(GibPackedTag *) loc_3023 = 0;

            GibCursor writetag_6829 = loc_3023 + 1;
            GibCursor after_tag_6830 = loc_3023 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3024,
                                                                        end_r_3025,
                                                                        jump_4370,
                                                                        loc_3023,
                                                                        after_tag_6830};
            break;
        }

      case 1:
        {
            GibFloat tmpval_10223 = *(GibFloat *) tmpcur_10218;
            GibCursor tmpcur_10224 = tmpcur_10218 + sizeof(GibFloat);
            GibFloat fltPrm_1189_1437 = (GibFloat) n_271_876_1434;
            GibFloat fltPkd_1188_1438 = tmpval_10223 / fltPrm_1189_1437;
            GibInt fltAppE_1191_1439 = n_271_876_1434 + 1;
            GibCursor loc_3708 = loc_3023 + 5;

            *(GibPackedTag *) loc_3023 = 1;

            GibCursor writetag_6841 = loc_3023 + 1;
            GibCursor after_tag_6842 = loc_3023 + 1;

            *(GibFloat *) after_tag_6842 = fltPkd_1188_1438;

            GibCursor writecur_6846 = after_tag_6842 + sizeof(GibFloat);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_133 =
                                                               int1(end_r_3024, end_r_3025, loc_3708, tmpcur_10224, fltAppE_1191_1439);
            GibCursor pvrtmp_10225 = tmp_struct_133.field0;
            GibCursor pvrtmp_10226 = tmp_struct_133.field1;
            GibCursor pvrtmp_10227 = tmp_struct_133.field2;
            GibCursor pvrtmp_10228 = tmp_struct_133.field3;
            GibCursor pvrtmp_10229 = tmp_struct_133.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_10225,
                                                                        pvrtmp_10226,
                                                                        pvrtmp_10227,
                                                                        loc_3023,
                                                                        pvrtmp_10229};
            break;
        }

      case 2:
        {
            GibCursor jump_4375 = a_270_875_1433 + 1;

            *(GibPackedTag *) loc_3023 = 2;

            GibCursor writetag_6851 = loc_3023 + 1;
            GibCursor after_tag_6852 = loc_3023 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3024,
                                                                        end_r_3025,
                                                                        jump_4375,
                                                                        loc_3023,
                                                                        after_tag_6852};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_135 = *(uintptr_t *) tmpcur_10218;
            GibCursor tmpcur_10242 = GIB_UNTAG(tagged_tmpcur_135);
            GibCursor tmpaftercur_10243 = tmpcur_10218 + 8;
            uint16_t tmptag_10244 = GIB_GET_TAG(tagged_tmpcur_135);
            GibCursor end_from_tagged_indr_4615 = tmpcur_10242 + tmptag_10244;
            GibCursor jump_4617 = tmpcur_10218 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_134 =
                                                               int1(end_from_tagged_indr_4615, end_r_3025, loc_3023, tmpcur_10242, n_271_876_1434);
            GibCursor pvrtmp_10245 = tmp_struct_134.field0;
            GibCursor pvrtmp_10246 = tmp_struct_134.field1;
            GibCursor pvrtmp_10247 = tmp_struct_134.field2;
            GibCursor pvrtmp_10248 = tmp_struct_134.field3;
            GibCursor pvrtmp_10249 = tmp_struct_134.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3024,
                                                                        pvrtmp_10246,
                                                                        jump_4617,
                                                                        pvrtmp_10248,
                                                                        pvrtmp_10249};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_137 = *(uintptr_t *) tmpcur_10218;
            GibCursor tmpcur_10256 = GIB_UNTAG(tagged_tmpcur_137);
            GibCursor tmpaftercur_10257 = tmpcur_10218 + 8;
            uint16_t tmptag_10258 = GIB_GET_TAG(tagged_tmpcur_137);
            GibCursor end_from_tagged_indr_4615 = tmpcur_10256 + tmptag_10258;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_136 =
                                                               int1(end_from_tagged_indr_4615, end_r_3025, loc_3023, tmpcur_10256, n_271_876_1434);
            GibCursor pvrtmp_10259 = tmp_struct_136.field0;
            GibCursor pvrtmp_10260 = tmp_struct_136.field1;
            GibCursor pvrtmp_10261 = tmp_struct_136.field2;
            GibCursor pvrtmp_10262 = tmp_struct_136.field3;
            GibCursor pvrtmp_10263 = tmp_struct_136.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_10259,
                                                                        pvrtmp_10260,
                                                                        pvrtmp_10261,
                                                                        pvrtmp_10262,
                                                                        pvrtmp_10263};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_10217");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd deriv(GibCursor end_r_3028,
                                                        GibCursor end_r_3029,
                                                        GibCursor loc_3027,
                                                        GibCursor a_274_879_1441)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_3027 + 18 > end_r_3029) {
        gib_grow_region(&loc_3027, &end_r_3029);
    }

    GibPackedTag tmpval_10271 = *(GibPackedTag *) a_274_879_1441;
    GibCursor tmpcur_10272 = a_274_879_1441 + 1;


  switch_10322:
    ;
    switch (tmpval_10271) {

      case 0:
        {
            GibCursor jump_4377 = a_274_879_1441 + 1;

            *(GibPackedTag *) loc_3027 = 0;

            GibCursor writetag_6869 = loc_3027 + 1;
            GibCursor after_tag_6870 = loc_3027 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3028,
                                                                        end_r_3029,
                                                                        jump_4377,
                                                                        loc_3027,
                                                                        after_tag_6870};
            break;
        }

      case 1:
        {
            GibFloat tmpval_10277 = *(GibFloat *) tmpcur_10272;
            GibCursor tmpcur_10278 = tmpcur_10272 + sizeof(GibFloat);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_141 =
                                                               deriv1(end_r_3028, end_r_3029, loc_3027, tmpcur_10278, 1);
            GibCursor pvrtmp_10279 = tmp_struct_141.field0;
            GibCursor pvrtmp_10280 = tmp_struct_141.field1;
            GibCursor pvrtmp_10281 = tmp_struct_141.field2;
            GibCursor pvrtmp_10282 = tmp_struct_141.field3;
            GibCursor pvrtmp_10283 = tmp_struct_141.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_10279,
                                                                        pvrtmp_10280,
                                                                        pvrtmp_10281,
                                                                        pvrtmp_10282,
                                                                        pvrtmp_10283};
            break;
        }

      case 2:
        {
            GibCursor jump_4382 = a_274_879_1441 + 1;

            *(GibPackedTag *) loc_3027 = 2;

            GibCursor writetag_6882 = loc_3027 + 1;
            GibCursor after_tag_6883 = loc_3027 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3028,
                                                                        end_r_3029,
                                                                        jump_4382,
                                                                        loc_3027,
                                                                        after_tag_6883};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_143 = *(uintptr_t *) tmpcur_10272;
            GibCursor tmpcur_10294 = GIB_UNTAG(tagged_tmpcur_143);
            GibCursor tmpaftercur_10295 = tmpcur_10272 + 8;
            uint16_t tmptag_10296 = GIB_GET_TAG(tagged_tmpcur_143);
            GibCursor end_from_tagged_indr_4621 = tmpcur_10294 + tmptag_10296;
            GibCursor jump_4623 = tmpcur_10272 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_142 =
                                                               deriv(end_from_tagged_indr_4621, end_r_3029, loc_3027, tmpcur_10294);
            GibCursor pvrtmp_10297 = tmp_struct_142.field0;
            GibCursor pvrtmp_10298 = tmp_struct_142.field1;
            GibCursor pvrtmp_10299 = tmp_struct_142.field2;
            GibCursor pvrtmp_10300 = tmp_struct_142.field3;
            GibCursor pvrtmp_10301 = tmp_struct_142.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3028,
                                                                        pvrtmp_10298,
                                                                        jump_4623,
                                                                        pvrtmp_10300,
                                                                        pvrtmp_10301};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_145 = *(uintptr_t *) tmpcur_10272;
            GibCursor tmpcur_10308 = GIB_UNTAG(tagged_tmpcur_145);
            GibCursor tmpaftercur_10309 = tmpcur_10272 + 8;
            uint16_t tmptag_10310 = GIB_GET_TAG(tagged_tmpcur_145);
            GibCursor end_from_tagged_indr_4621 = tmpcur_10308 + tmptag_10310;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_144 =
                                                               deriv(end_from_tagged_indr_4621, end_r_3029, loc_3027, tmpcur_10308);
            GibCursor pvrtmp_10311 = tmp_struct_144.field0;
            GibCursor pvrtmp_10312 = tmp_struct_144.field1;
            GibCursor pvrtmp_10313 = tmp_struct_144.field2;
            GibCursor pvrtmp_10314 = tmp_struct_144.field3;
            GibCursor pvrtmp_10315 = tmp_struct_144.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_10311,
                                                                        pvrtmp_10312,
                                                                        pvrtmp_10313,
                                                                        pvrtmp_10314,
                                                                        pvrtmp_10315};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_10271");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd deriv1(GibCursor end_r_3032,
                                                         GibCursor end_r_3033,
                                                         GibCursor loc_3031,
                                                         GibCursor a_277_882_1444,
                                                         GibInt n_278_883_1445)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_3031 + 18 > end_r_3033) {
        gib_grow_region(&loc_3031, &end_r_3033);
    }

    GibPackedTag tmpval_10323 = *(GibPackedTag *) a_277_882_1444;
    GibCursor tmpcur_10324 = a_277_882_1444 + 1;


  switch_10376:
    ;
    switch (tmpval_10323) {

      case 0:
        {
            GibCursor jump_4384 = a_277_882_1444 + 1;

            *(GibPackedTag *) loc_3031 = 0;

            GibCursor writetag_6900 = loc_3031 + 1;
            GibCursor after_tag_6901 = loc_3031 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3032,
                                                                        end_r_3033,
                                                                        jump_4384,
                                                                        loc_3031,
                                                                        after_tag_6901};
            break;
        }

      case 1:
        {
            GibFloat tmpval_10329 = *(GibFloat *) tmpcur_10324;
            GibCursor tmpcur_10330 = tmpcur_10324 + sizeof(GibFloat);
            GibFloat fltPrm_1193_1448 = (GibFloat) n_278_883_1445;
            GibFloat fltPkd_1192_1449 = fltPrm_1193_1448 * tmpval_10329;
            GibInt fltAppE_1195_1450 = n_278_883_1445 + 1;
            GibCursor loc_3732 = loc_3031 + 5;

            *(GibPackedTag *) loc_3031 = 1;

            GibCursor writetag_6912 = loc_3031 + 1;
            GibCursor after_tag_6913 = loc_3031 + 1;

            *(GibFloat *) after_tag_6913 = fltPkd_1192_1449;

            GibCursor writecur_6917 = after_tag_6913 + sizeof(GibFloat);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_149 =
                                                               deriv1(end_r_3032, end_r_3033, loc_3732, tmpcur_10330, fltAppE_1195_1450);
            GibCursor pvrtmp_10331 = tmp_struct_149.field0;
            GibCursor pvrtmp_10332 = tmp_struct_149.field1;
            GibCursor pvrtmp_10333 = tmp_struct_149.field2;
            GibCursor pvrtmp_10334 = tmp_struct_149.field3;
            GibCursor pvrtmp_10335 = tmp_struct_149.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_10331,
                                                                        pvrtmp_10332,
                                                                        pvrtmp_10333,
                                                                        loc_3031,
                                                                        pvrtmp_10335};
            break;
        }

      case 2:
        {
            GibCursor jump_4389 = a_277_882_1444 + 1;

            *(GibPackedTag *) loc_3031 = 2;

            GibCursor writetag_6922 = loc_3031 + 1;
            GibCursor after_tag_6923 = loc_3031 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3032,
                                                                        end_r_3033,
                                                                        jump_4389,
                                                                        loc_3031,
                                                                        after_tag_6923};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_151 = *(uintptr_t *) tmpcur_10324;
            GibCursor tmpcur_10348 = GIB_UNTAG(tagged_tmpcur_151);
            GibCursor tmpaftercur_10349 = tmpcur_10324 + 8;
            uint16_t tmptag_10350 = GIB_GET_TAG(tagged_tmpcur_151);
            GibCursor end_from_tagged_indr_4627 = tmpcur_10348 + tmptag_10350;
            GibCursor jump_4629 = tmpcur_10324 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_150 =
                                                               deriv1(end_from_tagged_indr_4627, end_r_3033, loc_3031, tmpcur_10348, n_278_883_1445);
            GibCursor pvrtmp_10351 = tmp_struct_150.field0;
            GibCursor pvrtmp_10352 = tmp_struct_150.field1;
            GibCursor pvrtmp_10353 = tmp_struct_150.field2;
            GibCursor pvrtmp_10354 = tmp_struct_150.field3;
            GibCursor pvrtmp_10355 = tmp_struct_150.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3032,
                                                                        pvrtmp_10352,
                                                                        jump_4629,
                                                                        pvrtmp_10354,
                                                                        pvrtmp_10355};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_153 = *(uintptr_t *) tmpcur_10324;
            GibCursor tmpcur_10362 = GIB_UNTAG(tagged_tmpcur_153);
            GibCursor tmpaftercur_10363 = tmpcur_10324 + 8;
            uint16_t tmptag_10364 = GIB_GET_TAG(tagged_tmpcur_153);
            GibCursor end_from_tagged_indr_4627 = tmpcur_10362 + tmptag_10364;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_152 =
                                                               deriv1(end_from_tagged_indr_4627, end_r_3033, loc_3031, tmpcur_10362, n_278_883_1445);
            GibCursor pvrtmp_10365 = tmp_struct_152.field0;
            GibCursor pvrtmp_10366 = tmp_struct_152.field1;
            GibCursor pvrtmp_10367 = tmp_struct_152.field2;
            GibCursor pvrtmp_10368 = tmp_struct_152.field3;
            GibCursor pvrtmp_10369 = tmp_struct_152.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_10365,
                                                                        pvrtmp_10366,
                                                                        pvrtmp_10367,
                                                                        pvrtmp_10368,
                                                                        pvrtmp_10369};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_10323");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd revert(GibCursor end_r_3036,
                                                GibCursor end_r_3037,
                                                GibCursor loc_3035,
                                                GibInt n_281_886_1452,
                                                GibCursor a_282_887_1453)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_3035 + 18 > end_r_3037) {
        gib_grow_region(&loc_3035, &end_r_3037);
    }

    GibPackedTag tmpval_10377 = *(GibPackedTag *) a_282_887_1453;
    GibCursor tmpcur_10378 = a_282_887_1453 + 1;


  switch_10432:
    ;
    switch (tmpval_10377) {

      case 0:
        {
            *(GibPackedTag *) loc_3035 = 2;

            GibCursor writetag_6940 = loc_3035 + 1;
            GibCursor after_tag_6941 = loc_3035 + 1;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_3036,
                                                               end_r_3037,
                                                               loc_3035,
                                                               after_tag_6941};
            break;
        }

      case 1:
        {
            GibFloat tmpval_10383 = *(GibFloat *) tmpcur_10378;
            GibCursor tmpcur_10384 = tmpcur_10378 + sizeof(GibFloat);
            GibBool fltIf_1196_1456 = tmpval_10383 == 0.0;

            if (fltIf_1196_1456) {
                GibCursorGibCursorGibCursorGibCursorProd tmp_struct_157 =
                                                          getRs(end_r_3036, end_r_3037, loc_3035, n_281_886_1452, tmpcur_10384);
                GibCursor pvrtmp_10385 = tmp_struct_157.field0;
                GibCursor pvrtmp_10386 = tmp_struct_157.field1;
                GibCursor pvrtmp_10387 = tmp_struct_157.field2;
                GibCursor pvrtmp_10388 = tmp_struct_157.field3;

                return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_10385,
                                                                   pvrtmp_10386,
                                                                   pvrtmp_10387,
                                                                   pvrtmp_10388};
            } else {
                GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_158
                                                                  =
                                                                   caseFn_818(end_r_3036, end_r_3037, loc_3035, tmpval_10383, tmpcur_10384);
                GibCursor pvrtmp_10395 = tmp_struct_158.field0;
                GibCursor pvrtmp_10396 = tmp_struct_158.field1;
                GibCursor pvrtmp_10397 = tmp_struct_158.field2;
                GibCursor pvrtmp_10398 = tmp_struct_158.field3;
                GibCursor pvrtmp_10399 = tmp_struct_158.field4;

                return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_10395,
                                                                   pvrtmp_10396,
                                                                   pvrtmp_10398,
                                                                   pvrtmp_10399};
            }
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_160 = *(uintptr_t *) tmpcur_10378;
            GibCursor tmpcur_10406 = GIB_UNTAG(tagged_tmpcur_160);
            GibCursor tmpaftercur_10407 = tmpcur_10378 + 8;
            uint16_t tmptag_10408 = GIB_GET_TAG(tagged_tmpcur_160);
            GibCursor end_from_tagged_indr_4633 = tmpcur_10406 + tmptag_10408;
            GibCursor jump_4635 = tmpcur_10378 + 8;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_159 =
                                                      revert(end_from_tagged_indr_4633, end_r_3037, loc_3035, n_281_886_1452, tmpcur_10406);
            GibCursor pvrtmp_10409 = tmp_struct_159.field0;
            GibCursor pvrtmp_10410 = tmp_struct_159.field1;
            GibCursor pvrtmp_10411 = tmp_struct_159.field2;
            GibCursor pvrtmp_10412 = tmp_struct_159.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_3036,
                                                               pvrtmp_10410,
                                                               pvrtmp_10411,
                                                               pvrtmp_10412};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_162 = *(uintptr_t *) tmpcur_10378;
            GibCursor tmpcur_10419 = GIB_UNTAG(tagged_tmpcur_162);
            GibCursor tmpaftercur_10420 = tmpcur_10378 + 8;
            uint16_t tmptag_10421 = GIB_GET_TAG(tagged_tmpcur_162);
            GibCursor end_from_tagged_indr_4633 = tmpcur_10419 + tmptag_10421;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_161 =
                                                      revert(end_from_tagged_indr_4633, end_r_3037, loc_3035, n_281_886_1452, tmpcur_10419);
            GibCursor pvrtmp_10422 = tmp_struct_161.field0;
            GibCursor pvrtmp_10423 = tmp_struct_161.field1;
            GibCursor pvrtmp_10424 = tmp_struct_161.field2;
            GibCursor pvrtmp_10425 = tmp_struct_161.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_10422,
                                                               pvrtmp_10423,
                                                               pvrtmp_10424,
                                                               pvrtmp_10425};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_10377");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd getRs(GibCursor end_r_3040,
                                               GibCursor end_r_3041,
                                               GibCursor loc_3039,
                                               GibInt n_287_890_1457,
                                               GibCursor fs_288_891_1458)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_3039 + 18 > end_r_3041) {
        gib_grow_region(&loc_3039, &end_r_3041);
    }

    GibBool fltIf_1197_1459 = n_287_890_1457 == 0;

    if (fltIf_1197_1459) {
        *(GibPackedTag *) loc_3039 = 0;

        GibCursor writetag_6965 = loc_3039 + 1;
        GibCursor after_tag_6966 = loc_3039 + 1;

        return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_3040,
                                                           end_r_3041, loc_3039,
                                                           after_tag_6966};
    } else {
        GibInt fltAppE_1199_1460 = n_287_890_1457 - 1;

        gib_shadowstack_push(rstack, fs_288_891_1458, end_r_3040, Stk, Ps_T);
        gib_shadowstack_push(wstack, loc_3039, end_r_3041, Stk, Ps_T);

        GibChunk region_10437 = gib_alloc_region(gib_get_inf_init_chunk_size());
        GibCursor r_3773 = region_10437.start;
        GibCursor end_r_3773 = region_10437.end;

        frame = gib_shadowstack_pop(wstack);
        loc_3039 = frame->ptr;
        end_r_3041 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        fs_288_891_1458 = frame->ptr;
        end_r_3040 = frame->endptr;

        GibCursorGibCursorGibCursorProd tmp_struct_166 =
                                         pone(end_r_3773, r_3773);
        GibCursor pvrtmp_10438 = tmp_struct_166.field0;
        GibCursor pvrtmp_10439 = tmp_struct_166.field1;
        GibCursor pvrtmp_10440 = tmp_struct_166.field2;
        GibInt fltAppE_1203_1462 = n_287_890_1457 - 1;

        gib_shadowstack_push(rstack, pvrtmp_10439, pvrtmp_10438, Stk, Ps_T);
        gib_shadowstack_push(rstack, fs_288_891_1458, end_r_3040, Stk, Ps_T);
        gib_shadowstack_push(wstack, loc_3039, end_r_3041, Stk, Ps_T);

        GibChunk region_10445 = gib_alloc_region(gib_get_inf_init_chunk_size());
        GibCursor r_3772 = region_10445.start;
        GibCursor end_r_3772 = region_10445.end;

        frame = gib_shadowstack_pop(wstack);
        loc_3039 = frame->ptr;
        end_r_3041 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        fs_288_891_1458 = frame->ptr;
        end_r_3040 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        pvrtmp_10439 = frame->ptr;
        pvrtmp_10438 = frame->endptr;
        gib_shadowstack_push(rstack, pvrtmp_10439, pvrtmp_10438, Stk, Ps_T);
        gib_shadowstack_push(rstack, fs_288_891_1458, end_r_3040, Stk, Ps_T);
        gib_shadowstack_push(wstack, loc_3039, end_r_3041, Stk, Ps_T);

        GibCursorGibCursorGibCursorGibCursorProd tmp_struct_167 =
                                                  getRs(end_r_3040, end_r_3772, r_3772, fltAppE_1203_1462, fs_288_891_1458);
        GibCursor pvrtmp_10446 = tmp_struct_167.field0;
        GibCursor pvrtmp_10447 = tmp_struct_167.field1;
        GibCursor pvrtmp_10448 = tmp_struct_167.field2;
        GibCursor pvrtmp_10449 = tmp_struct_167.field3;

        frame = gib_shadowstack_pop(wstack);
        loc_3039 = frame->ptr;
        end_r_3041 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        fs_288_891_1458 = frame->ptr;
        end_r_3040 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        pvrtmp_10439 = frame->ptr;
        pvrtmp_10438 = frame->endptr;
        gib_shadowstack_push(rstack, pvrtmp_10439, pvrtmp_10438, Stk, Ps_T);
        gib_shadowstack_push(rstack, pvrtmp_10448, pvrtmp_10447, Stk, Ps_T);
        gib_shadowstack_push(rstack, fs_288_891_1458, end_r_3040, Stk, Ps_T);
        gib_shadowstack_push(wstack, loc_3039, end_r_3041, Stk, Ps_T);

        GibChunk region_10454 = gib_alloc_region(gib_get_inf_init_chunk_size());
        GibCursor r_3771 = region_10454.start;
        GibCursor end_r_3771 = region_10454.end;

        frame = gib_shadowstack_pop(wstack);
        loc_3039 = frame->ptr;
        end_r_3041 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        fs_288_891_1458 = frame->ptr;
        end_r_3040 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        pvrtmp_10448 = frame->ptr;
        pvrtmp_10447 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        pvrtmp_10439 = frame->ptr;
        pvrtmp_10438 = frame->endptr;
        gib_shadowstack_push(rstack, pvrtmp_10439, pvrtmp_10438, Stk, Ps_T);
        gib_shadowstack_push(wstack, loc_3039, end_r_3041, Stk, Ps_T);

        GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_168 =
                                                           compose(end_r_3040, pvrtmp_10447, end_r_3771, r_3771, fs_288_891_1458, pvrtmp_10448);
        GibCursor pvrtmp_10455 = tmp_struct_168.field0;
        GibCursor pvrtmp_10456 = tmp_struct_168.field1;
        GibCursor pvrtmp_10457 = tmp_struct_168.field2;
        GibCursor pvrtmp_10458 = tmp_struct_168.field3;
        GibCursor pvrtmp_10459 = tmp_struct_168.field4;

        frame = gib_shadowstack_pop(wstack);
        loc_3039 = frame->ptr;
        end_r_3041 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        pvrtmp_10439 = frame->ptr;
        pvrtmp_10438 = frame->endptr;

        GibCursor loc_3769 = loc_3039 + 5;

        *(GibPackedTag *) loc_3039 = 1;

        GibCursor writetag_6985 = loc_3039 + 1;
        GibCursor after_tag_6986 = loc_3039 + 1;

        *(GibFloat *) after_tag_6986 = 0.0;

        GibCursor writecur_6990 = after_tag_6986 + sizeof(GibFloat);

        gib_shadowstack_push(rstack, loc_3039, end_r_3041, Stk, Ps_T);

        GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_169 =
                                                           psDiv(pvrtmp_10438, pvrtmp_10457, end_r_3041, loc_3769, fltAppE_1199_1460, pvrtmp_10439, pvrtmp_10458);
        GibCursor pvrtmp_10464 = tmp_struct_169.field0;
        GibCursor pvrtmp_10465 = tmp_struct_169.field1;
        GibCursor pvrtmp_10466 = tmp_struct_169.field2;
        GibCursor pvrtmp_10467 = tmp_struct_169.field3;
        GibCursor pvrtmp_10468 = tmp_struct_169.field4;

        frame = gib_shadowstack_pop(rstack);
        loc_3039 = frame->ptr;
        end_r_3041 = frame->endptr;
        return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_10455,
                                                           pvrtmp_10466,
                                                           loc_3039,
                                                           pvrtmp_10468};
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd compose(GibCursor end_r_3045,
                                                          GibCursor end_r_3046,
                                                          GibCursor end_r_3047,
                                                          GibCursor loc_3044,
                                                          GibCursor a_289_892_1466,
                                                          GibCursor b_290_893_1467)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_3044 + 18 > end_r_3047) {
        gib_grow_region(&loc_3044, &end_r_3047);
    }

    GibPackedTag tmpval_10477 = *(GibPackedTag *) a_289_892_1466;
    GibCursor tmpcur_10478 = a_289_892_1466 + 1;


  switch_10528:
    ;
    switch (tmpval_10477) {

      case 0:
        {
            *(GibPackedTag *) loc_3044 = 0;

            GibCursor writetag_6995 = loc_3044 + 1;
            GibCursor after_tag_6996 = loc_3044 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3045,
                                                                        end_r_3046,
                                                                        end_r_3047,
                                                                        loc_3044,
                                                                        after_tag_6996};
            break;
        }

      case 1:
        {
            GibFloat tmpval_10483 = *(GibFloat *) tmpcur_10478;
            GibCursor tmpcur_10484 = tmpcur_10478 + sizeof(GibFloat);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_173 =
                                                               caseFn_821(end_r_3046, end_r_3045, end_r_3047, loc_3044, b_290_893_1467, tmpval_10483, tmpcur_10484);
            GibCursor pvrtmp_10485 = tmp_struct_173.field0;
            GibCursor pvrtmp_10486 = tmp_struct_173.field1;
            GibCursor pvrtmp_10487 = tmp_struct_173.field2;
            GibCursor pvrtmp_10488 = tmp_struct_173.field3;
            GibCursor pvrtmp_10489 = tmp_struct_173.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_10486,
                                                                        pvrtmp_10485,
                                                                        pvrtmp_10487,
                                                                        pvrtmp_10488,
                                                                        pvrtmp_10489};
            break;
        }

      case 2:
        {
            *(GibPackedTag *) loc_3044 = 2;

            GibCursor writetag_7009 = loc_3044 + 1;
            GibCursor after_tag_7010 = loc_3044 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3045,
                                                                        end_r_3046,
                                                                        end_r_3047,
                                                                        loc_3044,
                                                                        after_tag_7010};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_175 = *(uintptr_t *) tmpcur_10478;
            GibCursor tmpcur_10500 = GIB_UNTAG(tagged_tmpcur_175);
            GibCursor tmpaftercur_10501 = tmpcur_10478 + 8;
            uint16_t tmptag_10502 = GIB_GET_TAG(tagged_tmpcur_175);
            GibCursor end_from_tagged_indr_4638 = tmpcur_10500 + tmptag_10502;
            GibCursor jump_4640 = tmpcur_10478 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_174 =
                                                               compose(end_from_tagged_indr_4638, end_r_3046, end_r_3047, loc_3044, tmpcur_10500, b_290_893_1467);
            GibCursor pvrtmp_10503 = tmp_struct_174.field0;
            GibCursor pvrtmp_10504 = tmp_struct_174.field1;
            GibCursor pvrtmp_10505 = tmp_struct_174.field2;
            GibCursor pvrtmp_10506 = tmp_struct_174.field3;
            GibCursor pvrtmp_10507 = tmp_struct_174.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3045,
                                                                        pvrtmp_10504,
                                                                        pvrtmp_10505,
                                                                        pvrtmp_10506,
                                                                        pvrtmp_10507};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_177 = *(uintptr_t *) tmpcur_10478;
            GibCursor tmpcur_10514 = GIB_UNTAG(tagged_tmpcur_177);
            GibCursor tmpaftercur_10515 = tmpcur_10478 + 8;
            uint16_t tmptag_10516 = GIB_GET_TAG(tagged_tmpcur_177);
            GibCursor end_from_tagged_indr_4638 = tmpcur_10514 + tmptag_10516;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_176 =
                                                               compose(end_from_tagged_indr_4638, end_r_3046, end_r_3047, loc_3044, tmpcur_10514, b_290_893_1467);
            GibCursor pvrtmp_10517 = tmp_struct_176.field0;
            GibCursor pvrtmp_10518 = tmp_struct_176.field1;
            GibCursor pvrtmp_10519 = tmp_struct_176.field2;
            GibCursor pvrtmp_10520 = tmp_struct_176.field3;
            GibCursor pvrtmp_10521 = tmp_struct_176.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_10517,
                                                                        pvrtmp_10518,
                                                                        pvrtmp_10519,
                                                                        pvrtmp_10520,
                                                                        pvrtmp_10521};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_10477");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorProd list(GibCursor end_r_3049, GibCursor loc_3048,
                                     GibInt n_295_896_1470)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_3048 + 18 > end_r_3049) {
        gib_grow_region(&loc_3048, &end_r_3049);
    }

    GibBool fltIf_1204_1471 = n_295_896_1470 == 0;

    if (fltIf_1204_1471) {
        *(GibPackedTag *) loc_3048 = 0;

        GibCursor writetag_7028 = loc_3048 + 1;
        GibCursor after_tag_7029 = loc_3048 + 1;

        return (GibCursorGibCursorGibCursorProd) {end_r_3049, loc_3048,
                                                  after_tag_7029};
    } else {
        GibInt fltAppE_1206_1472 = n_295_896_1470 - 1;
        GibCursor loc_3789 = loc_3048 + 5;

        *(GibPackedTag *) loc_3048 = 1;

        GibCursor writetag_7037 = loc_3048 + 1;
        GibCursor after_tag_7038 = loc_3048 + 1;

        *(GibFloat *) after_tag_7038 = 1.0;

        GibCursor writecur_7042 = after_tag_7038 + sizeof(GibFloat);
        GibCursorGibCursorGibCursorProd tmp_struct_181 =
                                         list(end_r_3049, loc_3789, fltAppE_1206_1472);
        GibCursor pvrtmp_10533 = tmp_struct_181.field0;
        GibCursor pvrtmp_10534 = tmp_struct_181.field1;
        GibCursor pvrtmp_10535 = tmp_struct_181.field2;

        return (GibCursorGibCursorGibCursorProd) {pvrtmp_10533, loc_3048,
                                                  pvrtmp_10535};
    }
}
GibCursorGibCursorGibCursorProd ts(GibCursor end_r_3051, GibCursor loc_3050,
                                   GibInt n_296_897_1474)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_3050 + 18 > end_r_3051) {
        gib_grow_region(&loc_3050, &end_r_3051);
    }

    GibBool fltIf_1207_1475 = n_296_897_1474 == 0;

    if (fltIf_1207_1475) {
        *(GibPackedTag *) loc_3050 = 0;

        GibCursor writetag_7046 = loc_3050 + 1;
        GibCursor after_tag_7047 = loc_3050 + 1;

        return (GibCursorGibCursorGibCursorProd) {end_r_3051, loc_3050,
                                                  after_tag_7047};
    } else {
        GibInt fltAppE_1209_1476 = n_296_897_1474 - 1;
        GibInt fltAppE_1212_1477 = n_296_897_1474 - 1;

        gib_shadowstack_push(wstack, loc_3050, end_r_3051, Stk, Ps_T);

        GibChunk region_10548 = gib_alloc_region(gib_get_inf_init_chunk_size());
        GibCursor r_3810 = region_10548.start;
        GibCursor end_r_3810 = region_10548.end;

        frame = gib_shadowstack_pop(wstack);
        loc_3050 = frame->ptr;
        end_r_3051 = frame->endptr;
        gib_shadowstack_push(wstack, loc_3050, end_r_3051, Stk, Ps_T);

        GibCursorGibCursorGibCursorProd tmp_struct_185 =
                                         ts(end_r_3810, r_3810, fltAppE_1212_1477);
        GibCursor pvrtmp_10549 = tmp_struct_185.field0;
        GibCursor pvrtmp_10550 = tmp_struct_185.field1;
        GibCursor pvrtmp_10551 = tmp_struct_185.field2;

        frame = gib_shadowstack_pop(wstack);
        loc_3050 = frame->ptr;
        end_r_3051 = frame->endptr;

        GibInt fltAppE_1214_1479 = n_296_897_1474 - 1;

        gib_shadowstack_push(rstack, pvrtmp_10550, pvrtmp_10549, Stk, Ps_T);
        gib_shadowstack_push(wstack, loc_3050, end_r_3051, Stk, Ps_T);

        GibChunk region_10556 = gib_alloc_region(gib_get_inf_init_chunk_size());
        GibCursor r_3809 = region_10556.start;
        GibCursor end_r_3809 = region_10556.end;

        frame = gib_shadowstack_pop(wstack);
        loc_3050 = frame->ptr;
        end_r_3051 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        pvrtmp_10550 = frame->ptr;
        pvrtmp_10549 = frame->endptr;
        gib_shadowstack_push(rstack, pvrtmp_10550, pvrtmp_10549, Stk, Ps_T);
        gib_shadowstack_push(wstack, loc_3050, end_r_3051, Stk, Ps_T);

        GibCursorGibCursorGibCursorProd tmp_struct_186 =
                                         ts(end_r_3809, r_3809, fltAppE_1214_1479);
        GibCursor pvrtmp_10557 = tmp_struct_186.field0;
        GibCursor pvrtmp_10558 = tmp_struct_186.field1;
        GibCursor pvrtmp_10559 = tmp_struct_186.field2;

        frame = gib_shadowstack_pop(wstack);
        loc_3050 = frame->ptr;
        end_r_3051 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        pvrtmp_10550 = frame->ptr;
        pvrtmp_10549 = frame->endptr;
        gib_shadowstack_push(rstack, pvrtmp_10550, pvrtmp_10549, Stk, Ps_T);
        gib_shadowstack_push(rstack, pvrtmp_10558, pvrtmp_10557, Stk, Ps_T);
        gib_shadowstack_push(wstack, loc_3050, end_r_3051, Stk, Ps_T);

        GibChunk region_10564 = gib_alloc_region(gib_get_inf_init_chunk_size());
        GibCursor r_3808 = region_10564.start;
        GibCursor end_r_3808 = region_10564.end;

        frame = gib_shadowstack_pop(wstack);
        loc_3050 = frame->ptr;
        end_r_3051 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        pvrtmp_10558 = frame->ptr;
        pvrtmp_10557 = frame->endptr;
        frame = gib_shadowstack_pop(rstack);
        pvrtmp_10550 = frame->ptr;
        pvrtmp_10549 = frame->endptr;
        gib_shadowstack_push(wstack, loc_3050, end_r_3051, Stk, Ps_T);

        GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_187 =
                                                           psMult(pvrtmp_10549, pvrtmp_10557, end_r_3808, r_3808, pvrtmp_10550, pvrtmp_10558);
        GibCursor pvrtmp_10565 = tmp_struct_187.field0;
        GibCursor pvrtmp_10566 = tmp_struct_187.field1;
        GibCursor pvrtmp_10567 = tmp_struct_187.field2;
        GibCursor pvrtmp_10568 = tmp_struct_187.field3;
        GibCursor pvrtmp_10569 = tmp_struct_187.field4;

        frame = gib_shadowstack_pop(wstack);
        loc_3050 = frame->ptr;
        end_r_3051 = frame->endptr;

        GibCursor loc_3806 = loc_3050 + 5;

        *(GibPackedTag *) loc_3050 = 1;

        GibCursor writetag_7064 = loc_3050 + 1;
        GibCursor after_tag_7065 = loc_3050 + 1;

        *(GibFloat *) after_tag_7065 = 1.0;

        GibCursor writecur_7069 = after_tag_7065 + sizeof(GibFloat);
        GibCursorGibCursorGibCursorGibCursorProd tmp_struct_188 =
                                                  takePs(pvrtmp_10567, end_r_3051, loc_3806, fltAppE_1209_1476, pvrtmp_10568);
        GibCursor pvrtmp_10574 = tmp_struct_188.field0;
        GibCursor pvrtmp_10575 = tmp_struct_188.field1;
        GibCursor pvrtmp_10576 = tmp_struct_188.field2;
        GibCursor pvrtmp_10577 = tmp_struct_188.field3;

        return (GibCursorGibCursorGibCursorProd) {pvrtmp_10575, loc_3050,
                                                  pvrtmp_10577};
    }
}
GibCursorGibCursorGibCursorGibCursorProd takePs(GibCursor end_r_3054,
                                                GibCursor end_r_3055,
                                                GibCursor loc_3053,
                                                GibInt n_297_898_1483,
                                                GibCursor fs_298_899_1484)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_3053 + 18 > end_r_3055) {
        gib_grow_region(&loc_3053, &end_r_3055);
    }

    GibBool fltIf_1215_1485 = n_297_898_1483 == 0;

    if (fltIf_1215_1485) {
        *(GibPackedTag *) loc_3053 = 0;

        GibCursor writetag_7073 = loc_3053 + 1;
        GibCursor after_tag_7074 = loc_3053 + 1;

        return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_3054,
                                                           end_r_3055, loc_3053,
                                                           after_tag_7074};
    } else {
        GibCursorGibCursorGibCursorGibCursorProd tmp_struct_192 =
                                                  caseFn_825(end_r_3054, end_r_3055, loc_3053, n_297_898_1483, fs_298_899_1484);
        GibCursor pvrtmp_10590 = tmp_struct_192.field0;
        GibCursor pvrtmp_10591 = tmp_struct_192.field1;
        GibCursor pvrtmp_10592 = tmp_struct_192.field2;
        GibCursor pvrtmp_10593 = tmp_struct_192.field3;

        return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_10590,
                                                           pvrtmp_10591,
                                                           pvrtmp_10592,
                                                           pvrtmp_10593};
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd psDiv(GibCursor end_r_3059,
                                                        GibCursor end_r_3060,
                                                        GibCursor end_r_3061,
                                                        GibCursor loc_3058,
                                                        GibInt n_301_900_1486,
                                                        GibCursor a_302_901_1487,
                                                        GibCursor b_303_902_1488)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_3058 + 18 > end_r_3061) {
        gib_grow_region(&loc_3058, &end_r_3061);
    }

    GibBool fltIf_1216_1489 = n_301_900_1486 == 0;

    if (fltIf_1216_1489) {
        *(GibPackedTag *) loc_3058 = 0;

        GibCursor writetag_7083 = loc_3058 + 1;
        GibCursor after_tag_7084 = loc_3058 + 1;

        return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3059,
                                                                    end_r_3060,
                                                                    end_r_3061,
                                                                    loc_3058,
                                                                    after_tag_7084};
    } else {
        GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_196 =
                                                           caseFn_836(end_r_3059, end_r_3060, end_r_3061, loc_3058, n_301_900_1486, a_302_901_1487, b_303_902_1488);
        GibCursor pvrtmp_10604 = tmp_struct_196.field0;
        GibCursor pvrtmp_10605 = tmp_struct_196.field1;
        GibCursor pvrtmp_10606 = tmp_struct_196.field2;
        GibCursor pvrtmp_10607 = tmp_struct_196.field3;
        GibCursor pvrtmp_10608 = tmp_struct_196.field4;

        return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_10604,
                                                                    pvrtmp_10605,
                                                                    pvrtmp_10606,
                                                                    pvrtmp_10607,
                                                                    pvrtmp_10608};
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd psMult(GibCursor end_r_3065,
                                                         GibCursor end_r_3066,
                                                         GibCursor end_r_3067,
                                                         GibCursor loc_3064,
                                                         GibCursor a_311_903_1490,
                                                         GibCursor b_312_904_1491)
{
    // GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    // GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    // GibShadowstackFrame *frame;

    if (loc_3064 + 18 > end_r_3067) {
        gib_grow_region(&loc_3064, &end_r_3067);
    }

    GibPackedTag tmpval_10615 = *(GibPackedTag *) a_311_903_1490;
    GibCursor tmpcur_10616 = a_311_903_1490 + 1;


  switch_10667:
    ;
    switch (tmpval_10615) {

      case 0:
        {
            *(GibPackedTag *) loc_3064 = 0;

            GibCursor writetag_7095 = loc_3064 + 1;
            GibCursor after_tag_7096 = loc_3064 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3065,
                                                                        end_r_3066,
                                                                        end_r_3067,
                                                                        loc_3064,
                                                                        after_tag_7096};
            break;
        }

      case 1:
        {
            GibFloat tmpval_10621 = *(GibFloat *) tmpcur_10616;
            GibCursor tmpcur_10622 = tmpcur_10616 + sizeof(GibFloat);
            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_200 =
             caseFn_840(end_r_3066, end_r_3065, end_r_3067, loc_3064, b_312_904_1491, tmpval_10621, tmpcur_10622);
            GibCursor pvrtmp_10623 = tmp_struct_200.field0;
            GibCursor pvrtmp_10624 = tmp_struct_200.field1;
            GibCursor pvrtmp_10625 = tmp_struct_200.field2;
            GibCursor pvrtmp_10626 = tmp_struct_200.field3;
            GibCursor pvrtmp_10627 = tmp_struct_200.field4;
            GibCursor pvrtmp_10628 = tmp_struct_200.field5;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_10624,
                                                                        pvrtmp_10623,
                                                                        pvrtmp_10625,
                                                                        pvrtmp_10627,
                                                                        pvrtmp_10628};
            break;
        }

      case 2:
        {
            *(GibPackedTag *) loc_3064 = 2;

            GibCursor writetag_7109 = loc_3064 + 1;
            GibCursor after_tag_7110 = loc_3064 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3065,
                                                                        end_r_3066,
                                                                        end_r_3067,
                                                                        loc_3064,
                                                                        after_tag_7110};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_202 = *(uintptr_t *) tmpcur_10616;
            GibCursor tmpcur_10639 = GIB_UNTAG(tagged_tmpcur_202);
            GibCursor tmpaftercur_10640 = tmpcur_10616 + 8;
            uint16_t tmptag_10641 = GIB_GET_TAG(tagged_tmpcur_202);
            GibCursor end_from_tagged_indr_4643 = tmpcur_10639 + tmptag_10641;
            GibCursor jump_4645 = tmpcur_10616 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_201 =
                                                               psMult(end_from_tagged_indr_4643, end_r_3066, end_r_3067, loc_3064, tmpcur_10639, b_312_904_1491);
            GibCursor pvrtmp_10642 = tmp_struct_201.field0;
            GibCursor pvrtmp_10643 = tmp_struct_201.field1;
            GibCursor pvrtmp_10644 = tmp_struct_201.field2;
            GibCursor pvrtmp_10645 = tmp_struct_201.field3;
            GibCursor pvrtmp_10646 = tmp_struct_201.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3065,
                                                                        pvrtmp_10643,
                                                                        pvrtmp_10644,
                                                                        pvrtmp_10645,
                                                                        pvrtmp_10646};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_204 = *(uintptr_t *) tmpcur_10616;
            GibCursor tmpcur_10653 = GIB_UNTAG(tagged_tmpcur_204);
            GibCursor tmpaftercur_10654 = tmpcur_10616 + 8;
            uint16_t tmptag_10655 = GIB_GET_TAG(tagged_tmpcur_204);
            GibCursor end_from_tagged_indr_4643 = tmpcur_10653 + tmptag_10655;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_203 =
                                                               psMult(end_from_tagged_indr_4643, end_r_3066, end_r_3067, loc_3064, tmpcur_10653, b_312_904_1491);
            GibCursor pvrtmp_10656 = tmp_struct_203.field0;
            GibCursor pvrtmp_10657 = tmp_struct_203.field1;
            GibCursor pvrtmp_10658 = tmp_struct_203.field2;
            GibCursor pvrtmp_10659 = tmp_struct_203.field3;
            GibCursor pvrtmp_10660 = tmp_struct_203.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_10656,
                                                                        pvrtmp_10657,
                                                                        pvrtmp_10658,
                                                                        pvrtmp_10659,
                                                                        pvrtmp_10660};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_10615");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd psAdd(GibCursor end_r_3071,
                                                        GibCursor end_r_3072,
                                                        GibCursor end_r_3073,
                                                        GibCursor loc_3070,
                                                        GibCursor a_317_907_1494,
                                                        GibCursor b_318_908_1495)
{
    // GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    // GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    // GibShadowstackFrame *frame;

    if (loc_3070 + 18 > end_r_3073) {
        gib_grow_region(&loc_3070, &end_r_3073);
    }

    GibPackedTag tmpval_10668 = *(GibPackedTag *) a_317_907_1494;
    GibCursor tmpcur_10669 = a_317_907_1494 + 1;


  switch_10720:
    ;
    switch (tmpval_10668) {

      case 0:
        {
            // if (loc_3070 + 18 > end_r_3073) {
            //     gib_grow_region(&loc_3070, &end_r_3073);
            // }
            gib_indirection_barrier(loc_3070, end_r_3073, b_318_908_1495,
                                    end_r_3072, Ps_T);

            GibCursor end_7130 = loc_3070 + 9;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3071,
                                                                        end_r_3072,
                                                                        end_r_3073,
                                                                        loc_3070,
                                                                        end_7130};
            break;
        }

      case 1:
        {
            GibFloat tmpval_10674 = *(GibFloat *) tmpcur_10669;
            GibCursor tmpcur_10675 = tmpcur_10669 + sizeof(GibFloat);
            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_211 =
             caseFn_844(end_r_3071, end_r_3072, end_r_3071, end_r_3073, loc_3070, a_317_907_1494, b_318_908_1495, tmpval_10674, tmpcur_10675);
            GibCursor pvrtmp_10676 = tmp_struct_211.field0;
            GibCursor pvrtmp_10677 = tmp_struct_211.field1;
            GibCursor pvrtmp_10678 = tmp_struct_211.field2;
            GibCursor pvrtmp_10679 = tmp_struct_211.field3;
            GibCursor pvrtmp_10680 = tmp_struct_211.field4;
            GibCursor pvrtmp_10681 = tmp_struct_211.field5;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_10678,
                                                                        pvrtmp_10677,
                                                                        pvrtmp_10679,
                                                                        pvrtmp_10680,
                                                                        pvrtmp_10681};
            break;
        }

      case 2:
        {
            *(GibPackedTag *) loc_3070 = 2;

            GibCursor writetag_7140 = loc_3070 + 1;
            GibCursor after_tag_7141 = loc_3070 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3071,
                                                                        end_r_3072,
                                                                        end_r_3073,
                                                                        loc_3070,
                                                                        after_tag_7141};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_213 = *(uintptr_t *) tmpcur_10669;
            GibCursor tmpcur_10692 = GIB_UNTAG(tagged_tmpcur_213);
            GibCursor tmpaftercur_10693 = tmpcur_10669 + 8;
            uint16_t tmptag_10694 = GIB_GET_TAG(tagged_tmpcur_213);
            GibCursor end_from_tagged_indr_4648 = tmpcur_10692 + tmptag_10694;
            GibCursor jump_4650 = tmpcur_10669 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_212 =
                                                               psAdd(end_from_tagged_indr_4648, end_r_3072, end_r_3073, loc_3070, tmpcur_10692, b_318_908_1495);
            GibCursor pvrtmp_10695 = tmp_struct_212.field0;
            GibCursor pvrtmp_10696 = tmp_struct_212.field1;
            GibCursor pvrtmp_10697 = tmp_struct_212.field2;
            GibCursor pvrtmp_10698 = tmp_struct_212.field3;
            GibCursor pvrtmp_10699 = tmp_struct_212.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3071,
                                                                        pvrtmp_10696,
                                                                        pvrtmp_10697,
                                                                        pvrtmp_10698,
                                                                        pvrtmp_10699};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_215 = *(uintptr_t *) tmpcur_10669;
            GibCursor tmpcur_10706 = GIB_UNTAG(tagged_tmpcur_215);
            GibCursor tmpaftercur_10707 = tmpcur_10669 + 8;
            uint16_t tmptag_10708 = GIB_GET_TAG(tagged_tmpcur_215);
            GibCursor end_from_tagged_indr_4648 = tmpcur_10706 + tmptag_10708;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_214 =
                                                               psAdd(end_from_tagged_indr_4648, end_r_3072, end_r_3073, loc_3070, tmpcur_10706, b_318_908_1495);
            GibCursor pvrtmp_10709 = tmp_struct_214.field0;
            GibCursor pvrtmp_10710 = tmp_struct_214.field1;
            GibCursor pvrtmp_10711 = tmp_struct_214.field2;
            GibCursor pvrtmp_10712 = tmp_struct_214.field3;
            GibCursor pvrtmp_10713 = tmp_struct_214.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_10709,
                                                                        pvrtmp_10710,
                                                                        pvrtmp_10711,
                                                                        pvrtmp_10712,
                                                                        pvrtmp_10713};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_10668");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd psNeg(GibCursor end_r_3076,
                                                        GibCursor end_r_3077,
                                                        GibCursor loc_3075,
                                                        GibCursor a_323_911_1498)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_3075 + 18 > end_r_3077) {
        gib_grow_region(&loc_3075, &end_r_3077);
    }

    GibPackedTag tmpval_10721 = *(GibPackedTag *) a_323_911_1498;
    GibCursor tmpcur_10722 = a_323_911_1498 + 1;


  switch_10774:
    ;
    switch (tmpval_10721) {

      case 0:
        {
            GibCursor jump_4425 = a_323_911_1498 + 1;

            *(GibPackedTag *) loc_3075 = 0;

            GibCursor writetag_7160 = loc_3075 + 1;
            GibCursor after_tag_7161 = loc_3075 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3076,
                                                                        end_r_3077,
                                                                        jump_4425,
                                                                        loc_3075,
                                                                        after_tag_7161};
            break;
        }

      case 1:
        {
            GibFloat tmpval_10727 = *(GibFloat *) tmpcur_10722;
            GibCursor tmpcur_10728 = tmpcur_10722 + sizeof(GibFloat);
            GibFloat fltPkd_1217_1501 = 0.0 - tmpval_10727;
            GibCursor loc_3857 = loc_3075 + 5;

            *(GibPackedTag *) loc_3075 = 1;

            GibCursor writetag_7172 = loc_3075 + 1;
            GibCursor after_tag_7173 = loc_3075 + 1;

            *(GibFloat *) after_tag_7173 = fltPkd_1217_1501;

            GibCursor writecur_7177 = after_tag_7173 + sizeof(GibFloat);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_219 =
                                                               psNeg(end_r_3076, end_r_3077, loc_3857, tmpcur_10728);
            GibCursor pvrtmp_10729 = tmp_struct_219.field0;
            GibCursor pvrtmp_10730 = tmp_struct_219.field1;
            GibCursor pvrtmp_10731 = tmp_struct_219.field2;
            GibCursor pvrtmp_10732 = tmp_struct_219.field3;
            GibCursor pvrtmp_10733 = tmp_struct_219.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_10729,
                                                                        pvrtmp_10730,
                                                                        pvrtmp_10731,
                                                                        loc_3075,
                                                                        pvrtmp_10733};
            break;
        }

      case 2:
        {
            GibCursor jump_4430 = a_323_911_1498 + 1;

            *(GibPackedTag *) loc_3075 = 2;

            GibCursor writetag_7182 = loc_3075 + 1;
            GibCursor after_tag_7183 = loc_3075 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3076,
                                                                        end_r_3077,
                                                                        jump_4430,
                                                                        loc_3075,
                                                                        after_tag_7183};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_221 = *(uintptr_t *) tmpcur_10722;
            GibCursor tmpcur_10746 = GIB_UNTAG(tagged_tmpcur_221);
            GibCursor tmpaftercur_10747 = tmpcur_10722 + 8;
            uint16_t tmptag_10748 = GIB_GET_TAG(tagged_tmpcur_221);
            GibCursor end_from_tagged_indr_4653 = tmpcur_10746 + tmptag_10748;
            GibCursor jump_4655 = tmpcur_10722 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_220 =
                                                               psNeg(end_from_tagged_indr_4653, end_r_3077, loc_3075, tmpcur_10746);
            GibCursor pvrtmp_10749 = tmp_struct_220.field0;
            GibCursor pvrtmp_10750 = tmp_struct_220.field1;
            GibCursor pvrtmp_10751 = tmp_struct_220.field2;
            GibCursor pvrtmp_10752 = tmp_struct_220.field3;
            GibCursor pvrtmp_10753 = tmp_struct_220.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3076,
                                                                        pvrtmp_10750,
                                                                        jump_4655,
                                                                        pvrtmp_10752,
                                                                        pvrtmp_10753};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_223 = *(uintptr_t *) tmpcur_10722;
            GibCursor tmpcur_10760 = GIB_UNTAG(tagged_tmpcur_223);
            GibCursor tmpaftercur_10761 = tmpcur_10722 + 8;
            uint16_t tmptag_10762 = GIB_GET_TAG(tagged_tmpcur_223);
            GibCursor end_from_tagged_indr_4653 = tmpcur_10760 + tmptag_10762;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_222 =
                                                               psNeg(end_from_tagged_indr_4653, end_r_3077, loc_3075, tmpcur_10760);
            GibCursor pvrtmp_10763 = tmp_struct_222.field0;
            GibCursor pvrtmp_10764 = tmp_struct_222.field1;
            GibCursor pvrtmp_10765 = tmp_struct_222.field2;
            GibCursor pvrtmp_10766 = tmp_struct_222.field3;
            GibCursor pvrtmp_10767 = tmp_struct_222.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_10763,
                                                                        pvrtmp_10764,
                                                                        pvrtmp_10765,
                                                                        pvrtmp_10766,
                                                                        pvrtmp_10767};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_10721");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorProd psX(GibCursor end_r_3079, GibCursor loc_3078)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_3078 + 18 > end_r_3079) {
        gib_grow_region(&loc_3078, &end_r_3079);
    }

    GibCursor loc_3869 = loc_3078 + 5;
    GibCursor loc_3866 = loc_3078 + 10;

    *(GibPackedTag *) loc_3078 = 1;

    GibCursor writetag_7215 = loc_3078 + 1;
    GibCursor after_tag_7216 = loc_3078 + 1;

    *(GibFloat *) after_tag_7216 = 0.0;

    GibCursor writecur_7220 = after_tag_7216 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3866 = 0;

    GibCursor writetag_7199 = loc_3866 + 1;
    GibCursor after_tag_7200 = loc_3866 + 1;

    *(GibPackedTag *) loc_3869 = 1;

    GibCursor writetag_7206 = loc_3869 + 1;
    GibCursor after_tag_7207 = loc_3869 + 1;

    *(GibFloat *) after_tag_7207 = 1.0;

    GibCursor writecur_7211 = after_tag_7207 + sizeof(GibFloat);

    return (GibCursorGibCursorGibCursorProd) {end_r_3079, loc_3078,
                                              after_tag_7200};
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd dot(GibCursor end_r_3082,
                                                      GibCursor end_r_3083,
                                                      GibCursor loc_3081,
                                                      GibFloat c_326_914_1505,
                                                      GibCursor b_327_915_1506)
{
    // GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    // GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    // GibShadowstackFrame *frame;

    if (loc_3081 + 18 > end_r_3083) {
        gib_grow_region(&loc_3081, &end_r_3083);
    }

    GibPackedTag tmpval_10783 = *(GibPackedTag *) b_327_915_1506;
    GibCursor tmpcur_10784 = b_327_915_1506 + 1;


  switch_10836:
    ;
    switch (tmpval_10783) {

      case 0:
        {
            GibCursor jump_4433 = b_327_915_1506 + 1;

            *(GibPackedTag *) loc_3081 = 0;

            GibCursor writetag_7225 = loc_3081 + 1;
            GibCursor after_tag_7226 = loc_3081 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3082,
                                                                        end_r_3083,
                                                                        jump_4433,
                                                                        loc_3081,
                                                                        after_tag_7226};
            break;
        }

      case 1:
        {
            GibFloat tmpval_10789 = *(GibFloat *) tmpcur_10784;
            GibCursor tmpcur_10790 = tmpcur_10784 + sizeof(GibFloat);
            GibFloat fltPkd_1221_1509 = c_326_914_1505 * tmpval_10789;
            GibCursor loc_3880 = loc_3081 + 5;

            *(GibPackedTag *) loc_3081 = 1;

            GibCursor writetag_7237 = loc_3081 + 1;
            GibCursor after_tag_7238 = loc_3081 + 1;

            *(GibFloat *) after_tag_7238 = fltPkd_1221_1509;

            GibCursor writecur_7242 = after_tag_7238 + sizeof(GibFloat);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_230 =
                                                               dot(end_r_3082, end_r_3083, loc_3880, c_326_914_1505, tmpcur_10790);
            GibCursor pvrtmp_10791 = tmp_struct_230.field0;
            GibCursor pvrtmp_10792 = tmp_struct_230.field1;
            GibCursor pvrtmp_10793 = tmp_struct_230.field2;
            GibCursor pvrtmp_10794 = tmp_struct_230.field3;
            GibCursor pvrtmp_10795 = tmp_struct_230.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_10791,
                                                                        pvrtmp_10792,
                                                                        pvrtmp_10793,
                                                                        loc_3081,
                                                                        pvrtmp_10795};
            break;
        }

      case 2:
        {
            GibCursor jump_4438 = b_327_915_1506 + 1;

            *(GibPackedTag *) loc_3081 = 2;

            GibCursor writetag_7247 = loc_3081 + 1;
            GibCursor after_tag_7248 = loc_3081 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3082,
                                                                        end_r_3083,
                                                                        jump_4438,
                                                                        loc_3081,
                                                                        after_tag_7248};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_232 = *(uintptr_t *) tmpcur_10784;
            GibCursor tmpcur_10808 = GIB_UNTAG(tagged_tmpcur_232);
            GibCursor tmpaftercur_10809 = tmpcur_10784 + 8;
            uint16_t tmptag_10810 = GIB_GET_TAG(tagged_tmpcur_232);
            GibCursor end_from_tagged_indr_4659 = tmpcur_10808 + tmptag_10810;
            GibCursor jump_4661 = tmpcur_10784 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_231 =
                                                               dot(end_from_tagged_indr_4659, end_r_3083, loc_3081, c_326_914_1505, tmpcur_10808);
            GibCursor pvrtmp_10811 = tmp_struct_231.field0;
            GibCursor pvrtmp_10812 = tmp_struct_231.field1;
            GibCursor pvrtmp_10813 = tmp_struct_231.field2;
            GibCursor pvrtmp_10814 = tmp_struct_231.field3;
            GibCursor pvrtmp_10815 = tmp_struct_231.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3082,
                                                                        pvrtmp_10812,
                                                                        jump_4661,
                                                                        pvrtmp_10814,
                                                                        pvrtmp_10815};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_234 = *(uintptr_t *) tmpcur_10784;
            GibCursor tmpcur_10822 = GIB_UNTAG(tagged_tmpcur_234);
            GibCursor tmpaftercur_10823 = tmpcur_10784 + 8;
            uint16_t tmptag_10824 = GIB_GET_TAG(tagged_tmpcur_234);
            GibCursor end_from_tagged_indr_4659 = tmpcur_10822 + tmptag_10824;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_233 =
                                                               dot(end_from_tagged_indr_4659, end_r_3083, loc_3081, c_326_914_1505, tmpcur_10822);
            GibCursor pvrtmp_10825 = tmp_struct_233.field0;
            GibCursor pvrtmp_10826 = tmp_struct_233.field1;
            GibCursor pvrtmp_10827 = tmp_struct_233.field2;
            GibCursor pvrtmp_10828 = tmp_struct_233.field3;
            GibCursor pvrtmp_10829 = tmp_struct_233.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_10825,
                                                                        pvrtmp_10826,
                                                                        pvrtmp_10827,
                                                                        pvrtmp_10828,
                                                                        pvrtmp_10829};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_10783");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorProd pone(GibCursor end_r_3085, GibCursor loc_3084)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_3084 + 18 > end_r_3085) {
        gib_grow_region(&loc_3084, &end_r_3085);
    }

    GibCursor loc_3888 = loc_3084 + 5;

    *(GibPackedTag *) loc_3084 = 1;

    GibCursor writetag_7271 = loc_3084 + 1;
    GibCursor after_tag_7272 = loc_3084 + 1;

    *(GibFloat *) after_tag_7272 = 1.0;

    GibCursor writecur_7276 = after_tag_7272 + sizeof(GibFloat);

    *(GibPackedTag *) loc_3888 = 0;

    GibCursor writetag_7264 = loc_3888 + 1;
    GibCursor after_tag_7265 = loc_3888 + 1;

    return (GibCursorGibCursorGibCursorProd) {end_r_3085, loc_3084,
                                              after_tag_7265};
}
GibCursorGibCursorGibIntProd size(GibCursor end_r_3087,
                                  GibCursor ls_330_918_1512)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_10843 = *(GibPackedTag *) ls_330_918_1512;
    GibCursor tmpcur_10844 = ls_330_918_1512 + 1;


  switch_10862:
    ;
    switch (tmpval_10843) {

      case 0:
        {
            GibCursor jump_4442 = ls_330_918_1512 + 1;

            return (GibCursorGibCursorGibIntProd) {end_r_3087, jump_4442, 0};
            break;
        }

      case 1:
        {
            GibFloat tmpval_10845 = *(GibFloat *) tmpcur_10844;
            GibCursor tmpcur_10846 = tmpcur_10844 + sizeof(GibFloat);
            GibCursorGibCursorGibIntProd tmp_struct_241 =
                                          size(end_r_3087, tmpcur_10846);
            GibCursor pvrtmp_10847 = tmp_struct_241.field0;
            GibCursor pvrtmp_10848 = tmp_struct_241.field1;
            GibInt pvrtmp_10849 = tmp_struct_241.field2;
            GibInt tailprim_4445 = 1 + pvrtmp_10849;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_10847, pvrtmp_10848,
                                                   tailprim_4445};
            break;
        }

      case 2:
        {
            GibCursor jump_4446 = ls_330_918_1512 + 1;
            GibInt tailprim_4447 = 0 - 1;

            return (GibCursorGibCursorGibIntProd) {end_r_3087, jump_4446,
                                                   tailprim_4447};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_243 = *(uintptr_t *) tmpcur_10844;
            GibCursor tmpcur_10850 = GIB_UNTAG(tagged_tmpcur_243);
            GibCursor tmpaftercur_10851 = tmpcur_10844 + 8;
            uint16_t tmptag_10852 = GIB_GET_TAG(tagged_tmpcur_243);
            GibCursor end_from_tagged_indr_4665 = tmpcur_10850 + tmptag_10852;
            GibCursor jump_4667 = tmpcur_10844 + 8;
            GibCursorGibCursorGibIntProd tmp_struct_242 =
                                          size(end_from_tagged_indr_4665, tmpcur_10850);
            GibCursor pvrtmp_10853 = tmp_struct_242.field0;
            GibCursor pvrtmp_10854 = tmp_struct_242.field1;
            GibInt pvrtmp_10855 = tmp_struct_242.field2;

            return (GibCursorGibCursorGibIntProd) {end_r_3087, jump_4667,
                                                   pvrtmp_10855};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_245 = *(uintptr_t *) tmpcur_10844;
            GibCursor tmpcur_10856 = GIB_UNTAG(tagged_tmpcur_245);
            GibCursor tmpaftercur_10857 = tmpcur_10844 + 8;
            uint16_t tmptag_10858 = GIB_GET_TAG(tagged_tmpcur_245);
            GibCursor end_from_tagged_indr_4665 = tmpcur_10856 + tmptag_10858;
            GibCursorGibCursorGibIntProd tmp_struct_244 =
                                          size(end_from_tagged_indr_4665, tmpcur_10856);
            GibCursor pvrtmp_10859 = tmp_struct_244.field0;
            GibCursor pvrtmp_10860 = tmp_struct_244.field1;
            GibInt pvrtmp_10861 = tmp_struct_244.field2;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_10859, pvrtmp_10860,
                                                   pvrtmp_10861};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_10843");
            exit(1);
        }
    }
}
unsigned char print_check(GibBool b_333_921_1516)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (b_333_921_1516) {
        unsigned char wildcard__14_334_922_1517 = gib_print_symbol(9421);

        return 0;
    } else {
        unsigned char wildcard__16_335_923_1518 = gib_print_symbol(9422);

        return 0;
    }
}
unsigned char print_space(unsigned char wildcard__20_336_924_1519)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    unsigned char tailprim_4450 = gib_print_symbol(9432);

    return tailprim_4450;
}
unsigned char print_newline(unsigned char wildcard__18_337_925_1520)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    unsigned char tailprim_4451 = gib_print_symbol(9433);

    return tailprim_4451;
}
GibInt compare_int(GibInt r1_338_926_1521, GibInt r2_339_927_1522)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_1225_1523 = r1_338_926_1521 < r2_339_927_1522;

    if (fltIf_1225_1523) {
        GibInt tailprim_4454 = 0 - 1;

        return tailprim_4454;
    } else {
        GibBool fltIf_1226_1524 = r1_338_926_1521 > r2_339_927_1522;

        if (fltIf_1226_1524) {
            return 1;
        } else {
            return 0;
        }
    }
}
GibInt compare_float(GibFloat r1_340_928_1525, GibFloat r2_341_929_1526)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_1227_1527 = r1_340_928_1525 < r2_341_929_1526;

    if (fltIf_1227_1527) {
        GibInt tailprim_4457 = 0 - 1;

        return tailprim_4457;
    } else {
        GibBool fltIf_1228_1528 = r1_340_928_1525 > r2_341_929_1526;

        if (fltIf_1228_1528) {
            return 1;
        } else {
            return 0;
        }
    }
}
GibFloat float_abs(GibFloat f_342_930_1529)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_1229_1530 = f_342_930_1529 < 0.0;

    if (fltIf_1229_1530) {
        GibFloat fltPrm_1230_1531 = 0.0 - 1.0;
        GibFloat tailprim_4458 = f_342_930_1529 * fltPrm_1230_1531;

        return tailprim_4458;
    } else {
        return f_342_930_1529;
    }
}
GibFloat minFloat(GibFloat a_343_931_1532, GibFloat b_344_932_1533)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_1231_1534 = a_343_931_1532 < b_344_932_1533;

    if (fltIf_1231_1534) {
        return a_343_931_1532;
    } else {
        return b_344_932_1533;
    }
}
GibFloat maxFloat(GibFloat a_345_933_1535, GibFloat b_346_934_1536)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_1232_1537 = a_345_933_1535 > b_346_934_1536;

    if (fltIf_1232_1537) {
        return a_345_933_1535;
    } else {
        return b_346_934_1536;
    }
}
GibInt minInt(GibInt a_347_935_1538, GibInt b_348_936_1539)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_1233_1540 = a_347_935_1538 < b_348_936_1539;

    if (fltIf_1233_1540) {
        return a_347_935_1538;
    } else {
        return b_348_936_1539;
    }
}
GibInt maxInt(GibInt a_349_937_1541, GibInt b_350_938_1542)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_1234_1543 = a_349_937_1541 > b_350_938_1542;

    if (fltIf_1234_1543) {
        return a_349_937_1541;
    } else {
        return b_350_938_1542;
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_Ps(GibCursor end_r_3090,
                                                           GibCursor end_r_3091,
                                                           GibCursor loc_3089,
                                                           GibCursor arg_743_939_1544)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_3089 + 18 > end_r_3091) {
        gib_grow_region(&loc_3089, &end_r_3091);
    }

    GibPackedTag tmpval_10863 = *(GibPackedTag *) arg_743_939_1544;
    GibCursor tmpcur_10864 = arg_743_939_1544 + 1;


  switch_10916:
    ;
    switch (tmpval_10863) {

      case 0:
        {
            GibCursor jump_4459 = arg_743_939_1544 + 1;

            *(GibPackedTag *) loc_3089 = 0;

            GibCursor writetag_7295 = loc_3089 + 1;
            GibCursor after_tag_7296 = loc_3089 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3090,
                                                                        end_r_3091,
                                                                        jump_4459,
                                                                        loc_3089,
                                                                        after_tag_7296};
            break;
        }

      case 1:
        {
            GibFloat tmpval_10869 = *(GibFloat *) tmpcur_10864;
            GibCursor tmpcur_10870 = tmpcur_10864 + sizeof(GibFloat);
            GibCursor loc_3905 = loc_3089 + 5;

            *(GibPackedTag *) loc_3089 = 1;

            GibCursor writetag_7307 = loc_3089 + 1;
            GibCursor after_tag_7308 = loc_3089 + 1;

            *(GibFloat *) after_tag_7308 = tmpval_10869;

            GibCursor writecur_7312 = after_tag_7308 + sizeof(GibFloat);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_246 =
                                                               _copy_Ps(end_r_3090, end_r_3091, loc_3905, tmpcur_10870);
            GibCursor pvrtmp_10871 = tmp_struct_246.field0;
            GibCursor pvrtmp_10872 = tmp_struct_246.field1;
            GibCursor pvrtmp_10873 = tmp_struct_246.field2;
            GibCursor pvrtmp_10874 = tmp_struct_246.field3;
            GibCursor pvrtmp_10875 = tmp_struct_246.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_10871,
                                                                        pvrtmp_10872,
                                                                        pvrtmp_10873,
                                                                        loc_3089,
                                                                        pvrtmp_10875};
            break;
        }

      case 2:
        {
            GibCursor jump_4464 = arg_743_939_1544 + 1;

            *(GibPackedTag *) loc_3089 = 2;

            GibCursor writetag_7317 = loc_3089 + 1;
            GibCursor after_tag_7318 = loc_3089 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3090,
                                                                        end_r_3091,
                                                                        jump_4464,
                                                                        loc_3089,
                                                                        after_tag_7318};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_248 = *(uintptr_t *) tmpcur_10864;
            GibCursor tmpcur_10888 = GIB_UNTAG(tagged_tmpcur_248);
            GibCursor tmpaftercur_10889 = tmpcur_10864 + 8;
            uint16_t tmptag_10890 = GIB_GET_TAG(tagged_tmpcur_248);
            GibCursor end_from_tagged_indr_4671 = tmpcur_10888 + tmptag_10890;
            GibCursor jump_4673 = tmpcur_10864 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_247 =
                                                               _copy_Ps(end_from_tagged_indr_4671, end_r_3091, loc_3089, tmpcur_10888);
            GibCursor pvrtmp_10891 = tmp_struct_247.field0;
            GibCursor pvrtmp_10892 = tmp_struct_247.field1;
            GibCursor pvrtmp_10893 = tmp_struct_247.field2;
            GibCursor pvrtmp_10894 = tmp_struct_247.field3;
            GibCursor pvrtmp_10895 = tmp_struct_247.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3090,
                                                                        pvrtmp_10892,
                                                                        jump_4673,
                                                                        pvrtmp_10894,
                                                                        pvrtmp_10895};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_250 = *(uintptr_t *) tmpcur_10864;
            GibCursor tmpcur_10902 = GIB_UNTAG(tagged_tmpcur_250);
            GibCursor tmpaftercur_10903 = tmpcur_10864 + 8;
            uint16_t tmptag_10904 = GIB_GET_TAG(tagged_tmpcur_250);
            GibCursor end_from_tagged_indr_4671 = tmpcur_10902 + tmptag_10904;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_249 =
                                                               _copy_Ps(end_from_tagged_indr_4671, end_r_3091, loc_3089, tmpcur_10902);
            GibCursor pvrtmp_10905 = tmp_struct_249.field0;
            GibCursor pvrtmp_10906 = tmp_struct_249.field1;
            GibCursor pvrtmp_10907 = tmp_struct_249.field2;
            GibCursor pvrtmp_10908 = tmp_struct_249.field3;
            GibCursor pvrtmp_10909 = tmp_struct_249.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_10905,
                                                                        pvrtmp_10906,
                                                                        pvrtmp_10907,
                                                                        pvrtmp_10908,
                                                                        pvrtmp_10909};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_10863");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_Ps(GibCursor end_r_3094,
                                                                        GibCursor end_r_3095,
                                                                        GibCursor loc_3093,
                                                                        GibCursor arg_748_944_1549)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_10917 = *(GibPackedTag *) arg_748_944_1549;
    GibCursor tmpcur_10918 = arg_748_944_1549 + 1;


  switch_10970:
    ;
    switch (tmpval_10917) {

      case 0:
        {
            GibCursor jump_4466 = arg_748_944_1549 + 1;

            *(GibPackedTag *) loc_3093 = 0;

            GibCursor writetag_7335 = loc_3093 + 1;
            GibCursor after_tag_7336 = loc_3093 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3094,
                                                                        end_r_3095,
                                                                        jump_4466,
                                                                        loc_3093,
                                                                        after_tag_7336};
            break;
        }

      case 1:
        {
            GibFloat tmpval_10923 = *(GibFloat *) tmpcur_10918;
            GibCursor tmpcur_10924 = tmpcur_10918 + sizeof(GibFloat);
            GibCursor loc_3919 = loc_3093 + 5;

            *(GibPackedTag *) loc_3093 = 1;

            GibCursor writetag_7347 = loc_3093 + 1;
            GibCursor after_tag_7348 = loc_3093 + 1;

            *(GibFloat *) after_tag_7348 = tmpval_10923;

            GibCursor writecur_7352 = after_tag_7348 + sizeof(GibFloat);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_254 =
                                                               _copy_without_ptrs_Ps(end_r_3094, end_r_3095, loc_3919, tmpcur_10924);
            GibCursor pvrtmp_10925 = tmp_struct_254.field0;
            GibCursor pvrtmp_10926 = tmp_struct_254.field1;
            GibCursor pvrtmp_10927 = tmp_struct_254.field2;
            GibCursor pvrtmp_10928 = tmp_struct_254.field3;
            GibCursor pvrtmp_10929 = tmp_struct_254.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_10925,
                                                                        pvrtmp_10926,
                                                                        pvrtmp_10927,
                                                                        loc_3093,
                                                                        pvrtmp_10929};
            break;
        }

      case 2:
        {
            GibCursor jump_4471 = arg_748_944_1549 + 1;

            *(GibPackedTag *) loc_3093 = 2;

            GibCursor writetag_7357 = loc_3093 + 1;
            GibCursor after_tag_7358 = loc_3093 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3094,
                                                                        end_r_3095,
                                                                        jump_4471,
                                                                        loc_3093,
                                                                        after_tag_7358};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_256 = *(uintptr_t *) tmpcur_10918;
            GibCursor tmpcur_10942 = GIB_UNTAG(tagged_tmpcur_256);
            GibCursor tmpaftercur_10943 = tmpcur_10918 + 8;
            uint16_t tmptag_10944 = GIB_GET_TAG(tagged_tmpcur_256);
            GibCursor end_from_tagged_indr_4677 = tmpcur_10942 + tmptag_10944;
            GibCursor jump_4679 = tmpcur_10918 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_255 =
                                                               _copy_without_ptrs_Ps(end_from_tagged_indr_4677, end_r_3095, loc_3093, tmpcur_10942);
            GibCursor pvrtmp_10945 = tmp_struct_255.field0;
            GibCursor pvrtmp_10946 = tmp_struct_255.field1;
            GibCursor pvrtmp_10947 = tmp_struct_255.field2;
            GibCursor pvrtmp_10948 = tmp_struct_255.field3;
            GibCursor pvrtmp_10949 = tmp_struct_255.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3094,
                                                                        pvrtmp_10946,
                                                                        jump_4679,
                                                                        pvrtmp_10948,
                                                                        pvrtmp_10949};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_258 = *(uintptr_t *) tmpcur_10918;
            GibCursor tmpcur_10956 = GIB_UNTAG(tagged_tmpcur_258);
            GibCursor tmpaftercur_10957 = tmpcur_10918 + 8;
            uint16_t tmptag_10958 = GIB_GET_TAG(tagged_tmpcur_258);
            GibCursor end_from_tagged_indr_4677 = tmpcur_10956 + tmptag_10958;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_257 =
                                                               _copy_without_ptrs_Ps(end_from_tagged_indr_4677, end_r_3095, loc_3093, tmpcur_10956);
            GibCursor pvrtmp_10959 = tmp_struct_257.field0;
            GibCursor pvrtmp_10960 = tmp_struct_257.field1;
            GibCursor pvrtmp_10961 = tmp_struct_257.field2;
            GibCursor pvrtmp_10962 = tmp_struct_257.field3;
            GibCursor pvrtmp_10963 = tmp_struct_257.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_10959,
                                                                        pvrtmp_10960,
                                                                        pvrtmp_10961,
                                                                        pvrtmp_10962,
                                                                        pvrtmp_10963};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_10917");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_Ps(GibCursor end_r_3097,
                                    GibCursor arg_753_949_1554)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_10971 = *(GibPackedTag *) arg_753_949_1554;
    GibCursor tmpcur_10972 = arg_753_949_1554 + 1;


  switch_10987:
    ;
    switch (tmpval_10971) {

      case 0:
        {
            GibCursor jump_4473 = arg_753_949_1554 + 1;

            return (GibCursorGibCursorProd) {end_r_3097, jump_4473};
            break;
        }

      case 1:
        {
            GibFloat tmpval_10973 = *(GibFloat *) tmpcur_10972;
            GibCursor tmpcur_10974 = tmpcur_10972 + sizeof(GibFloat);
            GibCursorGibCursorProd tmp_struct_259 =
                                    _traverse_Ps(end_r_3097, tmpcur_10974);
            GibCursor pvrtmp_10975 = tmp_struct_259.field0;
            GibCursor pvrtmp_10976 = tmp_struct_259.field1;

            return (GibCursorGibCursorProd) {pvrtmp_10975, pvrtmp_10976};
            break;
        }

      case 2:
        {
            GibCursor jump_4478 = arg_753_949_1554 + 1;

            return (GibCursorGibCursorProd) {end_r_3097, jump_4478};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_261 = *(uintptr_t *) tmpcur_10972;
            GibCursor tmpcur_10977 = GIB_UNTAG(tagged_tmpcur_261);
            GibCursor tmpaftercur_10978 = tmpcur_10972 + 8;
            uint16_t tmptag_10979 = GIB_GET_TAG(tagged_tmpcur_261);
            GibCursor end_from_tagged_indr_4683 = tmpcur_10977 + tmptag_10979;
            GibCursor jump_4685 = tmpcur_10972 + 8;
            GibCursorGibCursorProd tmp_struct_260 =
                                    _traverse_Ps(end_from_tagged_indr_4683, tmpcur_10977);
            GibCursor pvrtmp_10980 = tmp_struct_260.field0;
            GibCursor pvrtmp_10981 = tmp_struct_260.field1;

            return (GibCursorGibCursorProd) {end_r_3097, jump_4685};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_263 = *(uintptr_t *) tmpcur_10972;
            GibCursor tmpcur_10982 = GIB_UNTAG(tagged_tmpcur_263);
            GibCursor tmpaftercur_10983 = tmpcur_10972 + 8;
            uint16_t tmptag_10984 = GIB_GET_TAG(tagged_tmpcur_263);
            GibCursor end_from_tagged_indr_4683 = tmpcur_10982 + tmptag_10984;
            GibCursorGibCursorProd tmp_struct_262 =
                                    _traverse_Ps(end_from_tagged_indr_4683, tmpcur_10982);
            GibCursor pvrtmp_10985 = tmp_struct_262.field0;
            GibCursor pvrtmp_10986 = tmp_struct_262.field1;

            return (GibCursorGibCursorProd) {pvrtmp_10985, pvrtmp_10986};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_10971");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_Ps(GibCursor end_r_3099,
                                 GibCursor arg_758_953_1558)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_10988 = *(GibPackedTag *) arg_758_953_1558;
    GibCursor tmpcur_10989 = arg_758_953_1558 + 1;


  switch_11004:
    ;
    switch (tmpval_10988) {

      case 0:
        {
            GibCursor jump_4480 = arg_758_953_1558 + 1;
            unsigned char wildcard_759_954_1559 = gib_print_symbol(9424);
            unsigned char wildcard_760_955_1560 = gib_print_symbol(9423);

            return (GibCursorGibCursorProd) {end_r_3099, jump_4480};
            break;
        }

      case 1:
        {
            GibFloat tmpval_10990 = *(GibFloat *) tmpcur_10989;
            GibCursor tmpcur_10991 = tmpcur_10989 + sizeof(GibFloat);
            unsigned char wildcard_765_958_1563 = gib_print_symbol(9425);
            unsigned char wildcard_770_959_1564 = gib_print_symbol(9432);
            unsigned char y_763_960_1565 = printf("%.2f", tmpval_10990);
            unsigned char wildcard_769_961_1566 = gib_print_symbol(9432);
            unsigned char y_763_962_1567 = gib_print_symbol(9432);
            unsigned char wildcard_768_963_1568 = gib_print_symbol(9432);
            GibCursorGibCursorProd tmp_struct_264 =
                                    _print_Ps(end_r_3099, tmpcur_10991);
            GibCursor pvrtmp_10992 = tmp_struct_264.field0;
            GibCursor pvrtmp_10993 = tmp_struct_264.field1;
            unsigned char wildcard_767_965_1570 = gib_print_symbol(9432);
            unsigned char y_764_966_1571 = gib_print_symbol(9432);
            unsigned char wildcard_766_967_1572 = gib_print_symbol(9423);

            return (GibCursorGibCursorProd) {pvrtmp_10992, pvrtmp_10993};
            break;
        }

      case 2:
        {
            GibCursor jump_4485 = arg_758_953_1558 + 1;
            unsigned char wildcard_771_968_1573 = gib_print_symbol(9428);
            unsigned char wildcard_772_969_1574 = gib_print_symbol(9423);

            return (GibCursorGibCursorProd) {end_r_3099, jump_4485};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_266 = *(uintptr_t *) tmpcur_10989;
            GibCursor tmpcur_10994 = GIB_UNTAG(tagged_tmpcur_266);
            GibCursor tmpaftercur_10995 = tmpcur_10989 + 8;
            uint16_t tmptag_10996 = GIB_GET_TAG(tagged_tmpcur_266);
            GibCursor end_from_tagged_indr_4689 = tmpcur_10994 + tmptag_10996;
            GibCursor jump_4691 = tmpcur_10989 + 8;
            unsigned char wildcard_4694 = gib_print_symbol(9431);
            GibCursorGibCursorProd tmp_struct_265 =
                                    _print_Ps(end_from_tagged_indr_4689, tmpcur_10994);
            GibCursor pvrtmp_10997 = tmp_struct_265.field0;
            GibCursor pvrtmp_10998 = tmp_struct_265.field1;

            return (GibCursorGibCursorProd) {end_r_3099, jump_4691};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_268 = *(uintptr_t *) tmpcur_10989;
            GibCursor tmpcur_10999 = GIB_UNTAG(tagged_tmpcur_268);
            GibCursor tmpaftercur_11000 = tmpcur_10989 + 8;
            uint16_t tmptag_11001 = GIB_GET_TAG(tagged_tmpcur_268);
            GibCursor end_from_tagged_indr_4689 = tmpcur_10999 + tmptag_11001;
            unsigned char wildcard_4694 = gib_print_symbol(9430);
            GibCursorGibCursorProd tmp_struct_267 =
                                    _print_Ps(end_from_tagged_indr_4689, tmpcur_10999);
            GibCursor pvrtmp_11002 = tmp_struct_267.field0;
            GibCursor pvrtmp_11003 = tmp_struct_267.field1;

            return (GibCursorGibCursorProd) {pvrtmp_11002, pvrtmp_11003};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_10988");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_PList1(GibCursor end_r_3102,
                                                               GibCursor end_r_3103,
                                                               GibCursor loc_3101,
                                                               GibCursor arg_773_970_1575)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_3101 + 18 > end_r_3103) {
        gib_grow_region(&loc_3101, &end_r_3103);
    }

    GibPackedTag tmpval_11005 = *(GibPackedTag *) arg_773_970_1575;
    GibCursor tmpcur_11006 = arg_773_970_1575 + 1;


  switch_11058:
    ;
    switch (tmpval_11005) {

      case 0:
        {
            GibCursor jump_4487 = arg_773_970_1575 + 1;

            *(GibPackedTag *) loc_3101 = 0;

            GibCursor writetag_7403 = loc_3101 + 1;
            GibCursor after_tag_7404 = loc_3101 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3102,
                                                                        end_r_3103,
                                                                        jump_4487,
                                                                        loc_3101,
                                                                        after_tag_7404};
            break;
        }

      case 1:
        {
            GibFloat tmpval_11011 = *(GibFloat *) tmpcur_11006;
            GibCursor tmpcur_11012 = tmpcur_11006 + sizeof(GibFloat);
            GibCursor loc_3945 = loc_3101 + 5;

            *(GibPackedTag *) loc_3101 = 1;

            GibCursor writetag_7415 = loc_3101 + 1;
            GibCursor after_tag_7416 = loc_3101 + 1;

            *(GibFloat *) after_tag_7416 = tmpval_11011;

            GibCursor writecur_7420 = after_tag_7416 + sizeof(GibFloat);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_269 =
                                                               _copy_PList1(end_r_3102, end_r_3103, loc_3945, tmpcur_11012);
            GibCursor pvrtmp_11013 = tmp_struct_269.field0;
            GibCursor pvrtmp_11014 = tmp_struct_269.field1;
            GibCursor pvrtmp_11015 = tmp_struct_269.field2;
            GibCursor pvrtmp_11016 = tmp_struct_269.field3;
            GibCursor pvrtmp_11017 = tmp_struct_269.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_11013,
                                                                        pvrtmp_11014,
                                                                        pvrtmp_11015,
                                                                        loc_3101,
                                                                        pvrtmp_11017};
            break;
        }

      case 2:
        {
            GibCursor jump_4492 = arg_773_970_1575 + 1;

            *(GibPackedTag *) loc_3101 = 2;

            GibCursor writetag_7425 = loc_3101 + 1;
            GibCursor after_tag_7426 = loc_3101 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3102,
                                                                        end_r_3103,
                                                                        jump_4492,
                                                                        loc_3101,
                                                                        after_tag_7426};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_271 = *(uintptr_t *) tmpcur_11006;
            GibCursor tmpcur_11030 = GIB_UNTAG(tagged_tmpcur_271);
            GibCursor tmpaftercur_11031 = tmpcur_11006 + 8;
            uint16_t tmptag_11032 = GIB_GET_TAG(tagged_tmpcur_271);
            GibCursor end_from_tagged_indr_4695 = tmpcur_11030 + tmptag_11032;
            GibCursor jump_4697 = tmpcur_11006 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_270 =
                                                               _copy_PList1(end_from_tagged_indr_4695, end_r_3103, loc_3101, tmpcur_11030);
            GibCursor pvrtmp_11033 = tmp_struct_270.field0;
            GibCursor pvrtmp_11034 = tmp_struct_270.field1;
            GibCursor pvrtmp_11035 = tmp_struct_270.field2;
            GibCursor pvrtmp_11036 = tmp_struct_270.field3;
            GibCursor pvrtmp_11037 = tmp_struct_270.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3102,
                                                                        pvrtmp_11034,
                                                                        jump_4697,
                                                                        pvrtmp_11036,
                                                                        pvrtmp_11037};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_273 = *(uintptr_t *) tmpcur_11006;
            GibCursor tmpcur_11044 = GIB_UNTAG(tagged_tmpcur_273);
            GibCursor tmpaftercur_11045 = tmpcur_11006 + 8;
            uint16_t tmptag_11046 = GIB_GET_TAG(tagged_tmpcur_273);
            GibCursor end_from_tagged_indr_4695 = tmpcur_11044 + tmptag_11046;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_272 =
                                                               _copy_PList1(end_from_tagged_indr_4695, end_r_3103, loc_3101, tmpcur_11044);
            GibCursor pvrtmp_11047 = tmp_struct_272.field0;
            GibCursor pvrtmp_11048 = tmp_struct_272.field1;
            GibCursor pvrtmp_11049 = tmp_struct_272.field2;
            GibCursor pvrtmp_11050 = tmp_struct_272.field3;
            GibCursor pvrtmp_11051 = tmp_struct_272.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_11047,
                                                                        pvrtmp_11048,
                                                                        pvrtmp_11049,
                                                                        pvrtmp_11050,
                                                                        pvrtmp_11051};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_11005");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_PList1(GibCursor end_r_3106,
                                                                            GibCursor end_r_3107,
                                                                            GibCursor loc_3105,
                                                                            GibCursor arg_778_975_1580)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_11059 = *(GibPackedTag *) arg_778_975_1580;
    GibCursor tmpcur_11060 = arg_778_975_1580 + 1;


  switch_11112:
    ;
    switch (tmpval_11059) {

      case 0:
        {
            GibCursor jump_4494 = arg_778_975_1580 + 1;

            *(GibPackedTag *) loc_3105 = 0;

            GibCursor writetag_7443 = loc_3105 + 1;
            GibCursor after_tag_7444 = loc_3105 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3106,
                                                                        end_r_3107,
                                                                        jump_4494,
                                                                        loc_3105,
                                                                        after_tag_7444};
            break;
        }

      case 1:
        {
            GibFloat tmpval_11065 = *(GibFloat *) tmpcur_11060;
            GibCursor tmpcur_11066 = tmpcur_11060 + sizeof(GibFloat);
            GibCursor loc_3959 = loc_3105 + 5;

            *(GibPackedTag *) loc_3105 = 1;

            GibCursor writetag_7455 = loc_3105 + 1;
            GibCursor after_tag_7456 = loc_3105 + 1;

            *(GibFloat *) after_tag_7456 = tmpval_11065;

            GibCursor writecur_7460 = after_tag_7456 + sizeof(GibFloat);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_277 =
                                                               _copy_without_ptrs_PList1(end_r_3106, end_r_3107, loc_3959, tmpcur_11066);
            GibCursor pvrtmp_11067 = tmp_struct_277.field0;
            GibCursor pvrtmp_11068 = tmp_struct_277.field1;
            GibCursor pvrtmp_11069 = tmp_struct_277.field2;
            GibCursor pvrtmp_11070 = tmp_struct_277.field3;
            GibCursor pvrtmp_11071 = tmp_struct_277.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_11067,
                                                                        pvrtmp_11068,
                                                                        pvrtmp_11069,
                                                                        loc_3105,
                                                                        pvrtmp_11071};
            break;
        }

      case 2:
        {
            GibCursor jump_4499 = arg_778_975_1580 + 1;

            *(GibPackedTag *) loc_3105 = 2;

            GibCursor writetag_7465 = loc_3105 + 1;
            GibCursor after_tag_7466 = loc_3105 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3106,
                                                                        end_r_3107,
                                                                        jump_4499,
                                                                        loc_3105,
                                                                        after_tag_7466};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_279 = *(uintptr_t *) tmpcur_11060;
            GibCursor tmpcur_11084 = GIB_UNTAG(tagged_tmpcur_279);
            GibCursor tmpaftercur_11085 = tmpcur_11060 + 8;
            uint16_t tmptag_11086 = GIB_GET_TAG(tagged_tmpcur_279);
            GibCursor end_from_tagged_indr_4701 = tmpcur_11084 + tmptag_11086;
            GibCursor jump_4703 = tmpcur_11060 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_278 =
                                                               _copy_without_ptrs_PList1(end_from_tagged_indr_4701, end_r_3107, loc_3105, tmpcur_11084);
            GibCursor pvrtmp_11087 = tmp_struct_278.field0;
            GibCursor pvrtmp_11088 = tmp_struct_278.field1;
            GibCursor pvrtmp_11089 = tmp_struct_278.field2;
            GibCursor pvrtmp_11090 = tmp_struct_278.field3;
            GibCursor pvrtmp_11091 = tmp_struct_278.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3106,
                                                                        pvrtmp_11088,
                                                                        jump_4703,
                                                                        pvrtmp_11090,
                                                                        pvrtmp_11091};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_281 = *(uintptr_t *) tmpcur_11060;
            GibCursor tmpcur_11098 = GIB_UNTAG(tagged_tmpcur_281);
            GibCursor tmpaftercur_11099 = tmpcur_11060 + 8;
            uint16_t tmptag_11100 = GIB_GET_TAG(tagged_tmpcur_281);
            GibCursor end_from_tagged_indr_4701 = tmpcur_11098 + tmptag_11100;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_280 =
                                                               _copy_without_ptrs_PList1(end_from_tagged_indr_4701, end_r_3107, loc_3105, tmpcur_11098);
            GibCursor pvrtmp_11101 = tmp_struct_280.field0;
            GibCursor pvrtmp_11102 = tmp_struct_280.field1;
            GibCursor pvrtmp_11103 = tmp_struct_280.field2;
            GibCursor pvrtmp_11104 = tmp_struct_280.field3;
            GibCursor pvrtmp_11105 = tmp_struct_280.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_11101,
                                                                        pvrtmp_11102,
                                                                        pvrtmp_11103,
                                                                        pvrtmp_11104,
                                                                        pvrtmp_11105};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_11059");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_PList1(GibCursor end_r_3109,
                                        GibCursor arg_783_980_1585)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_11113 = *(GibPackedTag *) arg_783_980_1585;
    GibCursor tmpcur_11114 = arg_783_980_1585 + 1;


  switch_11129:
    ;
    switch (tmpval_11113) {

      case 0:
        {
            GibCursor jump_4501 = arg_783_980_1585 + 1;

            return (GibCursorGibCursorProd) {end_r_3109, jump_4501};
            break;
        }

      case 1:
        {
            GibFloat tmpval_11115 = *(GibFloat *) tmpcur_11114;
            GibCursor tmpcur_11116 = tmpcur_11114 + sizeof(GibFloat);
            GibCursorGibCursorProd tmp_struct_282 =
                                    _traverse_PList1(end_r_3109, tmpcur_11116);
            GibCursor pvrtmp_11117 = tmp_struct_282.field0;
            GibCursor pvrtmp_11118 = tmp_struct_282.field1;

            return (GibCursorGibCursorProd) {pvrtmp_11117, pvrtmp_11118};
            break;
        }

      case 2:
        {
            GibCursor jump_4506 = arg_783_980_1585 + 1;

            return (GibCursorGibCursorProd) {end_r_3109, jump_4506};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_284 = *(uintptr_t *) tmpcur_11114;
            GibCursor tmpcur_11119 = GIB_UNTAG(tagged_tmpcur_284);
            GibCursor tmpaftercur_11120 = tmpcur_11114 + 8;
            uint16_t tmptag_11121 = GIB_GET_TAG(tagged_tmpcur_284);
            GibCursor end_from_tagged_indr_4707 = tmpcur_11119 + tmptag_11121;
            GibCursor jump_4709 = tmpcur_11114 + 8;
            GibCursorGibCursorProd tmp_struct_283 =
                                    _traverse_PList1(end_from_tagged_indr_4707, tmpcur_11119);
            GibCursor pvrtmp_11122 = tmp_struct_283.field0;
            GibCursor pvrtmp_11123 = tmp_struct_283.field1;

            return (GibCursorGibCursorProd) {end_r_3109, jump_4709};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_286 = *(uintptr_t *) tmpcur_11114;
            GibCursor tmpcur_11124 = GIB_UNTAG(tagged_tmpcur_286);
            GibCursor tmpaftercur_11125 = tmpcur_11114 + 8;
            uint16_t tmptag_11126 = GIB_GET_TAG(tagged_tmpcur_286);
            GibCursor end_from_tagged_indr_4707 = tmpcur_11124 + tmptag_11126;
            GibCursorGibCursorProd tmp_struct_285 =
                                    _traverse_PList1(end_from_tagged_indr_4707, tmpcur_11124);
            GibCursor pvrtmp_11127 = tmp_struct_285.field0;
            GibCursor pvrtmp_11128 = tmp_struct_285.field1;

            return (GibCursorGibCursorProd) {pvrtmp_11127, pvrtmp_11128};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_11113");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_PList1(GibCursor end_r_3111,
                                     GibCursor arg_788_984_1589)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_11130 = *(GibPackedTag *) arg_788_984_1589;
    GibCursor tmpcur_11131 = arg_788_984_1589 + 1;


  switch_11146:
    ;
    switch (tmpval_11130) {

      case 0:
        {
            GibCursor jump_4508 = arg_788_984_1589 + 1;
            unsigned char wildcard_789_985_1590 = gib_print_symbol(9426);
            unsigned char wildcard_790_986_1591 = gib_print_symbol(9423);

            return (GibCursorGibCursorProd) {end_r_3111, jump_4508};
            break;
        }

      case 1:
        {
            GibFloat tmpval_11132 = *(GibFloat *) tmpcur_11131;
            GibCursor tmpcur_11133 = tmpcur_11131 + sizeof(GibFloat);
            unsigned char wildcard_795_989_1594 = gib_print_symbol(9429);
            unsigned char wildcard_800_990_1595 = gib_print_symbol(9432);
            unsigned char y_793_991_1596 = printf("%.2f", tmpval_11132);
            unsigned char wildcard_799_992_1597 = gib_print_symbol(9432);
            unsigned char y_793_993_1598 = gib_print_symbol(9432);
            unsigned char wildcard_798_994_1599 = gib_print_symbol(9432);
            GibCursorGibCursorProd tmp_struct_287 =
                                    _print_PList1(end_r_3111, tmpcur_11133);
            GibCursor pvrtmp_11134 = tmp_struct_287.field0;
            GibCursor pvrtmp_11135 = tmp_struct_287.field1;
            unsigned char wildcard_797_996_1601 = gib_print_symbol(9432);
            unsigned char y_794_997_1602 = gib_print_symbol(9432);
            unsigned char wildcard_796_998_1603 = gib_print_symbol(9423);

            return (GibCursorGibCursorProd) {pvrtmp_11134, pvrtmp_11135};
            break;
        }

      case 2:
        {
            GibCursor jump_4513 = arg_788_984_1589 + 1;
            unsigned char wildcard_801_999_1604 = gib_print_symbol(9427);
            unsigned char wildcard_802_1000_1605 = gib_print_symbol(9423);

            return (GibCursorGibCursorProd) {end_r_3111, jump_4513};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_289 = *(uintptr_t *) tmpcur_11131;
            GibCursor tmpcur_11136 = GIB_UNTAG(tagged_tmpcur_289);
            GibCursor tmpaftercur_11137 = tmpcur_11131 + 8;
            uint16_t tmptag_11138 = GIB_GET_TAG(tagged_tmpcur_289);
            GibCursor end_from_tagged_indr_4713 = tmpcur_11136 + tmptag_11138;
            GibCursor jump_4715 = tmpcur_11131 + 8;
            unsigned char wildcard_4718 = gib_print_symbol(9431);
            GibCursorGibCursorProd tmp_struct_288 =
                                    _print_PList1(end_from_tagged_indr_4713, tmpcur_11136);
            GibCursor pvrtmp_11139 = tmp_struct_288.field0;
            GibCursor pvrtmp_11140 = tmp_struct_288.field1;

            return (GibCursorGibCursorProd) {end_r_3111, jump_4715};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_291 = *(uintptr_t *) tmpcur_11131;
            GibCursor tmpcur_11141 = GIB_UNTAG(tagged_tmpcur_291);
            GibCursor tmpaftercur_11142 = tmpcur_11131 + 8;
            uint16_t tmptag_11143 = GIB_GET_TAG(tagged_tmpcur_291);
            GibCursor end_from_tagged_indr_4713 = tmpcur_11141 + tmptag_11143;
            unsigned char wildcard_4718 = gib_print_symbol(9430);
            GibCursorGibCursorProd tmp_struct_290 =
                                    _print_PList1(end_from_tagged_indr_4713, tmpcur_11141);
            GibCursor pvrtmp_11144 = tmp_struct_290.field0;
            GibCursor pvrtmp_11145 = tmp_struct_290.field1;

            return (GibCursorGibCursorProd) {pvrtmp_11144, pvrtmp_11145};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_11130");
            exit(1);
        }
    }
}
GibCursorGibBoolProd caseFn_803(GibCursor end_r_3113,
                                GibCursor bs_248_804_1001_1606)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_11147 = *(GibPackedTag *) bs_248_804_1001_1606;
    GibCursor tmpcur_11148 = bs_248_804_1001_1606 + 1;


  switch_11161:
    ;
    switch (tmpval_11147) {

      case 0:
        {
            return (GibCursorGibBoolProd) {end_r_3113, false};
            break;
        }

      case 1:
        {
            GibFloat tmpval_11149 = *(GibFloat *) tmpcur_11148;
            GibCursor tmpcur_11150 = tmpcur_11148 + sizeof(GibFloat);

            return (GibCursorGibBoolProd) {end_r_3113, false};
            break;
        }

      case 2:
        {
            return (GibCursorGibBoolProd) {end_r_3113, true};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_293 = *(uintptr_t *) tmpcur_11148;
            GibCursor tmpcur_11151 = GIB_UNTAG(tagged_tmpcur_293);
            GibCursor tmpaftercur_11152 = tmpcur_11148 + 8;
            uint16_t tmptag_11153 = GIB_GET_TAG(tagged_tmpcur_293);
            GibCursor end_from_tagged_indr_4719 = tmpcur_11151 + tmptag_11153;
            GibCursor jump_4721 = tmpcur_11148 + 8;
            GibCursorGibBoolProd tmp_struct_292 =
                                  caseFn_803(end_from_tagged_indr_4719, tmpcur_11151);
            GibCursor pvrtmp_11154 = tmp_struct_292.field0;
            GibBool pvrtmp_11155 = tmp_struct_292.field1;

            return (GibCursorGibBoolProd) {end_r_3113, pvrtmp_11155};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_295 = *(uintptr_t *) tmpcur_11148;
            GibCursor tmpcur_11156 = GIB_UNTAG(tagged_tmpcur_295);
            GibCursor tmpaftercur_11157 = tmpcur_11148 + 8;
            uint16_t tmptag_11158 = GIB_GET_TAG(tagged_tmpcur_295);
            GibCursor end_from_tagged_indr_4719 = tmpcur_11156 + tmptag_11158;
            GibCursorGibBoolProd tmp_struct_294 =
                                  caseFn_803(end_from_tagged_indr_4719, tmpcur_11156);
            GibCursor pvrtmp_11159 = tmp_struct_294.field0;
            GibBool pvrtmp_11160 = tmp_struct_294.field1;

            return (GibCursorGibBoolProd) {pvrtmp_11159, pvrtmp_11160};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_11147");
            exit(1);
        }
    }
}
GibCursorGibBoolProd caseFn_805(GibCursor end_r_3115,
                                GibCursor bs_248_806_1004_1609)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_11162 = *(GibPackedTag *) bs_248_806_1004_1609;
    GibCursor tmpcur_11163 = bs_248_806_1004_1609 + 1;


  switch_11176:
    ;
    switch (tmpval_11162) {

      case 0:
        {
            return (GibCursorGibBoolProd) {end_r_3115, true};
            break;
        }

      case 1:
        {
            GibFloat tmpval_11164 = *(GibFloat *) tmpcur_11163;
            GibCursor tmpcur_11165 = tmpcur_11163 + sizeof(GibFloat);

            return (GibCursorGibBoolProd) {end_r_3115, false};
            break;
        }

      case 2:
        {
            return (GibCursorGibBoolProd) {end_r_3115, false};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_297 = *(uintptr_t *) tmpcur_11163;
            GibCursor tmpcur_11166 = GIB_UNTAG(tagged_tmpcur_297);
            GibCursor tmpaftercur_11167 = tmpcur_11163 + 8;
            uint16_t tmptag_11168 = GIB_GET_TAG(tagged_tmpcur_297);
            GibCursor end_from_tagged_indr_4724 = tmpcur_11166 + tmptag_11168;
            GibCursor jump_4726 = tmpcur_11163 + 8;
            GibCursorGibBoolProd tmp_struct_296 =
                                  caseFn_805(end_from_tagged_indr_4724, tmpcur_11166);
            GibCursor pvrtmp_11169 = tmp_struct_296.field0;
            GibBool pvrtmp_11170 = tmp_struct_296.field1;

            return (GibCursorGibBoolProd) {end_r_3115, pvrtmp_11170};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_299 = *(uintptr_t *) tmpcur_11163;
            GibCursor tmpcur_11171 = GIB_UNTAG(tagged_tmpcur_299);
            GibCursor tmpaftercur_11172 = tmpcur_11163 + 8;
            uint16_t tmptag_11173 = GIB_GET_TAG(tagged_tmpcur_299);
            GibCursor end_from_tagged_indr_4724 = tmpcur_11171 + tmptag_11173;
            GibCursorGibBoolProd tmp_struct_298 =
                                  caseFn_805(end_from_tagged_indr_4724, tmpcur_11171);
            GibCursor pvrtmp_11174 = tmp_struct_298.field0;
            GibBool pvrtmp_11175 = tmp_struct_298.field1;

            return (GibCursorGibBoolProd) {pvrtmp_11174, pvrtmp_11175};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_11162");
            exit(1);
        }
    }
}
GibCursorGibCursorGibBoolProd caseFn_807(GibCursor end_r_3118,
                                         GibCursor end_r_3119,
                                         GibCursor bs_248_808_1007_1612,
                                         GibFloat a_253_809_1008_1613,
                                         GibCursor as__254_810_1009_1614)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_11177 = *(GibPackedTag *) bs_248_808_1007_1612;
    GibCursor tmpcur_11178 = bs_248_808_1007_1612 + 1;


  switch_11196:
    ;
    switch (tmpval_11177) {

      case 0:
        {
            return (GibCursorGibCursorGibBoolProd) {end_r_3118, end_r_3119,
                                                    false};
            break;
        }

      case 1:
        {
            GibFloat tmpval_11179 = *(GibFloat *) tmpcur_11178;
            GibCursor tmpcur_11180 = tmpcur_11178 + sizeof(GibFloat);
            GibFloat d_257_1012_1617 = a_253_809_1008_1613 - tmpval_11179;
            GibFloat fltPrm_1236_1618 = 0.0 - 1.0e-7;
            GibBool fltPrm_1235_1619 = fltPrm_1236_1618 < d_257_1012_1617;
            GibBool fltPrm_1238_1620 = d_257_1012_1617 < 1.0e-7;
            GibCursorGibCursorGibBoolProd tmp_struct_300 =
                                           equal(end_r_3119, end_r_3118, as__254_810_1009_1614, tmpcur_11180);
            GibCursor pvrtmp_11181 = tmp_struct_300.field0;
            GibCursor pvrtmp_11182 = tmp_struct_300.field1;
            GibBool pvrtmp_11183 = tmp_struct_300.field2;
            GibBool fltPrm_1237_1622 = fltPrm_1238_1620 && pvrtmp_11183;
            GibBool tailprim_4531 = fltPrm_1235_1619 && fltPrm_1237_1622;

            return (GibCursorGibCursorGibBoolProd) {pvrtmp_11182, pvrtmp_11181,
                                                    tailprim_4531};
            break;
        }

      case 2:
        {
            return (GibCursorGibCursorGibBoolProd) {end_r_3118, end_r_3119,
                                                    false};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_302 = *(uintptr_t *) tmpcur_11178;
            GibCursor tmpcur_11184 = GIB_UNTAG(tagged_tmpcur_302);
            GibCursor tmpaftercur_11185 = tmpcur_11178 + 8;
            uint16_t tmptag_11186 = GIB_GET_TAG(tagged_tmpcur_302);
            GibCursor end_from_tagged_indr_4729 = tmpcur_11184 + tmptag_11186;
            GibCursor jump_4731 = tmpcur_11178 + 8;
            GibCursorGibCursorGibBoolProd tmp_struct_301 =
                                           caseFn_807(end_from_tagged_indr_4729, end_r_3119, tmpcur_11184, a_253_809_1008_1613, as__254_810_1009_1614);
            GibCursor pvrtmp_11187 = tmp_struct_301.field0;
            GibCursor pvrtmp_11188 = tmp_struct_301.field1;
            GibBool pvrtmp_11189 = tmp_struct_301.field2;

            return (GibCursorGibCursorGibBoolProd) {end_r_3118, pvrtmp_11188,
                                                    pvrtmp_11189};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_304 = *(uintptr_t *) tmpcur_11178;
            GibCursor tmpcur_11190 = GIB_UNTAG(tagged_tmpcur_304);
            GibCursor tmpaftercur_11191 = tmpcur_11178 + 8;
            uint16_t tmptag_11192 = GIB_GET_TAG(tagged_tmpcur_304);
            GibCursor end_from_tagged_indr_4729 = tmpcur_11190 + tmptag_11192;
            GibCursorGibCursorGibBoolProd tmp_struct_303 =
                                           caseFn_807(end_from_tagged_indr_4729, end_r_3119, tmpcur_11190, a_253_809_1008_1613, as__254_810_1009_1614);
            GibCursor pvrtmp_11193 = tmp_struct_303.field0;
            GibCursor pvrtmp_11194 = tmp_struct_303.field1;
            GibBool pvrtmp_11195 = tmp_struct_303.field2;

            return (GibCursorGibCursorGibBoolProd) {pvrtmp_11193, pvrtmp_11194,
                                                    pvrtmp_11195};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_11177");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd caseFn_811(GibCursor end_r_3122,
                                                    GibCursor end_r_3123,
                                                    GibCursor loc_3121,
                                                    GibInt n_261_812_1013_1623,
                                                    GibCursor fs_264_813_1014_1624)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_3121 + 18 > end_r_3123) {
        gib_grow_region(&loc_3121, &end_r_3123);
    }

    GibPackedTag tmpval_11197 = *(GibPackedTag *) fs_264_813_1014_1624;
    GibCursor tmpcur_11198 = fs_264_813_1014_1624 + 1;


  switch_11251:
    ;
    switch (tmpval_11197) {

      case 0:
        {
            *(GibPackedTag *) loc_3121 = 2;

            GibCursor writetag_7552 = loc_3121 + 1;
            GibCursor after_tag_7553 = loc_3121 + 1;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_3122,
                                                               end_r_3123,
                                                               loc_3121,
                                                               after_tag_7553};
            break;
        }

      case 1:
        {
            GibFloat tmpval_11203 = *(GibFloat *) tmpcur_11198;
            GibCursor tmpcur_11204 = tmpcur_11198 + sizeof(GibFloat);
            GibBool fltIf_1240_1627 = tmpval_11203 == 0.0;

            if (fltIf_1240_1627) {
                GibInt fltAppE_1242_1628 = n_261_812_1013_1623 - 1;
                GibCursor loc_4001 = loc_3121 + 5;

                *(GibPackedTag *) loc_3121 = 1;

                GibCursor writetag_7564 = loc_3121 + 1;
                GibCursor after_tag_7565 = loc_3121 + 1;

                *(GibFloat *) after_tag_7565 = 0.0;

                GibCursor writecur_7569 = after_tag_7565 + sizeof(GibFloat);

                gib_shadowstack_push(rstack, loc_3121, end_r_3123, Stk, Ps_T);

                GibCursorGibCursorGibCursorGibCursorProd tmp_struct_305 =
                                                          psSqrt(end_r_3122, end_r_3123, loc_4001, fltAppE_1242_1628, tmpcur_11204);
                GibCursor pvrtmp_11205 = tmp_struct_305.field0;
                GibCursor pvrtmp_11206 = tmp_struct_305.field1;
                GibCursor pvrtmp_11207 = tmp_struct_305.field2;
                GibCursor pvrtmp_11208 = tmp_struct_305.field3;

                frame = gib_shadowstack_pop(rstack);
                loc_3121 = frame->ptr;
                end_r_3123 = frame->endptr;
                return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_11205,
                                                                   pvrtmp_11206,
                                                                   loc_3121,
                                                                   pvrtmp_11208};
            } else {
                *(GibPackedTag *) loc_3121 = 2;

                GibCursor writetag_7573 = loc_3121 + 1;
                GibCursor after_tag_7574 = loc_3121 + 1;

                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_3122,
                                                                   end_r_3123,
                                                                   loc_3121,
                                                                   after_tag_7574};
            }
            break;
        }

      case 2:
        {
            *(GibPackedTag *) loc_3121 = 2;

            GibCursor writetag_7581 = loc_3121 + 1;
            GibCursor after_tag_7582 = loc_3121 + 1;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_3122,
                                                               end_r_3123,
                                                               loc_3121,
                                                               after_tag_7582};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_307 = *(uintptr_t *) tmpcur_11198;
            GibCursor tmpcur_11225 = GIB_UNTAG(tagged_tmpcur_307);
            GibCursor tmpaftercur_11226 = tmpcur_11198 + 8;
            uint16_t tmptag_11227 = GIB_GET_TAG(tagged_tmpcur_307);
            GibCursor end_from_tagged_indr_4734 = tmpcur_11225 + tmptag_11227;
            GibCursor jump_4736 = tmpcur_11198 + 8;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_306 =
                                                      caseFn_811(end_from_tagged_indr_4734, end_r_3123, loc_3121, n_261_812_1013_1623, tmpcur_11225);
            GibCursor pvrtmp_11228 = tmp_struct_306.field0;
            GibCursor pvrtmp_11229 = tmp_struct_306.field1;
            GibCursor pvrtmp_11230 = tmp_struct_306.field2;
            GibCursor pvrtmp_11231 = tmp_struct_306.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_3122,
                                                               pvrtmp_11229,
                                                               pvrtmp_11230,
                                                               pvrtmp_11231};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_309 = *(uintptr_t *) tmpcur_11198;
            GibCursor tmpcur_11238 = GIB_UNTAG(tagged_tmpcur_309);
            GibCursor tmpaftercur_11239 = tmpcur_11198 + 8;
            uint16_t tmptag_11240 = GIB_GET_TAG(tagged_tmpcur_309);
            GibCursor end_from_tagged_indr_4734 = tmpcur_11238 + tmptag_11240;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_308 =
                                                      caseFn_811(end_from_tagged_indr_4734, end_r_3123, loc_3121, n_261_812_1013_1623, tmpcur_11238);
            GibCursor pvrtmp_11241 = tmp_struct_308.field0;
            GibCursor pvrtmp_11242 = tmp_struct_308.field1;
            GibCursor pvrtmp_11243 = tmp_struct_308.field2;
            GibCursor pvrtmp_11244 = tmp_struct_308.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_11241,
                                                               pvrtmp_11242,
                                                               pvrtmp_11243,
                                                               pvrtmp_11244};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_11197");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd caseFn_814(GibCursor end_r_3126,
                                                             GibCursor end_r_3127,
                                                             GibCursor loc_3125,
                                                             GibFloat f_283_815_1017_1630,
                                                             GibCursor fs__286_816_1018_1631,
                                                             GibFloat f__285_817_1019_1632)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_3125 + 18 > end_r_3127) {
        gib_grow_region(&loc_3125, &end_r_3127);
    }

    GibPackedTag tmpval_11252 = *(GibPackedTag *) fs__286_816_1018_1631;
    GibCursor tmpcur_11253 = fs__286_816_1018_1631 + 1;


  switch_11290:
    ;
    switch (tmpval_11252) {

      case 0:
        {
            GibCursor jump_4540 = fs__286_816_1018_1631 + 1;
            GibFloat fltPkd_1243_1633 = f_283_815_1017_1630 /
                     f__285_817_1019_1632;
            GibFloat fltPrm_1246_1634 = 0.0 - 1.0;
            GibFloat fltPkd_1245_1635 = fltPrm_1246_1634 / f__285_817_1019_1632;
            GibCursor loc_4016 = loc_3125 + 5;
            GibCursor loc_4011 = loc_3125 + 10;

            *(GibPackedTag *) loc_3125 = 1;

            GibCursor writetag_7615 = loc_3125 + 1;
            GibCursor after_tag_7616 = loc_3125 + 1;

            *(GibFloat *) after_tag_7616 = fltPkd_1243_1633;

            GibCursor writecur_7620 = after_tag_7616 + sizeof(GibFloat);

            *(GibPackedTag *) loc_4011 = 0;

            GibCursor writetag_7599 = loc_4011 + 1;
            GibCursor after_tag_7600 = loc_4011 + 1;

            *(GibPackedTag *) loc_4016 = 1;

            GibCursor writetag_7606 = loc_4016 + 1;
            GibCursor after_tag_7607 = loc_4016 + 1;

            *(GibFloat *) after_tag_7607 = fltPkd_1245_1635;

            GibCursor writecur_7611 = after_tag_7607 + sizeof(GibFloat);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3126,
                                                                        end_r_3127,
                                                                        jump_4540,
                                                                        loc_3125,
                                                                        after_tag_7600};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_314 = *(uintptr_t *) tmpcur_11253;
            GibCursor tmpcur_11262 = GIB_UNTAG(tagged_tmpcur_314);
            GibCursor tmpaftercur_11263 = tmpcur_11253 + 8;
            uint16_t tmptag_11264 = GIB_GET_TAG(tagged_tmpcur_314);
            GibCursor end_from_tagged_indr_4739 = tmpcur_11262 + tmptag_11264;
            GibCursor jump_4741 = tmpcur_11253 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_313 =
                                                               caseFn_814(end_from_tagged_indr_4739, end_r_3127, loc_3125, f_283_815_1017_1630, tmpcur_11262, f__285_817_1019_1632);
            GibCursor pvrtmp_11265 = tmp_struct_313.field0;
            GibCursor pvrtmp_11266 = tmp_struct_313.field1;
            GibCursor pvrtmp_11267 = tmp_struct_313.field2;
            GibCursor pvrtmp_11268 = tmp_struct_313.field3;
            GibCursor pvrtmp_11269 = tmp_struct_313.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3126,
                                                                        pvrtmp_11266,
                                                                        jump_4741,
                                                                        pvrtmp_11268,
                                                                        pvrtmp_11269};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_316 = *(uintptr_t *) tmpcur_11253;
            GibCursor tmpcur_11276 = GIB_UNTAG(tagged_tmpcur_316);
            GibCursor tmpaftercur_11277 = tmpcur_11253 + 8;
            uint16_t tmptag_11278 = GIB_GET_TAG(tagged_tmpcur_316);
            GibCursor end_from_tagged_indr_4739 = tmpcur_11276 + tmptag_11278;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_315 =
                                                               caseFn_814(end_from_tagged_indr_4739, end_r_3127, loc_3125, f_283_815_1017_1630, tmpcur_11276, f__285_817_1019_1632);
            GibCursor pvrtmp_11279 = tmp_struct_315.field0;
            GibCursor pvrtmp_11280 = tmp_struct_315.field1;
            GibCursor pvrtmp_11281 = tmp_struct_315.field2;
            GibCursor pvrtmp_11282 = tmp_struct_315.field3;
            GibCursor pvrtmp_11283 = tmp_struct_315.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_11279,
                                                                        pvrtmp_11280,
                                                                        pvrtmp_11281,
                                                                        pvrtmp_11282,
                                                                        pvrtmp_11283};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_11252");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd caseFn_818(GibCursor end_r_3130,
                                                             GibCursor end_r_3131,
                                                             GibCursor loc_3129,
                                                             GibFloat f_283_819_1020_1638,
                                                             GibCursor fs_284_820_1021_1639)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_3129 + 18 > end_r_3131) {
        gib_grow_region(&loc_3129, &end_r_3131);
    }

    GibPackedTag tmpval_11291 = *(GibPackedTag *) fs_284_820_1021_1639;
    GibCursor tmpcur_11292 = fs_284_820_1021_1639 + 1;


  switch_11334:
    ;
    switch (tmpval_11291) {

      case 1:
        {
            GibFloat tmpval_11293 = *(GibFloat *) tmpcur_11292;
            GibCursor tmpcur_11294 = tmpcur_11292 + sizeof(GibFloat);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_320 =
                                                               caseFn_814(end_r_3130, end_r_3131, loc_3129, f_283_819_1020_1638, tmpcur_11294, tmpval_11293);
            GibCursor pvrtmp_11295 = tmp_struct_320.field0;
            GibCursor pvrtmp_11296 = tmp_struct_320.field1;
            GibCursor pvrtmp_11297 = tmp_struct_320.field2;
            GibCursor pvrtmp_11298 = tmp_struct_320.field3;
            GibCursor pvrtmp_11299 = tmp_struct_320.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_11295,
                                                                        pvrtmp_11296,
                                                                        pvrtmp_11297,
                                                                        pvrtmp_11298,
                                                                        pvrtmp_11299};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_322 = *(uintptr_t *) tmpcur_11292;
            GibCursor tmpcur_11306 = GIB_UNTAG(tagged_tmpcur_322);
            GibCursor tmpaftercur_11307 = tmpcur_11292 + 8;
            uint16_t tmptag_11308 = GIB_GET_TAG(tagged_tmpcur_322);
            GibCursor end_from_tagged_indr_4745 = tmpcur_11306 + tmptag_11308;
            GibCursor jump_4747 = tmpcur_11292 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_321 =
                                                               caseFn_818(end_from_tagged_indr_4745, end_r_3131, loc_3129, f_283_819_1020_1638, tmpcur_11306);
            GibCursor pvrtmp_11309 = tmp_struct_321.field0;
            GibCursor pvrtmp_11310 = tmp_struct_321.field1;
            GibCursor pvrtmp_11311 = tmp_struct_321.field2;
            GibCursor pvrtmp_11312 = tmp_struct_321.field3;
            GibCursor pvrtmp_11313 = tmp_struct_321.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3130,
                                                                        pvrtmp_11310,
                                                                        jump_4747,
                                                                        pvrtmp_11312,
                                                                        pvrtmp_11313};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_324 = *(uintptr_t *) tmpcur_11292;
            GibCursor tmpcur_11320 = GIB_UNTAG(tagged_tmpcur_324);
            GibCursor tmpaftercur_11321 = tmpcur_11292 + 8;
            uint16_t tmptag_11322 = GIB_GET_TAG(tagged_tmpcur_324);
            GibCursor end_from_tagged_indr_4745 = tmpcur_11320 + tmptag_11322;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_323 =
                                                               caseFn_818(end_from_tagged_indr_4745, end_r_3131, loc_3129, f_283_819_1020_1638, tmpcur_11320);
            GibCursor pvrtmp_11323 = tmp_struct_323.field0;
            GibCursor pvrtmp_11324 = tmp_struct_323.field1;
            GibCursor pvrtmp_11325 = tmp_struct_323.field2;
            GibCursor pvrtmp_11326 = tmp_struct_323.field3;
            GibCursor pvrtmp_11327 = tmp_struct_323.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_11323,
                                                                        pvrtmp_11324,
                                                                        pvrtmp_11325,
                                                                        pvrtmp_11326,
                                                                        pvrtmp_11327};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_11291");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd caseFn_821(GibCursor end_r_3135,
                                                             GibCursor end_r_3136,
                                                             GibCursor end_r_3137,
                                                             GibCursor loc_3134,
                                                             GibCursor b_290_822_1024_1642,
                                                             GibFloat f_291_823_1025_1643,
                                                             GibCursor fs_292_824_1026_1644)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_3134 + 18 > end_r_3137) {
        gib_grow_region(&loc_3134, &end_r_3137);
    }

    GibPackedTag tmpval_11335 = *(GibPackedTag *) b_290_822_1024_1642;
    GibCursor tmpcur_11336 = b_290_822_1024_1642 + 1;


  switch_11441:
    ;
    switch (tmpval_11335) {

      case 0:
        {
            GibCursor loc_4033 = loc_3134 + 5;

            *(GibPackedTag *) loc_3134 = 1;

            GibCursor writetag_7657 = loc_3134 + 1;
            GibCursor after_tag_7658 = loc_3134 + 1;

            *(GibFloat *) after_tag_7658 = f_291_823_1025_1643;

            GibCursor writecur_7662 = after_tag_7658 + sizeof(GibFloat);

            *(GibPackedTag *) loc_4033 = 0;

            GibCursor writetag_7650 = loc_4033 + 1;
            GibCursor after_tag_7651 = loc_4033 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3135,
                                                                        end_r_3136,
                                                                        end_r_3137,
                                                                        loc_3134,
                                                                        after_tag_7651};
            break;
        }

      case 1:
        {
            GibFloat tmpval_11343 = *(GibFloat *) tmpcur_11336;
            GibCursor tmpcur_11344 = tmpcur_11336 + sizeof(GibFloat);
            GibBool fltIf_1249_1648 = tmpval_11343 == 0.0;

            if (fltIf_1249_1648) {
                gib_shadowstack_push(rstack, fs_292_824_1026_1644, end_r_3136,
                                     Stk, Ps_T);
                gib_shadowstack_push(rstack, tmpcur_11344, end_r_3135, Stk,
                                     Ps_T);
                gib_shadowstack_push(wstack, loc_3134, end_r_3137, Stk, Ps_T);

                GibChunk region_11345 =
                         gib_alloc_region(gib_get_inf_init_chunk_size());
                GibCursor r_4061 = region_11345.start;
                GibCursor end_r_4061 = region_11345.end;

                frame = gib_shadowstack_pop(wstack);
                loc_3134 = frame->ptr;
                end_r_3137 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                tmpcur_11344 = frame->ptr;
                end_r_3135 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                fs_292_824_1026_1644 = frame->ptr;
                end_r_3136 = frame->endptr;

                GibCursor loc_4041 = r_4061 + 5;

                *(GibPackedTag *) r_4061 = 1;

                GibCursor writetag_7671 = r_4061 + 1;
                GibCursor after_tag_7672 = r_4061 + 1;

                *(GibFloat *) after_tag_7672 = 0.0;

                GibCursor writecur_7676 = after_tag_7672 + sizeof(GibFloat);

                // if (loc_4041 + 18 > end_r_4061) {
                //     gib_grow_region(&loc_4041, &end_r_4061);
                // }
                gib_indirection_barrier(loc_4041, end_r_4061, tmpcur_11344,
                                        end_r_3135, Ps_T);

                GibCursor end_7669 = loc_4041 + 9;

                gib_shadowstack_push(rstack, fs_292_824_1026_1644, end_r_3136,
                                     Stk, Ps_T);
                gib_shadowstack_push(rstack, r_4061, end_r_4061, Stk, Ps_T);
                gib_shadowstack_push(rstack, tmpcur_11344, end_r_3135, Stk,
                                     Ps_T);
                gib_shadowstack_push(wstack, loc_3134, end_r_3137, Stk, Ps_T);

                GibChunk region_11350 =
                         gib_alloc_region(gib_get_inf_init_chunk_size());
                GibCursor r_4060 = region_11350.start;
                GibCursor end_r_4060 = region_11350.end;

                frame = gib_shadowstack_pop(wstack);
                loc_3134 = frame->ptr;
                end_r_3137 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                tmpcur_11344 = frame->ptr;
                end_r_3135 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                r_4061 = frame->ptr;
                end_r_4061 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                fs_292_824_1026_1644 = frame->ptr;
                end_r_3136 = frame->endptr;
                gib_shadowstack_push(rstack, tmpcur_11344, end_r_3135, Stk,
                                     Ps_T);
                gib_shadowstack_push(wstack, loc_3134, end_r_3137, Stk, Ps_T);

                GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_328
                                                                  =
                                                                   compose(end_r_3136, end_r_4061, end_r_4060, r_4060, fs_292_824_1026_1644, r_4061);
                GibCursor pvrtmp_11351 = tmp_struct_328.field0;
                GibCursor pvrtmp_11352 = tmp_struct_328.field1;
                GibCursor pvrtmp_11353 = tmp_struct_328.field2;
                GibCursor pvrtmp_11354 = tmp_struct_328.field3;
                GibCursor pvrtmp_11355 = tmp_struct_328.field4;

                frame = gib_shadowstack_pop(wstack);
                loc_3134 = frame->ptr;
                end_r_3137 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                tmpcur_11344 = frame->ptr;
                end_r_3135 = frame->endptr;

                GibCursor loc_4033 = loc_3134 + 5;

                *(GibPackedTag *) loc_3134 = 1;

                GibCursor writetag_7688 = loc_3134 + 1;
                GibCursor after_tag_7689 = loc_3134 + 1;

                *(GibFloat *) after_tag_7689 = f_291_823_1025_1643;

                GibCursor writecur_7693 = after_tag_7689 + sizeof(GibFloat);

                gib_shadowstack_push(rstack, loc_3134, end_r_3137, Stk, Ps_T);

                GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_329
                                                                  =
                                                                   psMult(end_r_3135, pvrtmp_11353, end_r_3137, loc_4033, tmpcur_11344, pvrtmp_11354);
                GibCursor pvrtmp_11360 = tmp_struct_329.field0;
                GibCursor pvrtmp_11361 = tmp_struct_329.field1;
                GibCursor pvrtmp_11362 = tmp_struct_329.field2;
                GibCursor pvrtmp_11363 = tmp_struct_329.field3;
                GibCursor pvrtmp_11364 = tmp_struct_329.field4;

                frame = gib_shadowstack_pop(rstack);
                loc_3134 = frame->ptr;
                end_r_3137 = frame->endptr;
                return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_11360,
                                                                            pvrtmp_11351,
                                                                            pvrtmp_11362,
                                                                            loc_3134,
                                                                            pvrtmp_11364};
            } else {
                gib_shadowstack_push(rstack, b_290_822_1024_1642, end_r_3135,
                                     Stk, Ps_T);
                gib_shadowstack_push(rstack, fs_292_824_1026_1644, end_r_3136,
                                     Stk, Ps_T);
                gib_shadowstack_push(wstack, loc_3134, end_r_3137, Stk, Ps_T);

                GibChunk region_11373 =
                         gib_alloc_region(gib_get_inf_init_chunk_size());
                GibCursor r_4091 = region_11373.start;
                GibCursor end_r_4091 = region_11373.end;

                frame = gib_shadowstack_pop(wstack);
                loc_3134 = frame->ptr;
                end_r_3137 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                fs_292_824_1026_1644 = frame->ptr;
                end_r_3136 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                b_290_822_1024_1642 = frame->ptr;
                end_r_3135 = frame->endptr;

                GibCursor loc_4066 = r_4091 + 5;

                *(GibPackedTag *) r_4091 = 1;

                GibCursor writetag_7704 = r_4091 + 1;
                GibCursor after_tag_7705 = r_4091 + 1;

                *(GibFloat *) after_tag_7705 = f_291_823_1025_1643;

                GibCursor writecur_7709 = after_tag_7705 + sizeof(GibFloat);

                *(GibPackedTag *) loc_4066 = 0;

                GibCursor writetag_7697 = loc_4066 + 1;
                GibCursor after_tag_7698 = loc_4066 + 1;

                gib_shadowstack_push(rstack, r_4091, end_r_4091, Stk, Ps_T);
                gib_shadowstack_push(rstack, b_290_822_1024_1642, end_r_3135,
                                     Stk, Ps_T);
                gib_shadowstack_push(rstack, fs_292_824_1026_1644, end_r_3136,
                                     Stk, Ps_T);
                gib_shadowstack_push(wstack, loc_3134, end_r_3137, Stk, Ps_T);

                GibChunk region_11378 =
                         gib_alloc_region(gib_get_inf_init_chunk_size());
                GibCursor r_4090 = region_11378.start;
                GibCursor end_r_4090 = region_11378.end;

                frame = gib_shadowstack_pop(wstack);
                loc_3134 = frame->ptr;
                end_r_3137 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                fs_292_824_1026_1644 = frame->ptr;
                end_r_3136 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                b_290_822_1024_1642 = frame->ptr;
                end_r_3135 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                r_4091 = frame->ptr;
                end_r_4091 = frame->endptr;
                gib_shadowstack_push(rstack, r_4091, end_r_4091, Stk, Ps_T);
                gib_shadowstack_push(rstack, b_290_822_1024_1642, end_r_3135,
                                     Stk, Ps_T);
                gib_shadowstack_push(wstack, loc_3134, end_r_3137, Stk, Ps_T);

                GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_333
                                                                  =
                                                                   compose(end_r_3136, end_r_3135, end_r_4090, r_4090, fs_292_824_1026_1644, b_290_822_1024_1642);
                GibCursor pvrtmp_11379 = tmp_struct_333.field0;
                GibCursor pvrtmp_11380 = tmp_struct_333.field1;
                GibCursor pvrtmp_11381 = tmp_struct_333.field2;
                GibCursor pvrtmp_11382 = tmp_struct_333.field3;
                GibCursor pvrtmp_11383 = tmp_struct_333.field4;

                frame = gib_shadowstack_pop(wstack);
                loc_3134 = frame->ptr;
                end_r_3137 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                b_290_822_1024_1642 = frame->ptr;
                end_r_3135 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                r_4091 = frame->ptr;
                end_r_4091 = frame->endptr;
                gib_shadowstack_push(rstack, r_4091, end_r_4091, Stk, Ps_T);
                gib_shadowstack_push(rstack, pvrtmp_11382, pvrtmp_11381, Stk,
                                     Ps_T);
                gib_shadowstack_push(rstack, b_290_822_1024_1642, end_r_3135,
                                     Stk, Ps_T);
                gib_shadowstack_push(wstack, loc_3134, end_r_3137, Stk, Ps_T);

                GibChunk region_11388 =
                         gib_alloc_region(gib_get_inf_init_chunk_size());
                GibCursor r_4089 = region_11388.start;
                GibCursor end_r_4089 = region_11388.end;

                frame = gib_shadowstack_pop(wstack);
                loc_3134 = frame->ptr;
                end_r_3137 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                b_290_822_1024_1642 = frame->ptr;
                end_r_3135 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                pvrtmp_11382 = frame->ptr;
                pvrtmp_11381 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                r_4091 = frame->ptr;
                end_r_4091 = frame->endptr;
                gib_shadowstack_push(rstack, r_4091, end_r_4091, Stk, Ps_T);
                gib_shadowstack_push(wstack, loc_3134, end_r_3137, Stk, Ps_T);

                GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_334
                                                                  =
                                                                   psMult(end_r_3135, pvrtmp_11381, end_r_4089, r_4089, b_290_822_1024_1642, pvrtmp_11382);
                GibCursor pvrtmp_11389 = tmp_struct_334.field0;
                GibCursor pvrtmp_11390 = tmp_struct_334.field1;
                GibCursor pvrtmp_11391 = tmp_struct_334.field2;
                GibCursor pvrtmp_11392 = tmp_struct_334.field3;
                GibCursor pvrtmp_11393 = tmp_struct_334.field4;

                frame = gib_shadowstack_pop(wstack);
                loc_3134 = frame->ptr;
                end_r_3137 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                r_4091 = frame->ptr;
                end_r_4091 = frame->endptr;

                GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_335
                                                                  =
                                                                   psAdd(end_r_4091, pvrtmp_11391, end_r_3137, loc_3134, r_4091, pvrtmp_11392);
                GibCursor pvrtmp_11398 = tmp_struct_335.field0;
                GibCursor pvrtmp_11399 = tmp_struct_335.field1;
                GibCursor pvrtmp_11400 = tmp_struct_335.field2;
                GibCursor pvrtmp_11401 = tmp_struct_335.field3;
                GibCursor pvrtmp_11402 = tmp_struct_335.field4;

                return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_11389,
                                                                            pvrtmp_11379,
                                                                            pvrtmp_11400,
                                                                            pvrtmp_11401,
                                                                            pvrtmp_11402};
            }
            break;
        }

      case 2:
        {
            *(GibPackedTag *) loc_3134 = 2;

            GibCursor writetag_7726 = loc_3134 + 1;
            GibCursor after_tag_7727 = loc_3134 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3135,
                                                                        end_r_3136,
                                                                        end_r_3137,
                                                                        loc_3134,
                                                                        after_tag_7727};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_337 = *(uintptr_t *) tmpcur_11336;
            GibCursor tmpcur_11413 = GIB_UNTAG(tagged_tmpcur_337);
            GibCursor tmpaftercur_11414 = tmpcur_11336 + 8;
            uint16_t tmptag_11415 = GIB_GET_TAG(tagged_tmpcur_337);
            GibCursor end_from_tagged_indr_4751 = tmpcur_11413 + tmptag_11415;
            GibCursor jump_4753 = tmpcur_11336 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_336 =
                                                               caseFn_821(end_from_tagged_indr_4751, end_r_3136, end_r_3137, loc_3134, tmpcur_11413, f_291_823_1025_1643, fs_292_824_1026_1644);
            GibCursor pvrtmp_11416 = tmp_struct_336.field0;
            GibCursor pvrtmp_11417 = tmp_struct_336.field1;
            GibCursor pvrtmp_11418 = tmp_struct_336.field2;
            GibCursor pvrtmp_11419 = tmp_struct_336.field3;
            GibCursor pvrtmp_11420 = tmp_struct_336.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3135,
                                                                        pvrtmp_11417,
                                                                        pvrtmp_11418,
                                                                        pvrtmp_11419,
                                                                        pvrtmp_11420};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_339 = *(uintptr_t *) tmpcur_11336;
            GibCursor tmpcur_11427 = GIB_UNTAG(tagged_tmpcur_339);
            GibCursor tmpaftercur_11428 = tmpcur_11336 + 8;
            uint16_t tmptag_11429 = GIB_GET_TAG(tagged_tmpcur_339);
            GibCursor end_from_tagged_indr_4751 = tmpcur_11427 + tmptag_11429;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_338 =
                                                               caseFn_821(end_from_tagged_indr_4751, end_r_3136, end_r_3137, loc_3134, tmpcur_11427, f_291_823_1025_1643, fs_292_824_1026_1644);
            GibCursor pvrtmp_11430 = tmp_struct_338.field0;
            GibCursor pvrtmp_11431 = tmp_struct_338.field1;
            GibCursor pvrtmp_11432 = tmp_struct_338.field2;
            GibCursor pvrtmp_11433 = tmp_struct_338.field3;
            GibCursor pvrtmp_11434 = tmp_struct_338.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_11430,
                                                                        pvrtmp_11431,
                                                                        pvrtmp_11432,
                                                                        pvrtmp_11433,
                                                                        pvrtmp_11434};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_11335");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd caseFn_825(GibCursor end_r_3140,
                                                    GibCursor end_r_3141,
                                                    GibCursor loc_3139,
                                                    GibInt n_297_826_1029_1656,
                                                    GibCursor fs_298_827_1030_1657)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_3139 + 18 > end_r_3141) {
        gib_grow_region(&loc_3139, &end_r_3141);
    }

    GibPackedTag tmpval_11442 = *(GibPackedTag *) fs_298_827_1030_1657;
    GibCursor tmpcur_11443 = fs_298_827_1030_1657 + 1;


  switch_11492:
    ;
    switch (tmpval_11442) {

      case 0:
        {
            *(GibPackedTag *) loc_3139 = 0;

            GibCursor writetag_7746 = loc_3139 + 1;
            GibCursor after_tag_7747 = loc_3139 + 1;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_3140,
                                                               end_r_3141,
                                                               loc_3139,
                                                               after_tag_7747};
            break;
        }

      case 1:
        {
            GibFloat tmpval_11448 = *(GibFloat *) tmpcur_11443;
            GibCursor tmpcur_11449 = tmpcur_11443 + sizeof(GibFloat);
            GibInt fltAppE_1258_1660 = n_297_826_1029_1656 - 1;
            GibCursor loc_4102 = loc_3139 + 5;

            *(GibPackedTag *) loc_3139 = 1;

            GibCursor writetag_7758 = loc_3139 + 1;
            GibCursor after_tag_7759 = loc_3139 + 1;

            *(GibFloat *) after_tag_7759 = tmpval_11448;

            GibCursor writecur_7763 = after_tag_7759 + sizeof(GibFloat);
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_343 =
                                                      takePs(end_r_3140, end_r_3141, loc_4102, fltAppE_1258_1660, tmpcur_11449);
            GibCursor pvrtmp_11450 = tmp_struct_343.field0;
            GibCursor pvrtmp_11451 = tmp_struct_343.field1;
            GibCursor pvrtmp_11452 = tmp_struct_343.field2;
            GibCursor pvrtmp_11453 = tmp_struct_343.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_11450,
                                                               pvrtmp_11451,
                                                               loc_3139,
                                                               pvrtmp_11453};
            break;
        }

      case 2:
        {
            *(GibPackedTag *) loc_3139 = 2;

            GibCursor writetag_7768 = loc_3139 + 1;
            GibCursor after_tag_7769 = loc_3139 + 1;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_3140,
                                                               end_r_3141,
                                                               loc_3139,
                                                               after_tag_7769};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_345 = *(uintptr_t *) tmpcur_11443;
            GibCursor tmpcur_11466 = GIB_UNTAG(tagged_tmpcur_345);
            GibCursor tmpaftercur_11467 = tmpcur_11443 + 8;
            uint16_t tmptag_11468 = GIB_GET_TAG(tagged_tmpcur_345);
            GibCursor end_from_tagged_indr_4756 = tmpcur_11466 + tmptag_11468;
            GibCursor jump_4758 = tmpcur_11443 + 8;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_344 =
                                                      caseFn_825(end_from_tagged_indr_4756, end_r_3141, loc_3139, n_297_826_1029_1656, tmpcur_11466);
            GibCursor pvrtmp_11469 = tmp_struct_344.field0;
            GibCursor pvrtmp_11470 = tmp_struct_344.field1;
            GibCursor pvrtmp_11471 = tmp_struct_344.field2;
            GibCursor pvrtmp_11472 = tmp_struct_344.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_3140,
                                                               pvrtmp_11470,
                                                               pvrtmp_11471,
                                                               pvrtmp_11472};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_347 = *(uintptr_t *) tmpcur_11443;
            GibCursor tmpcur_11479 = GIB_UNTAG(tagged_tmpcur_347);
            GibCursor tmpaftercur_11480 = tmpcur_11443 + 8;
            uint16_t tmptag_11481 = GIB_GET_TAG(tagged_tmpcur_347);
            GibCursor end_from_tagged_indr_4756 = tmpcur_11479 + tmptag_11481;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_346 =
                                                      caseFn_825(end_from_tagged_indr_4756, end_r_3141, loc_3139, n_297_826_1029_1656, tmpcur_11479);
            GibCursor pvrtmp_11482 = tmp_struct_346.field0;
            GibCursor pvrtmp_11483 = tmp_struct_346.field1;
            GibCursor pvrtmp_11484 = tmp_struct_346.field2;
            GibCursor pvrtmp_11485 = tmp_struct_346.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_11482,
                                                               pvrtmp_11483,
                                                               pvrtmp_11484,
                                                               pvrtmp_11485};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_11442");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd caseFn_828(GibCursor end_r_3144,
                                                    GibCursor end_r_3145,
                                                    GibCursor loc_3143,
                                                    GibInt n_301_829_1033_1662,
                                                    GibCursor b_303_830_1034_1663)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_3143 + 18 > end_r_3145) {
        gib_grow_region(&loc_3143, &end_r_3145);
    }

    GibPackedTag tmpval_11493 = *(GibPackedTag *) b_303_830_1034_1663;
    GibCursor tmpcur_11494 = b_303_830_1034_1663 + 1;


  switch_11549:
    ;
    switch (tmpval_11493) {

      case 0:
        {
            *(GibPackedTag *) loc_3143 = 2;

            GibCursor writetag_7786 = loc_3143 + 1;
            GibCursor after_tag_7787 = loc_3143 + 1;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_3144,
                                                               end_r_3145,
                                                               loc_3143,
                                                               after_tag_7787};
            break;
        }

      case 1:
        {
            GibFloat tmpval_11499 = *(GibFloat *) tmpcur_11494;
            GibCursor tmpcur_11500 = tmpcur_11494 + sizeof(GibFloat);
            GibBool fltIf_1259_1666 = tmpval_11499 == 0.0;

            if (fltIf_1259_1666) {
                gib_shadowstack_push(rstack, tmpcur_11500, end_r_3144, Stk,
                                     Ps_T);
                gib_shadowstack_push(wstack, loc_3143, end_r_3145, Stk, Ps_T);

                GibChunk region_11501 =
                         gib_alloc_region(gib_get_inf_init_chunk_size());
                GibCursor r_4121 = region_11501.start;
                GibCursor end_r_4121 = region_11501.end;

                frame = gib_shadowstack_pop(wstack);
                loc_3143 = frame->ptr;
                end_r_3145 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                tmpcur_11500 = frame->ptr;
                end_r_3144 = frame->endptr;
                *(GibPackedTag *) r_4121 = 0;

                GibCursor writetag_7795 = r_4121 + 1;
                GibCursor after_tag_7796 = r_4121 + 1;
                GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_351
                                                                  =
                                                                   psDiv(end_r_4121, end_r_3144, end_r_3145, loc_3143, n_301_829_1033_1662, r_4121, tmpcur_11500);
                GibCursor pvrtmp_11504 = tmp_struct_351.field0;
                GibCursor pvrtmp_11505 = tmp_struct_351.field1;
                GibCursor pvrtmp_11506 = tmp_struct_351.field2;
                GibCursor pvrtmp_11507 = tmp_struct_351.field3;
                GibCursor pvrtmp_11508 = tmp_struct_351.field4;

                return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_11505,
                                                                   pvrtmp_11506,
                                                                   pvrtmp_11507,
                                                                   pvrtmp_11508};
            } else {
                *(GibPackedTag *) loc_3143 = 0;

                GibCursor writetag_7806 = loc_3143 + 1;
                GibCursor after_tag_7807 = loc_3143 + 1;

                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_3144,
                                                                   end_r_3145,
                                                                   loc_3143,
                                                                   after_tag_7807};
            }
            break;
        }

      case 2:
        {
            *(GibPackedTag *) loc_3143 = 2;

            GibCursor writetag_7814 = loc_3143 + 1;
            GibCursor after_tag_7815 = loc_3143 + 1;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_3144,
                                                               end_r_3145,
                                                               loc_3143,
                                                               after_tag_7815};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_353 = *(uintptr_t *) tmpcur_11494;
            GibCursor tmpcur_11523 = GIB_UNTAG(tagged_tmpcur_353);
            GibCursor tmpaftercur_11524 = tmpcur_11494 + 8;
            uint16_t tmptag_11525 = GIB_GET_TAG(tagged_tmpcur_353);
            GibCursor end_from_tagged_indr_4761 = tmpcur_11523 + tmptag_11525;
            GibCursor jump_4763 = tmpcur_11494 + 8;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_352 =
                                                      caseFn_828(end_from_tagged_indr_4761, end_r_3145, loc_3143, n_301_829_1033_1662, tmpcur_11523);
            GibCursor pvrtmp_11526 = tmp_struct_352.field0;
            GibCursor pvrtmp_11527 = tmp_struct_352.field1;
            GibCursor pvrtmp_11528 = tmp_struct_352.field2;
            GibCursor pvrtmp_11529 = tmp_struct_352.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_3144,
                                                               pvrtmp_11527,
                                                               pvrtmp_11528,
                                                               pvrtmp_11529};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_355 = *(uintptr_t *) tmpcur_11494;
            GibCursor tmpcur_11536 = GIB_UNTAG(tagged_tmpcur_355);
            GibCursor tmpaftercur_11537 = tmpcur_11494 + 8;
            uint16_t tmptag_11538 = GIB_GET_TAG(tagged_tmpcur_355);
            GibCursor end_from_tagged_indr_4761 = tmpcur_11536 + tmptag_11538;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_354 =
                                                      caseFn_828(end_from_tagged_indr_4761, end_r_3145, loc_3143, n_301_829_1033_1662, tmpcur_11536);
            GibCursor pvrtmp_11539 = tmp_struct_354.field0;
            GibCursor pvrtmp_11540 = tmp_struct_354.field1;
            GibCursor pvrtmp_11541 = tmp_struct_354.field2;
            GibCursor pvrtmp_11542 = tmp_struct_354.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_11539,
                                                               pvrtmp_11540,
                                                               pvrtmp_11541,
                                                               pvrtmp_11542};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_11493");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd caseFn_831(GibCursor end_r_3149,
                                                             GibCursor end_r_3150,
                                                             GibCursor end_r_3151,
                                                             GibCursor loc_3148,
                                                             GibInt n_301_832_1037_1668,
                                                             GibCursor b_303_833_1038_1669,
                                                             GibFloat f_306_834_1039_1670,
                                                             GibCursor fs_307_835_1040_1671)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_3148 + 18 > end_r_3151) {
        gib_grow_region(&loc_3148, &end_r_3151);
    }

    GibPackedTag tmpval_11550 = *(GibPackedTag *) b_303_833_1038_1669;
    GibCursor tmpcur_11551 = b_303_833_1038_1669 + 1;


  switch_11644:
    ;
    switch (tmpval_11550) {

      case 0:
        {
            *(GibPackedTag *) loc_3148 = 2;

            GibCursor writetag_7832 = loc_3148 + 1;
            GibCursor after_tag_7833 = loc_3148 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3149,
                                                                        end_r_3150,
                                                                        end_r_3151,
                                                                        loc_3148,
                                                                        after_tag_7833};
            break;
        }

      case 1:
        {
            GibFloat tmpval_11556 = *(GibFloat *) tmpcur_11551;
            GibCursor tmpcur_11557 = tmpcur_11551 + sizeof(GibFloat);
            GibBool fltPrm_1262_1674 = f_306_834_1039_1670 == 0.0;
            GibBool fltPrm_1263_1675 = tmpval_11556 == 0.0;
            GibBool fltIf_1261_1676 = fltPrm_1262_1674 && fltPrm_1263_1675;

            if (fltIf_1261_1676) {
                GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_359
                                                                  =
                                                                   psDiv(end_r_3150, end_r_3149, end_r_3151, loc_3148, n_301_832_1037_1668, fs_307_835_1040_1671, tmpcur_11557);
                GibCursor pvrtmp_11558 = tmp_struct_359.field0;
                GibCursor pvrtmp_11559 = tmp_struct_359.field1;
                GibCursor pvrtmp_11560 = tmp_struct_359.field2;
                GibCursor pvrtmp_11561 = tmp_struct_359.field3;
                GibCursor pvrtmp_11562 = tmp_struct_359.field4;

                return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_11559,
                                                                            pvrtmp_11558,
                                                                            pvrtmp_11560,
                                                                            pvrtmp_11561,
                                                                            pvrtmp_11562};
            } else {
                GibFloat q_310_1043_1677 = f_306_834_1039_1670 / tmpval_11556;
                GibInt fltAppE_1265_1678 = n_301_832_1037_1668 - 1;

                gib_shadowstack_push(rstack, b_303_833_1038_1669, end_r_3149,
                                     Stk, Ps_T);
                gib_shadowstack_push(rstack, fs_307_835_1040_1671, end_r_3150,
                                     Stk, Ps_T);
                gib_shadowstack_push(rstack, tmpcur_11557, end_r_3149, Stk,
                                     Ps_T);
                gib_shadowstack_push(wstack, loc_3148, end_r_3151, Stk, Ps_T);

                GibChunk region_11569 =
                         gib_alloc_region(gib_get_inf_init_chunk_size());
                GibCursor r_4161 = region_11569.start;
                GibCursor end_r_4161 = region_11569.end;

                frame = gib_shadowstack_pop(wstack);
                loc_3148 = frame->ptr;
                end_r_3151 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                tmpcur_11557 = frame->ptr;
                end_r_3149 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                fs_307_835_1040_1671 = frame->ptr;
                end_r_3150 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                b_303_833_1038_1669 = frame->ptr;
                end_r_3149 = frame->endptr;

                GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_360
                                                                  =
                                                                   dot(end_r_3149, end_r_4161, r_4161, q_310_1043_1677, tmpcur_11557);
                GibCursor pvrtmp_11570 = tmp_struct_360.field0;
                GibCursor pvrtmp_11571 = tmp_struct_360.field1;
                GibCursor pvrtmp_11572 = tmp_struct_360.field2;
                GibCursor pvrtmp_11573 = tmp_struct_360.field3;
                GibCursor pvrtmp_11574 = tmp_struct_360.field4;

                gib_shadowstack_push(rstack, pvrtmp_11573, pvrtmp_11571, Stk,
                                     Ps_T);
                gib_shadowstack_push(rstack, b_303_833_1038_1669, end_r_3149,
                                     Stk, Ps_T);
                gib_shadowstack_push(rstack, fs_307_835_1040_1671, end_r_3150,
                                     Stk, Ps_T);
                gib_shadowstack_push(wstack, loc_3148, end_r_3151, Stk, Ps_T);

                GibChunk region_11579 =
                         gib_alloc_region(gib_get_inf_init_chunk_size());
                GibCursor r_4160 = region_11579.start;
                GibCursor end_r_4160 = region_11579.end;

                frame = gib_shadowstack_pop(wstack);
                loc_3148 = frame->ptr;
                end_r_3151 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                fs_307_835_1040_1671 = frame->ptr;
                end_r_3150 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                b_303_833_1038_1669 = frame->ptr;
                end_r_3149 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                pvrtmp_11573 = frame->ptr;
                pvrtmp_11571 = frame->endptr;

                GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_361
                                                                  =
                                                                   psNeg(pvrtmp_11571, end_r_4160, r_4160, pvrtmp_11573);
                GibCursor pvrtmp_11580 = tmp_struct_361.field0;
                GibCursor pvrtmp_11581 = tmp_struct_361.field1;
                GibCursor pvrtmp_11582 = tmp_struct_361.field2;
                GibCursor pvrtmp_11583 = tmp_struct_361.field3;
                GibCursor pvrtmp_11584 = tmp_struct_361.field4;

                gib_shadowstack_push(rstack, pvrtmp_11583, pvrtmp_11581, Stk,
                                     Ps_T);
                gib_shadowstack_push(rstack, b_303_833_1038_1669, end_r_3149,
                                     Stk, Ps_T);
                gib_shadowstack_push(rstack, fs_307_835_1040_1671, end_r_3150,
                                     Stk, Ps_T);
                gib_shadowstack_push(wstack, loc_3148, end_r_3151, Stk, Ps_T);

                GibChunk region_11589 =
                         gib_alloc_region(gib_get_inf_init_chunk_size());
                GibCursor r_4159 = region_11589.start;
                GibCursor end_r_4159 = region_11589.end;

                frame = gib_shadowstack_pop(wstack);
                loc_3148 = frame->ptr;
                end_r_3151 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                fs_307_835_1040_1671 = frame->ptr;
                end_r_3150 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                b_303_833_1038_1669 = frame->ptr;
                end_r_3149 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                pvrtmp_11583 = frame->ptr;
                pvrtmp_11581 = frame->endptr;

                GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_362
                                                                  =
                                                                   psAdd(end_r_3150, pvrtmp_11581, end_r_4159, r_4159, fs_307_835_1040_1671, pvrtmp_11583);
                GibCursor pvrtmp_11590 = tmp_struct_362.field0;
                GibCursor pvrtmp_11591 = tmp_struct_362.field1;
                GibCursor pvrtmp_11592 = tmp_struct_362.field2;
                GibCursor pvrtmp_11593 = tmp_struct_362.field3;
                GibCursor pvrtmp_11594 = tmp_struct_362.field4;
                GibCursor loc_4155 = loc_3148 + 5;

                *(GibPackedTag *) loc_3148 = 1;

                GibCursor writetag_7859 = loc_3148 + 1;
                GibCursor after_tag_7860 = loc_3148 + 1;

                *(GibFloat *) after_tag_7860 = q_310_1043_1677;

                GibCursor writecur_7864 = after_tag_7860 + sizeof(GibFloat);

                gib_shadowstack_push(rstack, loc_3148, end_r_3151, Stk, Ps_T);

                GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_363
                                                                  =
                                                                   psDiv(pvrtmp_11592, end_r_3149, end_r_3151, loc_4155, fltAppE_1265_1678, pvrtmp_11593, b_303_833_1038_1669);
                GibCursor pvrtmp_11599 = tmp_struct_363.field0;
                GibCursor pvrtmp_11600 = tmp_struct_363.field1;
                GibCursor pvrtmp_11601 = tmp_struct_363.field2;
                GibCursor pvrtmp_11602 = tmp_struct_363.field3;
                GibCursor pvrtmp_11603 = tmp_struct_363.field4;

                frame = gib_shadowstack_pop(rstack);
                loc_3148 = frame->ptr;
                end_r_3151 = frame->endptr;
                return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_11600,
                                                                            pvrtmp_11590,
                                                                            pvrtmp_11601,
                                                                            loc_3148,
                                                                            pvrtmp_11603};
            }
            break;
        }

      case 2:
        {
            *(GibPackedTag *) loc_3148 = 2;

            GibCursor writetag_7869 = loc_3148 + 1;
            GibCursor after_tag_7870 = loc_3148 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3149,
                                                                        end_r_3150,
                                                                        end_r_3151,
                                                                        loc_3148,
                                                                        after_tag_7870};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_365 = *(uintptr_t *) tmpcur_11551;
            GibCursor tmpcur_11616 = GIB_UNTAG(tagged_tmpcur_365);
            GibCursor tmpaftercur_11617 = tmpcur_11551 + 8;
            uint16_t tmptag_11618 = GIB_GET_TAG(tagged_tmpcur_365);
            GibCursor end_from_tagged_indr_4766 = tmpcur_11616 + tmptag_11618;
            GibCursor jump_4768 = tmpcur_11551 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_364 =
                                                               caseFn_831(end_from_tagged_indr_4766, end_r_3150, end_r_3151, loc_3148, n_301_832_1037_1668, tmpcur_11616, f_306_834_1039_1670, fs_307_835_1040_1671);
            GibCursor pvrtmp_11619 = tmp_struct_364.field0;
            GibCursor pvrtmp_11620 = tmp_struct_364.field1;
            GibCursor pvrtmp_11621 = tmp_struct_364.field2;
            GibCursor pvrtmp_11622 = tmp_struct_364.field3;
            GibCursor pvrtmp_11623 = tmp_struct_364.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3149,
                                                                        pvrtmp_11620,
                                                                        pvrtmp_11621,
                                                                        pvrtmp_11622,
                                                                        pvrtmp_11623};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_367 = *(uintptr_t *) tmpcur_11551;
            GibCursor tmpcur_11630 = GIB_UNTAG(tagged_tmpcur_367);
            GibCursor tmpaftercur_11631 = tmpcur_11551 + 8;
            uint16_t tmptag_11632 = GIB_GET_TAG(tagged_tmpcur_367);
            GibCursor end_from_tagged_indr_4766 = tmpcur_11630 + tmptag_11632;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_366 =
                                                               caseFn_831(end_from_tagged_indr_4766, end_r_3150, end_r_3151, loc_3148, n_301_832_1037_1668, tmpcur_11630, f_306_834_1039_1670, fs_307_835_1040_1671);
            GibCursor pvrtmp_11633 = tmp_struct_366.field0;
            GibCursor pvrtmp_11634 = tmp_struct_366.field1;
            GibCursor pvrtmp_11635 = tmp_struct_366.field2;
            GibCursor pvrtmp_11636 = tmp_struct_366.field3;
            GibCursor pvrtmp_11637 = tmp_struct_366.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_11633,
                                                                        pvrtmp_11634,
                                                                        pvrtmp_11635,
                                                                        pvrtmp_11636,
                                                                        pvrtmp_11637};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_11550");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd caseFn_836(GibCursor end_r_3155,
                                                             GibCursor end_r_3156,
                                                             GibCursor end_r_3157,
                                                             GibCursor loc_3154,
                                                             GibInt n_301_837_1044_1683,
                                                             GibCursor a_302_838_1045_1684,
                                                             GibCursor b_303_839_1046_1685)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_3154 + 18 > end_r_3157) {
        gib_grow_region(&loc_3154, &end_r_3157);
    }

    GibPackedTag tmpval_11645 = *(GibPackedTag *) a_302_838_1045_1684;
    GibCursor tmpcur_11646 = a_302_838_1045_1684 + 1;


  switch_11702:
    ;
    switch (tmpval_11645) {

      case 0:
        {
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_371 =
                                                      caseFn_828(end_r_3156, end_r_3157, loc_3154, n_301_837_1044_1683, b_303_839_1046_1685);
            GibCursor pvrtmp_11647 = tmp_struct_371.field0;
            GibCursor pvrtmp_11648 = tmp_struct_371.field1;
            GibCursor pvrtmp_11649 = tmp_struct_371.field2;
            GibCursor pvrtmp_11650 = tmp_struct_371.field3;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3155,
                                                                        pvrtmp_11647,
                                                                        pvrtmp_11648,
                                                                        pvrtmp_11649,
                                                                        pvrtmp_11650};
            break;
        }

      case 1:
        {
            GibFloat tmpval_11657 = *(GibFloat *) tmpcur_11646;
            GibCursor tmpcur_11658 = tmpcur_11646 + sizeof(GibFloat);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_372 =
                                                               caseFn_831(end_r_3156, end_r_3155, end_r_3157, loc_3154, n_301_837_1044_1683, b_303_839_1046_1685, tmpval_11657, tmpcur_11658);
            GibCursor pvrtmp_11659 = tmp_struct_372.field0;
            GibCursor pvrtmp_11660 = tmp_struct_372.field1;
            GibCursor pvrtmp_11661 = tmp_struct_372.field2;
            GibCursor pvrtmp_11662 = tmp_struct_372.field3;
            GibCursor pvrtmp_11663 = tmp_struct_372.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_11660,
                                                                        pvrtmp_11659,
                                                                        pvrtmp_11661,
                                                                        pvrtmp_11662,
                                                                        pvrtmp_11663};
            break;
        }

      case 2:
        {
            *(GibPackedTag *) loc_3154 = 2;

            GibCursor writetag_7899 = loc_3154 + 1;
            GibCursor after_tag_7900 = loc_3154 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3155,
                                                                        end_r_3156,
                                                                        end_r_3157,
                                                                        loc_3154,
                                                                        after_tag_7900};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_374 = *(uintptr_t *) tmpcur_11646;
            GibCursor tmpcur_11674 = GIB_UNTAG(tagged_tmpcur_374);
            GibCursor tmpaftercur_11675 = tmpcur_11646 + 8;
            uint16_t tmptag_11676 = GIB_GET_TAG(tagged_tmpcur_374);
            GibCursor end_from_tagged_indr_4771 = tmpcur_11674 + tmptag_11676;
            GibCursor jump_4773 = tmpcur_11646 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_373 =
                                                               caseFn_836(end_from_tagged_indr_4771, end_r_3156, end_r_3157, loc_3154, n_301_837_1044_1683, tmpcur_11674, b_303_839_1046_1685);
            GibCursor pvrtmp_11677 = tmp_struct_373.field0;
            GibCursor pvrtmp_11678 = tmp_struct_373.field1;
            GibCursor pvrtmp_11679 = tmp_struct_373.field2;
            GibCursor pvrtmp_11680 = tmp_struct_373.field3;
            GibCursor pvrtmp_11681 = tmp_struct_373.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3155,
                                                                        pvrtmp_11678,
                                                                        pvrtmp_11679,
                                                                        pvrtmp_11680,
                                                                        pvrtmp_11681};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_376 = *(uintptr_t *) tmpcur_11646;
            GibCursor tmpcur_11688 = GIB_UNTAG(tagged_tmpcur_376);
            GibCursor tmpaftercur_11689 = tmpcur_11646 + 8;
            uint16_t tmptag_11690 = GIB_GET_TAG(tagged_tmpcur_376);
            GibCursor end_from_tagged_indr_4771 = tmpcur_11688 + tmptag_11690;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_375 =
                                                               caseFn_836(end_from_tagged_indr_4771, end_r_3156, end_r_3157, loc_3154, n_301_837_1044_1683, tmpcur_11688, b_303_839_1046_1685);
            GibCursor pvrtmp_11691 = tmp_struct_375.field0;
            GibCursor pvrtmp_11692 = tmp_struct_375.field1;
            GibCursor pvrtmp_11693 = tmp_struct_375.field2;
            GibCursor pvrtmp_11694 = tmp_struct_375.field3;
            GibCursor pvrtmp_11695 = tmp_struct_375.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_11691,
                                                                        pvrtmp_11692,
                                                                        pvrtmp_11693,
                                                                        pvrtmp_11694,
                                                                        pvrtmp_11695};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_11645");
            exit(1);
        }
    }
}
static inline
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd caseFn_840(GibCursor end_r_3161,
                                                                      GibCursor end_r_3162,
                                                                      GibCursor end_r_3163,
                                                                      GibCursor loc_3160,
                                                                      GibCursor b_312_841_1049_1688,
                                                                      GibFloat f_313_842_1050_1689,
                                                                      GibCursor fs_314_843_1051_1690)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_3160 + 18 > end_r_3163) {
        gib_grow_region(&loc_3160, &end_r_3163);
    }

    GibPackedTag tmpval_11703 = *(GibPackedTag *) b_312_841_1049_1688;
    GibCursor tmpcur_11704 = b_312_841_1049_1688 + 1;


  switch_11816:
    ;
    switch (tmpval_11703) {

      case 0:
        {
            GibCursor jump_4580 = b_312_841_1049_1688 + 1;

            *(GibPackedTag *) loc_3160 = 0;

            GibCursor writetag_7919 = loc_3160 + 1;
            GibCursor after_tag_7920 = loc_3160 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3161,
                                                                                 end_r_3162,
                                                                                 end_r_3163,
                                                                                 jump_4580,
                                                                                 loc_3160,
                                                                                 after_tag_7920};
            break;
        }

      case 1:
        {
            GibFloat tmpval_11709 = *(GibFloat *) tmpcur_11704;
            GibCursor tmpcur_11710 = tmpcur_11704 + sizeof(GibFloat);
            GibFloat fltPkd_1269_1693 = f_313_842_1050_1689 * tmpval_11709;

            gib_shadowstack_push(rstack, fs_314_843_1051_1690, end_r_3162, Stk,
                                 Ps_T);
            gib_shadowstack_push(rstack, tmpcur_11710, end_r_3161, Stk, Ps_T);
            gib_shadowstack_push(wstack, loc_3160, end_r_3163, Stk, Ps_T);

            GibChunk region_11711 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_4226 = region_11711.start;
            GibCursor end_r_4226 = region_11711.end;

            frame = gib_shadowstack_pop(wstack);
            loc_3160 = frame->ptr;
            end_r_3163 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tmpcur_11710 = frame->ptr;
            end_r_3161 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            fs_314_843_1051_1690 = frame->ptr;
            end_r_3162 = frame->endptr;

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_380 =
                                                               dot(end_r_3161, end_r_4226, r_4226, f_313_842_1050_1689, tmpcur_11710);
            GibCursor pvrtmp_11712 = tmp_struct_380.field0;
            GibCursor pvrtmp_11713 = tmp_struct_380.field1;
            GibCursor pvrtmp_11714 = tmp_struct_380.field2;
            GibCursor pvrtmp_11715 = tmp_struct_380.field3;
            GibCursor pvrtmp_11716 = tmp_struct_380.field4;

            gib_shadowstack_push(rstack, pvrtmp_11715, pvrtmp_11713, Stk, Ps_T);
            gib_shadowstack_push(rstack, fs_314_843_1051_1690, end_r_3162, Stk,
                                 Ps_T);
            gib_shadowstack_push(rstack, tmpcur_11710, end_r_3161, Stk, Ps_T);
            gib_shadowstack_push(wstack, loc_3160, end_r_3163, Stk, Ps_T);

            GibChunk region_11721 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_4225 = region_11721.start;
            GibCursor end_r_4225 = region_11721.end;

            frame = gib_shadowstack_pop(wstack);
            loc_3160 = frame->ptr;
            end_r_3163 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tmpcur_11710 = frame->ptr;
            end_r_3161 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            fs_314_843_1051_1690 = frame->ptr;
            end_r_3162 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_11715 = frame->ptr;
            pvrtmp_11713 = frame->endptr;

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_381 =
                                                               dot(end_r_3162, end_r_4225, r_4225, tmpval_11709, fs_314_843_1051_1690);
            GibCursor pvrtmp_11722 = tmp_struct_381.field0;
            GibCursor pvrtmp_11723 = tmp_struct_381.field1;
            GibCursor pvrtmp_11724 = tmp_struct_381.field2;
            GibCursor pvrtmp_11725 = tmp_struct_381.field3;
            GibCursor pvrtmp_11726 = tmp_struct_381.field4;

            gib_shadowstack_push(rstack, pvrtmp_11715, pvrtmp_11713, Stk, Ps_T);
            gib_shadowstack_push(rstack, pvrtmp_11725, pvrtmp_11723, Stk, Ps_T);
            gib_shadowstack_push(rstack, fs_314_843_1051_1690, end_r_3162, Stk,
                                 Ps_T);
            gib_shadowstack_push(rstack, tmpcur_11710, end_r_3161, Stk, Ps_T);
            gib_shadowstack_push(wstack, loc_3160, end_r_3163, Stk, Ps_T);

            GibChunk region_11731 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_4224 = region_11731.start;
            GibCursor end_r_4224 = region_11731.end;

            frame = gib_shadowstack_pop(wstack);
            loc_3160 = frame->ptr;
            end_r_3163 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tmpcur_11710 = frame->ptr;
            end_r_3161 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            fs_314_843_1051_1690 = frame->ptr;
            end_r_3162 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_11725 = frame->ptr;
            pvrtmp_11723 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_11715 = frame->ptr;
            pvrtmp_11713 = frame->endptr;

            GibCursorGibCursorGibCursorProd tmp_struct_382 =
                                             psX(end_r_4224, r_4224);
            GibCursor pvrtmp_11732 = tmp_struct_382.field0;
            GibCursor pvrtmp_11733 = tmp_struct_382.field1;
            GibCursor pvrtmp_11734 = tmp_struct_382.field2;

            gib_shadowstack_push(rstack, pvrtmp_11715, pvrtmp_11713, Stk, Ps_T);
            gib_shadowstack_push(rstack, pvrtmp_11725, pvrtmp_11723, Stk, Ps_T);
            gib_shadowstack_push(rstack, pvrtmp_11733, pvrtmp_11732, Stk, Ps_T);
            gib_shadowstack_push(rstack, fs_314_843_1051_1690, end_r_3162, Stk,
                                 Ps_T);
            gib_shadowstack_push(rstack, tmpcur_11710, end_r_3161, Stk, Ps_T);
            gib_shadowstack_push(wstack, loc_3160, end_r_3163, Stk, Ps_T);

            GibChunk region_11739 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_4223 = region_11739.start;
            GibCursor end_r_4223 = region_11739.end;

            frame = gib_shadowstack_pop(wstack);
            loc_3160 = frame->ptr;
            end_r_3163 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tmpcur_11710 = frame->ptr;
            end_r_3161 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            fs_314_843_1051_1690 = frame->ptr;
            end_r_3162 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_11733 = frame->ptr;
            pvrtmp_11732 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_11725 = frame->ptr;
            pvrtmp_11723 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_11715 = frame->ptr;
            pvrtmp_11713 = frame->endptr;
            gib_shadowstack_push(rstack, pvrtmp_11715, pvrtmp_11713, Stk, Ps_T);
            gib_shadowstack_push(rstack, pvrtmp_11725, pvrtmp_11723, Stk, Ps_T);
            gib_shadowstack_push(rstack, pvrtmp_11733, pvrtmp_11732, Stk, Ps_T);
            gib_shadowstack_push(wstack, loc_3160, end_r_3163, Stk, Ps_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_383 =
                                                               psMult(end_r_3162, end_r_3161, end_r_4223, r_4223, fs_314_843_1051_1690, tmpcur_11710);
            GibCursor pvrtmp_11740 = tmp_struct_383.field0;
            GibCursor pvrtmp_11741 = tmp_struct_383.field1;
            GibCursor pvrtmp_11742 = tmp_struct_383.field2;
            GibCursor pvrtmp_11743 = tmp_struct_383.field3;
            GibCursor pvrtmp_11744 = tmp_struct_383.field4;

            frame = gib_shadowstack_pop(wstack);
            loc_3160 = frame->ptr;
            end_r_3163 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_11733 = frame->ptr;
            pvrtmp_11732 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_11725 = frame->ptr;
            pvrtmp_11723 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_11715 = frame->ptr;
            pvrtmp_11713 = frame->endptr;
            gib_shadowstack_push(rstack, pvrtmp_11715, pvrtmp_11713, Stk, Ps_T);
            gib_shadowstack_push(rstack, pvrtmp_11725, pvrtmp_11723, Stk, Ps_T);
            gib_shadowstack_push(rstack, pvrtmp_11733, pvrtmp_11732, Stk, Ps_T);
            gib_shadowstack_push(rstack, pvrtmp_11743, pvrtmp_11742, Stk, Ps_T);
            gib_shadowstack_push(wstack, loc_3160, end_r_3163, Stk, Ps_T);

            GibChunk region_11749 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_4222 = region_11749.start;
            GibCursor end_r_4222 = region_11749.end;

            frame = gib_shadowstack_pop(wstack);
            loc_3160 = frame->ptr;
            end_r_3163 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_11743 = frame->ptr;
            pvrtmp_11742 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_11733 = frame->ptr;
            pvrtmp_11732 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_11725 = frame->ptr;
            pvrtmp_11723 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_11715 = frame->ptr;
            pvrtmp_11713 = frame->endptr;
            gib_shadowstack_push(rstack, pvrtmp_11715, pvrtmp_11713, Stk, Ps_T);
            gib_shadowstack_push(rstack, pvrtmp_11725, pvrtmp_11723, Stk, Ps_T);
            gib_shadowstack_push(wstack, loc_3160, end_r_3163, Stk, Ps_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_384 =
                                                               psMult(pvrtmp_11732, pvrtmp_11742, end_r_4222, r_4222, pvrtmp_11733, pvrtmp_11743);
            GibCursor pvrtmp_11750 = tmp_struct_384.field0;
            GibCursor pvrtmp_11751 = tmp_struct_384.field1;
            GibCursor pvrtmp_11752 = tmp_struct_384.field2;
            GibCursor pvrtmp_11753 = tmp_struct_384.field3;
            GibCursor pvrtmp_11754 = tmp_struct_384.field4;

            frame = gib_shadowstack_pop(wstack);
            loc_3160 = frame->ptr;
            end_r_3163 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_11725 = frame->ptr;
            pvrtmp_11723 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_11715 = frame->ptr;
            pvrtmp_11713 = frame->endptr;
            gib_shadowstack_push(rstack, pvrtmp_11715, pvrtmp_11713, Stk, Ps_T);
            gib_shadowstack_push(rstack, pvrtmp_11725, pvrtmp_11723, Stk, Ps_T);
            gib_shadowstack_push(rstack, pvrtmp_11753, pvrtmp_11752, Stk, Ps_T);
            gib_shadowstack_push(wstack, loc_3160, end_r_3163, Stk, Ps_T);

            GibChunk region_11759 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_4221 = region_11759.start;
            GibCursor end_r_4221 = region_11759.end;

            frame = gib_shadowstack_pop(wstack);
            loc_3160 = frame->ptr;
            end_r_3163 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_11753 = frame->ptr;
            pvrtmp_11752 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_11725 = frame->ptr;
            pvrtmp_11723 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            pvrtmp_11715 = frame->ptr;
            pvrtmp_11713 = frame->endptr;

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_385 =
                                                               psAdd(pvrtmp_11723, pvrtmp_11752, end_r_4221, r_4221, pvrtmp_11725, pvrtmp_11753);
            GibCursor pvrtmp_11760 = tmp_struct_385.field0;
            GibCursor pvrtmp_11761 = tmp_struct_385.field1;
            GibCursor pvrtmp_11762 = tmp_struct_385.field2;
            GibCursor pvrtmp_11763 = tmp_struct_385.field3;
            GibCursor pvrtmp_11764 = tmp_struct_385.field4;
            GibCursor loc_4217 = loc_3160 + 5;

            *(GibPackedTag *) loc_3160 = 1;

            GibCursor writetag_7952 = loc_3160 + 1;
            GibCursor after_tag_7953 = loc_3160 + 1;

            *(GibFloat *) after_tag_7953 = fltPkd_1269_1693;

            GibCursor writecur_7957 = after_tag_7953 + sizeof(GibFloat);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_386 =
                                                               psAdd(pvrtmp_11713, pvrtmp_11762, end_r_3163, loc_4217, pvrtmp_11715, pvrtmp_11763);
            GibCursor pvrtmp_11769 = tmp_struct_386.field0;
            GibCursor pvrtmp_11770 = tmp_struct_386.field1;
            GibCursor pvrtmp_11771 = tmp_struct_386.field2;
            GibCursor pvrtmp_11772 = tmp_struct_386.field3;
            GibCursor pvrtmp_11773 = tmp_struct_386.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_11741,
                                                                                 pvrtmp_11740,
                                                                                 pvrtmp_11771,
                                                                                 pvrtmp_11714,
                                                                                 loc_3160,
                                                                                 pvrtmp_11773};
            break;
        }

      case 2:
        {
            GibCursor jump_4586 = b_312_841_1049_1688 + 1;

            *(GibPackedTag *) loc_3160 = 2;

            GibCursor writetag_7962 = loc_3160 + 1;
            GibCursor after_tag_7963 = loc_3160 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3161,
                                                                                 end_r_3162,
                                                                                 end_r_3163,
                                                                                 jump_4586,
                                                                                 loc_3160,
                                                                                 after_tag_7963};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_388 = *(uintptr_t *) tmpcur_11704;
            GibCursor tmpcur_11786 = GIB_UNTAG(tagged_tmpcur_388);
            GibCursor tmpaftercur_11787 = tmpcur_11704 + 8;
            uint16_t tmptag_11788 = GIB_GET_TAG(tagged_tmpcur_388);
            GibCursor end_from_tagged_indr_4776 = tmpcur_11786 + tmptag_11788;
            GibCursor jump_4778 = tmpcur_11704 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_387 =
             caseFn_840(end_from_tagged_indr_4776, end_r_3162, end_r_3163, loc_3160, tmpcur_11786, f_313_842_1050_1689, fs_314_843_1051_1690);
            GibCursor pvrtmp_11789 = tmp_struct_387.field0;
            GibCursor pvrtmp_11790 = tmp_struct_387.field1;
            GibCursor pvrtmp_11791 = tmp_struct_387.field2;
            GibCursor pvrtmp_11792 = tmp_struct_387.field3;
            GibCursor pvrtmp_11793 = tmp_struct_387.field4;
            GibCursor pvrtmp_11794 = tmp_struct_387.field5;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3161,
                                                                                 pvrtmp_11790,
                                                                                 pvrtmp_11791,
                                                                                 jump_4778,
                                                                                 pvrtmp_11793,
                                                                                 pvrtmp_11794};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_390 = *(uintptr_t *) tmpcur_11704;
            GibCursor tmpcur_11801 = GIB_UNTAG(tagged_tmpcur_390);
            GibCursor tmpaftercur_11802 = tmpcur_11704 + 8;
            uint16_t tmptag_11803 = GIB_GET_TAG(tagged_tmpcur_390);
            GibCursor end_from_tagged_indr_4776 = tmpcur_11801 + tmptag_11803;
            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_389 =
             caseFn_840(end_from_tagged_indr_4776, end_r_3162, end_r_3163, loc_3160, tmpcur_11801, f_313_842_1050_1689, fs_314_843_1051_1690);
            GibCursor pvrtmp_11804 = tmp_struct_389.field0;
            GibCursor pvrtmp_11805 = tmp_struct_389.field1;
            GibCursor pvrtmp_11806 = tmp_struct_389.field2;
            GibCursor pvrtmp_11807 = tmp_struct_389.field3;
            GibCursor pvrtmp_11808 = tmp_struct_389.field4;
            GibCursor pvrtmp_11809 = tmp_struct_389.field5;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_11804,
                                                                                 pvrtmp_11805,
                                                                                 pvrtmp_11806,
                                                                                 pvrtmp_11807,
                                                                                 pvrtmp_11808,
                                                                                 pvrtmp_11809};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_11703");
            exit(1);
        }
    }
}
static inline
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd caseFn_844(GibCursor end_r_3168,
                                                                      GibCursor end_r_3169,
                                                                      GibCursor end_r_3170,
                                                                      GibCursor end_r_3171,
                                                                      GibCursor loc_3167,
                                                                      GibCursor a_317_845_1054_1701,
                                                                      GibCursor b_318_846_1055_1702,
                                                                      GibFloat f_319_847_1056_1703,
                                                                      GibCursor fs_320_848_1057_1704)
{
    // GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    // GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    // GibShadowstackFrame *frame;

    if (loc_3167 + 18 > end_r_3171) {
        gib_grow_region(&loc_3167, &end_r_3171);
    }

    GibPackedTag tmpval_11817 = *(GibPackedTag *) b_318_846_1055_1702;
    GibCursor tmpcur_11818 = b_318_846_1055_1702 + 1;


  switch_11872:
    ;
    switch (tmpval_11817) {

      case 0:
        {
            // if (loc_3167 + 18 > end_r_3171) {
            //     gib_grow_region(&loc_3167, &end_r_3171);
            // }
            gib_indirection_barrier(loc_3167, end_r_3171, a_317_845_1054_1701,
                                    end_r_3168, Ps_T);

            GibCursor end_7983 = loc_3167 + 9;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3168,
                                                                                 end_r_3169,
                                                                                 end_r_3170,
                                                                                 end_r_3171,
                                                                                 loc_3167,
                                                                                 end_7983};
            break;
        }

      case 1:
        {
            GibFloat tmpval_11823 = *(GibFloat *) tmpcur_11818;
            GibCursor tmpcur_11824 = tmpcur_11818 + sizeof(GibFloat);
            GibFloat fltPkd_1277_1707 = f_319_847_1056_1703 + tmpval_11823;
            GibCursor loc_4238 = loc_3167 + 5;

            *(GibPackedTag *) loc_3167 = 1;

            GibCursor writetag_7991 = loc_3167 + 1;
            GibCursor after_tag_7992 = loc_3167 + 1;

            *(GibFloat *) after_tag_7992 = fltPkd_1277_1707;

            GibCursor writecur_7996 = after_tag_7992 + sizeof(GibFloat);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_397 =
                                                               psAdd(end_r_3170, end_r_3169, end_r_3171, loc_4238, fs_320_848_1057_1704, tmpcur_11824);
            GibCursor pvrtmp_11825 = tmp_struct_397.field0;
            GibCursor pvrtmp_11826 = tmp_struct_397.field1;
            GibCursor pvrtmp_11827 = tmp_struct_397.field2;
            GibCursor pvrtmp_11828 = tmp_struct_397.field3;
            GibCursor pvrtmp_11829 = tmp_struct_397.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3168,
                                                                                 pvrtmp_11826,
                                                                                 pvrtmp_11825,
                                                                                 pvrtmp_11827,
                                                                                 loc_3167,
                                                                                 pvrtmp_11829};
            break;
        }

      case 2:
        {
            *(GibPackedTag *) loc_3167 = 2;

            GibCursor writetag_8001 = loc_3167 + 1;
            GibCursor after_tag_8002 = loc_3167 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_3168,
                                                                                 end_r_3169,
                                                                                 end_r_3170,
                                                                                 end_r_3171,
                                                                                 loc_3167,
                                                                                 after_tag_8002};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_399 = *(uintptr_t *) tmpcur_11818;
            GibCursor tmpcur_11842 = GIB_UNTAG(tagged_tmpcur_399);
            GibCursor tmpaftercur_11843 = tmpcur_11818 + 8;
            uint16_t tmptag_11844 = GIB_GET_TAG(tagged_tmpcur_399);
            GibCursor end_from_tagged_indr_4782 = tmpcur_11842 + tmptag_11844;
            GibCursor jump_4784 = tmpcur_11818 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_398 =
             caseFn_844(end_r_3168, end_from_tagged_indr_4782, end_r_3170, end_r_3171, loc_3167, a_317_845_1054_1701, tmpcur_11842, f_319_847_1056_1703, fs_320_848_1057_1704);
            GibCursor pvrtmp_11845 = tmp_struct_398.field0;
            GibCursor pvrtmp_11846 = tmp_struct_398.field1;
            GibCursor pvrtmp_11847 = tmp_struct_398.field2;
            GibCursor pvrtmp_11848 = tmp_struct_398.field3;
            GibCursor pvrtmp_11849 = tmp_struct_398.field4;
            GibCursor pvrtmp_11850 = tmp_struct_398.field5;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_11845,
                                                                                 end_r_3169,
                                                                                 pvrtmp_11847,
                                                                                 pvrtmp_11848,
                                                                                 pvrtmp_11849,
                                                                                 pvrtmp_11850};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_401 = *(uintptr_t *) tmpcur_11818;
            GibCursor tmpcur_11857 = GIB_UNTAG(tagged_tmpcur_401);
            GibCursor tmpaftercur_11858 = tmpcur_11818 + 8;
            uint16_t tmptag_11859 = GIB_GET_TAG(tagged_tmpcur_401);
            GibCursor end_from_tagged_indr_4782 = tmpcur_11857 + tmptag_11859;
            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_400 =
             caseFn_844(end_r_3168, end_from_tagged_indr_4782, end_r_3170, end_r_3171, loc_3167, a_317_845_1054_1701, tmpcur_11857, f_319_847_1056_1703, fs_320_848_1057_1704);
            GibCursor pvrtmp_11860 = tmp_struct_400.field0;
            GibCursor pvrtmp_11861 = tmp_struct_400.field1;
            GibCursor pvrtmp_11862 = tmp_struct_400.field2;
            GibCursor pvrtmp_11863 = tmp_struct_400.field3;
            GibCursor pvrtmp_11864 = tmp_struct_400.field4;
            GibCursor pvrtmp_11865 = tmp_struct_400.field5;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_11860,
                                                                                 pvrtmp_11861,
                                                                                 pvrtmp_11862,
                                                                                 pvrtmp_11863,
                                                                                 pvrtmp_11864,
                                                                                 pvrtmp_11865};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_11817");
            exit(1);
        }
    }
}
int main(int argc, char **argv)
{
    int init_405 = gib_init(argc, argv);

    info_table_initialize();
    symbol_table_initialize();

    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool fltIf_1060_1279 = strcmp("ts", gib_read_bench_prog_param()) == 0;

    if (fltIf_1060_1279) {
        unsigned char tailapp_4593 =  bench_ts();

        printf("'#()");
        printf("\n");
        // return 0;
    } else {
        GibBool fltIf_1061_1280 = strcmp("psb", gib_read_bench_prog_param()) ==
                0;

        if (fltIf_1061_1280) {
            unsigned char tailapp_4594 =  bench_psb();

            printf("'#()");
            printf("\n");
            // return 0;
        } else {
            GibBool fltIf_1062_1281 = strcmp("psc",
                                             gib_read_bench_prog_param()) == 0;

            if (fltIf_1062_1281) {
                unsigned char tailapp_4595 =  bench_psc();

                printf("'#()");
                printf("\n");
                // return 0;
            } else {
                unsigned char wildcard__232_235_849_1282 =
                              gib_print_symbol(9420);

                printf("'#()");
                printf("\n");
                // return 0;
            }
        }
    }

    int exit_406 = gib_exit();

    return exit_406;
}
