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
typedef struct GibCursorGibIntProd_struct {
            GibCursor field0;
            GibInt field1;
        } GibCursorGibIntProd;
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
GibCursorGibCursorGibCursorProd helper(GibCursor end_r_851, GibCursor loc_850,
                                       GibInt s_58_235_367,
                                       GibInt e_59_236_368);
GibCursorGibCursorGibIntProd countnodes(GibCursor end_r_853,
                                        GibCursor tr_61_238_378);
GibCursorGibCursorGibCursorGibCursorProd loop(GibCursor end_r_856,
                                              GibCursor end_r_857,
                                              GibCursor loc_855,
                                              GibCursor tr_66_243_386,
                                              GibInt n_67_244_387);
GibCursorGibCursorGibIntProd sum_tree(GibCursor end_r_859,
                                      GibCursor tr_69_246_398);
GibCursorGibCursorGibCursorGibCursorProd tree_delete(GibCursor end_r_862,
                                                     GibCursor end_r_863,
                                                     GibCursor loc_861,
                                                     GibCursor tr_74_251_406,
                                                     GibInt n_75_252_407);
GibCursorGibIntProd min_tree(GibCursor end_r_865, GibCursor tr_81_258_422);
GibCursorGibCursorGibCursorGibCursorProd tree_insert(GibCursor end_r_868,
                                                     GibCursor end_r_869,
                                                     GibCursor loc_867,
                                                     GibCursor tr_90_263_427,
                                                     GibInt n_91_264_428);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_SearchTree(GibCursor end_r_872, GibCursor end_r_873, GibCursor loc_871,
                 GibCursor arg_184_269_443);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_SearchTree(GibCursor end_r_876, GibCursor end_r_877,
                              GibCursor loc_875, GibCursor arg_193_278_452);
GibCursorGibCursorProd _traverse_SearchTree(GibCursor end_r_879,
                                            GibCursor arg_202_287_461);
GibCursorGibCursorProd _print_SearchTree(GibCursor end_r_881,
                                         GibCursor arg_211_294_468);
GibCursorGibIntProd caseFn_226(GibCursor end_r_883, GibInt n_83_227_309_483,
                               GibCursor l_84_228_310_484);
typedef enum {
            GibInt_T,
            GibFloat_T,
            GibSym_T,
            GibBool_T,
            GibVector_T,
            GibList_T,
            GibCursor_T,
            SearchTree_T,
        } GibDatatype;
void info_table_initialize(void)
{
    int error = gib_info_table_initialize(8);

    if (error < 0) {
        fprintf(stderr, "Couldn't initialize info table, errorno=%d", error);
        exit(1);
    }

    GibDatatype field_tys[3];

    error = gib_info_table_insert_packed_dcon(SearchTree_T, 1, 8, 0, 1, 0,
                                              field_tys, 0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, SearchTree_T, 1);
        exit(1);
    }
    field_tys[0] = SearchTree_T;
    field_tys[1] = SearchTree_T;
    error = gib_info_table_insert_packed_dcon(SearchTree_T, 2, 8, 0, 1, 2,
                                              field_tys, 2);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, SearchTree_T, 2);
        exit(1);
    }
    field_tys[0] = SearchTree_T;
    field_tys[1] = SearchTree_T;
    error = gib_info_table_insert_packed_dcon(SearchTree_T, 3, 8, 1, 1, 2,
                                              field_tys, 2);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, SearchTree_T, 3);
        exit(1);
    }
    error = gib_info_table_insert_packed_dcon(SearchTree_T, 0, 0, 0, 0, 0,
                                              field_tys, 0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, SearchTree_T, 0);
        exit(1);
    }
    gib_info_table_finalize();
}
void symbol_table_initialize(void)
{
    gib_add_symbol(2217, ")");
    gib_add_symbol(2218, "(Null ");
    gib_add_symbol(2219, "(Node ");
    gib_add_symbol(2220, "(Leaf ");
    gib_add_symbol(2221, " ->r ");
    gib_add_symbol(2222, " ->i ");
}
#define REGION_SIZE 1024
#define TREE_HEIGHT 2
GibCursorGibCursorGibCursorProd helper(GibCursor end_r_851, GibCursor loc_850,
                                       GibInt s_58_235_367, GibInt e_59_236_368)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_850 + 26 > end_r_851) {
        gib_grow_region(&loc_850, &end_r_851);
    }

    GibBool fltIf_317_369 = e_59_236_368 < s_58_235_367;

    if (fltIf_317_369) {
        *(GibPackedTag *) loc_850 = 0;

        GibCursor writetag_1483 = loc_850 + 1;
        GibCursor after_tag_1484 = loc_850 + 1;

        return (GibCursorGibCursorGibCursorProd) {end_r_851, loc_850,
                                                  after_tag_1484};
    } else {
        GibBool fltIf_318_370 = s_58_235_367 == e_59_236_368;

        if (fltIf_318_370) {
            *(GibPackedTag *) loc_850 = 1;

            GibCursor writetag_1490 = loc_850 + 1;
            GibCursor after_tag_1491 = loc_850 + 1;

            *(GibInt *) after_tag_1491 = s_58_235_367;

            GibCursor writecur_1495 = after_tag_1491 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorProd) {end_r_851, loc_850,
                                                      writecur_1495};
        } else {
            GibInt fltPrm_320_371 = e_59_236_368 - s_58_235_367;
            GibInt fltPrm_319_372 = fltPrm_320_371 / 2;
            GibInt m_60_237_373 = fltPrm_319_372 + s_58_235_367;
            GibInt fltAppE_322_374 = m_60_237_373 - 1;
            GibCursor loc_910 = loc_850 + 17;

            *(GibPackedTag *) loc_850 = 3;

            GibCursor writetag_1502 = loc_850 + 1;

            gib_shadowstack_push(rstack, loc_850, end_r_851, Stk, SearchTree_T);

            GibBool chk_1498 = loc_910 < end_r_851;

            #ifdef _GIBBON_DEBUG
            assert(chk_1498);
            #endif

            GibCursorGibCursorGibCursorProd tmp_struct_0 =
                                             helper(end_r_851, loc_910, s_58_235_367, fltAppE_322_374);
            GibCursor pvrtmp_2280 = tmp_struct_0.field0;
            GibCursor pvrtmp_2281 = tmp_struct_0.field1;
            GibCursor pvrtmp_2282 = tmp_struct_0.field2;

            frame = gib_shadowstack_pop(rstack);
            loc_850 = frame->ptr;
            end_r_851 = frame->endptr;

            GibInt fltAppE_324_376 = m_60_237_373 + 1;

            gib_shadowstack_push(rstack, loc_850, pvrtmp_2280, Stk,
                                 SearchTree_T);

            GibBool chk_1500 = pvrtmp_2282 < pvrtmp_2280;

            #ifdef _GIBBON_DEBUG
            assert(chk_1500);
            #endif

            GibCursorGibCursorGibCursorProd tmp_struct_1 =
                                             helper(pvrtmp_2280, pvrtmp_2282, fltAppE_324_376, e_59_236_368);
            GibCursor pvrtmp_2287 = tmp_struct_1.field0;
            GibCursor pvrtmp_2288 = tmp_struct_1.field1;
            GibCursor pvrtmp_2289 = tmp_struct_1.field2;

            frame = gib_shadowstack_pop(rstack);
            loc_850 = frame->ptr;
            pvrtmp_2280 = frame->endptr;

            uint16_t offset_2 = pvrtmp_2280 - pvrtmp_2282;
            uintptr_t ran_795 = GIB_STORE_TAG(pvrtmp_2282, offset_2);
            GibCursor after_tag_1503 = loc_850 + 1;

            *(uintptr_t *) after_tag_1503 = ran_795;

            GibCursor writecur_1507 = after_tag_1503 + 8;

            *(GibInt *) writecur_1507 = m_60_237_373;

            GibCursor writecur_1508 = writecur_1507 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorProd) {pvrtmp_2287, loc_850,
                                                      pvrtmp_2289};
        }
    }
}
GibCursorGibCursorGibIntProd countnodes(GibCursor end_r_853,
                                        GibCursor tr_61_238_378)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2298 = *(GibPackedTag *) tr_61_238_378;
    GibCursor tmpcur_2299 = tr_61_238_378 + 1;


  switch_2325:
    ;
    switch (tmpval_2298) {

      case 0:
        {
            GibCursor jump_1225 = tr_61_238_378 + 1;

            return (GibCursorGibCursorGibIntProd) {end_r_853, jump_1225, 0};
            break;
        }

      case 1:
        {
            GibInt tmpval_2300 = *(GibInt *) tmpcur_2299;
            GibCursor tmpcur_2301 = tmpcur_2299 + sizeof(GibInt);
            GibCursor jump_1226 = tmpcur_2299 + 8;

            return (GibCursorGibCursorGibIntProd) {end_r_853, jump_1226, 1};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_8 = *(uintptr_t *) tmpcur_2299;
            GibCursor tmpcur_2302 = GIB_UNTAG(tagged_tmpcur_8);
            GibCursor tmpaftercur_2303 = tmpcur_2299 + 8;
            uint16_t tmptag_2304 = GIB_GET_TAG(tagged_tmpcur_8);
            GibCursor end_from_tagged_absran_796 = tmpcur_2302 + tmptag_2304;
            GibInt tmpval_2305 = *(GibInt *) tmpaftercur_2303;
            GibCursor tmpcur_2306 = tmpaftercur_2303 + sizeof(GibInt);

            gib_shadowstack_push(rstack, tmpcur_2302, end_r_853, Stk,
                                 SearchTree_T);

            GibBool chk_1520 = tmpcur_2306 < end_r_853;

            #ifdef _GIBBON_DEBUG
            assert(chk_1520);
            #endif

            GibCursorGibCursorGibIntProd tmp_struct_6 =
                                          countnodes(end_r_853, tmpcur_2306);
            GibCursor pvrtmp_2307 = tmp_struct_6.field0;
            GibCursor pvrtmp_2308 = tmp_struct_6.field1;
            GibInt pvrtmp_2309 = tmp_struct_6.field2;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_2302 = frame->ptr;
            end_r_853 = frame->endptr;

            GibBool chk_1522 = tmpcur_2302 < pvrtmp_2307;

            #ifdef _GIBBON_DEBUG
            assert(chk_1522);
            #endif

            GibCursorGibCursorGibIntProd tmp_struct_7 =
                                          countnodes(end_from_tagged_absran_796, tmpcur_2302);
            GibCursor pvrtmp_2310 = tmp_struct_7.field0;
            GibCursor pvrtmp_2311 = tmp_struct_7.field1;
            GibInt pvrtmp_2312 = tmp_struct_7.field2;
            GibInt fltPrm_325_385 = pvrtmp_2309 + pvrtmp_2312;
            GibInt tailprim_1231 = 1 + fltPrm_325_385;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_2310, pvrtmp_2311,
                                                   tailprim_1231};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_10 = *(uintptr_t *) tmpcur_2299;
            GibCursor tmpcur_2313 = GIB_UNTAG(tagged_tmpcur_10);
            GibCursor tmpaftercur_2314 = tmpcur_2299 + 8;
            uint16_t tmptag_2315 = GIB_GET_TAG(tagged_tmpcur_10);
            GibCursor end_from_tagged_indr_1316 = tmpcur_2313 + tmptag_2315;
            GibCursor jump_1318 = tmpcur_2299 + 8;
            GibBool chk_1526 = tmpcur_2313 < end_from_tagged_indr_1316;

            #ifdef _GIBBON_DEBUG
            assert(chk_1526);
            #endif

            GibCursorGibCursorGibIntProd tmp_struct_9 =
                                          countnodes(end_from_tagged_indr_1316, tmpcur_2313);
            GibCursor pvrtmp_2316 = tmp_struct_9.field0;
            GibCursor pvrtmp_2317 = tmp_struct_9.field1;
            GibInt pvrtmp_2318 = tmp_struct_9.field2;

            return (GibCursorGibCursorGibIntProd) {end_r_853, jump_1318,
                                                   pvrtmp_2318};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_12 = *(uintptr_t *) tmpcur_2299;
            GibCursor tmpcur_2319 = GIB_UNTAG(tagged_tmpcur_12);
            GibCursor tmpaftercur_2320 = tmpcur_2299 + 8;
            uint16_t tmptag_2321 = GIB_GET_TAG(tagged_tmpcur_12);
            GibCursor end_from_tagged_indr_1316 = tmpcur_2319 + tmptag_2321;
            GibBool chk_1530 = tmpcur_2319 < end_from_tagged_indr_1316;

            #ifdef _GIBBON_DEBUG
            assert(chk_1530);
            #endif

            GibCursorGibCursorGibIntProd tmp_struct_11 =
                                          countnodes(end_from_tagged_indr_1316, tmpcur_2319);
            GibCursor pvrtmp_2322 = tmp_struct_11.field0;
            GibCursor pvrtmp_2323 = tmp_struct_11.field1;
            GibInt pvrtmp_2324 = tmp_struct_11.field2;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_2322, pvrtmp_2323,
                                                   pvrtmp_2324};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2298");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd loop(GibCursor end_r_856,
                                              GibCursor end_r_857,
                                              GibCursor loc_855,
                                              GibCursor tr_66_243_386,
                                              GibInt n_67_244_387)
{
#if defined _GIBBON_VERBOSITY && _GIBBON_VERBOSITY >= 3
    // printf("start of loop:\n");
    // _print_SearchTree(NULL, tr_66_243_386);
    // printf("\n");
    // fflush(stdout);
#endif

    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_855 + 26 > end_r_857) {
        gib_grow_region(&loc_855, &end_r_857);
    }

    GibBool fltIf_328_388 = n_67_244_387 == 0;

    if (fltIf_328_388) {
        if (loc_855 + 18 > end_r_857) {
            gib_grow_region(&loc_855, &end_r_857);
        }
        gib_indirection_barrier(loc_855, end_r_857, tr_66_243_386, end_r_856,
                                SearchTree_T);

        GibCursor end_1533 = loc_855 + 9;

        return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_856, end_r_857,
                                                           loc_855, end_1533};
    } else {
        GibInt fltPrm_329_389 = rand();
        GibInt j_68_245_390 = fltPrm_329_389 % 1000;
        GibInt fltPrm_331_391 = j_68_245_390 % 2;
        GibBool fltIf_330_392 = 0 == fltPrm_331_391;

        if (fltIf_330_392) {
            gib_shadowstack_push(rstack, tr_66_243_386, end_r_856, Stk,
                                 SearchTree_T);
            gib_shadowstack_push(wstack, loc_855, end_r_857, Stk, SearchTree_T);

            GibChunk region_2330 =
                     gib_alloc_region(REGION_SIZE);
            GibCursor r_938 = region_2330.start;
            GibCursor end_r_938 = region_2330.end;

            frame = gib_shadowstack_pop(wstack);
            loc_855 = frame->ptr;
            end_r_857 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tr_66_243_386 = frame->ptr;
            end_r_856 = frame->endptr;
            gib_shadowstack_push(wstack, loc_855, end_r_857, Stk, SearchTree_T);

            GibBool chk_1536 = tr_66_243_386 < end_r_856;

            #ifdef _GIBBON_DEBUG
            assert(chk_1536);
            #endif

            GibBool chk_1535 = r_938 < end_r_938;

            #ifdef _GIBBON_DEBUG
            assert(chk_1535);
            #endif

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_16 =
                                                      tree_insert(end_r_856, end_r_938, r_938, tr_66_243_386, j_68_245_390);
            GibCursor pvrtmp_2331 = tmp_struct_16.field0;
            GibCursor pvrtmp_2332 = tmp_struct_16.field1;
            GibCursor pvrtmp_2333 = tmp_struct_16.field2;
            GibCursor pvrtmp_2334 = tmp_struct_16.field3;

            frame = gib_shadowstack_pop(wstack);
            loc_855 = frame->ptr;
            end_r_857 = frame->endptr;

            GibInt fltAppE_333_394 = n_67_244_387 - 1;
            GibBool chk_1539 = r_938 < pvrtmp_2332;

            #ifdef _GIBBON_DEBUG
            assert(chk_1539);
            #endif

            GibBool chk_1538 = loc_855 < end_r_857;

            #ifdef _GIBBON_DEBUG
            assert(chk_1538);
            #endif

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_17 =
                                                      loop(pvrtmp_2332, end_r_857, loc_855, pvrtmp_2333, fltAppE_333_394);
            GibCursor pvrtmp_2339 = tmp_struct_17.field0;
            GibCursor pvrtmp_2340 = tmp_struct_17.field1;
            GibCursor pvrtmp_2341 = tmp_struct_17.field2;
            GibCursor pvrtmp_2342 = tmp_struct_17.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2331,
                                                               pvrtmp_2340,
                                                               pvrtmp_2341,
                                                               pvrtmp_2342};
        } else {
            GibInt fltAppE_335_395 = j_68_245_390 - 1;

            gib_shadowstack_push(rstack, tr_66_243_386, end_r_856, Stk,
                                 SearchTree_T);
            gib_shadowstack_push(wstack, loc_855, end_r_857, Stk, SearchTree_T);

            GibChunk region_2349 =
                     gib_alloc_region(REGION_SIZE);
            GibCursor r_947 = region_2349.start;
            GibCursor end_r_947 = region_2349.end;

            frame = gib_shadowstack_pop(wstack);
            loc_855 = frame->ptr;
            end_r_857 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tr_66_243_386 = frame->ptr;
            end_r_856 = frame->endptr;
            gib_shadowstack_push(wstack, loc_855, end_r_857, Stk, SearchTree_T);

            GibBool chk_1542 = tr_66_243_386 < end_r_856;

            #ifdef _GIBBON_DEBUG
            assert(chk_1542);
            #endif

            GibBool chk_1541 = r_947 < end_r_947;

            #ifdef _GIBBON_DEBUG
            assert(chk_1541);
            #endif

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_18 =
                                                      tree_delete(end_r_856, end_r_947, r_947, tr_66_243_386, fltAppE_335_395);
            GibCursor pvrtmp_2350 = tmp_struct_18.field0;
            GibCursor pvrtmp_2351 = tmp_struct_18.field1;
            GibCursor pvrtmp_2352 = tmp_struct_18.field2;
            GibCursor pvrtmp_2353 = tmp_struct_18.field3;

            frame = gib_shadowstack_pop(wstack);
            loc_855 = frame->ptr;
            end_r_857 = frame->endptr;

            GibInt fltAppE_336_397 = n_67_244_387 - 1;
            GibBool chk_1545 = r_947 < pvrtmp_2351;

            #ifdef _GIBBON_DEBUG
            assert(chk_1545);
            #endif

            GibBool chk_1544 = loc_855 < end_r_857;

            #ifdef _GIBBON_DEBUG
            assert(chk_1544);
            #endif

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_19 =
                                                      loop(pvrtmp_2351, end_r_857, loc_855, pvrtmp_2352, fltAppE_336_397);
            GibCursor pvrtmp_2358 = tmp_struct_19.field0;
            GibCursor pvrtmp_2359 = tmp_struct_19.field1;
            GibCursor pvrtmp_2360 = tmp_struct_19.field2;
            GibCursor pvrtmp_2361 = tmp_struct_19.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2350,
                                                               pvrtmp_2359,
                                                               pvrtmp_2360,
                                                               pvrtmp_2361};
        }
    }
}
GibCursorGibCursorGibIntProd sum_tree(GibCursor end_r_859,
                                      GibCursor tr_69_246_398)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2368 = *(GibPackedTag *) tr_69_246_398;
    GibCursor tmpcur_2369 = tr_69_246_398 + 1;


  switch_2395:
    ;
    switch (tmpval_2368) {

      case 0:
        {
            GibCursor jump_1235 = tr_69_246_398 + 1;

            return (GibCursorGibCursorGibIntProd) {end_r_859, jump_1235, 0};
            break;
        }

      case 1:
        {
            GibInt tmpval_2370 = *(GibInt *) tmpcur_2369;
            GibCursor tmpcur_2371 = tmpcur_2369 + sizeof(GibInt);
            GibCursor jump_1236 = tmpcur_2369 + 8;

            return (GibCursorGibCursorGibIntProd) {end_r_859, jump_1236,
                                                   tmpval_2370};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_25 = *(uintptr_t *) tmpcur_2369;
            GibCursor tmpcur_2372 = GIB_UNTAG(tagged_tmpcur_25);
            GibCursor tmpaftercur_2373 = tmpcur_2369 + 8;
            uint16_t tmptag_2374 = GIB_GET_TAG(tagged_tmpcur_25);
            GibCursor end_from_tagged_absran_799 = tmpcur_2372 + tmptag_2374;
            GibInt tmpval_2375 = *(GibInt *) tmpaftercur_2373;
            GibCursor tmpcur_2376 = tmpaftercur_2373 + sizeof(GibInt);

            gib_shadowstack_push(rstack, tmpcur_2372, end_r_859, Stk,
                                 SearchTree_T);

            GibBool chk_1553 = tmpcur_2376 < end_r_859;

            #ifdef _GIBBON_DEBUG
            assert(chk_1553);
            #endif

            GibCursorGibCursorGibIntProd tmp_struct_23 =
                                          sum_tree(end_r_859, tmpcur_2376);
            GibCursor pvrtmp_2377 = tmp_struct_23.field0;
            GibCursor pvrtmp_2378 = tmp_struct_23.field1;
            GibInt pvrtmp_2379 = tmp_struct_23.field2;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_2372 = frame->ptr;
            end_r_859 = frame->endptr;

            GibBool chk_1555 = tmpcur_2372 < end_from_tagged_absran_799;

            #ifdef _GIBBON_DEBUG
            assert(chk_1555);
            #endif

            GibCursorGibCursorGibIntProd tmp_struct_24 =
                                          sum_tree(end_from_tagged_absran_799, tmpcur_2372);
            GibCursor pvrtmp_2380 = tmp_struct_24.field0;
            GibCursor pvrtmp_2381 = tmp_struct_24.field1;
            GibInt pvrtmp_2382 = tmp_struct_24.field2;
            GibInt fltPrm_337_405 = pvrtmp_2379 + pvrtmp_2382;
            GibInt tailprim_1241 = tmpval_2375 + fltPrm_337_405;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_2380, pvrtmp_2381,
                                                   tailprim_1241};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_27 = *(uintptr_t *) tmpcur_2369;
            GibCursor tmpcur_2383 = GIB_UNTAG(tagged_tmpcur_27);
            GibCursor tmpaftercur_2384 = tmpcur_2369 + 8;
            uint16_t tmptag_2385 = GIB_GET_TAG(tagged_tmpcur_27);
            GibCursor end_from_tagged_indr_1322 = tmpcur_2383 + tmptag_2385;
            GibCursor jump_1324 = tmpcur_2369 + 8;
            GibBool chk_1559 = tmpcur_2383 < end_from_tagged_indr_1322;

            #ifdef _GIBBON_DEBUG
            assert(chk_1559);
            #endif

            GibCursorGibCursorGibIntProd tmp_struct_26 =
                                          sum_tree(end_from_tagged_indr_1322, tmpcur_2383);
            GibCursor pvrtmp_2386 = tmp_struct_26.field0;
            GibCursor pvrtmp_2387 = tmp_struct_26.field1;
            GibInt pvrtmp_2388 = tmp_struct_26.field2;

            return (GibCursorGibCursorGibIntProd) {end_r_859, jump_1324,
                                                   pvrtmp_2388};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_29 = *(uintptr_t *) tmpcur_2369;
            GibCursor tmpcur_2389 = GIB_UNTAG(tagged_tmpcur_29);
            GibCursor tmpaftercur_2390 = tmpcur_2369 + 8;
            uint16_t tmptag_2391 = GIB_GET_TAG(tagged_tmpcur_29);
            GibCursor end_from_tagged_indr_1322 = tmpcur_2389 + tmptag_2391;
            GibBool chk_1563 = tmpcur_2389 < end_from_tagged_indr_1322;

            #ifdef _GIBBON_DEBUG
            assert(chk_1563);
            #endif

            GibCursorGibCursorGibIntProd tmp_struct_28 =
                                          sum_tree(end_from_tagged_indr_1322, tmpcur_2389);
            GibCursor pvrtmp_2392 = tmp_struct_28.field0;
            GibCursor pvrtmp_2393 = tmp_struct_28.field1;
            GibInt pvrtmp_2394 = tmp_struct_28.field2;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_2392, pvrtmp_2393,
                                                   pvrtmp_2394};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2368");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd tree_delete(GibCursor end_r_862,
                                                     GibCursor end_r_863,
                                                     GibCursor loc_861,
                                                     GibCursor tr_74_251_406,
                                                     GibInt n_75_252_407)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_861 + 26 > end_r_863) {
        gib_grow_region(&loc_861, &end_r_863);
    }

    GibPackedTag tmpval_2396 = *(GibPackedTag *) tr_74_251_406;
    GibCursor tmpcur_2397 = tr_74_251_406 + 1;


  switch_2487:
    ;
    switch (tmpval_2396) {

      case 0:
        {
            *(GibPackedTag *) loc_861 = 1;

            GibCursor writetag_1566 = loc_861 + 1;
            GibCursor after_tag_1567 = loc_861 + 1;

            *(GibInt *) after_tag_1567 = n_75_252_407;

            GibCursor writecur_1571 = after_tag_1567 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_862,
                                                               end_r_863,
                                                               loc_861,
                                                               writecur_1571};
            break;
        }

      case 1:
        {
            GibInt tmpval_2402 = *(GibInt *) tmpcur_2397;
            GibCursor tmpcur_2403 = tmpcur_2397 + sizeof(GibInt);
            GibBool fltIf_340_409 = tmpval_2402 == n_75_252_407;

            if (fltIf_340_409) {
                *(GibPackedTag *) loc_861 = 0;

                GibCursor writetag_1576 = loc_861 + 1;
                GibCursor after_tag_1577 = loc_861 + 1;

                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_862,
                                                                   end_r_863,
                                                                   loc_861,
                                                                   after_tag_1577};
            } else {
                *(GibPackedTag *) loc_861 = 1;

                GibCursor writetag_1583 = loc_861 + 1;
                GibCursor after_tag_1584 = loc_861 + 1;

                *(GibInt *) after_tag_1584 = tmpval_2402;

                GibCursor writecur_1588 = after_tag_1584 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_862,
                                                                   end_r_863,
                                                                   loc_861,
                                                                   writecur_1588};
            }
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_46 = *(uintptr_t *) tmpcur_2397;
            GibCursor tmpcur_2412 = GIB_UNTAG(tagged_tmpcur_46);
            GibCursor tmpaftercur_2413 = tmpcur_2397 + 8;
            uint16_t tmptag_2414 = GIB_GET_TAG(tagged_tmpcur_46);
            GibCursor end_from_tagged_absran_805 = tmpcur_2412 + tmptag_2414;
            GibInt tmpval_2415 = *(GibInt *) tmpaftercur_2413;
            GibCursor tmpcur_2416 = tmpaftercur_2413 + sizeof(GibInt);
            GibBool fltIf_341_413 = tmpval_2415 == n_75_252_407;

            if (fltIf_341_413) {
                gib_shadowstack_push(rstack, tmpcur_2412, end_r_862, Stk,
                                     SearchTree_T);
                gib_shadowstack_push(rstack, tmpcur_2416, end_r_862, Stk,
                                     SearchTree_T);
                gib_shadowstack_push(wstack, loc_861, end_r_863, Stk,
                                     SearchTree_T);

                GibBool chk_1594 = tmpcur_2412 < end_from_tagged_absran_805;

                #ifdef _GIBBON_DEBUG
                assert(chk_1594);
                #endif

                GibCursorGibIntProd tmp_struct_30 =
                                     min_tree(end_from_tagged_absran_805, tmpcur_2412);
                GibCursor pvrtmp_2417 = tmp_struct_30.field0;
                GibInt pvrtmp_2418 = tmp_struct_30.field1;

                frame = gib_shadowstack_pop(wstack);
                loc_861 = frame->ptr;
                end_r_863 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                tmpcur_2416 = frame->ptr;
                end_r_862 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                tmpcur_2412 = frame->ptr;
                end_r_862 = frame->endptr;

                GibCursor loc_983 = loc_861 + 17;

                *(GibPackedTag *) loc_861 = 3;

                GibCursor writetag_1602 = loc_861 + 1;

                if (loc_983 + 18 > end_r_863) {
                    gib_grow_region(&loc_983, &end_r_863);
                }
                gib_indirection_barrier(loc_983, end_r_863, tmpcur_2416,
                                        end_r_862, SearchTree_T);

                GibCursor end_1597 = loc_983 + 9;

                gib_shadowstack_push(rstack, loc_861, end_r_863, Stk,
                                     SearchTree_T);

                GibBool chk_1600 = tmpcur_2412 < end_from_tagged_absran_805;

                #ifdef _GIBBON_DEBUG
                assert(chk_1600);
                #endif

                GibBool chk_1599 = end_1597 < end_r_863;

                #ifdef _GIBBON_DEBUG
                assert(chk_1599);
                #endif

                GibCursorGibCursorGibCursorGibCursorProd tmp_struct_31 =
                                                          tree_delete(end_from_tagged_absran_805, end_r_863, end_1597, tmpcur_2412, pvrtmp_2418);
                GibCursor pvrtmp_2421 = tmp_struct_31.field0;
                GibCursor pvrtmp_2422 = tmp_struct_31.field1;
                GibCursor pvrtmp_2423 = tmp_struct_31.field2;
                GibCursor pvrtmp_2424 = tmp_struct_31.field3;

                frame = gib_shadowstack_pop(rstack);
                loc_861 = frame->ptr;
                end_r_863 = frame->endptr;

                uint16_t offset_32 = end_r_863 - end_1597;
                uintptr_t ran_808 = GIB_STORE_TAG(end_1597, offset_32);
                GibCursor after_tag_1603 = loc_861 + 1;

                *(uintptr_t *) after_tag_1603 = ran_808;

                GibCursor writecur_1607 = after_tag_1603 + 8;

                *(GibInt *) writecur_1607 = pvrtmp_2418;

                GibCursor writecur_1608 = writecur_1607 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2421,
                                                                   pvrtmp_2422,
                                                                   loc_861,
                                                                   pvrtmp_2424};
            } else {
                GibBool fltIf_344_417 = tmpval_2415 < n_75_252_407;

                if (fltIf_344_417) {
                    GibCursor loc_999 = loc_861 + 17;

                    *(GibPackedTag *) loc_861 = 3;

                    GibCursor writetag_1620 = loc_861 + 1;

                    if (loc_999 + 18 > end_r_863) {
                        gib_grow_region(&loc_999, &end_r_863);
                    }
                    gib_indirection_barrier(loc_999, end_r_863, tmpcur_2416,
                                            end_r_862, SearchTree_T);

                    GibCursor end_1615 = loc_999 + 9;

                    gib_shadowstack_push(rstack, loc_861, end_r_863, Stk,
                                         SearchTree_T);

                    GibBool chk_1618 = tmpcur_2412 < end_from_tagged_absran_805;

                    #ifdef _GIBBON_DEBUG
                    assert(chk_1618);
                    #endif

                    GibBool chk_1617 = end_1615 < end_r_863;

                    #ifdef _GIBBON_DEBUG
                    assert(chk_1617);
                    #endif

                    GibCursorGibCursorGibCursorGibCursorProd tmp_struct_36 =
                                                              tree_delete(end_from_tagged_absran_805, end_r_863, end_1615, tmpcur_2412, n_75_252_407);
                    GibCursor pvrtmp_2435 = tmp_struct_36.field0;
                    GibCursor pvrtmp_2436 = tmp_struct_36.field1;
                    GibCursor pvrtmp_2437 = tmp_struct_36.field2;
                    GibCursor pvrtmp_2438 = tmp_struct_36.field3;

                    frame = gib_shadowstack_pop(rstack);
                    loc_861 = frame->ptr;
                    end_r_863 = frame->endptr;

                    uint16_t offset_37 = end_r_863 - end_1615;
                    uintptr_t ran_809 = GIB_STORE_TAG(end_1615, offset_37);
                    GibCursor after_tag_1621 = loc_861 + 1;

                    *(uintptr_t *) after_tag_1621 = ran_809;

                    GibCursor writecur_1625 = after_tag_1621 + 8;

                    *(GibInt *) writecur_1625 = tmpval_2415;

                    GibCursor writecur_1626 = writecur_1625 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2435,
                                                                       pvrtmp_2436,
                                                                       loc_861,
                                                                       pvrtmp_2438};
                } else {
                    GibCursor loc_1015 = loc_861 + 17;

                    *(GibPackedTag *) loc_861 = 3;

                    GibCursor writetag_1638 = loc_861 + 1;

                    gib_shadowstack_push(rstack, loc_861, end_r_863, Stk,
                                         SearchTree_T);
                    gib_shadowstack_push(rstack, tmpcur_2412, end_r_862, Stk,
                                         SearchTree_T);

                    GibBool chk_1633 = tmpcur_2416 < end_r_862;

                    #ifdef _GIBBON_DEBUG
                    assert(chk_1633);
                    #endif

                    GibBool chk_1632 = loc_1015 < end_r_863;

                    #ifdef _GIBBON_DEBUG
                    assert(chk_1632);
                    #endif

                    GibCursorGibCursorGibCursorGibCursorProd tmp_struct_41 =
                                                              tree_delete(end_r_862, end_r_863, loc_1015, tmpcur_2416, n_75_252_407);
                    GibCursor pvrtmp_2447 = tmp_struct_41.field0;
                    GibCursor pvrtmp_2448 = tmp_struct_41.field1;
                    GibCursor pvrtmp_2449 = tmp_struct_41.field2;
                    GibCursor pvrtmp_2450 = tmp_struct_41.field3;

                    frame = gib_shadowstack_pop(rstack);
                    tmpcur_2412 = frame->ptr;
                    end_r_862 = frame->endptr;
                    frame = gib_shadowstack_pop(rstack);
                    loc_861 = frame->ptr;
                    end_r_863 = frame->endptr;
                    if (pvrtmp_2450 + 18 > pvrtmp_2448) {
                        gib_grow_region(&pvrtmp_2450, &pvrtmp_2448);
                    }
                    gib_indirection_barrier(pvrtmp_2450, pvrtmp_2448,
                                            tmpcur_2412,
                                            end_from_tagged_absran_805,
                                            SearchTree_T);

                    GibCursor end_1636 = pvrtmp_2450 + 9;
                    uint16_t offset_42 = pvrtmp_2448 - pvrtmp_2450;
                    uintptr_t ran_810 = GIB_STORE_TAG(pvrtmp_2450, offset_42);
                    GibCursor after_tag_1639 = loc_861 + 1;

                    *(uintptr_t *) after_tag_1639 = ran_810;

                    GibCursor writecur_1643 = after_tag_1639 + 8;

                    *(GibInt *) writecur_1643 = tmpval_2415;

                    GibCursor writecur_1644 = writecur_1643 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2447,
                                                                       pvrtmp_2448,
                                                                       loc_861,
                                                                       end_1636};
                }
            }
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_48 = *(uintptr_t *) tmpcur_2397;
            GibCursor tmpcur_2461 = GIB_UNTAG(tagged_tmpcur_48);
            GibCursor tmpaftercur_2462 = tmpcur_2397 + 8;
            uint16_t tmptag_2463 = GIB_GET_TAG(tagged_tmpcur_48);
            GibCursor end_from_tagged_indr_1328 = tmpcur_2461 + tmptag_2463;
            GibCursor jump_1330 = tmpcur_2397 + 8;
            GibBool chk_1653 = tmpcur_2461 < end_from_tagged_indr_1328;

            #ifdef _GIBBON_DEBUG
            assert(chk_1653);
            #endif

            GibBool chk_1652 = loc_861 < end_r_863;

            #ifdef _GIBBON_DEBUG
            assert(chk_1652);
            #endif

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_47 =
                                                      tree_delete(end_from_tagged_indr_1328, end_r_863, loc_861, tmpcur_2461, n_75_252_407);
            GibCursor pvrtmp_2464 = tmp_struct_47.field0;
            GibCursor pvrtmp_2465 = tmp_struct_47.field1;
            GibCursor pvrtmp_2466 = tmp_struct_47.field2;
            GibCursor pvrtmp_2467 = tmp_struct_47.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_862,
                                                               pvrtmp_2465,
                                                               pvrtmp_2466,
                                                               pvrtmp_2467};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_50 = *(uintptr_t *) tmpcur_2397;
            GibCursor tmpcur_2474 = GIB_UNTAG(tagged_tmpcur_50);
            GibCursor tmpaftercur_2475 = tmpcur_2397 + 8;
            uint16_t tmptag_2476 = GIB_GET_TAG(tagged_tmpcur_50);
            GibCursor end_from_tagged_indr_1328 = tmpcur_2474 + tmptag_2476;
            GibBool chk_1658 = tmpcur_2474 < end_from_tagged_indr_1328;

            #ifdef _GIBBON_DEBUG
            assert(chk_1658);
            #endif

            GibBool chk_1657 = loc_861 < end_r_863;

            #ifdef _GIBBON_DEBUG
            assert(chk_1657);
            #endif

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_49 =
                                                      tree_delete(end_from_tagged_indr_1328, end_r_863, loc_861, tmpcur_2474, n_75_252_407);
            GibCursor pvrtmp_2477 = tmp_struct_49.field0;
            GibCursor pvrtmp_2478 = tmp_struct_49.field1;
            GibCursor pvrtmp_2479 = tmp_struct_49.field2;
            GibCursor pvrtmp_2480 = tmp_struct_49.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2477,
                                                               pvrtmp_2478,
                                                               pvrtmp_2479,
                                                               pvrtmp_2480};
            break;
        }

      default:
        {
            printf("Unknown tag in: tmpval_2396: %d", tmpval_2396);
            exit(1);
        }
    }
}
GibCursorGibIntProd min_tree(GibCursor end_r_865, GibCursor tr_81_258_422)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2488 = *(GibPackedTag *) tr_81_258_422;
    GibCursor tmpcur_2489 = tr_81_258_422 + 1;


  switch_2509:
    ;
    switch (tmpval_2488) {

      case 0:
        {
            return (GibCursorGibIntProd) {end_r_865, 0};
            break;
        }

      case 1:
        {
            GibInt tmpval_2490 = *(GibInt *) tmpcur_2489;
            GibCursor tmpcur_2491 = tmpcur_2489 + sizeof(GibInt);

            return (GibCursorGibIntProd) {end_r_865, tmpval_2490};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_55 = *(uintptr_t *) tmpcur_2489;
            GibCursor tmpcur_2492 = GIB_UNTAG(tagged_tmpcur_55);
            GibCursor tmpaftercur_2493 = tmpcur_2489 + 8;
            uint16_t tmptag_2494 = GIB_GET_TAG(tagged_tmpcur_55);
            GibCursor end_from_tagged_absran_814 = tmpcur_2492 + tmptag_2494;
            GibInt tmpval_2495 = *(GibInt *) tmpaftercur_2493;
            GibCursor tmpcur_2496 = tmpaftercur_2493 + sizeof(GibInt);
            GibBool chk_1666 = tmpcur_2496 < end_r_865;

            #ifdef _GIBBON_DEBUG
            assert(chk_1666);
            #endif

            GibCursorGibIntProd tmp_struct_54 =
                                 caseFn_226(end_r_865, tmpval_2495, tmpcur_2496);
            GibCursor pvrtmp_2497 = tmp_struct_54.field0;
            GibInt pvrtmp_2498 = tmp_struct_54.field1;

            return (GibCursorGibIntProd) {pvrtmp_2497, pvrtmp_2498};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_57 = *(uintptr_t *) tmpcur_2489;
            GibCursor tmpcur_2499 = GIB_UNTAG(tagged_tmpcur_57);
            GibCursor tmpaftercur_2500 = tmpcur_2489 + 8;
            uint16_t tmptag_2501 = GIB_GET_TAG(tagged_tmpcur_57);
            GibCursor end_from_tagged_indr_1333 = tmpcur_2499 + tmptag_2501;
            GibCursor jump_1335 = tmpcur_2489 + 8;
            GibBool chk_1670 = tmpcur_2499 < end_from_tagged_indr_1333;

            #ifdef _GIBBON_DEBUG
            assert(chk_1670);
            #endif

            GibCursorGibIntProd tmp_struct_56 =
                                 min_tree(end_from_tagged_indr_1333, tmpcur_2499);
            GibCursor pvrtmp_2502 = tmp_struct_56.field0;
            GibInt pvrtmp_2503 = tmp_struct_56.field1;

            return (GibCursorGibIntProd) {end_r_865, pvrtmp_2503};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_59 = *(uintptr_t *) tmpcur_2489;
            GibCursor tmpcur_2504 = GIB_UNTAG(tagged_tmpcur_59);
            GibCursor tmpaftercur_2505 = tmpcur_2489 + 8;
            uint16_t tmptag_2506 = GIB_GET_TAG(tagged_tmpcur_59);
            GibCursor end_from_tagged_indr_1333 = tmpcur_2504 + tmptag_2506;
            GibBool chk_1674 = tmpcur_2504 < end_from_tagged_indr_1333;

            #ifdef _GIBBON_DEBUG
            assert(chk_1674);
            #endif

            GibCursorGibIntProd tmp_struct_58 =
                                 min_tree(end_from_tagged_indr_1333, tmpcur_2504);
            GibCursor pvrtmp_2507 = tmp_struct_58.field0;
            GibInt pvrtmp_2508 = tmp_struct_58.field1;

            return (GibCursorGibIntProd) {pvrtmp_2507, pvrtmp_2508};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2488");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd tree_insert(GibCursor end_r_868,
                                                     GibCursor end_r_869,
                                                     GibCursor loc_867,
                                                     GibCursor tr_90_263_427,
                                                     GibInt n_91_264_428)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_867 + 26 > end_r_869) {
        gib_grow_region(&loc_867, &end_r_869);
    }

    GibPackedTag tmpval_2510 = *(GibPackedTag *) tr_90_263_427;
    GibCursor tmpcur_2511 = tr_90_263_427 + 1;


  switch_2593:
    ;
    switch (tmpval_2510) {

      case 0:
        {
            *(GibPackedTag *) loc_867 = 1;

            GibCursor writetag_1677 = loc_867 + 1;
            GibCursor after_tag_1678 = loc_867 + 1;

            *(GibInt *) after_tag_1678 = n_91_264_428;

            GibCursor writecur_1682 = after_tag_1678 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_868,
                                                               end_r_869,
                                                               loc_867,
                                                               writecur_1682};
            break;
        }

      case 1:
        {
            GibInt tmpval_2516 = *(GibInt *) tmpcur_2511;
            GibCursor tmpcur_2517 = tmpcur_2511 + sizeof(GibInt);
            GibBool fltIf_349_430 = n_91_264_428 < tmpval_2516;

            if (fltIf_349_430) {
                GibCursor loc_1049 = loc_867 + 17;

                *(GibPackedTag *) loc_867 = 3;

                GibCursor writetag_1702 = loc_867 + 1;

                *(GibPackedTag *) loc_1049 = 1;

                GibCursor writetag_1687 = loc_1049 + 1;
                GibCursor after_tag_1688 = loc_1049 + 1;

                *(GibInt *) after_tag_1688 = n_91_264_428;

                GibCursor writecur_1692 = after_tag_1688 + sizeof(GibInt);

                *(GibPackedTag *) writecur_1692 = 0;

                GibCursor writetag_1695 = writecur_1692 + 1;
                GibCursor after_tag_1696 = writecur_1692 + 1;
                uint16_t offset_60 = end_r_869 - writecur_1692;
                uintptr_t ran_817 = GIB_STORE_TAG(writecur_1692, offset_60);
                GibCursor after_tag_1703 = loc_867 + 1;

                *(uintptr_t *) after_tag_1703 = ran_817;

                GibCursor writecur_1707 = after_tag_1703 + 8;

                *(GibInt *) writecur_1707 = tmpval_2516;

                GibCursor writecur_1708 = writecur_1707 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_868,
                                                                   end_r_869,
                                                                   loc_867,
                                                                   after_tag_1696};
            } else {
                GibCursor loc_1065 = loc_867 + 17;

                *(GibPackedTag *) loc_867 = 3;

                GibCursor writetag_1729 = loc_867 + 1;

                *(GibPackedTag *) loc_1065 = 0;

                GibCursor writetag_1714 = loc_1065 + 1;
                GibCursor after_tag_1715 = loc_1065 + 1;

                *(GibPackedTag *) after_tag_1715 = 1;

                GibCursor writetag_1721 = after_tag_1715 + 1;
                GibCursor after_tag_1722 = after_tag_1715 + 1;

                *(GibInt *) after_tag_1722 = n_91_264_428;

                GibCursor writecur_1726 = after_tag_1722 + sizeof(GibInt);
                uint16_t offset_61 = end_r_869 - after_tag_1715;
                uintptr_t ran_818 = GIB_STORE_TAG(after_tag_1715, offset_61);
                GibCursor after_tag_1730 = loc_867 + 1;

                *(uintptr_t *) after_tag_1730 = ran_818;

                GibCursor writecur_1734 = after_tag_1730 + 8;

                *(GibInt *) writecur_1734 = tmpval_2516;

                GibCursor writecur_1735 = writecur_1734 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_868,
                                                                   end_r_869,
                                                                   loc_867,
                                                                   writecur_1726};
            }
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_72 = *(uintptr_t *) tmpcur_2511;
            GibCursor tmpcur_2534 = GIB_UNTAG(tagged_tmpcur_72);
            GibCursor tmpaftercur_2535 = tmpcur_2511 + 8;
            uint16_t tmptag_2536 = GIB_GET_TAG(tagged_tmpcur_72);
            GibCursor end_from_tagged_absran_821 = tmpcur_2534 + tmptag_2536;
            GibInt tmpval_2537 = *(GibInt *) tmpaftercur_2535;
            GibCursor tmpcur_2538 = tmpaftercur_2535 + sizeof(GibInt);
            GibBool fltIf_354_438 = tmpval_2537 < n_91_264_428;

            if (fltIf_354_438) {
                GibCursor loc_1085 = loc_867 + 17;

                *(GibPackedTag *) loc_867 = 3;

                GibCursor writetag_1750 = loc_867 + 1;

                if (loc_1085 + 18 > end_r_869) {
                    gib_grow_region(&loc_1085, &end_r_869);
                }
                gib_indirection_barrier(loc_1085, end_r_869, tmpcur_2538,
                                        end_r_868, SearchTree_T);

                GibCursor end_1745 = loc_1085 + 9;

                gib_shadowstack_push(rstack, loc_867, end_r_869, Stk,
                                     SearchTree_T);

                GibBool chk_1748 = tmpcur_2534 < end_from_tagged_absran_821;

                #ifdef _GIBBON_DEBUG
                assert(chk_1748);
                #endif

                GibBool chk_1747 = end_1745 < end_r_869;

                #ifdef _GIBBON_DEBUG
                assert(chk_1747);
                #endif

                GibCursorGibCursorGibCursorGibCursorProd tmp_struct_62 =
                                                          tree_insert(end_from_tagged_absran_821, end_r_869, end_1745, tmpcur_2534, n_91_264_428);
                GibCursor pvrtmp_2541 = tmp_struct_62.field0;
                GibCursor pvrtmp_2542 = tmp_struct_62.field1;
                GibCursor pvrtmp_2543 = tmp_struct_62.field2;
                GibCursor pvrtmp_2544 = tmp_struct_62.field3;

                frame = gib_shadowstack_pop(rstack);
                loc_867 = frame->ptr;
                end_r_869 = frame->endptr;

                uint16_t offset_63 = end_r_869 - end_1745;
                uintptr_t ran_824 = GIB_STORE_TAG(end_1745, offset_63);
                GibCursor after_tag_1751 = loc_867 + 1;

                *(uintptr_t *) after_tag_1751 = ran_824;

                GibCursor writecur_1755 = after_tag_1751 + 8;

                *(GibInt *) writecur_1755 = tmpval_2537;

                GibCursor writecur_1756 = writecur_1755 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2541,
                                                                   pvrtmp_2542,
                                                                   loc_867,
                                                                   pvrtmp_2544};
            } else {
                GibCursor loc_1101 = loc_867 + 17;

                *(GibPackedTag *) loc_867 = 3;

                GibCursor writetag_1768 = loc_867 + 1;

                gib_shadowstack_push(rstack, loc_867, end_r_869, Stk,
                                     SearchTree_T);
                gib_shadowstack_push(rstack, tmpcur_2534, end_r_868, Stk,
                                     SearchTree_T);

                GibBool chk_1763 = tmpcur_2538 < end_r_868;

                #ifdef _GIBBON_DEBUG
                assert(chk_1763);
                #endif

                GibBool chk_1762 = loc_1101 < end_r_869;

                #ifdef _GIBBON_DEBUG
                assert(chk_1762);
                #endif

                GibCursorGibCursorGibCursorGibCursorProd tmp_struct_67 =
                                                          tree_insert(end_r_868, end_r_869, loc_1101, tmpcur_2538, n_91_264_428);
                GibCursor pvrtmp_2553 = tmp_struct_67.field0;
                GibCursor pvrtmp_2554 = tmp_struct_67.field1;
                GibCursor pvrtmp_2555 = tmp_struct_67.field2;
                GibCursor pvrtmp_2556 = tmp_struct_67.field3;

                frame = gib_shadowstack_pop(rstack);
                tmpcur_2534 = frame->ptr;
                end_r_868 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                loc_867 = frame->ptr;
                end_r_869 = frame->endptr;
                if (pvrtmp_2556 + 18 > pvrtmp_2554) {
                    gib_grow_region(&pvrtmp_2556, &pvrtmp_2554);
                }
                gib_indirection_barrier(pvrtmp_2556, pvrtmp_2554, tmpcur_2534,
                                        end_from_tagged_absran_821,
                                        SearchTree_T);

                GibCursor end_1766 = pvrtmp_2556 + 9;
                uint16_t offset_68 = pvrtmp_2554 - pvrtmp_2556;
                uintptr_t ran_825 = GIB_STORE_TAG(pvrtmp_2556, offset_68);
                GibCursor after_tag_1769 = loc_867 + 1;

                *(uintptr_t *) after_tag_1769 = ran_825;

                GibCursor writecur_1773 = after_tag_1769 + 8;

                *(GibInt *) writecur_1773 = tmpval_2537;

                GibCursor writecur_1774 = writecur_1773 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2553,
                                                                   pvrtmp_2554,
                                                                   loc_867,
                                                                   end_1766};
            }
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_74 = *(uintptr_t *) tmpcur_2511;
            GibCursor tmpcur_2567 = GIB_UNTAG(tagged_tmpcur_74);
            GibCursor tmpaftercur_2568 = tmpcur_2511 + 8;
            uint16_t tmptag_2569 = GIB_GET_TAG(tagged_tmpcur_74);
            GibCursor end_from_tagged_indr_1338 = tmpcur_2567 + tmptag_2569;
            GibCursor jump_1340 = tmpcur_2511 + 8;
            GibBool chk_1783 = tmpcur_2567 < end_from_tagged_indr_1338;

            #ifdef _GIBBON_DEBUG
            assert(chk_1783);
            #endif

            GibBool chk_1782 = loc_867 < end_r_869;

            #ifdef _GIBBON_DEBUG
            assert(chk_1782);
            #endif

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_73 =
                                                      tree_insert(end_from_tagged_indr_1338, end_r_869, loc_867, tmpcur_2567, n_91_264_428);
            GibCursor pvrtmp_2570 = tmp_struct_73.field0;
            GibCursor pvrtmp_2571 = tmp_struct_73.field1;
            GibCursor pvrtmp_2572 = tmp_struct_73.field2;
            GibCursor pvrtmp_2573 = tmp_struct_73.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_868,
                                                               pvrtmp_2571,
                                                               pvrtmp_2572,
                                                               pvrtmp_2573};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_76 = *(uintptr_t *) tmpcur_2511;
            GibCursor tmpcur_2580 = GIB_UNTAG(tagged_tmpcur_76);
            GibCursor tmpaftercur_2581 = tmpcur_2511 + 8;
            uint16_t tmptag_2582 = GIB_GET_TAG(tagged_tmpcur_76);
            GibCursor end_from_tagged_indr_1338 = tmpcur_2580 + tmptag_2582;
            GibBool chk_1788 = tmpcur_2580 < end_from_tagged_indr_1338;

            #ifdef _GIBBON_DEBUG
            assert(chk_1788);
            #endif

            GibBool chk_1787 = loc_867 < end_r_869;

            #ifdef _GIBBON_DEBUG
            assert(chk_1787);
            #endif

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_75 =
                                                      tree_insert(end_from_tagged_indr_1338, end_r_869, loc_867, tmpcur_2580, n_91_264_428);
            GibCursor pvrtmp_2583 = tmp_struct_75.field0;
            GibCursor pvrtmp_2584 = tmp_struct_75.field1;
            GibCursor pvrtmp_2585 = tmp_struct_75.field2;
            GibCursor pvrtmp_2586 = tmp_struct_75.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2583,
                                                               pvrtmp_2584,
                                                               pvrtmp_2585,
                                                               pvrtmp_2586};
            break;
        }

      default:
        {
            printf("Unknown tag in: tmpval_2510: %d", tmpval_2510);
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_SearchTree(GibCursor end_r_872,
                                                                   GibCursor end_r_873,
                                                                   GibCursor loc_871,
                                                                   GibCursor arg_184_269_443)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_871 + 26 > end_r_873) {
        gib_grow_region(&loc_871, &end_r_873);
    }

    GibPackedTag tmpval_2594 = *(GibPackedTag *) arg_184_269_443;
    GibCursor tmpcur_2595 = arg_184_269_443 + 1;


  switch_2661:
    ;
    switch (tmpval_2594) {

      case 0:
        {
            GibCursor jump_1267 = arg_184_269_443 + 1;

            *(GibPackedTag *) loc_871 = 0;

            GibCursor writetag_1791 = loc_871 + 1;
            GibCursor after_tag_1792 = loc_871 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_872,
                                                                        end_r_873,
                                                                        jump_1267,
                                                                        loc_871,
                                                                        after_tag_1792};
            break;
        }

      case 1:
        {
            GibInt tmpval_2600 = *(GibInt *) tmpcur_2595;
            GibCursor tmpcur_2601 = tmpcur_2595 + sizeof(GibInt);
            GibCursor jump_1269 = tmpcur_2595 + 8;

            *(GibPackedTag *) loc_871 = 1;

            GibCursor writetag_1800 = loc_871 + 1;
            GibCursor after_tag_1801 = loc_871 + 1;

            *(GibInt *) after_tag_1801 = tmpval_2600;

            GibCursor writecur_1805 = after_tag_1801 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_872,
                                                                        end_r_873,
                                                                        jump_1269,
                                                                        loc_871,
                                                                        writecur_1805};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_83 = *(uintptr_t *) tmpcur_2595;
            GibCursor tmpcur_2606 = GIB_UNTAG(tagged_tmpcur_83);
            GibCursor tmpaftercur_2607 = tmpcur_2595 + 8;
            uint16_t tmptag_2608 = GIB_GET_TAG(tagged_tmpcur_83);
            GibCursor end_from_tagged_absran_829 = tmpcur_2606 + tmptag_2608;
            GibInt tmpval_2609 = *(GibInt *) tmpaftercur_2607;
            GibCursor tmpcur_2610 = tmpaftercur_2607 + sizeof(GibInt);
            GibCursor loc_1132 = loc_871 + 17;

            *(GibPackedTag *) loc_871 = 3;

            GibCursor writetag_1817 = loc_871 + 1;

            gib_shadowstack_push(rstack, loc_871, end_r_873, Stk, SearchTree_T);
            gib_shadowstack_push(rstack, tmpcur_2606, end_r_872, Stk,
                                 SearchTree_T);

            GibBool chk_1812 = tmpcur_2610 < end_r_872;

            #ifdef _GIBBON_DEBUG
            assert(chk_1812);
            #endif

            GibBool chk_1811 = loc_1132 < end_r_873;

            #ifdef _GIBBON_DEBUG
            assert(chk_1811);
            #endif

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_80 =
                                                               _copy_SearchTree(end_r_872, end_r_873, loc_1132, tmpcur_2610);
            GibCursor pvrtmp_2611 = tmp_struct_80.field0;
            GibCursor pvrtmp_2612 = tmp_struct_80.field1;
            GibCursor pvrtmp_2613 = tmp_struct_80.field2;
            GibCursor pvrtmp_2614 = tmp_struct_80.field3;
            GibCursor pvrtmp_2615 = tmp_struct_80.field4;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_2606 = frame->ptr;
            end_r_872 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_871 = frame->ptr;
            end_r_873 = frame->endptr;
            gib_shadowstack_push(rstack, loc_871, pvrtmp_2612, Stk,
                                 SearchTree_T);

            GibBool chk_1815 = tmpcur_2606 < pvrtmp_2611;

            #ifdef _GIBBON_DEBUG
            assert(chk_1815);
            #endif

            GibBool chk_1814 = pvrtmp_2615 < pvrtmp_2612;

            #ifdef _GIBBON_DEBUG
            assert(chk_1814);
            #endif

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_81 =
                                                               _copy_SearchTree(end_from_tagged_absran_829, pvrtmp_2612, pvrtmp_2615, tmpcur_2606);
            GibCursor pvrtmp_2620 = tmp_struct_81.field0;
            GibCursor pvrtmp_2621 = tmp_struct_81.field1;
            GibCursor pvrtmp_2622 = tmp_struct_81.field2;
            GibCursor pvrtmp_2623 = tmp_struct_81.field3;
            GibCursor pvrtmp_2624 = tmp_struct_81.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_871 = frame->ptr;
            pvrtmp_2612 = frame->endptr;

            uint16_t offset_82 = pvrtmp_2612 - pvrtmp_2615;
            uintptr_t ran_832 = GIB_STORE_TAG(pvrtmp_2615, offset_82);
            GibCursor after_tag_1818 = loc_871 + 1;

            *(uintptr_t *) after_tag_1818 = ran_832;

            GibCursor writecur_1822 = after_tag_1818 + 8;

            *(GibInt *) writecur_1822 = tmpval_2609;

            GibCursor writecur_1823 = writecur_1822 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2620,
                                                                        pvrtmp_2621,
                                                                        pvrtmp_2622,
                                                                        loc_871,
                                                                        pvrtmp_2624};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_85 = *(uintptr_t *) tmpcur_2595;
            GibCursor tmpcur_2633 = GIB_UNTAG(tagged_tmpcur_85);
            GibCursor tmpaftercur_2634 = tmpcur_2595 + 8;
            uint16_t tmptag_2635 = GIB_GET_TAG(tagged_tmpcur_85);
            GibCursor end_from_tagged_indr_1343 = tmpcur_2633 + tmptag_2635;
            GibCursor jump_1345 = tmpcur_2595 + 8;
            GibBool chk_1832 = tmpcur_2633 < end_from_tagged_indr_1343;

            #ifdef _GIBBON_DEBUG
            assert(chk_1832);
            #endif

            GibBool chk_1831 = loc_871 < end_r_873;

            #ifdef _GIBBON_DEBUG
            assert(chk_1831);
            #endif

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_84 =
                                                               _copy_SearchTree(end_from_tagged_indr_1343, end_r_873, loc_871, tmpcur_2633);
            GibCursor pvrtmp_2636 = tmp_struct_84.field0;
            GibCursor pvrtmp_2637 = tmp_struct_84.field1;
            GibCursor pvrtmp_2638 = tmp_struct_84.field2;
            GibCursor pvrtmp_2639 = tmp_struct_84.field3;
            GibCursor pvrtmp_2640 = tmp_struct_84.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_872,
                                                                        pvrtmp_2637,
                                                                        jump_1345,
                                                                        pvrtmp_2639,
                                                                        pvrtmp_2640};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_87 = *(uintptr_t *) tmpcur_2595;
            GibCursor tmpcur_2647 = GIB_UNTAG(tagged_tmpcur_87);
            GibCursor tmpaftercur_2648 = tmpcur_2595 + 8;
            uint16_t tmptag_2649 = GIB_GET_TAG(tagged_tmpcur_87);
            GibCursor end_from_tagged_indr_1343 = tmpcur_2647 + tmptag_2649;
            GibBool chk_1837 = tmpcur_2647 < end_from_tagged_indr_1343;

            #ifdef _GIBBON_DEBUG
            assert(chk_1837);
            #endif

            GibBool chk_1836 = loc_871 < end_r_873;

            #ifdef _GIBBON_DEBUG
            assert(chk_1836);
            #endif

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_86 =
                                                               _copy_SearchTree(end_from_tagged_indr_1343, end_r_873, loc_871, tmpcur_2647);
            GibCursor pvrtmp_2650 = tmp_struct_86.field0;
            GibCursor pvrtmp_2651 = tmp_struct_86.field1;
            GibCursor pvrtmp_2652 = tmp_struct_86.field2;
            GibCursor pvrtmp_2653 = tmp_struct_86.field3;
            GibCursor pvrtmp_2654 = tmp_struct_86.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2650,
                                                                        pvrtmp_2651,
                                                                        pvrtmp_2652,
                                                                        pvrtmp_2653,
                                                                        pvrtmp_2654};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2594");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_SearchTree(GibCursor end_r_876,
                                                                                GibCursor end_r_877,
                                                                                GibCursor loc_875,
                                                                                GibCursor arg_193_278_452)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2662 = *(GibPackedTag *) arg_193_278_452;
    GibCursor tmpcur_2663 = arg_193_278_452 + 1;


  switch_2729:
    ;
    switch (tmpval_2662) {

      case 0:
        {
            GibCursor jump_1276 = arg_193_278_452 + 1;

            *(GibPackedTag *) loc_875 = 0;

            GibCursor writetag_1840 = loc_875 + 1;
            GibCursor after_tag_1841 = loc_875 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_876,
                                                                        end_r_877,
                                                                        jump_1276,
                                                                        loc_875,
                                                                        after_tag_1841};
            break;
        }

      case 1:
        {
            GibInt tmpval_2668 = *(GibInt *) tmpcur_2663;
            GibCursor tmpcur_2669 = tmpcur_2663 + sizeof(GibInt);
            GibCursor jump_1278 = tmpcur_2663 + 8;

            *(GibPackedTag *) loc_875 = 1;

            GibCursor writetag_1849 = loc_875 + 1;
            GibCursor after_tag_1850 = loc_875 + 1;

            *(GibInt *) after_tag_1850 = tmpval_2668;

            GibCursor writecur_1854 = after_tag_1850 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_876,
                                                                        end_r_877,
                                                                        jump_1278,
                                                                        loc_875,
                                                                        writecur_1854};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_93 = *(uintptr_t *) tmpcur_2663;
            GibCursor tmpcur_2674 = GIB_UNTAG(tagged_tmpcur_93);
            GibCursor tmpaftercur_2675 = tmpcur_2663 + 8;
            uint16_t tmptag_2676 = GIB_GET_TAG(tagged_tmpcur_93);
            GibCursor end_from_tagged_absran_834 = tmpcur_2674 + tmptag_2676;
            GibInt tmpval_2677 = *(GibInt *) tmpaftercur_2675;
            GibCursor tmpcur_2678 = tmpaftercur_2675 + sizeof(GibInt);
            GibCursor loc_1159 = loc_875 + 9;

            *(GibPackedTag *) loc_875 = 2;

            GibCursor writetag_1866 = loc_875 + 1;
            GibCursor after_tag_1867 = loc_875 + 1;

            *(GibInt *) after_tag_1867 = tmpval_2677;

            GibCursor writecur_1871 = after_tag_1867 + sizeof(GibInt);

            gib_shadowstack_push(rstack, loc_875, end_r_877, Stk, SearchTree_T);
            gib_shadowstack_push(rstack, tmpcur_2674, end_r_876, Stk,
                                 SearchTree_T);

            GibBool chk_1861 = tmpcur_2678 < end_r_876;

            #ifdef _GIBBON_DEBUG
            assert(chk_1861);
            #endif

            GibBool chk_1860 = loc_1159 < end_r_877;

            #ifdef _GIBBON_DEBUG
            assert(chk_1860);
            #endif

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_91 =
                                                               _copy_without_ptrs_SearchTree(end_r_876, end_r_877, loc_1159, tmpcur_2678);
            GibCursor pvrtmp_2679 = tmp_struct_91.field0;
            GibCursor pvrtmp_2680 = tmp_struct_91.field1;
            GibCursor pvrtmp_2681 = tmp_struct_91.field2;
            GibCursor pvrtmp_2682 = tmp_struct_91.field3;
            GibCursor pvrtmp_2683 = tmp_struct_91.field4;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_2674 = frame->ptr;
            end_r_876 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_875 = frame->ptr;
            end_r_877 = frame->endptr;
            gib_shadowstack_push(rstack, loc_875, pvrtmp_2680, Stk,
                                 SearchTree_T);

            GibBool chk_1864 = tmpcur_2674 < pvrtmp_2679;

            #ifdef _GIBBON_DEBUG
            assert(chk_1864);
            #endif

            GibBool chk_1863 = pvrtmp_2683 < pvrtmp_2680;

            #ifdef _GIBBON_DEBUG
            assert(chk_1863);
            #endif

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_92 =
                                                               _copy_without_ptrs_SearchTree(end_from_tagged_absran_834, pvrtmp_2680, pvrtmp_2683, tmpcur_2674);
            GibCursor pvrtmp_2688 = tmp_struct_92.field0;
            GibCursor pvrtmp_2689 = tmp_struct_92.field1;
            GibCursor pvrtmp_2690 = tmp_struct_92.field2;
            GibCursor pvrtmp_2691 = tmp_struct_92.field3;
            GibCursor pvrtmp_2692 = tmp_struct_92.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_875 = frame->ptr;
            pvrtmp_2680 = frame->endptr;
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2688,
                                                                        pvrtmp_2689,
                                                                        pvrtmp_2690,
                                                                        loc_875,
                                                                        pvrtmp_2692};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_95 = *(uintptr_t *) tmpcur_2663;
            GibCursor tmpcur_2701 = GIB_UNTAG(tagged_tmpcur_95);
            GibCursor tmpaftercur_2702 = tmpcur_2663 + 8;
            uint16_t tmptag_2703 = GIB_GET_TAG(tagged_tmpcur_95);
            GibCursor end_from_tagged_indr_1349 = tmpcur_2701 + tmptag_2703;
            GibCursor jump_1351 = tmpcur_2663 + 8;
            GibBool chk_1880 = tmpcur_2701 < end_from_tagged_indr_1349;

            #ifdef _GIBBON_DEBUG
            assert(chk_1880);
            #endif

            GibBool chk_1879 = loc_875 < end_r_877;

            #ifdef _GIBBON_DEBUG
            assert(chk_1879);
            #endif

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_94 =
                                                               _copy_without_ptrs_SearchTree(end_from_tagged_indr_1349, end_r_877, loc_875, tmpcur_2701);
            GibCursor pvrtmp_2704 = tmp_struct_94.field0;
            GibCursor pvrtmp_2705 = tmp_struct_94.field1;
            GibCursor pvrtmp_2706 = tmp_struct_94.field2;
            GibCursor pvrtmp_2707 = tmp_struct_94.field3;
            GibCursor pvrtmp_2708 = tmp_struct_94.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_876,
                                                                        pvrtmp_2705,
                                                                        jump_1351,
                                                                        pvrtmp_2707,
                                                                        pvrtmp_2708};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_97 = *(uintptr_t *) tmpcur_2663;
            GibCursor tmpcur_2715 = GIB_UNTAG(tagged_tmpcur_97);
            GibCursor tmpaftercur_2716 = tmpcur_2663 + 8;
            uint16_t tmptag_2717 = GIB_GET_TAG(tagged_tmpcur_97);
            GibCursor end_from_tagged_indr_1349 = tmpcur_2715 + tmptag_2717;
            GibBool chk_1885 = tmpcur_2715 < end_from_tagged_indr_1349;

            #ifdef _GIBBON_DEBUG
            assert(chk_1885);
            #endif

            GibBool chk_1884 = loc_875 < end_r_877;

            #ifdef _GIBBON_DEBUG
            assert(chk_1884);
            #endif

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_96 =
                                                               _copy_without_ptrs_SearchTree(end_from_tagged_indr_1349, end_r_877, loc_875, tmpcur_2715);
            GibCursor pvrtmp_2718 = tmp_struct_96.field0;
            GibCursor pvrtmp_2719 = tmp_struct_96.field1;
            GibCursor pvrtmp_2720 = tmp_struct_96.field2;
            GibCursor pvrtmp_2721 = tmp_struct_96.field3;
            GibCursor pvrtmp_2722 = tmp_struct_96.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2718,
                                                                        pvrtmp_2719,
                                                                        pvrtmp_2720,
                                                                        pvrtmp_2721,
                                                                        pvrtmp_2722};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2662");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_SearchTree(GibCursor end_r_879,
                                            GibCursor arg_202_287_461)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2730 = *(GibPackedTag *) arg_202_287_461;
    GibCursor tmpcur_2731 = arg_202_287_461 + 1;


  switch_2753:
    ;
    switch (tmpval_2730) {

      case 0:
        {
            GibCursor jump_1285 = arg_202_287_461 + 1;

            return (GibCursorGibCursorProd) {end_r_879, jump_1285};
            break;
        }

      case 1:
        {
            GibInt tmpval_2732 = *(GibInt *) tmpcur_2731;
            GibCursor tmpcur_2733 = tmpcur_2731 + sizeof(GibInt);
            GibCursor jump_1287 = tmpcur_2731 + 8;

            return (GibCursorGibCursorProd) {end_r_879, jump_1287};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_100 = *(uintptr_t *) tmpcur_2731;
            GibCursor tmpcur_2734 = GIB_UNTAG(tagged_tmpcur_100);
            GibCursor tmpaftercur_2735 = tmpcur_2731 + 8;
            uint16_t tmptag_2736 = GIB_GET_TAG(tagged_tmpcur_100);
            GibCursor end_from_tagged_absran_837 = tmpcur_2734 + tmptag_2736;
            GibInt tmpval_2737 = *(GibInt *) tmpaftercur_2735;
            GibCursor tmpcur_2738 = tmpaftercur_2735 + sizeof(GibInt);

            gib_shadowstack_push(rstack, tmpcur_2734, end_r_879, Stk,
                                 SearchTree_T);

            GibBool chk_1893 = tmpcur_2738 < end_r_879;

            #ifdef _GIBBON_DEBUG
            assert(chk_1893);
            #endif

            GibCursorGibCursorProd tmp_struct_98 =
                                    _traverse_SearchTree(end_r_879, tmpcur_2738);
            GibCursor pvrtmp_2739 = tmp_struct_98.field0;
            GibCursor pvrtmp_2740 = tmp_struct_98.field1;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_2734 = frame->ptr;
            end_r_879 = frame->endptr;

            GibBool chk_1895 = tmpcur_2734 < pvrtmp_2739;

            #ifdef _GIBBON_DEBUG
            assert(chk_1895);
            #endif

            GibCursorGibCursorProd tmp_struct_99 =
                                    _traverse_SearchTree(end_from_tagged_absran_837, tmpcur_2734);
            GibCursor pvrtmp_2741 = tmp_struct_99.field0;
            GibCursor pvrtmp_2742 = tmp_struct_99.field1;

            return (GibCursorGibCursorProd) {pvrtmp_2741, pvrtmp_2742};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_102 = *(uintptr_t *) tmpcur_2731;
            GibCursor tmpcur_2743 = GIB_UNTAG(tagged_tmpcur_102);
            GibCursor tmpaftercur_2744 = tmpcur_2731 + 8;
            uint16_t tmptag_2745 = GIB_GET_TAG(tagged_tmpcur_102);
            GibCursor end_from_tagged_indr_1355 = tmpcur_2743 + tmptag_2745;
            GibCursor jump_1357 = tmpcur_2731 + 8;
            GibBool chk_1899 = tmpcur_2743 < end_from_tagged_indr_1355;

            #ifdef _GIBBON_DEBUG
            assert(chk_1899);
            #endif

            GibCursorGibCursorProd tmp_struct_101 =
                                    _traverse_SearchTree(end_from_tagged_indr_1355, tmpcur_2743);
            GibCursor pvrtmp_2746 = tmp_struct_101.field0;
            GibCursor pvrtmp_2747 = tmp_struct_101.field1;

            return (GibCursorGibCursorProd) {end_r_879, jump_1357};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_104 = *(uintptr_t *) tmpcur_2731;
            GibCursor tmpcur_2748 = GIB_UNTAG(tagged_tmpcur_104);
            GibCursor tmpaftercur_2749 = tmpcur_2731 + 8;
            uint16_t tmptag_2750 = GIB_GET_TAG(tagged_tmpcur_104);
            GibCursor end_from_tagged_indr_1355 = tmpcur_2748 + tmptag_2750;
            GibBool chk_1903 = tmpcur_2748 < end_from_tagged_indr_1355;

            #ifdef _GIBBON_DEBUG
            assert(chk_1903);
            #endif

            GibCursorGibCursorProd tmp_struct_103 =
                                    _traverse_SearchTree(end_from_tagged_indr_1355, tmpcur_2748);
            GibCursor pvrtmp_2751 = tmp_struct_103.field0;
            GibCursor pvrtmp_2752 = tmp_struct_103.field1;

            return (GibCursorGibCursorProd) {pvrtmp_2751, pvrtmp_2752};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2730");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_SearchTree(GibCursor end_r_881,
                                         GibCursor arg_211_294_468)
{
    printf("%p:", arg_211_294_468);
    fflush(stdout);
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2754 = *(GibPackedTag *) arg_211_294_468;
    GibCursor tmpcur_2755 = arg_211_294_468 + 1;


  switch_2777:
    ;
    switch (tmpval_2754) {

      case 0:
        {
            GibCursor jump_1294 = arg_211_294_468 + 1;
            unsigned char wildcard_212_295_469 = gib_print_symbol(2218);
            unsigned char wildcard_213_296_470 = gib_print_symbol(2217);

            return (GibCursorGibCursorProd) {end_r_881, jump_1294};
            break;
        }

      case 1:
        {
            GibInt tmpval_2756 = *(GibInt *) tmpcur_2755;
            GibCursor tmpcur_2757 = tmpcur_2755 + sizeof(GibInt);
            GibCursor jump_1296 = tmpcur_2755 + 8;
            unsigned char wildcard_216_298_472 = gib_print_symbol(2220);
            unsigned char y_215_299_473 = printf("%ld", tmpval_2756);
            unsigned char wildcard_217_300_474 = gib_print_symbol(2217);

            return (GibCursorGibCursorProd) {end_r_881, jump_1296};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_107 = *(uintptr_t *) tmpcur_2755;
            GibCursor tmpcur_2758 = GIB_UNTAG(tagged_tmpcur_107);
            GibCursor tmpaftercur_2759 = tmpcur_2755 + 8;
            uint16_t tmptag_2760 = GIB_GET_TAG(tagged_tmpcur_107);
            GibCursor end_from_tagged_absran_840 = tmpcur_2758 + tmptag_2760;
            GibInt tmpval_2761 = *(GibInt *) tmpaftercur_2759;
            GibCursor tmpcur_2762 = tmpaftercur_2759 + sizeof(GibInt);
            unsigned char wildcard_224_304_478 = gib_print_symbol(2219);
            unsigned char y_221_305_479 = printf("%ld", tmpval_2761);

            gib_shadowstack_push(rstack, tmpcur_2758, end_r_881, Stk,
                                 SearchTree_T);

            GibBool chk_1911 = tmpcur_2762 < end_r_881;

            #ifdef _GIBBON_DEBUG
            // assert(chk_1911);
            #endif

            GibCursorGibCursorProd tmp_struct_105 =
                                    _print_SearchTree(end_r_881, tmpcur_2762);
            GibCursor pvrtmp_2763 = tmp_struct_105.field0;
            GibCursor pvrtmp_2764 = tmp_struct_105.field1;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_2758 = frame->ptr;
            end_r_881 = frame->endptr;

            GibBool chk_1913 = tmpcur_2758 < end_from_tagged_absran_840;

            #ifdef _GIBBON_DEBUG
            assert(chk_1913);
            #endif

            GibCursorGibCursorProd tmp_struct_106 =
                                    _print_SearchTree(end_from_tagged_absran_840, tmpcur_2758);
            GibCursor pvrtmp_2765 = tmp_struct_106.field0;
            GibCursor pvrtmp_2766 = tmp_struct_106.field1;
            unsigned char wildcard_225_308_482 = gib_print_symbol(2217);

            return (GibCursorGibCursorProd) {pvrtmp_2765, pvrtmp_2766};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_109 = *(uintptr_t *) tmpcur_2755;
            GibCursor tmpcur_2767 = GIB_UNTAG(tagged_tmpcur_109);
            GibCursor tmpaftercur_2768 = tmpcur_2755 + 8;
            uint16_t tmptag_2769 = GIB_GET_TAG(tagged_tmpcur_109);
            GibCursor end_from_tagged_indr_1361 = tmpcur_2767 + tmptag_2769;
            GibCursor jump_1363 = tmpcur_2755 + 8;
            unsigned char wildcard_1366 = gib_print_symbol(2222);
            GibBool chk_1917 = tmpcur_2767 < end_from_tagged_indr_1361;

            #ifdef _GIBBON_DEBUG
            assert(chk_1917);
            #endif

            // printf(" *%p <data>", tmpcur_2767);
            GibCursorGibCursorProd tmp_struct_108 =
                                    _print_SearchTree(end_from_tagged_indr_1361, tmpcur_2767);
            GibCursor pvrtmp_2770 = tmp_struct_108.field0;
            GibCursor pvrtmp_2771 = tmp_struct_108.field1;

            return (GibCursorGibCursorProd) {end_r_881, jump_1363};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_111 = *(uintptr_t *) tmpcur_2755;
            GibCursor tmpcur_2772 = GIB_UNTAG(tagged_tmpcur_111);
            GibCursor tmpaftercur_2773 = tmpcur_2755 + 8;
            uint16_t tmptag_2774 = GIB_GET_TAG(tagged_tmpcur_111);
            GibCursor end_from_tagged_indr_1361 = tmpcur_2772 + tmptag_2774;
            unsigned char wildcard_1366 = gib_print_symbol(2221);
            GibBool chk_1921 = tmpcur_2772 < end_from_tagged_indr_1361;

            #ifdef _GIBBON_DEBUG
            assert(chk_1921);
            #endif

            GibCursorGibCursorProd tmp_struct_110 =
                                    _print_SearchTree(end_from_tagged_indr_1361, tmpcur_2772);
            GibCursor pvrtmp_2775 = tmp_struct_110.field0;
            GibCursor pvrtmp_2776 = tmp_struct_110.field1;

            return (GibCursorGibCursorProd) {pvrtmp_2775, pvrtmp_2776};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2754");
            exit(1);
        }
    }
}
GibCursorGibIntProd caseFn_226(GibCursor end_r_883, GibInt n_83_227_309_483,
                               GibCursor l_84_228_310_484)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2778 = *(GibPackedTag *) l_84_228_310_484;
    GibCursor tmpcur_2779 = l_84_228_310_484 + 1;


  switch_2801:
    ;
    switch (tmpval_2778) {

      case 0:
        {
            return (GibCursorGibIntProd) {end_r_883, n_83_227_309_483};
            break;
        }

      case 1:
        {
            GibInt tmpval_2780 = *(GibInt *) tmpcur_2779;
            GibCursor tmpcur_2781 = tmpcur_2779 + sizeof(GibInt);
            GibBool chk_1926 = l_84_228_310_484 < end_r_883;

            #ifdef _GIBBON_DEBUG
            assert(chk_1926);
            #endif

            GibCursorGibIntProd tmp_struct_112 =
                                 min_tree(end_r_883, l_84_228_310_484);
            GibCursor pvrtmp_2782 = tmp_struct_112.field0;
            GibInt pvrtmp_2783 = tmp_struct_112.field1;

            return (GibCursorGibIntProd) {pvrtmp_2782, pvrtmp_2783};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_114 = *(uintptr_t *) tmpcur_2779;
            GibCursor tmpcur_2784 = GIB_UNTAG(tagged_tmpcur_114);
            GibCursor tmpaftercur_2785 = tmpcur_2779 + 8;
            uint16_t tmptag_2786 = GIB_GET_TAG(tagged_tmpcur_114);
            GibCursor end_from_tagged_absran_843 = tmpcur_2784 + tmptag_2786;
            GibInt tmpval_2787 = *(GibInt *) tmpaftercur_2785;
            GibCursor tmpcur_2788 = tmpaftercur_2785 + sizeof(GibInt);
            GibBool chk_1931 = l_84_228_310_484 < end_r_883;

            #ifdef _GIBBON_DEBUG
            assert(chk_1931);
            #endif

            GibCursorGibIntProd tmp_struct_113 =
                                 min_tree(end_r_883, l_84_228_310_484);
            GibCursor pvrtmp_2789 = tmp_struct_113.field0;
            GibInt pvrtmp_2790 = tmp_struct_113.field1;

            return (GibCursorGibIntProd) {pvrtmp_2789, pvrtmp_2790};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_116 = *(uintptr_t *) tmpcur_2779;
            GibCursor tmpcur_2791 = GIB_UNTAG(tagged_tmpcur_116);
            GibCursor tmpaftercur_2792 = tmpcur_2779 + 8;
            uint16_t tmptag_2793 = GIB_GET_TAG(tagged_tmpcur_116);
            GibCursor end_from_tagged_indr_1367 = tmpcur_2791 + tmptag_2793;
            GibCursor jump_1369 = tmpcur_2779 + 8;
            GibBool chk_1935 = tmpcur_2791 < end_from_tagged_indr_1367;

            #ifdef _GIBBON_DEBUG
            assert(chk_1935);
            #endif

            GibCursorGibIntProd tmp_struct_115 =
                                 caseFn_226(end_from_tagged_indr_1367, n_83_227_309_483, tmpcur_2791);
            GibCursor pvrtmp_2794 = tmp_struct_115.field0;
            GibInt pvrtmp_2795 = tmp_struct_115.field1;

            return (GibCursorGibIntProd) {end_r_883, pvrtmp_2795};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_118 = *(uintptr_t *) tmpcur_2779;
            GibCursor tmpcur_2796 = GIB_UNTAG(tagged_tmpcur_118);
            GibCursor tmpaftercur_2797 = tmpcur_2779 + 8;
            uint16_t tmptag_2798 = GIB_GET_TAG(tagged_tmpcur_118);
            GibCursor end_from_tagged_indr_1367 = tmpcur_2796 + tmptag_2798;
            GibBool chk_1939 = tmpcur_2796 < end_from_tagged_indr_1367;

            #ifdef _GIBBON_DEBUG
            assert(chk_1939);
            #endif

            GibCursorGibIntProd tmp_struct_117 =
                                 caseFn_226(end_from_tagged_indr_1367, n_83_227_309_483, tmpcur_2796);
            GibCursor pvrtmp_2799 = tmp_struct_117.field0;
            GibInt pvrtmp_2800 = tmp_struct_117.field1;

            return (GibCursorGibIntProd) {pvrtmp_2799, pvrtmp_2800};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2778");
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
    GibChunk region_2223 = gib_alloc_region(REGION_SIZE);
    GibCursor r_901 = region_2223.start;
    GibCursor end_r_901 = region_2223.end;
    GibChunk region_2224 = gib_alloc_region(REGION_SIZE);
    GibCursor r_900 = region_2224.start;
    GibCursor end_r_900 = region_2224.end;
    GibInt m_52_229_359 = gib_get_size_param();
    GibInt fltPrm_315_360 = gib_expll(2, TREE_HEIGHT);
    GibInt total_nodes_53_230_361 = fltPrm_315_360 - 1;
    GibCursor pvrtmp_2234;
    GibCursor pvrtmp_2235;
    GibCursor pvrtmp_2236;
    GibVector *times_123 = gib_vector_alloc(gib_get_iters_param(),
                                            sizeof(double));
    struct timespec begin_pvrtmp_2234;
    struct timespec end_pvrtmp_2234;

    clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_2234);
    {
        GibBool chk_1941 = r_901 < end_r_901;

        #ifdef _GIBBON_DEBUG
        assert(chk_1941);
        #endif

        GibCursorGibCursorGibCursorProd tmp_struct_119 =
                                         helper(end_r_901, r_901, 0, total_nodes_53_230_361);
        GibCursor pvrtmp_2225 = tmp_struct_119.field0;
        GibCursor pvrtmp_2226 = tmp_struct_119.field1;
        GibCursor pvrtmp_2227 = tmp_struct_119.field2;

        pvrtmp_2234 = pvrtmp_2225;
        pvrtmp_2235 = pvrtmp_2226;
        pvrtmp_2236 = pvrtmp_2227;
    }
    clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_2234);

    double selftimed_122 = gib_difftimespecs(&begin_pvrtmp_2234,
                                             &end_pvrtmp_2234);

    gib_vector_free(times_123);
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("SELFTIMED: %e\n", gib_difftimespecs(&begin_pvrtmp_2234,
                                                &end_pvrtmp_2234));
    gib_shadowstack_push(rstack, r_901, end_r_901, Stk, SearchTree_T);

    GibBool chk_1944 = r_901 < end_r_901;

    #ifdef _GIBBON_DEBUG
    assert(chk_1944);
    #endif

    GibCursorGibCursorGibIntProd tmp_struct_125 =
                                  countnodes(end_r_901, pvrtmp_2235);
    GibCursor pvrtmp_2244 = tmp_struct_125.field0;
    GibCursor pvrtmp_2245 = tmp_struct_125.field1;
    GibInt pvrtmp_2246 = tmp_struct_125.field2;

    frame = gib_shadowstack_pop(rstack);
    r_901 = frame->ptr;
    end_r_901 = frame->endptr;
    gib_shadowstack_push(rstack, r_901, end_r_901, Stk, SearchTree_T);
    frame = gib_shadowstack_pop(rstack);
    r_901 = frame->ptr;
    end_r_901 = frame->endptr;

    GibCursor pvrtmp_2257;
    GibCursor pvrtmp_2258;
    GibCursor pvrtmp_2259;
    GibVector *times_130 = gib_vector_alloc(gib_get_iters_param(),
                                            sizeof(double));
    struct timespec begin_pvrtmp_2257;
    struct timespec end_pvrtmp_2257;

    GibGcStateSnapshot *snapshot = gib_gc_init_state(2);

    for (long long iters_pvrtmp_2257 = 0; iters_pvrtmp_2257 <
         gib_get_iters_param(); iters_pvrtmp_2257++) {
        if (iters_pvrtmp_2257 != gib_get_iters_param() - 1) {
            gib_gc_save_state(snapshot, 2, region_2223.end, region_2224.end);
            gib_list_bumpalloc_save_state();
        }
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_2257);

        GibInt fltAppE_316_364 = gib_get_size_param();
        GibBool chk_1947 = r_901 < end_r_901;

        #ifdef _GIBBON_DEBUG
        assert(chk_1947);
        #endif

        GibBool chk_1946 = r_900 < end_r_900;

        #ifdef _GIBBON_DEBUG
        assert(chk_1946);
        #endif

        GibCursorGibCursorGibCursorGibCursorProd tmp_struct_126 =
                                                  loop(end_r_901, end_r_900, r_900, pvrtmp_2235, fltAppE_316_364);
        GibCursor pvrtmp_2247 = tmp_struct_126.field0;
        GibCursor pvrtmp_2248 = tmp_struct_126.field1;
        GibCursor pvrtmp_2249 = tmp_struct_126.field2;
        GibCursor pvrtmp_2250 = tmp_struct_126.field3;

        pvrtmp_2257 = pvrtmp_2248;
        pvrtmp_2258 = pvrtmp_2249;
        pvrtmp_2259 = pvrtmp_2250;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_2257);
        if (iters_pvrtmp_2257 != gib_get_iters_param() - 1) {
            gib_gc_restore_state(snapshot);
            gib_list_bumpalloc_restore_state();
        }

        double itertime_127 = gib_difftimespecs(&begin_pvrtmp_2257,
                                                &end_pvrtmp_2257);

        printf("itertime: %lf\n", itertime_127);
        gib_vector_inplace_update(times_130, iters_pvrtmp_2257, &itertime_127);
    }
    gib_vector_inplace_sort(times_130, gib_compare_doubles);

    double *tmp_131 = (double *) gib_vector_nth(times_130,
                                                gib_get_iters_param() / 2);
    double selftimed_129 = *tmp_131;
    double batchtime_128 = gib_sum_timing_array(times_130);

    gib_print_timing_array(times_130);
    gib_vector_free(times_130);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_128);
    printf("SELFTIMED: %e\n", selftimed_129);
    gib_shadowstack_push(rstack, r_900, end_r_900, Stk, SearchTree_T);

    GibBool chk_1950 = r_900 < end_r_900;

    #ifdef _GIBBON_DEBUG
    assert(chk_1950);
    #endif

    // GibCursorGibCursorProd tmp_struct_132 =
    //                         _print_SearchTree(end_r_900, pvrtmp_2258);
    // GibCursor pvrtmp_2267 = tmp_struct_132.field0;
    // GibCursor pvrtmp_2268 = tmp_struct_132.field1;

    frame = gib_shadowstack_pop(rstack);
    r_900 = frame->ptr;
    end_r_900 = frame->endptr;

    GibBool chk_1952 = r_900 < end_r_900;

    #ifdef _GIBBON_DEBUG
    assert(chk_1952);
    #endif

    GibCursorGibCursorGibIntProd tmp_struct_133 =
                                  sum_tree(end_r_900, pvrtmp_2258);
    GibCursor pvrtmp_2269 = tmp_struct_133.field0;
    GibCursor pvrtmp_2270 = tmp_struct_133.field1;
    GibInt pvrtmp_2271 = tmp_struct_133.field2;

    printf("%ld", pvrtmp_2271);
    printf("\n");
    return 0;
}
