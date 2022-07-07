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
GibCursorGibCursorGibCursorProd helper(GibCursor end_r_873, GibCursor loc_872,
                                       GibInt s_59_238_371,
                                       GibInt e_60_239_372);
GibCursorGibIntProd countnodes(GibCursor end_r_875, GibCursor tr_62_241_382);
GibCursorGibCursorGibCursorProd loop(GibCursor end_r_878, GibCursor end_r_879,
                                     GibCursor loc_877, GibCursor tr_67_246_390,
                                     GibInt n_68_247_391);
GibCursorGibIntProd sum_tree(GibCursor end_r_881, GibCursor tr_70_249_402);
GibCursorGibCursorGibCursorProd tree_delete(GibCursor end_r_884,
                                            GibCursor end_r_885,
                                            GibCursor loc_883,
                                            GibCursor tr_75_254_410,
                                            GibInt n_76_255_411);
GibInt min_tree(GibCursor end_r_887, GibCursor tr_83_262_426);
GibCursorGibCursorGibCursorProd tree_insert(GibCursor end_r_890,
                                            GibCursor end_r_891,
                                            GibCursor loc_889,
                                            GibCursor tr_92_267_431,
                                            GibInt n_93_268_432);
GibCursorGibCursorGibCursorGibCursorProd _copy_SearchTree(GibCursor end_r_894,
                                                          GibCursor end_r_895,
                                                          GibCursor loc_893,
                                                          GibCursor arg_186_273_447);
GibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_SearchTree(GibCursor end_r_898, GibCursor end_r_899,
                              GibCursor loc_897, GibCursor arg_195_282_456);
GibCursorProd _traverse_SearchTree(GibCursor end_r_901,
                                   GibCursor arg_204_291_465);
GibCursorProd _print_SearchTree(GibCursor end_r_903, GibCursor arg_213_298_472);
GibInt caseFn_228(GibCursor end_r_905, GibCursor l_86_229_313_487,
                  GibInt n_85_230_314_488);
GibCursorGibCursorGibCursorGibCursorProd
_add_size_and_rel_offsets_SearchTree(GibCursor end_r_908, GibCursor end_r_909,
                                     GibCursor loc_907, GibCursor arg_849);
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
    gib_add_symbol(2241, "newline");
    gib_add_symbol(2242, ")");
    gib_add_symbol(2243, "(Null ");
    gib_add_symbol(2244, "(Node ");
    gib_add_symbol(2245, "(Leaf ");
    gib_add_symbol(2246, " ->r ");
    gib_add_symbol(2247, " ->i ");
}
GibCursorGibCursorGibCursorProd helper(GibCursor end_r_873, GibCursor loc_872,
                                       GibInt s_59_238_371, GibInt e_60_239_372)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_872 + 34 > end_r_873) {
        gib_grow_region(&loc_872, &end_r_873);
    }

    GibBool fltIf_321_373 = e_60_239_372 < s_59_238_371;

    if (fltIf_321_373) {
        *(GibPackedTag *) loc_872 = 0;

        GibCursor writetag_1510 = loc_872 + 1;
        GibCursor after_tag_1511 = loc_872 + 1;

        return (GibCursorGibCursorGibCursorProd) {end_r_873, loc_872,
                                                  after_tag_1511};
    } else {
        GibBool fltIf_322_374 = s_59_238_371 == e_60_239_372;

        if (fltIf_322_374) {
            *(GibPackedTag *) loc_872 = 1;

            GibCursor writetag_1517 = loc_872 + 1;
            GibCursor after_tag_1518 = loc_872 + 1;

            *(GibInt *) after_tag_1518 = s_59_238_371;

            GibCursor writecur_1522 = after_tag_1518 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorProd) {end_r_873, loc_872,
                                                      writecur_1522};
        } else {
            GibInt fltPrm_324_375 = e_60_239_372 - s_59_238_371;
            GibInt fltPrm_323_376 = fltPrm_324_375 / 2;
            GibInt m_61_240_377 = fltPrm_323_376 + s_59_238_371;
            GibInt fltAppE_326_378 = m_61_240_377 - 1;
            GibCursor loc_934 = loc_872 + 17;

            *(GibPackedTag *) loc_872 = 3;

            GibCursor writetag_1527 = loc_872 + 1;

            gib_shadowstack_push(rstack, loc_872, end_r_873, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibCursorProd tmp_struct_0 =
                                             helper(end_r_873, loc_934, s_59_238_371, fltAppE_326_378);
            GibCursor pvrtmp_2300 = tmp_struct_0.field0;
            GibCursor pvrtmp_2301 = tmp_struct_0.field1;
            GibCursor pvrtmp_2302 = tmp_struct_0.field2;

            frame = gib_shadowstack_pop(rstack);
            loc_872 = frame->ptr;
            end_r_873 = frame->endptr;

            GibInt fltAppE_328_380 = m_61_240_377 + 1;

            gib_shadowstack_push(rstack, loc_872, pvrtmp_2300, Stk,
                                 SearchTree_T);
            gib_shadowstack_push(rstack, loc_934, pvrtmp_2300, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibCursorProd tmp_struct_1 =
                                             helper(pvrtmp_2300, pvrtmp_2302, fltAppE_328_380, e_60_239_372);
            GibCursor pvrtmp_2307 = tmp_struct_1.field0;
            GibCursor pvrtmp_2308 = tmp_struct_1.field1;
            GibCursor pvrtmp_2309 = tmp_struct_1.field2;

            frame = gib_shadowstack_pop(rstack);
            loc_934 = frame->ptr;
            pvrtmp_2300 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_872 = frame->ptr;
            pvrtmp_2300 = frame->endptr;

            GibCursor after_tag_1528 = loc_872 + 1;

            *(GibCursor *) after_tag_1528 = pvrtmp_2302;

            GibCursor writecur_1532 = after_tag_1528 + 8;

            *(GibInt *) writecur_1532 = m_61_240_377;

            GibCursor writecur_1533 = writecur_1532 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorProd) {pvrtmp_2307, loc_872,
                                                      pvrtmp_2309};
        }
    }
}
GibCursorGibIntProd countnodes(GibCursor end_r_875, GibCursor tr_62_241_382)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2318 = *(GibPackedTag *) tr_62_241_382;
    GibCursor tmpcur_2319 = tr_62_241_382 + 1;


  switch_2338:
    ;
    switch (tmpval_2318) {

      case 0:
        {
            GibCursor jump_1272 = tr_62_241_382 + 1;

            return (GibCursorGibIntProd) {jump_1272, 0};
            break;
        }

      case 1:
        {
            GibInt tmpval_2320 = *(GibInt *) tmpcur_2319;
            GibCursor tmpcur_2321 = tmpcur_2319 + sizeof(GibInt);
            GibCursor jump_1273 = tmpcur_2319 + 8;

            return (GibCursorGibIntProd) {jump_1273, 1};
            break;
        }

      case 3:
        {
            GibCursor tmpcur_2322 = *(GibCursor *) tmpcur_2319;
            GibCursor tmpaftercur_2323 = tmpcur_2319 + 8;
            GibInt tmpval_2324 = *(GibInt *) tmpaftercur_2323;
            GibCursor tmpcur_2325 = tmpaftercur_2323 + sizeof(GibInt);

            gib_shadowstack_push(rstack, tmpcur_2322, end_r_875, Stk,
                                 SearchTree_T);

            GibCursorGibIntProd tmp_struct_5 =
                                 countnodes(end_r_875, tmpcur_2325);
            GibCursor pvrtmp_2326 = tmp_struct_5.field0;
            GibInt pvrtmp_2327 = tmp_struct_5.field1;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_2322 = frame->ptr;
            end_r_875 = frame->endptr;

            GibCursorGibIntProd tmp_struct_6 =
                                 countnodes(end_r_875, tmpcur_2322);
            GibCursor pvrtmp_2328 = tmp_struct_6.field0;
            GibInt pvrtmp_2329 = tmp_struct_6.field1;
            GibInt fltPrm_329_389 = pvrtmp_2327 + pvrtmp_2329;
            GibInt tailprim_1278 = 1 + fltPrm_329_389;

            return (GibCursorGibIntProd) {pvrtmp_2328, tailprim_1278};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_8 = *(uintptr_t *) tmpcur_2319;
            GibCursor tmpcur_2330 = GIB_UNTAG(tagged_tmpcur_8);
            GibCursor tmpaftercur_2331 = tmpcur_2319 + 8;
            GibCursor jump_1372 = tmpcur_2319 + 8;
            GibCursorGibIntProd tmp_struct_7 =
                                 countnodes(end_r_875, tmpcur_2330);
            GibCursor pvrtmp_2332 = tmp_struct_7.field0;
            GibInt pvrtmp_2333 = tmp_struct_7.field1;

            return (GibCursorGibIntProd) {jump_1372, pvrtmp_2333};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_10 = *(uintptr_t *) tmpcur_2319;
            GibCursor tmpcur_2334 = GIB_UNTAG(tagged_tmpcur_10);
            GibCursor tmpaftercur_2335 = tmpcur_2319 + 8;
            GibCursorGibIntProd tmp_struct_9 =
                                 countnodes(end_r_875, tmpcur_2334);
            GibCursor pvrtmp_2336 = tmp_struct_9.field0;
            GibInt pvrtmp_2337 = tmp_struct_9.field1;

            return (GibCursorGibIntProd) {pvrtmp_2336, pvrtmp_2337};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2318");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorProd loop(GibCursor end_r_878, GibCursor end_r_879,
                                     GibCursor loc_877, GibCursor tr_67_246_390,
                                     GibInt n_68_247_391)
{
    _print_SearchTree(end_r_878, tr_67_246_390);
    printf("\n");
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_877 + 34 > end_r_879) {
        gib_grow_region(&loc_877, &end_r_879);
    }

    GibBool fltIf_332_392 = n_68_247_391 == 0;

    if (fltIf_332_392) {
        gib_indirection_barrier(loc_877, end_r_879, tr_67_246_390, end_r_878,
                                SearchTree_T);

        GibCursor end_1554 = loc_877 + 9;

        return (GibCursorGibCursorGibCursorProd) {end_r_879, loc_877, end_1554};
    } else {
        GibInt fltPrm_333_393 = rand();
        GibInt j_69_248_394 = fltPrm_333_393 % 1000;
        printf("j=%ld\n", j_69_248_394);
        GibInt fltPrm_335_395 = j_69_248_394 % 2;
        GibBool fltIf_334_396 = 0 == fltPrm_335_395;

        if (fltIf_334_396) {
            gib_shadowstack_push(rstack, tr_67_246_390, end_r_878, Stk,
                                 SearchTree_T);
            gib_shadowstack_push(wstack, loc_877, end_r_879, Stk,
                                 SearchTree_T);

            GibChunk region_2343 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_961 = region_2343.start;
            GibCursor end_r_961 = region_2343.end;

            frame = gib_shadowstack_pop(wstack);
            loc_877 = frame->ptr;
            end_r_879 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tr_67_246_390 = frame->ptr;
            end_r_878 = frame->endptr;
            gib_shadowstack_push(wstack, loc_877, end_r_879, Stk,
                                 SearchTree_T);

            _print_SearchTree(NULL, tr_67_246_390);
            printf("\n");

            GibCursorGibCursorGibCursorProd tmp_struct_11 =
                                             tree_insert(end_r_878, end_r_961, r_961, tr_67_246_390, j_69_248_394);
            GibCursor pvrtmp_2344 = tmp_struct_11.field0;
            GibCursor pvrtmp_2345 = tmp_struct_11.field1;
            GibCursor pvrtmp_2346 = tmp_struct_11.field2;

            frame = gib_shadowstack_pop(wstack);
            loc_877 = frame->ptr;
            end_r_879 = frame->endptr;

            GibInt fltAppE_337_398 = n_68_247_391 - 1;
            GibCursorGibCursorGibCursorProd tmp_struct_12 =
                                             loop(pvrtmp_2344, end_r_879, loc_877, pvrtmp_2345, fltAppE_337_398);
            GibCursor pvrtmp_2351 = tmp_struct_12.field0;
            GibCursor pvrtmp_2352 = tmp_struct_12.field1;
            GibCursor pvrtmp_2353 = tmp_struct_12.field2;

            return (GibCursorGibCursorGibCursorProd) {pvrtmp_2351, pvrtmp_2352,
                                                      pvrtmp_2353};
        } else {
            GibInt fltAppE_339_399 = j_69_248_394 - 1;

            gib_shadowstack_push(rstack, tr_67_246_390, end_r_878, Stk,
                                 SearchTree_T);
            gib_shadowstack_push(wstack, loc_877, end_r_879, Stk,
                                 SearchTree_T);

            GibChunk region_2360 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_970 = region_2360.start;
            GibCursor end_r_970 = region_2360.end;

            frame = gib_shadowstack_pop(wstack);
            loc_877 = frame->ptr;
            end_r_879 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tr_67_246_390 = frame->ptr;
            end_r_878 = frame->endptr;
            gib_shadowstack_push(wstack, loc_877, end_r_879, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibCursorProd tmp_struct_13 =
                                             tree_delete(end_r_878, end_r_970, r_970, tr_67_246_390, fltAppE_339_399);
            GibCursor pvrtmp_2361 = tmp_struct_13.field0;
            GibCursor pvrtmp_2362 = tmp_struct_13.field1;
            GibCursor pvrtmp_2363 = tmp_struct_13.field2;

            frame = gib_shadowstack_pop(wstack);
            loc_877 = frame->ptr;
            end_r_879 = frame->endptr;

            GibInt fltAppE_340_401 = n_68_247_391 - 1;
            GibCursorGibCursorGibCursorProd tmp_struct_14 =
                                             loop(pvrtmp_2361, end_r_879, loc_877, pvrtmp_2362, fltAppE_340_401);
            GibCursor pvrtmp_2368 = tmp_struct_14.field0;
            GibCursor pvrtmp_2369 = tmp_struct_14.field1;
            GibCursor pvrtmp_2370 = tmp_struct_14.field2;

            return (GibCursorGibCursorGibCursorProd) {pvrtmp_2368, pvrtmp_2369,
                                                      pvrtmp_2370};
        }
    }
}
GibCursorGibIntProd sum_tree(GibCursor end_r_881, GibCursor tr_70_249_402)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2377 = *(GibPackedTag *) tr_70_249_402;
    GibCursor tmpcur_2378 = tr_70_249_402 + 1;


  switch_2397:
    ;
    switch (tmpval_2377) {

      case 0:
        {
            GibCursor jump_1282 = tr_70_249_402 + 1;

            return (GibCursorGibIntProd) {jump_1282, 0};
            break;
        }

      case 1:
        {
            GibInt tmpval_2379 = *(GibInt *) tmpcur_2378;
            GibCursor tmpcur_2380 = tmpcur_2378 + sizeof(GibInt);
            GibCursor jump_1283 = tmpcur_2378 + 8;

            return (GibCursorGibIntProd) {jump_1283, tmpval_2379};
            break;
        }

      case 3:
        {
            GibCursor tmpcur_2381 = *(GibCursor *) tmpcur_2378;
            GibCursor tmpaftercur_2382 = tmpcur_2378 + 8;
            GibInt tmpval_2383 = *(GibInt *) tmpaftercur_2382;
            GibCursor tmpcur_2384 = tmpaftercur_2382 + sizeof(GibInt);

            gib_shadowstack_push(rstack, tmpcur_2381, end_r_881, Stk,
                                 SearchTree_T);

            GibCursorGibIntProd tmp_struct_18 =
                                 sum_tree(end_r_881, tmpcur_2384);
            GibCursor pvrtmp_2385 = tmp_struct_18.field0;
            GibInt pvrtmp_2386 = tmp_struct_18.field1;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_2381 = frame->ptr;
            end_r_881 = frame->endptr;

            GibCursorGibIntProd tmp_struct_19 =
                                 sum_tree(end_r_881, tmpcur_2381);
            GibCursor pvrtmp_2387 = tmp_struct_19.field0;
            GibInt pvrtmp_2388 = tmp_struct_19.field1;
            GibInt fltPrm_341_409 = pvrtmp_2386 + pvrtmp_2388;
            GibInt tailprim_1288 = tmpval_2383 + fltPrm_341_409;

            return (GibCursorGibIntProd) {pvrtmp_2387, tailprim_1288};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_21 = *(uintptr_t *) tmpcur_2378;
            GibCursor tmpcur_2389 = GIB_UNTAG(tagged_tmpcur_21);
            GibCursor tmpaftercur_2390 = tmpcur_2378 + 8;
            GibCursor jump_1378 = tmpcur_2378 + 8;
            GibCursorGibIntProd tmp_struct_20 =
                                 sum_tree(end_r_881, tmpcur_2389);
            GibCursor pvrtmp_2391 = tmp_struct_20.field0;
            GibInt pvrtmp_2392 = tmp_struct_20.field1;

            return (GibCursorGibIntProd) {jump_1378, pvrtmp_2392};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_23 = *(uintptr_t *) tmpcur_2378;
            GibCursor tmpcur_2393 = GIB_UNTAG(tagged_tmpcur_23);
            GibCursor tmpaftercur_2394 = tmpcur_2378 + 8;
            GibCursorGibIntProd tmp_struct_22 =
                                 sum_tree(end_r_881, tmpcur_2393);
            GibCursor pvrtmp_2395 = tmp_struct_22.field0;
            GibInt pvrtmp_2396 = tmp_struct_22.field1;

            return (GibCursorGibIntProd) {pvrtmp_2395, pvrtmp_2396};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2377");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorProd tree_delete(GibCursor end_r_884,
                                            GibCursor end_r_885,
                                            GibCursor loc_883,
                                            GibCursor tr_75_254_410,
                                            GibInt n_76_255_411)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_883 + 34 > end_r_885) {
        gib_grow_region(&loc_883, &end_r_885);
    }

    GibPackedTag tmpval_2398 = *(GibPackedTag *) tr_75_254_410;
    GibCursor tmpcur_2399 = tr_75_254_410 + 1;


  switch_2480:
    ;
    switch (tmpval_2398) {

      case 0:
        {
            *(GibPackedTag *) loc_883 = 0;
            GibCursor writetag_1575 = loc_883 + 1;

            return (GibCursorGibCursorGibCursorProd) {end_r_885, loc_883,
                                                      writetag_1575};
            break;
        }

      case 1:
        {
            GibInt tmpval_2404 = *(GibInt *) tmpcur_2399;
            GibCursor tmpcur_2405 = tmpcur_2399 + sizeof(GibInt);
            GibBool fltIf_344_413 = tmpval_2404 == n_76_255_411;

            if (fltIf_344_413) {
                *(GibPackedTag *) loc_883 = 0;

                GibCursor writetag_1585 = loc_883 + 1;
                GibCursor after_tag_1586 = loc_883 + 1;

                return (GibCursorGibCursorGibCursorProd) {end_r_885, loc_883,
                                                          after_tag_1586};
            } else {
                *(GibPackedTag *) loc_883 = 1;

                GibCursor writetag_1592 = loc_883 + 1;
                GibCursor after_tag_1593 = loc_883 + 1;

                *(GibInt *) after_tag_1593 = tmpval_2404;

                GibCursor writecur_1597 = after_tag_1593 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorProd) {end_r_885, loc_883,
                                                          writecur_1597};
            }
            break;
        }

      case 3:
        {
            GibCursor tmpcur_2414 = *(GibCursor *) tmpcur_2399;
            GibCursor tmpaftercur_2415 = tmpcur_2399 + 8;
            GibInt tmpval_2416 = *(GibInt *) tmpaftercur_2415;
            GibCursor tmpcur_2417 = tmpaftercur_2415 + sizeof(GibInt);
            GibBool fltIf_345_417 = tmpval_2416 == n_76_255_411;

            if (fltIf_345_417) {
                gib_shadowstack_push(rstack, tmpcur_2414, end_r_884, Stk,
                                     SearchTree_T);
                gib_shadowstack_push(rstack, tmpcur_2417, end_r_884, Stk,
                                     SearchTree_T);
                gib_shadowstack_push(wstack, loc_883, end_r_885, Stk,
                                     SearchTree_T);

                GibInt k_81_260_418 =  min_tree(end_r_884, tmpcur_2414);

                frame = gib_shadowstack_pop(wstack);
                loc_883 = frame->ptr;
                end_r_885 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                tmpcur_2417 = frame->ptr;
                end_r_884 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                tmpcur_2414 = frame->ptr;
                end_r_884 = frame->endptr;
                gib_shadowstack_push(rstack, tmpcur_2414, end_r_884, Stk,
                                     SearchTree_T);
                gib_shadowstack_push(rstack, tmpcur_2417, end_r_884, Stk,
                                     SearchTree_T);
                gib_shadowstack_push(wstack, loc_883, end_r_885, Stk,
                                     SearchTree_T);

                GibChunk region_2418 =
                         gib_alloc_region(gib_get_inf_init_chunk_size());
                GibCursor r_1046 = region_2418.start;
                GibCursor end_r_1046 = region_2418.end;

                frame = gib_shadowstack_pop(wstack);
                loc_883 = frame->ptr;
                end_r_885 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                tmpcur_2417 = frame->ptr;
                end_r_884 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                tmpcur_2414 = frame->ptr;
                end_r_884 = frame->endptr;
                gib_shadowstack_push(rstack, tmpcur_2417, end_r_884, Stk,
                                     SearchTree_T);
                gib_shadowstack_push(wstack, loc_883, end_r_885, Stk,
                                     SearchTree_T);

                GibCursorGibCursorGibCursorProd tmp_struct_24 =
                                                 tree_delete(end_r_884, end_r_1046, r_1046, tmpcur_2414, k_81_260_418);
                GibCursor pvrtmp_2419 = tmp_struct_24.field0;
                GibCursor pvrtmp_2420 = tmp_struct_24.field1;
                GibCursor pvrtmp_2421 = tmp_struct_24.field2;

                frame = gib_shadowstack_pop(wstack);
                loc_883 = frame->ptr;
                end_r_885 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                tmpcur_2417 = frame->ptr;
                end_r_884 = frame->endptr;

                GibCursor loc_1006 = loc_883 + 17;

                *(GibPackedTag *) loc_883 = 3;

                GibCursor writetag_1607 = loc_883 + 1;

                gib_indirection_barrier(loc_1006, end_r_885, tmpcur_2417,
                                        end_r_884, SearchTree_T);

                GibCursor end_1605 = loc_1006 + 9;
                GibCursor after_tag_1608 = loc_883 + 1;

                *(GibCursor *) after_tag_1608 = end_1605;

                GibCursor writecur_1612 = after_tag_1608 + 8;

                *(GibInt *) writecur_1612 = k_81_260_418;

                GibCursor writecur_1613 = writecur_1612 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorProd) {pvrtmp_2419, loc_883,
                                                          pvrtmp_2421};
            } else {
                GibBool fltIf_347_421 = tmpval_2416 < n_76_255_411;

                if (fltIf_347_421) {
                    GibCursor loc_1022 = loc_883 + 17;

                    *(GibPackedTag *) loc_883 = 3;

                    GibCursor writetag_1623 = loc_883 + 1;

                    gib_indirection_barrier(loc_1022, end_r_885, tmpcur_2417,
                                            end_r_884, SearchTree_T);

                    GibCursor end_1620 = loc_1022 + 9;

                    gib_shadowstack_push(rstack, loc_883, end_r_885, Stk,
                                         SearchTree_T);

                    GibCursorGibCursorGibCursorProd tmp_struct_25 =
                                                     tree_delete(end_r_884, end_r_885, end_1620, tmpcur_2414, n_76_255_411);
                    GibCursor pvrtmp_2434 = tmp_struct_25.field0;
                    GibCursor pvrtmp_2435 = tmp_struct_25.field1;
                    GibCursor pvrtmp_2436 = tmp_struct_25.field2;

                    frame = gib_shadowstack_pop(rstack);
                    loc_883 = frame->ptr;
                    end_r_885 = frame->endptr;

                    GibCursor after_tag_1624 = loc_883 + 1;

                    *(GibCursor *) after_tag_1624 = end_1620;

                    GibCursor writecur_1628 = after_tag_1624 + 8;

                    *(GibInt *) writecur_1628 = tmpval_2416;

                    GibCursor writecur_1629 = writecur_1628 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorProd) {pvrtmp_2434,
                                                              loc_883,
                                                              pvrtmp_2436};
                } else {
                    GibCursor loc_1038 = loc_883 + 17;

                    *(GibPackedTag *) loc_883 = 3;

                    GibCursor writetag_1639 = loc_883 + 1;

                    gib_shadowstack_push(rstack, loc_883, end_r_885, Stk,
                                         SearchTree_T);
                    gib_shadowstack_push(rstack, tmpcur_2414, end_r_884, Stk,
                                         SearchTree_T);

                    GibCursorGibCursorGibCursorProd tmp_struct_26 =
                                                     tree_delete(end_r_884, end_r_885, loc_1038, tmpcur_2414, n_76_255_411);
                    GibCursor pvrtmp_2445 = tmp_struct_26.field0;
                    GibCursor pvrtmp_2446 = tmp_struct_26.field1;
                    GibCursor pvrtmp_2447 = tmp_struct_26.field2;

                    frame = gib_shadowstack_pop(rstack);
                    tmpcur_2414 = frame->ptr;
                    end_r_884 = frame->endptr;
                    frame = gib_shadowstack_pop(rstack);
                    loc_883 = frame->ptr;
                    end_r_885 = frame->endptr;
                    gib_indirection_barrier(pvrtmp_2447, end_r_885, tmpcur_2414,
                                            end_r_884, SearchTree_T);

                    GibCursor end_1637 = pvrtmp_2447 + 9;
                    GibCursor after_tag_1640 = loc_883 + 1;

                    *(GibCursor *) after_tag_1640 = pvrtmp_2447;

                    GibCursor writecur_1644 = after_tag_1640 + 8;

                    *(GibInt *) writecur_1644 = tmpval_2416;

                    GibCursor writecur_1645 = writecur_1644 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorProd) {pvrtmp_2445,
                                                              loc_883,
                                                              end_1637};
                }
            }
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_28 = *(uintptr_t *) tmpcur_2399;
            GibCursor tmpcur_2458 = GIB_UNTAG(tagged_tmpcur_28);
            GibCursor tmpaftercur_2459 = tmpcur_2399 + 8;
            GibCursor jump_1384 = tmpcur_2399 + 8;
            GibCursorGibCursorGibCursorProd tmp_struct_27 =
                                             tree_delete(end_r_884, end_r_885, loc_883, tmpcur_2458, n_76_255_411);
            GibCursor pvrtmp_2460 = tmp_struct_27.field0;
            GibCursor pvrtmp_2461 = tmp_struct_27.field1;
            GibCursor pvrtmp_2462 = tmp_struct_27.field2;

            return (GibCursorGibCursorGibCursorProd) {pvrtmp_2460, pvrtmp_2461,
                                                      pvrtmp_2462};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_30 = *(uintptr_t *) tmpcur_2399;
            GibCursor tmpcur_2469 = GIB_UNTAG(tagged_tmpcur_30);
            GibCursor tmpaftercur_2470 = tmpcur_2399 + 8;
            GibCursorGibCursorGibCursorProd tmp_struct_29 =
                                             tree_delete(end_r_884, end_r_885, loc_883, tmpcur_2469, n_76_255_411);
            GibCursor pvrtmp_2471 = tmp_struct_29.field0;
            GibCursor pvrtmp_2472 = tmp_struct_29.field1;
            GibCursor pvrtmp_2473 = tmp_struct_29.field2;

            return (GibCursorGibCursorGibCursorProd) {pvrtmp_2471, pvrtmp_2472,
                                                      pvrtmp_2473};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2398");
            exit(1);
        }
    }
}
GibInt min_tree(GibCursor end_r_887, GibCursor tr_83_262_426)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2481 = *(GibPackedTag *) tr_83_262_426;
    GibCursor tmpcur_2482 = tr_83_262_426 + 1;


  switch_2493:
    ;
    switch (tmpval_2481) {

      case 0:
        {
            return 0;
            break;
        }

      case 1:
        {
            GibInt tmpval_2483 = *(GibInt *) tmpcur_2482;
            GibCursor tmpcur_2484 = tmpcur_2482 + sizeof(GibInt);

            return tmpval_2483;
            break;
        }

      case 3:
        {
            GibCursor tmpcur_2485 = *(GibCursor *) tmpcur_2482;
            GibCursor tmpaftercur_2486 = tmpcur_2482 + 8;
            GibInt tmpval_2487 = *(GibInt *) tmpaftercur_2486;
            GibCursor tmpcur_2488 = tmpaftercur_2486 + sizeof(GibInt);
            GibInt tailapp_1304 =
                    caseFn_228(end_r_887, tmpcur_2488, tmpval_2487);

            return tailapp_1304;
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_34 = *(uintptr_t *) tmpcur_2482;
            GibCursor tmpcur_2489 = GIB_UNTAG(tagged_tmpcur_34);
            GibCursor tmpaftercur_2490 = tmpcur_2482 + 8;
            GibCursor jump_1389 = tmpcur_2482 + 8;
            GibInt call_1390 =  min_tree(end_r_887, tmpcur_2489);

            return call_1390;
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_35 = *(uintptr_t *) tmpcur_2482;
            GibCursor tmpcur_2491 = GIB_UNTAG(tagged_tmpcur_35);
            GibCursor tmpaftercur_2492 = tmpcur_2482 + 8;
            GibInt call_1390 =  min_tree(end_r_887, tmpcur_2491);

            return call_1390;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2481");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorProd tree_insert(GibCursor end_r_890,
                                            GibCursor end_r_891,
                                            GibCursor loc_889,
                                            GibCursor tr_92_267_431,
                                            GibInt n_93_268_432)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_889 + 34 > end_r_891) {
        gib_grow_region(&loc_889, &end_r_891);
    }

    GibPackedTag tmpval_2494 = *(GibPackedTag *) tr_92_267_431;
    GibCursor tmpcur_2495 = tr_92_267_431 + 1;


  switch_2570:
    ;
    switch (tmpval_2494) {

      case 0:
        {
            *(GibPackedTag *) loc_889 = 1;

            GibCursor writetag_1668 = loc_889 + 1;
            GibCursor after_tag_1669 = loc_889 + 1;

            *(GibInt *) after_tag_1669 = n_93_268_432;

            GibCursor writecur_1673 = after_tag_1669 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorProd) {end_r_891, loc_889,
                                                      writecur_1673};
            break;
        }

      case 1:
        {
            GibInt tmpval_2500 = *(GibInt *) tmpcur_2495;
            GibCursor tmpcur_2501 = tmpcur_2495 + sizeof(GibInt);
            GibBool fltIf_352_434 = n_93_268_432 < tmpval_2500;

            if (fltIf_352_434) {
                GibCursor loc_1070 = loc_889 + 17;

                *(GibPackedTag *) loc_889 = 3;

                GibCursor writetag_1693 = loc_889 + 1;

                *(GibPackedTag *) loc_1070 = 1;

                GibCursor writetag_1678 = loc_1070 + 1;
                GibCursor after_tag_1679 = loc_1070 + 1;

                *(GibInt *) after_tag_1679 = n_93_268_432;

                GibCursor writecur_1683 = after_tag_1679 + sizeof(GibInt);

                *(GibPackedTag *) writecur_1683 = 0;

                GibCursor writetag_1686 = writecur_1683 + 1;
                GibCursor after_tag_1687 = writecur_1683 + 1;
                GibCursor after_tag_1694 = loc_889 + 1;

                *(GibCursor *) after_tag_1694 = writecur_1683;

                GibCursor writecur_1698 = after_tag_1694 + 8;

                *(GibInt *) writecur_1698 = tmpval_2500;

                GibCursor writecur_1699 = writecur_1698 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorProd) {end_r_891, loc_889,
                                                          after_tag_1687};
            } else {
                GibCursor loc_1086 = loc_889 + 17;

                *(GibPackedTag *) loc_889 = 3;

                GibCursor writetag_1720 = loc_889 + 1;

                *(GibPackedTag *) loc_1086 = 0;

                GibCursor writetag_1705 = loc_1086 + 1;
                GibCursor after_tag_1706 = loc_1086 + 1;

                *(GibPackedTag *) after_tag_1706 = 1;

                GibCursor writetag_1712 = after_tag_1706 + 1;
                GibCursor after_tag_1713 = after_tag_1706 + 1;

                *(GibInt *) after_tag_1713 = n_93_268_432;

                GibCursor writecur_1717 = after_tag_1713 + sizeof(GibInt);
                GibCursor after_tag_1721 = loc_889 + 1;

                *(GibCursor *) after_tag_1721 = after_tag_1706;

                GibCursor writecur_1725 = after_tag_1721 + 8;

                *(GibInt *) writecur_1725 = tmpval_2500;

                GibCursor writecur_1726 = writecur_1725 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorProd) {end_r_891, loc_889,
                                                          writecur_1717};
            }
            break;
        }

      case 3:
        {
            GibCursor tmpcur_2518 = *(GibCursor *) tmpcur_2495;
            GibCursor tmpaftercur_2519 = tmpcur_2495 + 8;
            GibInt tmpval_2520 = *(GibInt *) tmpaftercur_2519;
            GibCursor tmpcur_2521 = tmpaftercur_2519 + sizeof(GibInt);
            GibBool fltIf_357_442 = tmpval_2520 < n_93_268_432;

            if (fltIf_357_442) {
                GibCursor loc_1106 = loc_889 + 17;

                *(GibPackedTag *) loc_889 = 3;

                GibCursor writetag_1739 = loc_889 + 1;

                gib_indirection_barrier(loc_1106, end_r_891, tmpcur_2521,
                                        end_r_890, SearchTree_T);

                GibCursor end_1736 = loc_1106 + 9;

                gib_shadowstack_push(rstack, loc_889, end_r_891, Stk,
                                     SearchTree_T);

                GibCursorGibCursorGibCursorProd tmp_struct_36 =
                                                 tree_insert(end_r_890, end_r_891, end_1736, tmpcur_2518, n_93_268_432);
                GibCursor pvrtmp_2524 = tmp_struct_36.field0;
                GibCursor pvrtmp_2525 = tmp_struct_36.field1;
                GibCursor pvrtmp_2526 = tmp_struct_36.field2;

                frame = gib_shadowstack_pop(rstack);
                loc_889 = frame->ptr;
                end_r_891 = frame->endptr;

                GibCursor after_tag_1740 = loc_889 + 1;

                *(GibCursor *) after_tag_1740 = end_1736;

                GibCursor writecur_1744 = after_tag_1740 + 8;

                *(GibInt *) writecur_1744 = tmpval_2520;

                GibCursor writecur_1745 = writecur_1744 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorProd) {pvrtmp_2524, loc_889,
                                                          pvrtmp_2526};
            } else {
                GibCursor loc_1122 = loc_889 + 17;

                *(GibPackedTag *) loc_889 = 3;

                GibCursor writetag_1755 = loc_889 + 1;

                gib_shadowstack_push(rstack, loc_889, end_r_891, Stk,
                                     SearchTree_T);
                gib_shadowstack_push(rstack, tmpcur_2518, end_r_890, Stk,
                                     SearchTree_T);

                GibCursorGibCursorGibCursorProd tmp_struct_37 =
                                                 tree_insert(end_r_890, end_r_891, loc_1122, tmpcur_2521, n_93_268_432);
                GibCursor pvrtmp_2535 = tmp_struct_37.field0;
                GibCursor pvrtmp_2536 = tmp_struct_37.field1;
                GibCursor pvrtmp_2537 = tmp_struct_37.field2;

                frame = gib_shadowstack_pop(rstack);
                tmpcur_2518 = frame->ptr;
                end_r_890 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                loc_889 = frame->ptr;
                end_r_891 = frame->endptr;
                gib_indirection_barrier(pvrtmp_2537, end_r_891, tmpcur_2518,
                                        end_r_890, SearchTree_T);

                GibCursor end_1753 = pvrtmp_2537 + 9;
                GibCursor after_tag_1756 = loc_889 + 1;

                *(GibCursor *) after_tag_1756 = pvrtmp_2537;

                GibCursor writecur_1760 = after_tag_1756 + 8;

                *(GibInt *) writecur_1760 = tmpval_2520;

                GibCursor writecur_1761 = writecur_1760 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorProd) {pvrtmp_2535, loc_889,
                                                          end_1753};
            }
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_39 = *(uintptr_t *) tmpcur_2495;
            GibCursor tmpcur_2548 = GIB_UNTAG(tagged_tmpcur_39);
            GibCursor tmpaftercur_2549 = tmpcur_2495 + 8;
            GibCursor jump_1394 = tmpcur_2495 + 8;
            GibCursorGibCursorGibCursorProd tmp_struct_38 =
                                             tree_insert(end_r_890, end_r_891, loc_889, tmpcur_2548, n_93_268_432);
            GibCursor pvrtmp_2550 = tmp_struct_38.field0;
            GibCursor pvrtmp_2551 = tmp_struct_38.field1;
            GibCursor pvrtmp_2552 = tmp_struct_38.field2;

            return (GibCursorGibCursorGibCursorProd) {pvrtmp_2550, pvrtmp_2551,
                                                      pvrtmp_2552};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_41 = *(uintptr_t *) tmpcur_2495;
            GibCursor tmpcur_2559 = GIB_UNTAG(tagged_tmpcur_41);
            GibCursor tmpaftercur_2560 = tmpcur_2495 + 8;
            GibCursorGibCursorGibCursorProd tmp_struct_40 =
                                             tree_insert(end_r_890, end_r_891, loc_889, tmpcur_2559, n_93_268_432);
            GibCursor pvrtmp_2561 = tmp_struct_40.field0;
            GibCursor pvrtmp_2562 = tmp_struct_40.field1;
            GibCursor pvrtmp_2563 = tmp_struct_40.field2;

            return (GibCursorGibCursorGibCursorProd) {pvrtmp_2561, pvrtmp_2562,
                                                      pvrtmp_2563};
            break;
        }

      default:
        {
            printf("Unknown tag in tmpval_2494: %d", tmpval_2494);
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd _copy_SearchTree(GibCursor end_r_894,
                                                          GibCursor end_r_895,
                                                          GibCursor loc_893,
                                                          GibCursor arg_186_273_447)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_893 + 34 > end_r_895) {
        gib_grow_region(&loc_893, &end_r_895);
    }

    GibPackedTag tmpval_2571 = *(GibPackedTag *) arg_186_273_447;
    GibCursor tmpcur_2572 = arg_186_273_447 + 1;


  switch_2631:
    ;
    switch (tmpval_2571) {

      case 0:
        {
            GibCursor jump_1314 = arg_186_273_447 + 1;

            *(GibPackedTag *) loc_893 = 0;

            GibCursor writetag_1774 = loc_893 + 1;
            GibCursor after_tag_1775 = loc_893 + 1;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_895,
                                                               jump_1314,
                                                               loc_893,
                                                               after_tag_1775};
            break;
        }

      case 1:
        {
            GibInt tmpval_2577 = *(GibInt *) tmpcur_2572;
            GibCursor tmpcur_2578 = tmpcur_2572 + sizeof(GibInt);
            GibCursor jump_1316 = tmpcur_2572 + 8;

            *(GibPackedTag *) loc_893 = 1;

            GibCursor writetag_1783 = loc_893 + 1;
            GibCursor after_tag_1784 = loc_893 + 1;

            *(GibInt *) after_tag_1784 = tmpval_2577;

            GibCursor writecur_1788 = after_tag_1784 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_895,
                                                               jump_1316,
                                                               loc_893,
                                                               writecur_1788};
            break;
        }

      case 3:
        {
            GibCursor tmpcur_2583 = *(GibCursor *) tmpcur_2572;
            GibCursor tmpaftercur_2584 = tmpcur_2572 + 8;
            GibInt tmpval_2585 = *(GibInt *) tmpaftercur_2584;
            GibCursor tmpcur_2586 = tmpaftercur_2584 + sizeof(GibInt);
            GibCursor loc_1149 = loc_893 + 17;

            *(GibPackedTag *) loc_893 = 3;

            GibCursor writetag_1796 = loc_893 + 1;

            gib_shadowstack_push(rstack, loc_893, end_r_895, Stk,
                                 SearchTree_T);
            gib_shadowstack_push(rstack, tmpcur_2583, end_r_894, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_45 =
                                                      _copy_SearchTree(end_r_894, end_r_895, loc_1149, tmpcur_2586);
            GibCursor pvrtmp_2587 = tmp_struct_45.field0;
            GibCursor pvrtmp_2588 = tmp_struct_45.field1;
            GibCursor pvrtmp_2589 = tmp_struct_45.field2;
            GibCursor pvrtmp_2590 = tmp_struct_45.field3;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_2583 = frame->ptr;
            end_r_894 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_893 = frame->ptr;
            end_r_895 = frame->endptr;
            gib_shadowstack_push(rstack, loc_893, pvrtmp_2587, Stk,
                                 SearchTree_T);
            gib_shadowstack_push(rstack, loc_1149, pvrtmp_2587, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_46 =
                                                      _copy_SearchTree(end_r_894, pvrtmp_2587, pvrtmp_2590, tmpcur_2583);
            GibCursor pvrtmp_2595 = tmp_struct_46.field0;
            GibCursor pvrtmp_2596 = tmp_struct_46.field1;
            GibCursor pvrtmp_2597 = tmp_struct_46.field2;
            GibCursor pvrtmp_2598 = tmp_struct_46.field3;

            frame = gib_shadowstack_pop(rstack);
            loc_1149 = frame->ptr;
            pvrtmp_2587 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_893 = frame->ptr;
            pvrtmp_2587 = frame->endptr;

            GibCursor after_tag_1797 = loc_893 + 1;

            *(GibCursor *) after_tag_1797 = pvrtmp_2590;

            GibCursor writecur_1801 = after_tag_1797 + 8;

            *(GibInt *) writecur_1801 = tmpval_2585;

            GibCursor writecur_1802 = writecur_1801 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2595,
                                                               pvrtmp_2596,
                                                               loc_893,
                                                               pvrtmp_2598};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_48 = *(uintptr_t *) tmpcur_2572;
            GibCursor tmpcur_2607 = GIB_UNTAG(tagged_tmpcur_48);
            GibCursor tmpaftercur_2608 = tmpcur_2572 + 8;
            GibCursor jump_1399 = tmpcur_2572 + 8;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_47 =
                                                      _copy_SearchTree(end_r_894, end_r_895, loc_893, tmpcur_2607);
            GibCursor pvrtmp_2609 = tmp_struct_47.field0;
            GibCursor pvrtmp_2610 = tmp_struct_47.field1;
            GibCursor pvrtmp_2611 = tmp_struct_47.field2;
            GibCursor pvrtmp_2612 = tmp_struct_47.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2609,
                                                               jump_1399,
                                                               pvrtmp_2611,
                                                               pvrtmp_2612};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_50 = *(uintptr_t *) tmpcur_2572;
            GibCursor tmpcur_2619 = GIB_UNTAG(tagged_tmpcur_50);
            GibCursor tmpaftercur_2620 = tmpcur_2572 + 8;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_49 =
                                                      _copy_SearchTree(end_r_894, end_r_895, loc_893, tmpcur_2619);
            GibCursor pvrtmp_2621 = tmp_struct_49.field0;
            GibCursor pvrtmp_2622 = tmp_struct_49.field1;
            GibCursor pvrtmp_2623 = tmp_struct_49.field2;
            GibCursor pvrtmp_2624 = tmp_struct_49.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2621,
                                                               pvrtmp_2622,
                                                               pvrtmp_2623,
                                                               pvrtmp_2624};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2571");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_SearchTree(GibCursor end_r_898,
                                                                       GibCursor end_r_899,
                                                                       GibCursor loc_897,
                                                                       GibCursor arg_195_282_456)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2632 = *(GibPackedTag *) arg_195_282_456;
    GibCursor tmpcur_2633 = arg_195_282_456 + 1;


  switch_2692:
    ;
    switch (tmpval_2632) {

      case 0:
        {
            GibCursor jump_1323 = arg_195_282_456 + 1;

            *(GibPackedTag *) loc_897 = 0;

            GibCursor writetag_1815 = loc_897 + 1;
            GibCursor after_tag_1816 = loc_897 + 1;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_899,
                                                               jump_1323,
                                                               loc_897,
                                                               after_tag_1816};
            break;
        }

      case 1:
        {
            GibInt tmpval_2638 = *(GibInt *) tmpcur_2633;
            GibCursor tmpcur_2639 = tmpcur_2633 + sizeof(GibInt);
            GibCursor jump_1325 = tmpcur_2633 + 8;

            *(GibPackedTag *) loc_897 = 1;

            GibCursor writetag_1824 = loc_897 + 1;
            GibCursor after_tag_1825 = loc_897 + 1;

            *(GibInt *) after_tag_1825 = tmpval_2638;

            GibCursor writecur_1829 = after_tag_1825 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_899,
                                                               jump_1325,
                                                               loc_897,
                                                               writecur_1829};
            break;
        }

      case 3:
        {
            GibCursor tmpcur_2644 = *(GibCursor *) tmpcur_2633;
            GibCursor tmpaftercur_2645 = tmpcur_2633 + 8;
            GibInt tmpval_2646 = *(GibInt *) tmpaftercur_2645;
            GibCursor tmpcur_2647 = tmpaftercur_2645 + sizeof(GibInt);
            GibCursor loc_1175 = loc_897 + 9;

            *(GibPackedTag *) loc_897 = 2;

            GibCursor writetag_1837 = loc_897 + 1;
            GibCursor after_tag_1838 = loc_897 + 1;

            *(GibInt *) after_tag_1838 = tmpval_2646;

            GibCursor writecur_1842 = after_tag_1838 + sizeof(GibInt);

            gib_shadowstack_push(rstack, loc_897, end_r_899, Stk,
                                 SearchTree_T);
            gib_shadowstack_push(rstack, tmpcur_2644, end_r_898, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_54 =
                                                      _copy_without_ptrs_SearchTree(end_r_898, end_r_899, loc_1175, tmpcur_2647);
            GibCursor pvrtmp_2648 = tmp_struct_54.field0;
            GibCursor pvrtmp_2649 = tmp_struct_54.field1;
            GibCursor pvrtmp_2650 = tmp_struct_54.field2;
            GibCursor pvrtmp_2651 = tmp_struct_54.field3;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_2644 = frame->ptr;
            end_r_898 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_897 = frame->ptr;
            end_r_899 = frame->endptr;
            gib_shadowstack_push(rstack, loc_897, pvrtmp_2648, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_55 =
                                                      _copy_without_ptrs_SearchTree(end_r_898, pvrtmp_2648, pvrtmp_2651, tmpcur_2644);
            GibCursor pvrtmp_2656 = tmp_struct_55.field0;
            GibCursor pvrtmp_2657 = tmp_struct_55.field1;
            GibCursor pvrtmp_2658 = tmp_struct_55.field2;
            GibCursor pvrtmp_2659 = tmp_struct_55.field3;

            frame = gib_shadowstack_pop(rstack);
            loc_897 = frame->ptr;
            pvrtmp_2648 = frame->endptr;
            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2656,
                                                               pvrtmp_2657,
                                                               loc_897,
                                                               pvrtmp_2659};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_57 = *(uintptr_t *) tmpcur_2633;
            GibCursor tmpcur_2668 = GIB_UNTAG(tagged_tmpcur_57);
            GibCursor tmpaftercur_2669 = tmpcur_2633 + 8;
            GibCursor jump_1405 = tmpcur_2633 + 8;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_56 =
                                                      _copy_without_ptrs_SearchTree(end_r_898, end_r_899, loc_897, tmpcur_2668);
            GibCursor pvrtmp_2670 = tmp_struct_56.field0;
            GibCursor pvrtmp_2671 = tmp_struct_56.field1;
            GibCursor pvrtmp_2672 = tmp_struct_56.field2;
            GibCursor pvrtmp_2673 = tmp_struct_56.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2670,
                                                               jump_1405,
                                                               pvrtmp_2672,
                                                               pvrtmp_2673};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_59 = *(uintptr_t *) tmpcur_2633;
            GibCursor tmpcur_2680 = GIB_UNTAG(tagged_tmpcur_59);
            GibCursor tmpaftercur_2681 = tmpcur_2633 + 8;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_58 =
                                                      _copy_without_ptrs_SearchTree(end_r_898, end_r_899, loc_897, tmpcur_2680);
            GibCursor pvrtmp_2682 = tmp_struct_58.field0;
            GibCursor pvrtmp_2683 = tmp_struct_58.field1;
            GibCursor pvrtmp_2684 = tmp_struct_58.field2;
            GibCursor pvrtmp_2685 = tmp_struct_58.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2682,
                                                               pvrtmp_2683,
                                                               pvrtmp_2684,
                                                               pvrtmp_2685};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2632");
            exit(1);
        }
    }
}
GibCursorProd _traverse_SearchTree(GibCursor end_r_901,
                                   GibCursor arg_204_291_465)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2693 = *(GibPackedTag *) arg_204_291_465;
    GibCursor tmpcur_2694 = arg_204_291_465 + 1;


  switch_2709:
    ;
    switch (tmpval_2693) {

      case 0:
        {
            GibCursor jump_1332 = arg_204_291_465 + 1;

            return (GibCursorProd) {jump_1332};
            break;
        }

      case 1:
        {
            GibInt tmpval_2695 = *(GibInt *) tmpcur_2694;
            GibCursor tmpcur_2696 = tmpcur_2694 + sizeof(GibInt);
            GibCursor jump_1334 = tmpcur_2694 + 8;

            return (GibCursorProd) {jump_1334};
            break;
        }

      case 3:
        {
            GibCursor tmpcur_2697 = *(GibCursor *) tmpcur_2694;
            GibCursor tmpaftercur_2698 = tmpcur_2694 + 8;
            GibInt tmpval_2699 = *(GibInt *) tmpaftercur_2698;
            GibCursor tmpcur_2700 = tmpaftercur_2698 + sizeof(GibInt);

            gib_shadowstack_push(rstack, tmpcur_2697, end_r_901, Stk,
                                 SearchTree_T);

            GibCursorProd tmp_struct_60 =
                           _traverse_SearchTree(end_r_901, tmpcur_2700);
            GibCursor pvrtmp_2701 = tmp_struct_60.field0;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_2697 = frame->ptr;
            end_r_901 = frame->endptr;

            GibCursorProd tmp_struct_61 =
                           _traverse_SearchTree(end_r_901, tmpcur_2697);
            GibCursor pvrtmp_2702 = tmp_struct_61.field0;

            return (GibCursorProd) {pvrtmp_2702};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_63 = *(uintptr_t *) tmpcur_2694;
            GibCursor tmpcur_2703 = GIB_UNTAG(tagged_tmpcur_63);
            GibCursor tmpaftercur_2704 = tmpcur_2694 + 8;
            GibCursor jump_1411 = tmpcur_2694 + 8;
            GibCursorProd tmp_struct_62 =
                           _traverse_SearchTree(end_r_901, tmpcur_2703);
            GibCursor pvrtmp_2705 = tmp_struct_62.field0;

            return (GibCursorProd) {jump_1411};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_65 = *(uintptr_t *) tmpcur_2694;
            GibCursor tmpcur_2706 = GIB_UNTAG(tagged_tmpcur_65);
            GibCursor tmpaftercur_2707 = tmpcur_2694 + 8;
            GibCursorProd tmp_struct_64 =
                           _traverse_SearchTree(end_r_901, tmpcur_2706);
            GibCursor pvrtmp_2708 = tmp_struct_64.field0;

            return (GibCursorProd) {pvrtmp_2708};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2693");
            exit(1);
        }
    }
}
GibCursorProd _print_SearchTree(GibCursor end_r_903, GibCursor arg_213_298_472)
{
    printf("%p:", arg_213_298_472);
    fflush(stdout);
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2710 = *(GibPackedTag *) arg_213_298_472;
    GibCursor tmpcur_2711 = arg_213_298_472 + 1;


  switch_2726:
    ;
    switch (tmpval_2710) {

      case 0:
        {
            GibCursor jump_1341 = arg_213_298_472 + 1;
            unsigned char wildcard_214_299_473 = gib_print_symbol(2243);
            unsigned char wildcard_215_300_474 = gib_print_symbol(2242);

            return (GibCursorProd) {jump_1341};
            break;
        }

      case 1:
        {
            GibInt tmpval_2712 = *(GibInt *) tmpcur_2711;
            GibCursor tmpcur_2713 = tmpcur_2711 + sizeof(GibInt);
            GibCursor jump_1343 = tmpcur_2711 + 8;
            unsigned char wildcard_218_302_476 = gib_print_symbol(2245);
            unsigned char y_217_303_477 = printf("%ld", tmpval_2712);
            unsigned char wildcard_219_304_478 = gib_print_symbol(2242);

            return (GibCursorProd) {jump_1343};
            break;
        }

      case 3:
        {
            GibCursor tmpcur_2714 = *(GibCursor *) tmpcur_2711;
            GibCursor tmpaftercur_2715 = tmpcur_2711 + 8;
            GibInt tmpval_2716 = *(GibInt *) tmpaftercur_2715;
            GibCursor tmpcur_2717 = tmpaftercur_2715 + sizeof(GibInt);
            unsigned char wildcard_226_308_482 = gib_print_symbol(2244);
            printf("%p:%p ", tmpcur_2711, tmpcur_2714);
            unsigned char y_223_309_483 = printf("%p:%ld ", tmpaftercur_2715, tmpval_2716);

            gib_shadowstack_push(rstack, tmpcur_2714, end_r_903, Stk,
                                 SearchTree_T);

            GibCursorProd tmp_struct_66 =
                           _print_SearchTree(end_r_903, tmpcur_2717);
            GibCursor pvrtmp_2718 = tmp_struct_66.field0;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_2714 = frame->ptr;
            end_r_903 = frame->endptr;

            GibCursorProd tmp_struct_67 =
                           _print_SearchTree(end_r_903, tmpcur_2714);
            GibCursor pvrtmp_2719 = tmp_struct_67.field0;
            unsigned char wildcard_227_312_486 = gib_print_symbol(2242);

            return (GibCursorProd) {pvrtmp_2719};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_69 = *(uintptr_t *) tmpcur_2711;
            GibCursor tmpcur_2720 = GIB_UNTAG(tagged_tmpcur_69);
            GibCursor tmpaftercur_2721 = tmpcur_2711 + 8;
            GibCursor jump_1417 = tmpcur_2711 + 8;
            unsigned char wildcard_1420 = gib_print_symbol(2247);
            GibCursorProd tmp_struct_68 =
                           _print_SearchTree(end_r_903, tmpcur_2720);
            GibCursor pvrtmp_2722 = tmp_struct_68.field0;

            return (GibCursorProd) {jump_1417};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_71 = *(uintptr_t *) tmpcur_2711;
            GibCursor tmpcur_2723 = GIB_UNTAG(tagged_tmpcur_71);
            GibCursor tmpaftercur_2724 = tmpcur_2711 + 8;
            unsigned char wildcard_1420 = gib_print_symbol(2246);
            GibCursorProd tmp_struct_70 =
                           _print_SearchTree(end_r_903, tmpcur_2723);
            GibCursor pvrtmp_2725 = tmp_struct_70.field0;

            return (GibCursorProd) {pvrtmp_2725};
            break;
        }

      default:
        {
            printf("Unknown tag in tmpval_2710: %d@%p", tmpval_2710, arg_213_298_472);
            exit(1);
        }
    }
}
GibInt caseFn_228(GibCursor end_r_905, GibCursor l_86_229_313_487,
                  GibInt n_85_230_314_488)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2727 = *(GibPackedTag *) l_86_229_313_487;
    GibCursor tmpcur_2728 = l_86_229_313_487 + 1;


  switch_2739:
    ;
    switch (tmpval_2727) {

      case 0:
        {
            return n_85_230_314_488;
            break;
        }

      case 1:
        {
            GibInt tmpval_2729 = *(GibInt *) tmpcur_2728;
            GibCursor tmpcur_2730 = tmpcur_2728 + sizeof(GibInt);
            GibInt tailapp_1352 =  min_tree(end_r_905, l_86_229_313_487);

            return tailapp_1352;
            break;
        }

      case 3:
        {
            GibCursor tmpcur_2731 = *(GibCursor *) tmpcur_2728;
            GibCursor tmpaftercur_2732 = tmpcur_2728 + 8;
            GibInt tmpval_2733 = *(GibInt *) tmpaftercur_2732;
            GibCursor tmpcur_2734 = tmpaftercur_2732 + sizeof(GibInt);
            GibInt tailapp_1355 =  min_tree(end_r_905, l_86_229_313_487);

            return tailapp_1355;
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_72 = *(uintptr_t *) tmpcur_2728;
            GibCursor tmpcur_2735 = GIB_UNTAG(tagged_tmpcur_72);
            GibCursor tmpaftercur_2736 = tmpcur_2728 + 8;
            GibCursor jump_1423 = tmpcur_2728 + 8;
            GibInt call_1424 =
                    caseFn_228(end_r_905, tmpcur_2735, n_85_230_314_488);

            return call_1424;
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_73 = *(uintptr_t *) tmpcur_2728;
            GibCursor tmpcur_2737 = GIB_UNTAG(tagged_tmpcur_73);
            GibCursor tmpaftercur_2738 = tmpcur_2728 + 8;
            GibInt call_1424 =
                    caseFn_228(end_r_905, tmpcur_2737, n_85_230_314_488);

            return call_1424;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2727");
            exit(1);
        }
    }
}

const int TREE_HEIGHT = 2;

int gib_main_expr(void)
{
    info_table_initialize();
    symbol_table_initialize();

    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibChunk region_2248 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_925 = region_2248.start;
    GibCursor end_r_925 = region_2248.end;
    GibChunk region_2249 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_924 = region_2249.start;
    GibCursor end_r_924 = region_2249.end;
    GibInt m_52_231_362 = gib_get_size_param();
    GibInt fltPrm_319_363 = gib_expll(2, TREE_HEIGHT);
    GibInt total_nodes_53_232_364 = fltPrm_319_363 - 1;
    GibCursor pvrtmp_2259;
    GibCursor pvrtmp_2260;
    GibCursor pvrtmp_2261;
    GibVector *times_87 = gib_vector_alloc(gib_get_iters_param(),
                                           sizeof(double));
    struct timespec begin_pvrtmp_2259;
    struct timespec end_pvrtmp_2259;

    clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_2259);
    {
        GibCursorGibCursorGibCursorProd tmp_struct_83 =
                                         helper(end_r_925, r_925, 0, total_nodes_53_232_364);
        GibCursor pvrtmp_2250 = tmp_struct_83.field0;
        GibCursor pvrtmp_2251 = tmp_struct_83.field1;
        GibCursor pvrtmp_2252 = tmp_struct_83.field2;

        pvrtmp_2259 = pvrtmp_2250;
        pvrtmp_2260 = pvrtmp_2251;
        pvrtmp_2261 = pvrtmp_2252;
    }
    clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_2259);

    double selftimed_86 = gib_difftimespecs(&begin_pvrtmp_2259,
                                            &end_pvrtmp_2259);

    gib_vector_free(times_87);
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("SELFTIMED: %e\n", gib_difftimespecs(&begin_pvrtmp_2259,
                                                &end_pvrtmp_2259));

    GibCursorGibIntProd tmp_struct_89 =  countnodes(end_r_925, pvrtmp_2260);
    GibCursor pvrtmp_2269 = tmp_struct_89.field0;
    GibInt pvrtmp_2270 = tmp_struct_89.field1;
    GibCursor pvrtmp_2280;
    GibCursor pvrtmp_2281;
    GibCursor pvrtmp_2282;
    GibVector *times_94 = gib_vector_alloc(gib_get_iters_param(),
                                           sizeof(double));
    struct timespec begin_pvrtmp_2280;
    struct timespec end_pvrtmp_2280;

    for (long long iters_pvrtmp_2280 = 0; iters_pvrtmp_2280 <
         gib_get_iters_param(); iters_pvrtmp_2280++) {
        if (iters_pvrtmp_2280 != gib_get_iters_param() - 1)
            gib_list_bumpalloc_save_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_2280);

        GibInt fltAppE_320_367 = gib_get_size_param();
        GibCursorGibCursorGibCursorProd tmp_struct_90 =
                                         loop(end_r_925, end_r_924, r_924, pvrtmp_2260, fltAppE_320_367);
        GibCursor pvrtmp_2271 = tmp_struct_90.field0;
        GibCursor pvrtmp_2272 = tmp_struct_90.field1;
        GibCursor pvrtmp_2273 = tmp_struct_90.field2;

        pvrtmp_2280 = pvrtmp_2271;
        pvrtmp_2281 = pvrtmp_2272;
        pvrtmp_2282 = pvrtmp_2273;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_2280);
        if (iters_pvrtmp_2280 != gib_get_iters_param() - 1)
            gib_list_bumpalloc_restore_state();

        double itertime_91 = gib_difftimespecs(&begin_pvrtmp_2280,
                                               &end_pvrtmp_2280);

        printf("itertime: %lf\n", itertime_91);
        gib_vector_inplace_update(times_94, iters_pvrtmp_2280, &itertime_91);
    }
    gib_vector_inplace_sort(times_94, gib_compare_doubles);

    double *tmp_95 = (double *) gib_vector_nth(times_94, gib_get_iters_param() / 2);
    double selftimed_93 = *tmp_95;
    double batchtime_92 = gib_sum_timing_array(times_94);

    gib_print_timing_array(times_94);
    gib_vector_free(times_94);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_92);
    printf("SELFTIMED: %e\n", selftimed_93);

    unsigned char __57_236_369 = printf("%ld", pvrtmp_2270);
    printf("\n");
    GibCursorGibIntProd tmp_struct_96 =  sum_tree(end_r_924, pvrtmp_2281);
    GibCursor pvrtmp_2290 = tmp_struct_96.field0;
    GibInt pvrtmp_2291 = tmp_struct_96.field1;

    printf("%ld", pvrtmp_2291);
    printf("\n");

    _print_SearchTree(end_r_924, pvrtmp_2281);
    printf("\n");
    _print_SearchTree(pvrtmp_2259, pvrtmp_2260);
    printf("\n");
    return 0;
}
