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
GibCursorGibCursorGibCursorProd helper(GibCursor end_r_853, GibCursor loc_852,
                                       GibInt s_58_236_368,
                                       GibInt e_59_237_369);
GibCursorGibCursorGibIntProd countnodes(GibCursor end_r_855,
                                        GibCursor tr_61_239_379);
GibCursorGibCursorGibCursorGibCursorProd loop(GibCursor end_r_858,
                                              GibCursor end_r_859,
                                              GibCursor loc_857,
                                              GibCursor tr_66_244_387,
                                              GibInt n_67_245_388);
GibCursorGibCursorGibIntProd sum_tree(GibCursor end_r_861,
                                      GibCursor tr_69_247_399);
GibCursorGibCursorGibCursorGibCursorProd tree_delete(GibCursor end_r_864,
                                                     GibCursor end_r_865,
                                                     GibCursor loc_863,
                                                     GibCursor tr_74_252_407,
                                                     GibInt n_75_253_408);
GibCursorGibIntProd min_tree(GibCursor end_r_867, GibCursor tr_82_260_423);
GibCursorGibCursorGibCursorGibCursorProd tree_insert(GibCursor end_r_870,
                                                     GibCursor end_r_871,
                                                     GibCursor loc_869,
                                                     GibCursor tr_91_265_428,
                                                     GibInt n_92_266_429);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_SearchTree(GibCursor end_r_874, GibCursor end_r_875, GibCursor loc_873,
                 GibCursor arg_185_271_444);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_SearchTree(GibCursor end_r_878, GibCursor end_r_879,
                              GibCursor loc_877, GibCursor arg_194_280_453);
GibCursorGibCursorProd _traverse_SearchTree(GibCursor end_r_881,
                                            GibCursor arg_203_289_462);
GibCursorGibCursorProd _print_SearchTree(GibCursor end_r_883,
                                         GibCursor arg_212_296_469);
GibCursorGibIntProd caseFn_227(GibCursor end_r_885, GibInt n_84_228_311_484,
                               GibCursor l_85_229_312_485);
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
    gib_add_symbol(2150, ")");
    gib_add_symbol(2151, "(Null ");
    gib_add_symbol(2152, "(Node ");
    gib_add_symbol(2153, "(Leaf ");
    gib_add_symbol(2154, " ->r ");
    gib_add_symbol(2155, " ->i ");
}
#define REGION_SIZE 256
#define TREE_HEIGHT 7
GibCursorGibCursorGibCursorProd helper(GibCursor end_r_853, GibCursor loc_852,
                                       GibInt s_58_236_368, GibInt e_59_237_369)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_852 + 26 > end_r_853) {
        gib_grow_region(&loc_852, &end_r_853);
    }

    GibBool fltIf_319_370 = e_59_237_369 < s_58_236_368;

    if (fltIf_319_370) {
        *(GibPackedTag *) loc_852 = 0;

        GibCursor writetag_1490 = loc_852 + 1;
        GibCursor after_tag_1491 = loc_852 + 1;

        return (GibCursorGibCursorGibCursorProd) {end_r_853, loc_852,
                                                  after_tag_1491};
    } else {
        GibBool fltIf_320_371 = s_58_236_368 == e_59_237_369;

        if (fltIf_320_371) {
            *(GibPackedTag *) loc_852 = 1;

            GibCursor writetag_1497 = loc_852 + 1;
            GibCursor after_tag_1498 = loc_852 + 1;

            *(GibInt *) after_tag_1498 = s_58_236_368;

            GibCursor writecur_1502 = after_tag_1498 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorProd) {end_r_853, loc_852,
                                                      writecur_1502};
        } else {
            GibInt fltPrm_322_372 = e_59_237_369 - s_58_236_368;
            GibInt fltPrm_321_373 = fltPrm_322_372 / 2;
            GibInt m_60_238_374 = fltPrm_321_373 + s_58_236_368;
            GibInt fltAppE_324_375 = m_60_238_374 - 1;
            GibCursor loc_912 = loc_852 + 17;

            *(GibPackedTag *) loc_852 = 3;

            GibCursor writetag_1507 = loc_852 + 1;

            gib_shadowstack_push(rstack, loc_852, end_r_853, Stk, SearchTree_T);

            GibCursorGibCursorGibCursorProd tmp_struct_0 =
                                             helper(end_r_853, loc_912, s_58_236_368, fltAppE_324_375);
            GibCursor pvrtmp_2213 = tmp_struct_0.field0;
            GibCursor pvrtmp_2214 = tmp_struct_0.field1;
            GibCursor pvrtmp_2215 = tmp_struct_0.field2;

            frame = gib_shadowstack_pop(rstack);
            loc_852 = frame->ptr;
            end_r_853 = frame->endptr;

            GibInt fltAppE_326_377 = m_60_238_374 + 1;

            gib_shadowstack_push(rstack, loc_852, pvrtmp_2213, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibCursorProd tmp_struct_1 =
                                             helper(pvrtmp_2213, pvrtmp_2215, fltAppE_326_377, e_59_237_369);
            GibCursor pvrtmp_2220 = tmp_struct_1.field0;
            GibCursor pvrtmp_2221 = tmp_struct_1.field1;
            GibCursor pvrtmp_2222 = tmp_struct_1.field2;

            frame = gib_shadowstack_pop(rstack);
            loc_852 = frame->ptr;
            pvrtmp_2213 = frame->endptr;

            uint16_t offset_2 = pvrtmp_2213 - pvrtmp_2215;
            uintptr_t ran_797 = GIB_STORE_TAG(pvrtmp_2215, offset_2);
            GibCursor after_tag_1508 = loc_852 + 1;

            *(uintptr_t *) after_tag_1508 = ran_797;

            GibCursor writecur_1512 = after_tag_1508 + 8;

            *(GibInt *) writecur_1512 = m_60_238_374;

            GibCursor writecur_1513 = writecur_1512 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorProd) {pvrtmp_2220, loc_852,
                                                      pvrtmp_2222};
        }
    }
}
GibCursorGibCursorGibIntProd countnodes(GibCursor end_r_855,
                                        GibCursor tr_61_239_379)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2231 = *(GibPackedTag *) tr_61_239_379;
    GibCursor tmpcur_2232 = tr_61_239_379 + 1;


  switch_2258:
    ;
    switch (tmpval_2231) {

      case 0:
        {
            GibCursor jump_1228 = tr_61_239_379 + 1;

            return (GibCursorGibCursorGibIntProd) {end_r_855, jump_1228, 0};
            break;
        }

      case 1:
        {
            GibInt tmpval_2233 = *(GibInt *) tmpcur_2232;
            GibCursor tmpcur_2234 = tmpcur_2232 + sizeof(GibInt);
            GibCursor jump_1229 = tmpcur_2232 + 8;

            return (GibCursorGibCursorGibIntProd) {end_r_855, jump_1229, 1};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_8 = *(uintptr_t *) tmpcur_2232;
            GibCursor tmpcur_2235 = GIB_UNTAG(tagged_tmpcur_8);
            GibCursor tmpaftercur_2236 = tmpcur_2232 + 8;
            uint16_t tmptag_2237 = GIB_GET_TAG(tagged_tmpcur_8);
            GibCursor end_from_tagged_absran_798 = tmpcur_2235 + tmptag_2237;
            GibInt tmpval_2238 = *(GibInt *) tmpaftercur_2236;
            GibCursor tmpcur_2239 = tmpaftercur_2236 + sizeof(GibInt);

            gib_shadowstack_push(rstack, tmpcur_2235, end_r_855, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibIntProd tmp_struct_6 =
                                          countnodes(end_r_855, tmpcur_2239);
            GibCursor pvrtmp_2240 = tmp_struct_6.field0;
            GibCursor pvrtmp_2241 = tmp_struct_6.field1;
            GibInt pvrtmp_2242 = tmp_struct_6.field2;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_2235 = frame->ptr;
            end_r_855 = frame->endptr;

            GibCursorGibCursorGibIntProd tmp_struct_7 =
                                          countnodes(end_from_tagged_absran_798, tmpcur_2235);
            GibCursor pvrtmp_2243 = tmp_struct_7.field0;
            GibCursor pvrtmp_2244 = tmp_struct_7.field1;
            GibInt pvrtmp_2245 = tmp_struct_7.field2;
            GibInt fltPrm_327_386 = pvrtmp_2242 + pvrtmp_2245;
            GibInt tailprim_1234 = 1 + fltPrm_327_386;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_2243, pvrtmp_2244,
                                                   tailprim_1234};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_10 = *(uintptr_t *) tmpcur_2232;
            GibCursor tmpcur_2246 = GIB_UNTAG(tagged_tmpcur_10);
            GibCursor tmpaftercur_2247 = tmpcur_2232 + 8;
            uint16_t tmptag_2248 = GIB_GET_TAG(tagged_tmpcur_10);
            GibCursor end_from_tagged_indr_1319 = tmpcur_2246 + tmptag_2248;
            GibCursor jump_1321 = tmpcur_2232 + 8;
            GibCursorGibCursorGibIntProd tmp_struct_9 =
                                          countnodes(end_from_tagged_indr_1319, tmpcur_2246);
            GibCursor pvrtmp_2249 = tmp_struct_9.field0;
            GibCursor pvrtmp_2250 = tmp_struct_9.field1;
            GibInt pvrtmp_2251 = tmp_struct_9.field2;

            return (GibCursorGibCursorGibIntProd) {end_r_855, jump_1321,
                                                   pvrtmp_2251};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_12 = *(uintptr_t *) tmpcur_2232;
            GibCursor tmpcur_2252 = GIB_UNTAG(tagged_tmpcur_12);
            GibCursor tmpaftercur_2253 = tmpcur_2232 + 8;
            uint16_t tmptag_2254 = GIB_GET_TAG(tagged_tmpcur_12);
            GibCursor end_from_tagged_indr_1319 = tmpcur_2252 + tmptag_2254;
            GibCursorGibCursorGibIntProd tmp_struct_11 =
                                          countnodes(end_from_tagged_indr_1319, tmpcur_2252);
            GibCursor pvrtmp_2255 = tmp_struct_11.field0;
            GibCursor pvrtmp_2256 = tmp_struct_11.field1;
            GibInt pvrtmp_2257 = tmp_struct_11.field2;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_2255, pvrtmp_2256,
                                                   pvrtmp_2257};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2231");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd loop(GibCursor end_r_858,
                                              GibCursor end_r_859,
                                              GibCursor loc_857,
                                              GibCursor tr_66_244_387,
                                              GibInt n_67_245_388)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_857 + 26 > end_r_859) {
        gib_grow_region(&loc_857, &end_r_859);
    }

    GibBool fltIf_330_389 = n_67_245_388 == 0;

    if (fltIf_330_389) {
        gib_indirection_barrier(loc_857, end_r_859, tr_66_244_387, end_r_858,
                                SearchTree_T);

        GibCursor end_1534 = loc_857 + 9;

        return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_858, end_r_859,
                                                           loc_857, end_1534};
    } else {
        GibInt fltPrm_331_390 = rand();
        GibInt j_68_246_391 = fltPrm_331_390 % 1000;
        GibInt fltPrm_333_392 = j_68_246_391 % 2;
        GibBool fltIf_332_393 = 0 == fltPrm_333_392;

        if (fltIf_332_393) {
            gib_shadowstack_push(rstack, tr_66_244_387, end_r_858, Stk,
                                 SearchTree_T);
            gib_shadowstack_push(wstack, loc_857, end_r_859, Stk, SearchTree_T);

            GibChunk region_2263 =
                     gib_alloc_region(REGION_SIZE);
            GibCursor r_940 = region_2263.start;
            GibCursor end_r_940 = region_2263.end;

            frame = gib_shadowstack_pop(wstack);
            loc_857 = frame->ptr;
            end_r_859 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tr_66_244_387 = frame->ptr;
            end_r_858 = frame->endptr;
            gib_shadowstack_push(wstack, loc_857, end_r_859, Stk, SearchTree_T);

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_13 =
                                                      tree_insert(end_r_858, end_r_940, r_940, tr_66_244_387, j_68_246_391);
            GibCursor pvrtmp_2264 = tmp_struct_13.field0;
            GibCursor pvrtmp_2265 = tmp_struct_13.field1;
            GibCursor pvrtmp_2266 = tmp_struct_13.field2;
            GibCursor pvrtmp_2267 = tmp_struct_13.field3;

            frame = gib_shadowstack_pop(wstack);
            loc_857 = frame->ptr;
            end_r_859 = frame->endptr;

            GibInt fltAppE_335_395 = n_67_245_388 - 1;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_14 =
                                                      loop(pvrtmp_2265, end_r_859, loc_857, pvrtmp_2266, fltAppE_335_395);
            GibCursor pvrtmp_2272 = tmp_struct_14.field0;
            GibCursor pvrtmp_2273 = tmp_struct_14.field1;
            GibCursor pvrtmp_2274 = tmp_struct_14.field2;
            GibCursor pvrtmp_2275 = tmp_struct_14.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2264,
                                                               pvrtmp_2273,
                                                               pvrtmp_2274,
                                                               pvrtmp_2275};
        } else {
            GibInt fltAppE_337_396 = j_68_246_391 - 1;

            gib_shadowstack_push(rstack, tr_66_244_387, end_r_858, Stk,
                                 SearchTree_T);
            gib_shadowstack_push(wstack, loc_857, end_r_859, Stk, SearchTree_T);

            GibChunk region_2282 =
                     gib_alloc_region(REGION_SIZE);
            GibCursor r_949 = region_2282.start;
            GibCursor end_r_949 = region_2282.end;

            frame = gib_shadowstack_pop(wstack);
            loc_857 = frame->ptr;
            end_r_859 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tr_66_244_387 = frame->ptr;
            end_r_858 = frame->endptr;
            gib_shadowstack_push(wstack, loc_857, end_r_859, Stk, SearchTree_T);

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_15 =
                                                      tree_delete(end_r_858, end_r_949, r_949, tr_66_244_387, fltAppE_337_396);
            GibCursor pvrtmp_2283 = tmp_struct_15.field0;
            GibCursor pvrtmp_2284 = tmp_struct_15.field1;
            GibCursor pvrtmp_2285 = tmp_struct_15.field2;
            GibCursor pvrtmp_2286 = tmp_struct_15.field3;

            frame = gib_shadowstack_pop(wstack);
            loc_857 = frame->ptr;
            end_r_859 = frame->endptr;

            GibInt fltAppE_338_398 = n_67_245_388 - 1;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_16 =
                                                      loop(pvrtmp_2284, end_r_859, loc_857, pvrtmp_2285, fltAppE_338_398);
            GibCursor pvrtmp_2291 = tmp_struct_16.field0;
            GibCursor pvrtmp_2292 = tmp_struct_16.field1;
            GibCursor pvrtmp_2293 = tmp_struct_16.field2;
            GibCursor pvrtmp_2294 = tmp_struct_16.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2283,
                                                               pvrtmp_2292,
                                                               pvrtmp_2293,
                                                               pvrtmp_2294};
        }
    }
}
GibCursorGibCursorGibIntProd sum_tree(GibCursor end_r_861,
                                      GibCursor tr_69_247_399)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2301 = *(GibPackedTag *) tr_69_247_399;
    GibCursor tmpcur_2302 = tr_69_247_399 + 1;


  switch_2328:
    ;
    switch (tmpval_2301) {

      case 0:
        {
            GibCursor jump_1238 = tr_69_247_399 + 1;

            return (GibCursorGibCursorGibIntProd) {end_r_861, jump_1238, 0};
            break;
        }

      case 1:
        {
            GibInt tmpval_2303 = *(GibInt *) tmpcur_2302;
            GibCursor tmpcur_2304 = tmpcur_2302 + sizeof(GibInt);
            GibCursor jump_1239 = tmpcur_2302 + 8;

            return (GibCursorGibCursorGibIntProd) {end_r_861, jump_1239,
                                                   tmpval_2303};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_22 = *(uintptr_t *) tmpcur_2302;
            GibCursor tmpcur_2305 = GIB_UNTAG(tagged_tmpcur_22);
            GibCursor tmpaftercur_2306 = tmpcur_2302 + 8;
            uint16_t tmptag_2307 = GIB_GET_TAG(tagged_tmpcur_22);
            GibCursor end_from_tagged_absran_801 = tmpcur_2305 + tmptag_2307;
            GibInt tmpval_2308 = *(GibInt *) tmpaftercur_2306;
            GibCursor tmpcur_2309 = tmpaftercur_2306 + sizeof(GibInt);

            gib_shadowstack_push(rstack, tmpcur_2305, end_r_861, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibIntProd tmp_struct_20 =
                                          sum_tree(end_r_861, tmpcur_2309);
            GibCursor pvrtmp_2310 = tmp_struct_20.field0;
            GibCursor pvrtmp_2311 = tmp_struct_20.field1;
            GibInt pvrtmp_2312 = tmp_struct_20.field2;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_2305 = frame->ptr;
            end_r_861 = frame->endptr;

            GibCursorGibCursorGibIntProd tmp_struct_21 =
                                          sum_tree(end_from_tagged_absran_801, tmpcur_2305);
            GibCursor pvrtmp_2313 = tmp_struct_21.field0;
            GibCursor pvrtmp_2314 = tmp_struct_21.field1;
            GibInt pvrtmp_2315 = tmp_struct_21.field2;
            GibInt fltPrm_339_406 = pvrtmp_2312 + pvrtmp_2315;
            GibInt tailprim_1244 = tmpval_2308 + fltPrm_339_406;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_2313, pvrtmp_2314,
                                                   tailprim_1244};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_24 = *(uintptr_t *) tmpcur_2302;
            GibCursor tmpcur_2316 = GIB_UNTAG(tagged_tmpcur_24);
            GibCursor tmpaftercur_2317 = tmpcur_2302 + 8;
            uint16_t tmptag_2318 = GIB_GET_TAG(tagged_tmpcur_24);
            GibCursor end_from_tagged_indr_1325 = tmpcur_2316 + tmptag_2318;
            GibCursor jump_1327 = tmpcur_2302 + 8;
            GibCursorGibCursorGibIntProd tmp_struct_23 =
                                          sum_tree(end_from_tagged_indr_1325, tmpcur_2316);
            GibCursor pvrtmp_2319 = tmp_struct_23.field0;
            GibCursor pvrtmp_2320 = tmp_struct_23.field1;
            GibInt pvrtmp_2321 = tmp_struct_23.field2;

            return (GibCursorGibCursorGibIntProd) {end_r_861, jump_1327,
                                                   pvrtmp_2321};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_26 = *(uintptr_t *) tmpcur_2302;
            GibCursor tmpcur_2322 = GIB_UNTAG(tagged_tmpcur_26);
            GibCursor tmpaftercur_2323 = tmpcur_2302 + 8;
            uint16_t tmptag_2324 = GIB_GET_TAG(tagged_tmpcur_26);
            GibCursor end_from_tagged_indr_1325 = tmpcur_2322 + tmptag_2324;
            GibCursorGibCursorGibIntProd tmp_struct_25 =
                                          sum_tree(end_from_tagged_indr_1325, tmpcur_2322);
            GibCursor pvrtmp_2325 = tmp_struct_25.field0;
            GibCursor pvrtmp_2326 = tmp_struct_25.field1;
            GibInt pvrtmp_2327 = tmp_struct_25.field2;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_2325, pvrtmp_2326,
                                                   pvrtmp_2327};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2301");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd tree_delete(GibCursor end_r_864,
                                                     GibCursor end_r_865,
                                                     GibCursor loc_863,
                                                     GibCursor tr_74_252_407,
                                                     GibInt n_75_253_408)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_863 + 26 > end_r_865) {
        gib_grow_region(&loc_863, &end_r_865);
    }

    GibPackedTag tmpval_2329 = *(GibPackedTag *) tr_74_252_407;
    GibCursor tmpcur_2330 = tr_74_252_407 + 1;


  switch_2421:
    ;
    switch (tmpval_2329) {

      case 0:
        {
            *(GibPackedTag *) loc_863 = 1;

            GibCursor writetag_1555 = loc_863 + 1;
            GibCursor after_tag_1556 = loc_863 + 1;

            *(GibInt *) after_tag_1556 = n_75_253_408;

            GibCursor writecur_1560 = after_tag_1556 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_864,
                                                               end_r_865,
                                                               loc_863,
                                                               writecur_1560};
            break;
        }

      case 1:
        {
            GibInt tmpval_2335 = *(GibInt *) tmpcur_2330;
            GibCursor tmpcur_2336 = tmpcur_2330 + sizeof(GibInt);
            GibBool fltIf_342_410 = tmpval_2335 == n_75_253_408;

            if (fltIf_342_410) {
                *(GibPackedTag *) loc_863 = 0;

                GibCursor writetag_1565 = loc_863 + 1;
                GibCursor after_tag_1566 = loc_863 + 1;

                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_864,
                                                                   end_r_865,
                                                                   loc_863,
                                                                   after_tag_1566};
            } else {
                *(GibPackedTag *) loc_863 = 1;

                GibCursor writetag_1572 = loc_863 + 1;
                GibCursor after_tag_1573 = loc_863 + 1;

                *(GibInt *) after_tag_1573 = tmpval_2335;

                GibCursor writecur_1577 = after_tag_1573 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_864,
                                                                   end_r_865,
                                                                   loc_863,
                                                                   writecur_1577};
            }
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_34 = *(uintptr_t *) tmpcur_2330;
            GibCursor tmpcur_2345 = GIB_UNTAG(tagged_tmpcur_34);
            GibCursor tmpaftercur_2346 = tmpcur_2330 + 8;
            uint16_t tmptag_2347 = GIB_GET_TAG(tagged_tmpcur_34);
            GibCursor end_from_tagged_absran_807 = tmpcur_2345 + tmptag_2347;
            GibInt tmpval_2348 = *(GibInt *) tmpaftercur_2346;
            GibCursor tmpcur_2349 = tmpaftercur_2346 + sizeof(GibInt);
            GibBool fltIf_343_414 = tmpval_2348 == n_75_253_408;

            if (fltIf_343_414) {
                gib_shadowstack_push(rstack, tmpcur_2345, end_r_864, Stk,
                                     SearchTree_T);
                gib_shadowstack_push(rstack, tmpcur_2349, end_r_864, Stk,
                                     SearchTree_T);
                gib_shadowstack_push(wstack, loc_863, end_r_865, Stk,
                                     SearchTree_T);

                GibCursorGibIntProd tmp_struct_27 =
                                     min_tree(end_from_tagged_absran_807, tmpcur_2345);
                GibCursor pvrtmp_2350 = tmp_struct_27.field0;
                GibInt pvrtmp_2351 = tmp_struct_27.field1;

                frame = gib_shadowstack_pop(wstack);
                loc_863 = frame->ptr;
                end_r_865 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                tmpcur_2349 = frame->ptr;
                end_r_864 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                tmpcur_2345 = frame->ptr;
                end_r_864 = frame->endptr;
                gib_shadowstack_push(rstack, tmpcur_2345, end_r_864, Stk,
                                     SearchTree_T);
                gib_shadowstack_push(rstack, tmpcur_2349, end_r_864, Stk,
                                     SearchTree_T);
                gib_shadowstack_push(wstack, loc_863, end_r_865, Stk,
                                     SearchTree_T);

                GibChunk region_2352 =
                         gib_alloc_region(REGION_SIZE);
                GibCursor r_1028 = region_2352.start;
                GibCursor end_r_1028 = region_2352.end;

                frame = gib_shadowstack_pop(wstack);
                loc_863 = frame->ptr;
                end_r_865 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                tmpcur_2349 = frame->ptr;
                end_r_864 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                tmpcur_2345 = frame->ptr;
                end_r_864 = frame->endptr;
                gib_shadowstack_push(rstack, tmpcur_2349, end_r_864, Stk,
                                     SearchTree_T);
                gib_shadowstack_push(wstack, loc_863, end_r_865, Stk,
                                     SearchTree_T);

                GibCursorGibCursorGibCursorGibCursorProd tmp_struct_28 =
                                                          tree_delete(end_from_tagged_absran_807, end_r_1028, r_1028, tmpcur_2345, pvrtmp_2351);
                GibCursor pvrtmp_2353 = tmp_struct_28.field0;
                GibCursor pvrtmp_2354 = tmp_struct_28.field1;
                GibCursor pvrtmp_2355 = tmp_struct_28.field2;
                GibCursor pvrtmp_2356 = tmp_struct_28.field3;

                frame = gib_shadowstack_pop(wstack);
                loc_863 = frame->ptr;
                end_r_865 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                tmpcur_2349 = frame->ptr;
                end_r_864 = frame->endptr;

                GibCursor loc_985 = loc_863 + 17;

                *(GibPackedTag *) loc_863 = 3;

                GibCursor writetag_1588 = loc_863 + 1;

                gib_indirection_barrier(loc_985, end_r_865, tmpcur_2349,
                                        end_r_864, SearchTree_T);

                GibCursor end_1586 = loc_985 + 9;
                uint16_t offset_29 = end_r_1028 - r_1028;
                uintptr_t ran_810 = GIB_STORE_TAG(r_1028, offset_29);
                GibCursor after_tag_1589 = loc_863 + 1;

                *(uintptr_t *) after_tag_1589 = ran_810;

                GibCursor writecur_1593 = after_tag_1589 + 8;

                *(GibInt *) writecur_1593 = pvrtmp_2351;

                GibCursor writecur_1594 = writecur_1593 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2353,
                                                                   pvrtmp_2354,
                                                                   loc_863,
                                                                   pvrtmp_2356};
            } else {
                GibBool fltIf_345_418 = tmpval_2348 < n_75_253_408;

                if (fltIf_345_418) {
                    GibCursor loc_1001 = loc_863 + 17;

                    *(GibPackedTag *) loc_863 = 3;

                    GibCursor writetag_1604 = loc_863 + 1;

                    gib_indirection_barrier(loc_1001, end_r_865, tmpcur_2349,
                                            end_r_864, SearchTree_T);

                    GibCursor end_1601 = loc_1001 + 9;

                    gib_shadowstack_push(rstack, loc_863, end_r_865, Stk,
                                         SearchTree_T);

                    GibCursorGibCursorGibCursorGibCursorProd tmp_struct_30 =
                                                              tree_delete(end_from_tagged_absran_807, end_r_865, end_1601, tmpcur_2345, n_75_253_408);
                    GibCursor pvrtmp_2369 = tmp_struct_30.field0;
                    GibCursor pvrtmp_2370 = tmp_struct_30.field1;
                    GibCursor pvrtmp_2371 = tmp_struct_30.field2;
                    GibCursor pvrtmp_2372 = tmp_struct_30.field3;

                    frame = gib_shadowstack_pop(rstack);
                    loc_863 = frame->ptr;
                    end_r_865 = frame->endptr;

                    uint16_t offset_31 = end_r_865 - end_1601;
                    uintptr_t ran_811 = GIB_STORE_TAG(end_1601, offset_31);
                    GibCursor after_tag_1605 = loc_863 + 1;

                    *(uintptr_t *) after_tag_1605 = ran_811;

                    GibCursor writecur_1609 = after_tag_1605 + 8;

                    *(GibInt *) writecur_1609 = tmpval_2348;

                    GibCursor writecur_1610 = writecur_1609 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2369,
                                                                       pvrtmp_2370,
                                                                       loc_863,
                                                                       pvrtmp_2372};
                } else {
                    GibCursor loc_1017 = loc_863 + 17;

                    *(GibPackedTag *) loc_863 = 3;

                    GibCursor writetag_1620 = loc_863 + 1;

                    gib_shadowstack_push(rstack, loc_863, end_r_865, Stk,
                                         SearchTree_T);
                    gib_shadowstack_push(rstack, tmpcur_2345, end_r_864, Stk,
                                         SearchTree_T);

                    GibCursorGibCursorGibCursorGibCursorProd tmp_struct_32 =
                                                              tree_delete(end_r_864, end_r_865, loc_1017, tmpcur_2349, n_75_253_408);
                    GibCursor pvrtmp_2381 = tmp_struct_32.field0;
                    GibCursor pvrtmp_2382 = tmp_struct_32.field1;
                    GibCursor pvrtmp_2383 = tmp_struct_32.field2;
                    GibCursor pvrtmp_2384 = tmp_struct_32.field3;

                    frame = gib_shadowstack_pop(rstack);
                    tmpcur_2345 = frame->ptr;
                    end_r_864 = frame->endptr;
                    frame = gib_shadowstack_pop(rstack);
                    loc_863 = frame->ptr;
                    end_r_865 = frame->endptr;
                    gib_indirection_barrier(pvrtmp_2384, pvrtmp_2382,
                                            tmpcur_2345,
                                            end_from_tagged_absran_807,
                                            SearchTree_T);

                    GibCursor end_1618 = pvrtmp_2384 + 9;
                    uint16_t offset_33 = pvrtmp_2382 - pvrtmp_2384;
                    uintptr_t ran_812 = GIB_STORE_TAG(pvrtmp_2384, offset_33);
                    GibCursor after_tag_1621 = loc_863 + 1;

                    *(uintptr_t *) after_tag_1621 = ran_812;

                    GibCursor writecur_1625 = after_tag_1621 + 8;

                    *(GibInt *) writecur_1625 = tmpval_2348;

                    GibCursor writecur_1626 = writecur_1625 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2381,
                                                                       pvrtmp_2382,
                                                                       loc_863,
                                                                       end_1618};
                }
            }
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_36 = *(uintptr_t *) tmpcur_2330;
            GibCursor tmpcur_2395 = GIB_UNTAG(tagged_tmpcur_36);
            GibCursor tmpaftercur_2396 = tmpcur_2330 + 8;
            uint16_t tmptag_2397 = GIB_GET_TAG(tagged_tmpcur_36);
            GibCursor end_from_tagged_indr_1331 = tmpcur_2395 + tmptag_2397;
            GibCursor jump_1333 = tmpcur_2330 + 8;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_35 =
                                                      tree_delete(end_from_tagged_indr_1331, end_r_865, loc_863, tmpcur_2395, n_75_253_408);
            GibCursor pvrtmp_2398 = tmp_struct_35.field0;
            GibCursor pvrtmp_2399 = tmp_struct_35.field1;
            GibCursor pvrtmp_2400 = tmp_struct_35.field2;
            GibCursor pvrtmp_2401 = tmp_struct_35.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_864,
                                                               pvrtmp_2399,
                                                               pvrtmp_2400,
                                                               pvrtmp_2401};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_38 = *(uintptr_t *) tmpcur_2330;
            GibCursor tmpcur_2408 = GIB_UNTAG(tagged_tmpcur_38);
            GibCursor tmpaftercur_2409 = tmpcur_2330 + 8;
            uint16_t tmptag_2410 = GIB_GET_TAG(tagged_tmpcur_38);
            GibCursor end_from_tagged_indr_1331 = tmpcur_2408 + tmptag_2410;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_37 =
                                                      tree_delete(end_from_tagged_indr_1331, end_r_865, loc_863, tmpcur_2408, n_75_253_408);
            GibCursor pvrtmp_2411 = tmp_struct_37.field0;
            GibCursor pvrtmp_2412 = tmp_struct_37.field1;
            GibCursor pvrtmp_2413 = tmp_struct_37.field2;
            GibCursor pvrtmp_2414 = tmp_struct_37.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2411,
                                                               pvrtmp_2412,
                                                               pvrtmp_2413,
                                                               pvrtmp_2414};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2329");
            exit(1);
        }
    }
}
GibCursorGibIntProd min_tree(GibCursor end_r_867, GibCursor tr_82_260_423)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2422 = *(GibPackedTag *) tr_82_260_423;
    GibCursor tmpcur_2423 = tr_82_260_423 + 1;


  switch_2443:
    ;
    switch (tmpval_2422) {

      case 0:
        {
            return (GibCursorGibIntProd) {end_r_867, 0};
            break;
        }

      case 1:
        {
            GibInt tmpval_2424 = *(GibInt *) tmpcur_2423;
            GibCursor tmpcur_2425 = tmpcur_2423 + sizeof(GibInt);

            return (GibCursorGibIntProd) {end_r_867, tmpval_2424};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_43 = *(uintptr_t *) tmpcur_2423;
            GibCursor tmpcur_2426 = GIB_UNTAG(tagged_tmpcur_43);
            GibCursor tmpaftercur_2427 = tmpcur_2423 + 8;
            uint16_t tmptag_2428 = GIB_GET_TAG(tagged_tmpcur_43);
            GibCursor end_from_tagged_absran_816 = tmpcur_2426 + tmptag_2428;
            GibInt tmpval_2429 = *(GibInt *) tmpaftercur_2427;
            GibCursor tmpcur_2430 = tmpaftercur_2427 + sizeof(GibInt);
            GibCursorGibIntProd tmp_struct_42 =
                                 caseFn_227(end_r_867, tmpval_2429, tmpcur_2430);
            GibCursor pvrtmp_2431 = tmp_struct_42.field0;
            GibInt pvrtmp_2432 = tmp_struct_42.field1;

            return (GibCursorGibIntProd) {pvrtmp_2431, pvrtmp_2432};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_45 = *(uintptr_t *) tmpcur_2423;
            GibCursor tmpcur_2433 = GIB_UNTAG(tagged_tmpcur_45);
            GibCursor tmpaftercur_2434 = tmpcur_2423 + 8;
            uint16_t tmptag_2435 = GIB_GET_TAG(tagged_tmpcur_45);
            GibCursor end_from_tagged_indr_1336 = tmpcur_2433 + tmptag_2435;
            GibCursor jump_1338 = tmpcur_2423 + 8;
            GibCursorGibIntProd tmp_struct_44 =
                                 min_tree(end_from_tagged_indr_1336, tmpcur_2433);
            GibCursor pvrtmp_2436 = tmp_struct_44.field0;
            GibInt pvrtmp_2437 = tmp_struct_44.field1;

            return (GibCursorGibIntProd) {end_r_867, pvrtmp_2437};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_47 = *(uintptr_t *) tmpcur_2423;
            GibCursor tmpcur_2438 = GIB_UNTAG(tagged_tmpcur_47);
            GibCursor tmpaftercur_2439 = tmpcur_2423 + 8;
            uint16_t tmptag_2440 = GIB_GET_TAG(tagged_tmpcur_47);
            GibCursor end_from_tagged_indr_1336 = tmpcur_2438 + tmptag_2440;
            GibCursorGibIntProd tmp_struct_46 =
                                 min_tree(end_from_tagged_indr_1336, tmpcur_2438);
            GibCursor pvrtmp_2441 = tmp_struct_46.field0;
            GibInt pvrtmp_2442 = tmp_struct_46.field1;

            return (GibCursorGibIntProd) {pvrtmp_2441, pvrtmp_2442};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2422");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd tree_insert(GibCursor end_r_870,
                                                     GibCursor end_r_871,
                                                     GibCursor loc_869,
                                                     GibCursor tr_91_265_428,
                                                     GibInt n_92_266_429)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_869 + 26 > end_r_871) {
        gib_grow_region(&loc_869, &end_r_871);
    }

    GibPackedTag tmpval_2444 = *(GibPackedTag *) tr_91_265_428;
    GibCursor tmpcur_2445 = tr_91_265_428 + 1;


  switch_2527:
    ;
    switch (tmpval_2444) {

      case 0:
        {
            *(GibPackedTag *) loc_869 = 1;

            GibCursor writetag_1652 = loc_869 + 1;
            GibCursor after_tag_1653 = loc_869 + 1;

            *(GibInt *) after_tag_1653 = n_92_266_429;

            GibCursor writecur_1657 = after_tag_1653 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_870,
                                                               end_r_871,
                                                               loc_869,
                                                               writecur_1657};
            break;
        }

      case 1:
        {
            GibInt tmpval_2450 = *(GibInt *) tmpcur_2445;
            GibCursor tmpcur_2451 = tmpcur_2445 + sizeof(GibInt);
            GibBool fltIf_350_431 = n_92_266_429 < tmpval_2450;

            if (fltIf_350_431) {
                GibCursor loc_1052 = loc_869 + 17;

                *(GibPackedTag *) loc_869 = 3;

                GibCursor writetag_1677 = loc_869 + 1;

                *(GibPackedTag *) loc_1052 = 1;

                GibCursor writetag_1662 = loc_1052 + 1;
                GibCursor after_tag_1663 = loc_1052 + 1;

                *(GibInt *) after_tag_1663 = n_92_266_429;

                GibCursor writecur_1667 = after_tag_1663 + sizeof(GibInt);

                *(GibPackedTag *) writecur_1667 = 0;

                GibCursor writetag_1670 = writecur_1667 + 1;
                GibCursor after_tag_1671 = writecur_1667 + 1;
                uint16_t offset_48 = end_r_871 - writecur_1667;
                uintptr_t ran_819 = GIB_STORE_TAG(writecur_1667, offset_48);
                GibCursor after_tag_1678 = loc_869 + 1;

                *(uintptr_t *) after_tag_1678 = ran_819;

                GibCursor writecur_1682 = after_tag_1678 + 8;

                *(GibInt *) writecur_1682 = tmpval_2450;

                GibCursor writecur_1683 = writecur_1682 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_870,
                                                                   end_r_871,
                                                                   loc_869,
                                                                   after_tag_1671};
            } else {
                GibCursor loc_1068 = loc_869 + 17;

                *(GibPackedTag *) loc_869 = 3;

                GibCursor writetag_1704 = loc_869 + 1;

                *(GibPackedTag *) loc_1068 = 0;

                GibCursor writetag_1689 = loc_1068 + 1;
                GibCursor after_tag_1690 = loc_1068 + 1;

                *(GibPackedTag *) after_tag_1690 = 1;

                GibCursor writetag_1696 = after_tag_1690 + 1;
                GibCursor after_tag_1697 = after_tag_1690 + 1;

                *(GibInt *) after_tag_1697 = n_92_266_429;

                GibCursor writecur_1701 = after_tag_1697 + sizeof(GibInt);
                uint16_t offset_49 = end_r_871 - after_tag_1690;
                uintptr_t ran_820 = GIB_STORE_TAG(after_tag_1690, offset_49);
                GibCursor after_tag_1705 = loc_869 + 1;

                *(uintptr_t *) after_tag_1705 = ran_820;

                GibCursor writecur_1709 = after_tag_1705 + 8;

                *(GibInt *) writecur_1709 = tmpval_2450;

                GibCursor writecur_1710 = writecur_1709 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_870,
                                                                   end_r_871,
                                                                   loc_869,
                                                                   writecur_1701};
            }
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_54 = *(uintptr_t *) tmpcur_2445;
            GibCursor tmpcur_2468 = GIB_UNTAG(tagged_tmpcur_54);
            GibCursor tmpaftercur_2469 = tmpcur_2445 + 8;
            uint16_t tmptag_2470 = GIB_GET_TAG(tagged_tmpcur_54);
            GibCursor end_from_tagged_absran_823 = tmpcur_2468 + tmptag_2470;
            GibInt tmpval_2471 = *(GibInt *) tmpaftercur_2469;
            GibCursor tmpcur_2472 = tmpaftercur_2469 + sizeof(GibInt);
            GibBool fltIf_355_439 = tmpval_2471 < n_92_266_429;

            if (fltIf_355_439) {
                GibCursor loc_1088 = loc_869 + 17;

                *(GibPackedTag *) loc_869 = 3;

                GibCursor writetag_1723 = loc_869 + 1;

                gib_indirection_barrier(loc_1088, end_r_871, tmpcur_2472,
                                        end_r_870, SearchTree_T);

                GibCursor end_1720 = loc_1088 + 9;

                gib_shadowstack_push(rstack, loc_869, end_r_871, Stk,
                                     SearchTree_T);

                GibCursorGibCursorGibCursorGibCursorProd tmp_struct_50 =
                                                          tree_insert(end_from_tagged_absran_823, end_r_871, end_1720, tmpcur_2468, n_92_266_429);
                GibCursor pvrtmp_2475 = tmp_struct_50.field0;
                GibCursor pvrtmp_2476 = tmp_struct_50.field1;
                GibCursor pvrtmp_2477 = tmp_struct_50.field2;
                GibCursor pvrtmp_2478 = tmp_struct_50.field3;

                frame = gib_shadowstack_pop(rstack);
                loc_869 = frame->ptr;
                end_r_871 = frame->endptr;

                uint16_t offset_51 = end_r_871 - end_1720;
                uintptr_t ran_826 = GIB_STORE_TAG(end_1720, offset_51);
                GibCursor after_tag_1724 = loc_869 + 1;

                *(uintptr_t *) after_tag_1724 = ran_826;

                GibCursor writecur_1728 = after_tag_1724 + 8;

                *(GibInt *) writecur_1728 = tmpval_2471;

                GibCursor writecur_1729 = writecur_1728 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2475,
                                                                   pvrtmp_2476,
                                                                   loc_869,
                                                                   pvrtmp_2478};
            } else {
                GibCursor loc_1104 = loc_869 + 17;

                *(GibPackedTag *) loc_869 = 3;

                GibCursor writetag_1739 = loc_869 + 1;

                gib_shadowstack_push(rstack, loc_869, end_r_871, Stk,
                                     SearchTree_T);
                gib_shadowstack_push(rstack, tmpcur_2468, end_r_870, Stk,
                                     SearchTree_T);

                GibCursorGibCursorGibCursorGibCursorProd tmp_struct_52 =
                                                          tree_insert(end_r_870, end_r_871, loc_1104, tmpcur_2472, n_92_266_429);
                GibCursor pvrtmp_2487 = tmp_struct_52.field0;
                GibCursor pvrtmp_2488 = tmp_struct_52.field1;
                GibCursor pvrtmp_2489 = tmp_struct_52.field2;
                GibCursor pvrtmp_2490 = tmp_struct_52.field3;

                frame = gib_shadowstack_pop(rstack);
                tmpcur_2468 = frame->ptr;
                end_r_870 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                loc_869 = frame->ptr;
                end_r_871 = frame->endptr;
                gib_indirection_barrier(pvrtmp_2490, pvrtmp_2488, tmpcur_2468,
                                        end_from_tagged_absran_823,
                                        SearchTree_T);

                GibCursor end_1737 = pvrtmp_2490 + 9;
                uint16_t offset_53 = pvrtmp_2488 - pvrtmp_2490;
                uintptr_t ran_827 = GIB_STORE_TAG(pvrtmp_2490, offset_53);
                GibCursor after_tag_1740 = loc_869 + 1;

                *(uintptr_t *) after_tag_1740 = ran_827;

                GibCursor writecur_1744 = after_tag_1740 + 8;

                *(GibInt *) writecur_1744 = tmpval_2471;

                GibCursor writecur_1745 = writecur_1744 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2487,
                                                                   pvrtmp_2488,
                                                                   loc_869,
                                                                   end_1737};
            }
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_56 = *(uintptr_t *) tmpcur_2445;
            GibCursor tmpcur_2501 = GIB_UNTAG(tagged_tmpcur_56);
            GibCursor tmpaftercur_2502 = tmpcur_2445 + 8;
            uint16_t tmptag_2503 = GIB_GET_TAG(tagged_tmpcur_56);
            GibCursor end_from_tagged_indr_1341 = tmpcur_2501 + tmptag_2503;
            GibCursor jump_1343 = tmpcur_2445 + 8;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_55 =
                                                      tree_insert(end_from_tagged_indr_1341, end_r_871, loc_869, tmpcur_2501, n_92_266_429);
            GibCursor pvrtmp_2504 = tmp_struct_55.field0;
            GibCursor pvrtmp_2505 = tmp_struct_55.field1;
            GibCursor pvrtmp_2506 = tmp_struct_55.field2;
            GibCursor pvrtmp_2507 = tmp_struct_55.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_870,
                                                               pvrtmp_2505,
                                                               pvrtmp_2506,
                                                               pvrtmp_2507};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_58 = *(uintptr_t *) tmpcur_2445;
            GibCursor tmpcur_2514 = GIB_UNTAG(tagged_tmpcur_58);
            GibCursor tmpaftercur_2515 = tmpcur_2445 + 8;
            uint16_t tmptag_2516 = GIB_GET_TAG(tagged_tmpcur_58);
            GibCursor end_from_tagged_indr_1341 = tmpcur_2514 + tmptag_2516;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_57 =
                                                      tree_insert(end_from_tagged_indr_1341, end_r_871, loc_869, tmpcur_2514, n_92_266_429);
            GibCursor pvrtmp_2517 = tmp_struct_57.field0;
            GibCursor pvrtmp_2518 = tmp_struct_57.field1;
            GibCursor pvrtmp_2519 = tmp_struct_57.field2;
            GibCursor pvrtmp_2520 = tmp_struct_57.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2517,
                                                               pvrtmp_2518,
                                                               pvrtmp_2519,
                                                               pvrtmp_2520};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2444");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_SearchTree(GibCursor end_r_874,
                                                                   GibCursor end_r_875,
                                                                   GibCursor loc_873,
                                                                   GibCursor arg_185_271_444)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_873 + 26 > end_r_875) {
        gib_grow_region(&loc_873, &end_r_875);
    }

    GibPackedTag tmpval_2528 = *(GibPackedTag *) arg_185_271_444;
    GibCursor tmpcur_2529 = arg_185_271_444 + 1;


  switch_2595:
    ;
    switch (tmpval_2528) {

      case 0:
        {
            GibCursor jump_1270 = arg_185_271_444 + 1;

            *(GibPackedTag *) loc_873 = 0;

            GibCursor writetag_1758 = loc_873 + 1;
            GibCursor after_tag_1759 = loc_873 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_874,
                                                                        end_r_875,
                                                                        jump_1270,
                                                                        loc_873,
                                                                        after_tag_1759};
            break;
        }

      case 1:
        {
            GibInt tmpval_2534 = *(GibInt *) tmpcur_2529;
            GibCursor tmpcur_2535 = tmpcur_2529 + sizeof(GibInt);
            GibCursor jump_1272 = tmpcur_2529 + 8;

            *(GibPackedTag *) loc_873 = 1;

            GibCursor writetag_1767 = loc_873 + 1;
            GibCursor after_tag_1768 = loc_873 + 1;

            *(GibInt *) after_tag_1768 = tmpval_2534;

            GibCursor writecur_1772 = after_tag_1768 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_874,
                                                                        end_r_875,
                                                                        jump_1272,
                                                                        loc_873,
                                                                        writecur_1772};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_65 = *(uintptr_t *) tmpcur_2529;
            GibCursor tmpcur_2540 = GIB_UNTAG(tagged_tmpcur_65);
            GibCursor tmpaftercur_2541 = tmpcur_2529 + 8;
            uint16_t tmptag_2542 = GIB_GET_TAG(tagged_tmpcur_65);
            GibCursor end_from_tagged_absran_831 = tmpcur_2540 + tmptag_2542;
            GibInt tmpval_2543 = *(GibInt *) tmpaftercur_2541;
            GibCursor tmpcur_2544 = tmpaftercur_2541 + sizeof(GibInt);
            GibCursor loc_1135 = loc_873 + 17;

            *(GibPackedTag *) loc_873 = 3;

            GibCursor writetag_1780 = loc_873 + 1;

            gib_shadowstack_push(rstack, loc_873, end_r_875, Stk, SearchTree_T);
            gib_shadowstack_push(rstack, tmpcur_2540, end_r_874, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_62 =
                                                               _copy_SearchTree(end_r_874, end_r_875, loc_1135, tmpcur_2544);
            GibCursor pvrtmp_2545 = tmp_struct_62.field0;
            GibCursor pvrtmp_2546 = tmp_struct_62.field1;
            GibCursor pvrtmp_2547 = tmp_struct_62.field2;
            GibCursor pvrtmp_2548 = tmp_struct_62.field3;
            GibCursor pvrtmp_2549 = tmp_struct_62.field4;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_2540 = frame->ptr;
            end_r_874 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_873 = frame->ptr;
            end_r_875 = frame->endptr;
            gib_shadowstack_push(rstack, loc_873, pvrtmp_2546, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_63 =
                                                               _copy_SearchTree(end_from_tagged_absran_831, pvrtmp_2546, pvrtmp_2549, tmpcur_2540);
            GibCursor pvrtmp_2554 = tmp_struct_63.field0;
            GibCursor pvrtmp_2555 = tmp_struct_63.field1;
            GibCursor pvrtmp_2556 = tmp_struct_63.field2;
            GibCursor pvrtmp_2557 = tmp_struct_63.field3;
            GibCursor pvrtmp_2558 = tmp_struct_63.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_873 = frame->ptr;
            pvrtmp_2546 = frame->endptr;

            uint16_t offset_64 = pvrtmp_2546 - pvrtmp_2549;
            uintptr_t ran_834 = GIB_STORE_TAG(pvrtmp_2549, offset_64);
            GibCursor after_tag_1781 = loc_873 + 1;

            *(uintptr_t *) after_tag_1781 = ran_834;

            GibCursor writecur_1785 = after_tag_1781 + 8;

            *(GibInt *) writecur_1785 = tmpval_2543;

            GibCursor writecur_1786 = writecur_1785 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2554,
                                                                        pvrtmp_2555,
                                                                        pvrtmp_2556,
                                                                        loc_873,
                                                                        pvrtmp_2558};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_67 = *(uintptr_t *) tmpcur_2529;
            GibCursor tmpcur_2567 = GIB_UNTAG(tagged_tmpcur_67);
            GibCursor tmpaftercur_2568 = tmpcur_2529 + 8;
            uint16_t tmptag_2569 = GIB_GET_TAG(tagged_tmpcur_67);
            GibCursor end_from_tagged_indr_1346 = tmpcur_2567 + tmptag_2569;
            GibCursor jump_1348 = tmpcur_2529 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_66 =
                                                               _copy_SearchTree(end_from_tagged_indr_1346, end_r_875, loc_873, tmpcur_2567);
            GibCursor pvrtmp_2570 = tmp_struct_66.field0;
            GibCursor pvrtmp_2571 = tmp_struct_66.field1;
            GibCursor pvrtmp_2572 = tmp_struct_66.field2;
            GibCursor pvrtmp_2573 = tmp_struct_66.field3;
            GibCursor pvrtmp_2574 = tmp_struct_66.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_874,
                                                                        pvrtmp_2571,
                                                                        jump_1348,
                                                                        pvrtmp_2573,
                                                                        pvrtmp_2574};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_69 = *(uintptr_t *) tmpcur_2529;
            GibCursor tmpcur_2581 = GIB_UNTAG(tagged_tmpcur_69);
            GibCursor tmpaftercur_2582 = tmpcur_2529 + 8;
            uint16_t tmptag_2583 = GIB_GET_TAG(tagged_tmpcur_69);
            GibCursor end_from_tagged_indr_1346 = tmpcur_2581 + tmptag_2583;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_68 =
                                                               _copy_SearchTree(end_from_tagged_indr_1346, end_r_875, loc_873, tmpcur_2581);
            GibCursor pvrtmp_2584 = tmp_struct_68.field0;
            GibCursor pvrtmp_2585 = tmp_struct_68.field1;
            GibCursor pvrtmp_2586 = tmp_struct_68.field2;
            GibCursor pvrtmp_2587 = tmp_struct_68.field3;
            GibCursor pvrtmp_2588 = tmp_struct_68.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2584,
                                                                        pvrtmp_2585,
                                                                        pvrtmp_2586,
                                                                        pvrtmp_2587,
                                                                        pvrtmp_2588};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2528");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_SearchTree(GibCursor end_r_878,
                                                                                GibCursor end_r_879,
                                                                                GibCursor loc_877,
                                                                                GibCursor arg_194_280_453)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2596 = *(GibPackedTag *) arg_194_280_453;
    GibCursor tmpcur_2597 = arg_194_280_453 + 1;


  switch_2663:
    ;
    switch (tmpval_2596) {

      case 0:
        {
            GibCursor jump_1279 = arg_194_280_453 + 1;

            *(GibPackedTag *) loc_877 = 0;

            GibCursor writetag_1799 = loc_877 + 1;
            GibCursor after_tag_1800 = loc_877 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_878,
                                                                        end_r_879,
                                                                        jump_1279,
                                                                        loc_877,
                                                                        after_tag_1800};
            break;
        }

      case 1:
        {
            GibInt tmpval_2602 = *(GibInt *) tmpcur_2597;
            GibCursor tmpcur_2603 = tmpcur_2597 + sizeof(GibInt);
            GibCursor jump_1281 = tmpcur_2597 + 8;

            *(GibPackedTag *) loc_877 = 1;

            GibCursor writetag_1808 = loc_877 + 1;
            GibCursor after_tag_1809 = loc_877 + 1;

            *(GibInt *) after_tag_1809 = tmpval_2602;

            GibCursor writecur_1813 = after_tag_1809 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_878,
                                                                        end_r_879,
                                                                        jump_1281,
                                                                        loc_877,
                                                                        writecur_1813};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_75 = *(uintptr_t *) tmpcur_2597;
            GibCursor tmpcur_2608 = GIB_UNTAG(tagged_tmpcur_75);
            GibCursor tmpaftercur_2609 = tmpcur_2597 + 8;
            uint16_t tmptag_2610 = GIB_GET_TAG(tagged_tmpcur_75);
            GibCursor end_from_tagged_absran_836 = tmpcur_2608 + tmptag_2610;
            GibInt tmpval_2611 = *(GibInt *) tmpaftercur_2609;
            GibCursor tmpcur_2612 = tmpaftercur_2609 + sizeof(GibInt);
            GibCursor loc_1162 = loc_877 + 9;

            *(GibPackedTag *) loc_877 = 2;

            GibCursor writetag_1821 = loc_877 + 1;
            GibCursor after_tag_1822 = loc_877 + 1;

            *(GibInt *) after_tag_1822 = tmpval_2611;

            GibCursor writecur_1826 = after_tag_1822 + sizeof(GibInt);

            gib_shadowstack_push(rstack, loc_877, end_r_879, Stk, SearchTree_T);
            gib_shadowstack_push(rstack, tmpcur_2608, end_r_878, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_73 =
                                                               _copy_without_ptrs_SearchTree(end_r_878, end_r_879, loc_1162, tmpcur_2612);
            GibCursor pvrtmp_2613 = tmp_struct_73.field0;
            GibCursor pvrtmp_2614 = tmp_struct_73.field1;
            GibCursor pvrtmp_2615 = tmp_struct_73.field2;
            GibCursor pvrtmp_2616 = tmp_struct_73.field3;
            GibCursor pvrtmp_2617 = tmp_struct_73.field4;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_2608 = frame->ptr;
            end_r_878 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_877 = frame->ptr;
            end_r_879 = frame->endptr;
            gib_shadowstack_push(rstack, loc_877, pvrtmp_2614, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_74 =
                                                               _copy_without_ptrs_SearchTree(end_from_tagged_absran_836, pvrtmp_2614, pvrtmp_2617, tmpcur_2608);
            GibCursor pvrtmp_2622 = tmp_struct_74.field0;
            GibCursor pvrtmp_2623 = tmp_struct_74.field1;
            GibCursor pvrtmp_2624 = tmp_struct_74.field2;
            GibCursor pvrtmp_2625 = tmp_struct_74.field3;
            GibCursor pvrtmp_2626 = tmp_struct_74.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_877 = frame->ptr;
            pvrtmp_2614 = frame->endptr;
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2622,
                                                                        pvrtmp_2623,
                                                                        pvrtmp_2624,
                                                                        loc_877,
                                                                        pvrtmp_2626};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_77 = *(uintptr_t *) tmpcur_2597;
            GibCursor tmpcur_2635 = GIB_UNTAG(tagged_tmpcur_77);
            GibCursor tmpaftercur_2636 = tmpcur_2597 + 8;
            uint16_t tmptag_2637 = GIB_GET_TAG(tagged_tmpcur_77);
            GibCursor end_from_tagged_indr_1352 = tmpcur_2635 + tmptag_2637;
            GibCursor jump_1354 = tmpcur_2597 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_76 =
                                                               _copy_without_ptrs_SearchTree(end_from_tagged_indr_1352, end_r_879, loc_877, tmpcur_2635);
            GibCursor pvrtmp_2638 = tmp_struct_76.field0;
            GibCursor pvrtmp_2639 = tmp_struct_76.field1;
            GibCursor pvrtmp_2640 = tmp_struct_76.field2;
            GibCursor pvrtmp_2641 = tmp_struct_76.field3;
            GibCursor pvrtmp_2642 = tmp_struct_76.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_878,
                                                                        pvrtmp_2639,
                                                                        jump_1354,
                                                                        pvrtmp_2641,
                                                                        pvrtmp_2642};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_79 = *(uintptr_t *) tmpcur_2597;
            GibCursor tmpcur_2649 = GIB_UNTAG(tagged_tmpcur_79);
            GibCursor tmpaftercur_2650 = tmpcur_2597 + 8;
            uint16_t tmptag_2651 = GIB_GET_TAG(tagged_tmpcur_79);
            GibCursor end_from_tagged_indr_1352 = tmpcur_2649 + tmptag_2651;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_78 =
                                                               _copy_without_ptrs_SearchTree(end_from_tagged_indr_1352, end_r_879, loc_877, tmpcur_2649);
            GibCursor pvrtmp_2652 = tmp_struct_78.field0;
            GibCursor pvrtmp_2653 = tmp_struct_78.field1;
            GibCursor pvrtmp_2654 = tmp_struct_78.field2;
            GibCursor pvrtmp_2655 = tmp_struct_78.field3;
            GibCursor pvrtmp_2656 = tmp_struct_78.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2652,
                                                                        pvrtmp_2653,
                                                                        pvrtmp_2654,
                                                                        pvrtmp_2655,
                                                                        pvrtmp_2656};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2596");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_SearchTree(GibCursor end_r_881,
                                            GibCursor arg_203_289_462)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2664 = *(GibPackedTag *) arg_203_289_462;
    GibCursor tmpcur_2665 = arg_203_289_462 + 1;


  switch_2687:
    ;
    switch (tmpval_2664) {

      case 0:
        {
            GibCursor jump_1288 = arg_203_289_462 + 1;

            return (GibCursorGibCursorProd) {end_r_881, jump_1288};
            break;
        }

      case 1:
        {
            GibInt tmpval_2666 = *(GibInt *) tmpcur_2665;
            GibCursor tmpcur_2667 = tmpcur_2665 + sizeof(GibInt);
            GibCursor jump_1290 = tmpcur_2665 + 8;

            return (GibCursorGibCursorProd) {end_r_881, jump_1290};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_82 = *(uintptr_t *) tmpcur_2665;
            GibCursor tmpcur_2668 = GIB_UNTAG(tagged_tmpcur_82);
            GibCursor tmpaftercur_2669 = tmpcur_2665 + 8;
            uint16_t tmptag_2670 = GIB_GET_TAG(tagged_tmpcur_82);
            GibCursor end_from_tagged_absran_839 = tmpcur_2668 + tmptag_2670;
            GibInt tmpval_2671 = *(GibInt *) tmpaftercur_2669;
            GibCursor tmpcur_2672 = tmpaftercur_2669 + sizeof(GibInt);

            gib_shadowstack_push(rstack, tmpcur_2668, end_r_881, Stk,
                                 SearchTree_T);

            GibCursorGibCursorProd tmp_struct_80 =
                                    _traverse_SearchTree(end_r_881, tmpcur_2672);
            GibCursor pvrtmp_2673 = tmp_struct_80.field0;
            GibCursor pvrtmp_2674 = tmp_struct_80.field1;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_2668 = frame->ptr;
            end_r_881 = frame->endptr;

            GibCursorGibCursorProd tmp_struct_81 =
                                    _traverse_SearchTree(end_from_tagged_absran_839, tmpcur_2668);
            GibCursor pvrtmp_2675 = tmp_struct_81.field0;
            GibCursor pvrtmp_2676 = tmp_struct_81.field1;

            return (GibCursorGibCursorProd) {pvrtmp_2675, pvrtmp_2676};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_84 = *(uintptr_t *) tmpcur_2665;
            GibCursor tmpcur_2677 = GIB_UNTAG(tagged_tmpcur_84);
            GibCursor tmpaftercur_2678 = tmpcur_2665 + 8;
            uint16_t tmptag_2679 = GIB_GET_TAG(tagged_tmpcur_84);
            GibCursor end_from_tagged_indr_1358 = tmpcur_2677 + tmptag_2679;
            GibCursor jump_1360 = tmpcur_2665 + 8;
            GibCursorGibCursorProd tmp_struct_83 =
                                    _traverse_SearchTree(end_from_tagged_indr_1358, tmpcur_2677);
            GibCursor pvrtmp_2680 = tmp_struct_83.field0;
            GibCursor pvrtmp_2681 = tmp_struct_83.field1;

            return (GibCursorGibCursorProd) {end_r_881, jump_1360};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_86 = *(uintptr_t *) tmpcur_2665;
            GibCursor tmpcur_2682 = GIB_UNTAG(tagged_tmpcur_86);
            GibCursor tmpaftercur_2683 = tmpcur_2665 + 8;
            uint16_t tmptag_2684 = GIB_GET_TAG(tagged_tmpcur_86);
            GibCursor end_from_tagged_indr_1358 = tmpcur_2682 + tmptag_2684;
            GibCursorGibCursorProd tmp_struct_85 =
                                    _traverse_SearchTree(end_from_tagged_indr_1358, tmpcur_2682);
            GibCursor pvrtmp_2685 = tmp_struct_85.field0;
            GibCursor pvrtmp_2686 = tmp_struct_85.field1;

            return (GibCursorGibCursorProd) {pvrtmp_2685, pvrtmp_2686};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2664");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_SearchTree(GibCursor end_r_883,
                                         GibCursor arg_212_296_469)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2688 = *(GibPackedTag *) arg_212_296_469;
    GibCursor tmpcur_2689 = arg_212_296_469 + 1;


  switch_2711:
    ;
    switch (tmpval_2688) {

      case 0:
        {
            GibCursor jump_1297 = arg_212_296_469 + 1;
            unsigned char wildcard_213_297_470 = gib_print_symbol(2151);
            unsigned char wildcard_214_298_471 = gib_print_symbol(2150);

            return (GibCursorGibCursorProd) {end_r_883, jump_1297};
            break;
        }

      case 1:
        {
            GibInt tmpval_2690 = *(GibInt *) tmpcur_2689;
            GibCursor tmpcur_2691 = tmpcur_2689 + sizeof(GibInt);
            GibCursor jump_1299 = tmpcur_2689 + 8;
            unsigned char wildcard_217_300_473 = gib_print_symbol(2153);
            unsigned char y_216_301_474 = printf("%ld", tmpval_2690);
            unsigned char wildcard_218_302_475 = gib_print_symbol(2150);

            return (GibCursorGibCursorProd) {end_r_883, jump_1299};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_89 = *(uintptr_t *) tmpcur_2689;
            GibCursor tmpcur_2692 = GIB_UNTAG(tagged_tmpcur_89);
            GibCursor tmpaftercur_2693 = tmpcur_2689 + 8;
            uint16_t tmptag_2694 = GIB_GET_TAG(tagged_tmpcur_89);
            GibCursor end_from_tagged_absran_842 = tmpcur_2692 + tmptag_2694;
            GibInt tmpval_2695 = *(GibInt *) tmpaftercur_2693;
            GibCursor tmpcur_2696 = tmpaftercur_2693 + sizeof(GibInt);
            unsigned char wildcard_225_306_479 = gib_print_symbol(2152);
            unsigned char y_222_307_480 = printf("%ld", tmpval_2695);

            gib_shadowstack_push(rstack, tmpcur_2692, end_r_883, Stk,
                                 SearchTree_T);

            GibCursorGibCursorProd tmp_struct_87 =
                                    _print_SearchTree(end_r_883, tmpcur_2696);
            GibCursor pvrtmp_2697 = tmp_struct_87.field0;
            GibCursor pvrtmp_2698 = tmp_struct_87.field1;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_2692 = frame->ptr;
            end_r_883 = frame->endptr;

            GibCursorGibCursorProd tmp_struct_88 =
                                    _print_SearchTree(end_from_tagged_absran_842, tmpcur_2692);
            GibCursor pvrtmp_2699 = tmp_struct_88.field0;
            GibCursor pvrtmp_2700 = tmp_struct_88.field1;
            unsigned char wildcard_226_310_483 = gib_print_symbol(2150);

            return (GibCursorGibCursorProd) {pvrtmp_2699, pvrtmp_2700};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_91 = *(uintptr_t *) tmpcur_2689;
            GibCursor tmpcur_2701 = GIB_UNTAG(tagged_tmpcur_91);
            GibCursor tmpaftercur_2702 = tmpcur_2689 + 8;
            uint16_t tmptag_2703 = GIB_GET_TAG(tagged_tmpcur_91);
            GibCursor end_from_tagged_indr_1364 = tmpcur_2701 + tmptag_2703;
            GibCursor jump_1366 = tmpcur_2689 + 8;
            unsigned char wildcard_1369 = gib_print_symbol(2155);
            GibCursorGibCursorProd tmp_struct_90 =
                                    _print_SearchTree(end_from_tagged_indr_1364, tmpcur_2701);
            GibCursor pvrtmp_2704 = tmp_struct_90.field0;
            GibCursor pvrtmp_2705 = tmp_struct_90.field1;

            return (GibCursorGibCursorProd) {end_r_883, jump_1366};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_93 = *(uintptr_t *) tmpcur_2689;
            GibCursor tmpcur_2706 = GIB_UNTAG(tagged_tmpcur_93);
            GibCursor tmpaftercur_2707 = tmpcur_2689 + 8;
            uint16_t tmptag_2708 = GIB_GET_TAG(tagged_tmpcur_93);
            GibCursor end_from_tagged_indr_1364 = tmpcur_2706 + tmptag_2708;
            unsigned char wildcard_1369 = gib_print_symbol(2154);
            GibCursorGibCursorProd tmp_struct_92 =
                                    _print_SearchTree(end_from_tagged_indr_1364, tmpcur_2706);
            GibCursor pvrtmp_2709 = tmp_struct_92.field0;
            GibCursor pvrtmp_2710 = tmp_struct_92.field1;

            return (GibCursorGibCursorProd) {pvrtmp_2709, pvrtmp_2710};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2688");
            exit(1);
        }
    }
}
GibCursorGibIntProd caseFn_227(GibCursor end_r_885, GibInt n_84_228_311_484,
                               GibCursor l_85_229_312_485)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2712 = *(GibPackedTag *) l_85_229_312_485;
    GibCursor tmpcur_2713 = l_85_229_312_485 + 1;


  switch_2735:
    ;
    switch (tmpval_2712) {

      case 0:
        {
            return (GibCursorGibIntProd) {end_r_885, n_84_228_311_484};
            break;
        }

      case 1:
        {
            GibInt tmpval_2714 = *(GibInt *) tmpcur_2713;
            GibCursor tmpcur_2715 = tmpcur_2713 + sizeof(GibInt);
            GibCursorGibIntProd tmp_struct_94 =
                                 min_tree(end_r_885, l_85_229_312_485);
            GibCursor pvrtmp_2716 = tmp_struct_94.field0;
            GibInt pvrtmp_2717 = tmp_struct_94.field1;

            return (GibCursorGibIntProd) {pvrtmp_2716, pvrtmp_2717};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_96 = *(uintptr_t *) tmpcur_2713;
            GibCursor tmpcur_2718 = GIB_UNTAG(tagged_tmpcur_96);
            GibCursor tmpaftercur_2719 = tmpcur_2713 + 8;
            uint16_t tmptag_2720 = GIB_GET_TAG(tagged_tmpcur_96);
            GibCursor end_from_tagged_absran_845 = tmpcur_2718 + tmptag_2720;
            GibInt tmpval_2721 = *(GibInt *) tmpaftercur_2719;
            GibCursor tmpcur_2722 = tmpaftercur_2719 + sizeof(GibInt);
            GibCursorGibIntProd tmp_struct_95 =
                                 min_tree(end_r_885, l_85_229_312_485);
            GibCursor pvrtmp_2723 = tmp_struct_95.field0;
            GibInt pvrtmp_2724 = tmp_struct_95.field1;

            return (GibCursorGibIntProd) {pvrtmp_2723, pvrtmp_2724};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_98 = *(uintptr_t *) tmpcur_2713;
            GibCursor tmpcur_2725 = GIB_UNTAG(tagged_tmpcur_98);
            GibCursor tmpaftercur_2726 = tmpcur_2713 + 8;
            uint16_t tmptag_2727 = GIB_GET_TAG(tagged_tmpcur_98);
            GibCursor end_from_tagged_indr_1370 = tmpcur_2725 + tmptag_2727;
            GibCursor jump_1372 = tmpcur_2713 + 8;
            GibCursorGibIntProd tmp_struct_97 =
                                 caseFn_227(end_from_tagged_indr_1370, n_84_228_311_484, tmpcur_2725);
            GibCursor pvrtmp_2728 = tmp_struct_97.field0;
            GibInt pvrtmp_2729 = tmp_struct_97.field1;

            return (GibCursorGibIntProd) {end_r_885, pvrtmp_2729};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_100 = *(uintptr_t *) tmpcur_2713;
            GibCursor tmpcur_2730 = GIB_UNTAG(tagged_tmpcur_100);
            GibCursor tmpaftercur_2731 = tmpcur_2713 + 8;
            uint16_t tmptag_2732 = GIB_GET_TAG(tagged_tmpcur_100);
            GibCursor end_from_tagged_indr_1370 = tmpcur_2730 + tmptag_2732;
            GibCursorGibIntProd tmp_struct_99 =
                                 caseFn_227(end_from_tagged_indr_1370, n_84_228_311_484, tmpcur_2730);
            GibCursor pvrtmp_2733 = tmp_struct_99.field0;
            GibInt pvrtmp_2734 = tmp_struct_99.field1;

            return (GibCursorGibIntProd) {pvrtmp_2733, pvrtmp_2734};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2712");
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
    GibChunk region_2156 = gib_alloc_region(REGION_SIZE);
    GibCursor r_903 = region_2156.start;
    GibCursor end_r_903 = region_2156.end;
    GibChunk region_2157 = gib_alloc_region(REGION_SIZE);
    GibCursor r_902 = region_2157.start;
    GibCursor end_r_902 = region_2157.end;
    GibInt m_52_230_360 = gib_get_size_param();
    GibInt fltPrm_317_361 = gib_expll(2, TREE_HEIGHT);
    GibInt total_nodes_53_231_362 = fltPrm_317_361 - 1;
    GibCursor pvrtmp_2167;
    GibCursor pvrtmp_2168;
    GibCursor pvrtmp_2169;
    GibVector *times_105 = gib_vector_alloc(gib_get_iters_param(),
                                            sizeof(double));
    struct timespec begin_pvrtmp_2167;
    struct timespec end_pvrtmp_2167;

    clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_2167);
    {
        GibCursorGibCursorGibCursorProd tmp_struct_101 =
                                         helper(end_r_903, r_903, 0, total_nodes_53_231_362);
        GibCursor pvrtmp_2158 = tmp_struct_101.field0;
        GibCursor pvrtmp_2159 = tmp_struct_101.field1;
        GibCursor pvrtmp_2160 = tmp_struct_101.field2;

        pvrtmp_2167 = pvrtmp_2158;
        pvrtmp_2168 = pvrtmp_2159;
        pvrtmp_2169 = pvrtmp_2160;
    }
    clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_2167);

    double selftimed_104 = gib_difftimespecs(&begin_pvrtmp_2167,
                                             &end_pvrtmp_2167);

    gib_vector_free(times_105);
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("SELFTIMED: %e\n", gib_difftimespecs(&begin_pvrtmp_2167,
                                                &end_pvrtmp_2167));
    gib_shadowstack_push(rstack, r_903, end_r_903, Stk, SearchTree_T);

    GibCursorGibCursorGibIntProd tmp_struct_107 =
                                  countnodes(end_r_903, pvrtmp_2168);
    GibCursor pvrtmp_2177 = tmp_struct_107.field0;
    GibCursor pvrtmp_2178 = tmp_struct_107.field1;
    GibInt pvrtmp_2179 = tmp_struct_107.field2;

    frame = gib_shadowstack_pop(rstack);
    r_903 = frame->ptr;
    end_r_903 = frame->endptr;
    gib_shadowstack_push(rstack, r_903, end_r_903, Stk, SearchTree_T);
    frame = gib_shadowstack_pop(rstack);
    r_903 = frame->ptr;
    end_r_903 = frame->endptr;

    GibCursor pvrtmp_2190;
    GibCursor pvrtmp_2191;
    GibCursor pvrtmp_2192;
    GibVector *times_112 = gib_vector_alloc(gib_get_iters_param(),
                                            sizeof(double));
    struct timespec begin_pvrtmp_2190;
    struct timespec end_pvrtmp_2190;

    for (long long iters_pvrtmp_2190 = 0; iters_pvrtmp_2190 <
         gib_get_iters_param(); iters_pvrtmp_2190++) {
        if (iters_pvrtmp_2190 != gib_get_iters_param() - 1)
            gib_list_bumpalloc_save_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_2190);

        GibInt fltAppE_318_365 = gib_get_size_param();
        GibCursorGibCursorGibCursorGibCursorProd tmp_struct_108 =
                                                  loop(end_r_903, end_r_902, r_902, pvrtmp_2168, fltAppE_318_365);
        GibCursor pvrtmp_2180 = tmp_struct_108.field0;
        GibCursor pvrtmp_2181 = tmp_struct_108.field1;
        GibCursor pvrtmp_2182 = tmp_struct_108.field2;
        GibCursor pvrtmp_2183 = tmp_struct_108.field3;

        pvrtmp_2190 = pvrtmp_2181;
        pvrtmp_2191 = pvrtmp_2182;
        pvrtmp_2192 = pvrtmp_2183;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_2190);
        if (iters_pvrtmp_2190 != gib_get_iters_param() - 1)
            gib_list_bumpalloc_restore_state();

        double itertime_109 = gib_difftimespecs(&begin_pvrtmp_2190,
                                                &end_pvrtmp_2190);

        printf("itertime: %lf\n", itertime_109);
        gib_vector_inplace_update(times_112, iters_pvrtmp_2190, &itertime_109);
    }
    gib_vector_inplace_sort(times_112, gib_compare_doubles);

    double *tmp_113 = (double *) gib_vector_nth(times_112,
                                                gib_get_iters_param() / 2);
    double selftimed_111 = *tmp_113;
    double batchtime_110 = gib_sum_timing_array(times_112);

    gib_print_timing_array(times_112);
    gib_vector_free(times_112);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_110);
    printf("SELFTIMED: %e\n", selftimed_111);
    gib_shadowstack_push(rstack, r_902, end_r_902, Stk, SearchTree_T);

    GibCursorGibCursorProd tmp_struct_114 =
                            _print_SearchTree(end_r_902, pvrtmp_2191);
    GibCursor pvrtmp_2200 = tmp_struct_114.field0;
    GibCursor pvrtmp_2201 = tmp_struct_114.field1;

    frame = gib_shadowstack_pop(rstack);
    r_902 = frame->ptr;
    end_r_902 = frame->endptr;

    GibCursorGibCursorGibIntProd tmp_struct_115 =
                                  sum_tree(end_r_902, pvrtmp_2191);
    GibCursor pvrtmp_2202 = tmp_struct_115.field0;
    GibCursor pvrtmp_2203 = tmp_struct_115.field1;
    GibInt pvrtmp_2204 = tmp_struct_115.field2;

    printf("%ld", pvrtmp_2204);
    printf("\n");
    return 0;
}
