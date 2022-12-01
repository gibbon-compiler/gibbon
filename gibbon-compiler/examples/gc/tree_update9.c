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
GibCursorGibCursorGibCursorProd helper(GibCursor end_r_832, GibCursor loc_831,
                                       GibInt s_58_225_356,
                                       GibInt e_59_226_357);
GibCursorGibCursorGibCursorGibCursorProd loop(GibCursor end_r_835,
                                              GibCursor end_r_836,
                                              GibCursor loc_834,
                                              GibCursor tr_61_228_367,
                                              GibInt n_62_229_368);
GibCursorGibCursorGibIntProd countnodes(GibCursor end_r_838,
                                        GibCursor tr_64_231_379);
GibCursorGibCursorGibCursorGibCursorProd tree_delete(GibCursor end_r_841,
                                                     GibCursor end_r_842,
                                                     GibCursor loc_840,
                                                     GibCursor tr_69_236_387,
                                                     GibInt n_70_237_388);
GibCursorGibIntProd min_tree(GibCursor end_r_844, GibCursor tr_76_243_403);
GibCursorGibCursorGibCursorGibCursorProd tree_insert(GibCursor end_r_847,
                                                     GibCursor end_r_848,
                                                     GibCursor loc_846,
                                                     GibCursor tr_85_248_408,
                                                     GibInt n_86_249_409);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_SearchTree(GibCursor end_r_851, GibCursor end_r_852, GibCursor loc_850,
                 GibCursor arg_176_259_428);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_SearchTree(GibCursor end_r_855, GibCursor end_r_856,
                              GibCursor loc_854, GibCursor arg_185_268_437);
GibCursorGibCursorProd _traverse_SearchTree(GibCursor end_r_858,
                                            GibCursor arg_194_277_446);
GibCursorGibCursorProd _print_SearchTree(GibCursor end_r_860,
                                         GibCursor arg_203_284_453);
GibCursorGibIntProd caseFn_218(GibCursor end_r_862, GibCursor l_79_219_299_468,
                               GibInt n_78_220_300_469);
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
    gib_add_symbol(2180, ")");
    gib_add_symbol(2181, "(Null ");
    gib_add_symbol(2182, "(Node ");
    gib_add_symbol(2183, "(Leaf ");
    gib_add_symbol(2184, " ->r ");
    gib_add_symbol(2185, " ->i ");
}
GibCursorGibCursorGibCursorProd helper(GibCursor end_r_832, GibCursor loc_831,
                                       GibInt s_58_225_356, GibInt e_59_226_357)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_831 + 26 > end_r_832) {
        gib_grow_region(&loc_831, &end_r_832);
    }

    GibBool fltIf_307_358 = e_59_226_357 < s_58_225_356;

    if (fltIf_307_358) {
        *(GibPackedTag *) loc_831 = 0;

        GibCursor writetag_1439 = loc_831 + 1;
        GibCursor after_tag_1440 = loc_831 + 1;

        return (GibCursorGibCursorGibCursorProd) {end_r_832, loc_831,
                                                  after_tag_1440};
    } else {
        GibBool fltIf_308_359 = s_58_225_356 == e_59_226_357;

        if (fltIf_308_359) {
            *(GibPackedTag *) loc_831 = 1;

            GibCursor writetag_1446 = loc_831 + 1;
            GibCursor after_tag_1447 = loc_831 + 1;

            *(GibInt *) after_tag_1447 = s_58_225_356;

            GibCursor writecur_1451 = after_tag_1447 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorProd) {end_r_832, loc_831,
                                                      writecur_1451};
        } else {
            GibInt fltPrm_310_360 = e_59_226_357 - s_58_225_356;
            GibInt fltPrm_309_361 = fltPrm_310_360 / 2;
            GibInt m_60_227_362 = fltPrm_309_361 + s_58_225_356;
            GibInt fltAppE_312_363 = m_60_227_362 - 1;
            GibCursor loc_885 = loc_831 + 17;

            *(GibPackedTag *) loc_831 = 3;

            GibCursor writetag_1458 = loc_831 + 1;

            gib_shadowstack_push(rstack, loc_831, end_r_832, Stk, SearchTree_T);

            GibCursorGibCursorGibCursorProd tmp_struct_0 =
                                             helper(end_r_832, loc_885, s_58_225_356, fltAppE_312_363);
            GibCursor pvrtmp_2238 = tmp_struct_0.field0;
            GibCursor pvrtmp_2239 = tmp_struct_0.field1;
            GibCursor pvrtmp_2240 = tmp_struct_0.field2;

            frame = gib_shadowstack_pop(rstack);
            loc_831 = frame->ptr;
            end_r_832 = frame->endptr;

            GibInt fltAppE_314_365 = m_60_227_362 + 1;

            gib_shadowstack_push(rstack, loc_831, pvrtmp_2238, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibCursorProd tmp_struct_1 =
                                             helper(pvrtmp_2238, pvrtmp_2240, fltAppE_314_365, e_59_226_357);
            GibCursor pvrtmp_2245 = tmp_struct_1.field0;
            GibCursor pvrtmp_2246 = tmp_struct_1.field1;
            GibCursor pvrtmp_2247 = tmp_struct_1.field2;

            frame = gib_shadowstack_pop(rstack);
            loc_831 = frame->ptr;
            pvrtmp_2238 = frame->endptr;

            uint16_t offset_2 = pvrtmp_2238 - pvrtmp_2240;
            uintptr_t ran_776 = GIB_STORE_TAG(pvrtmp_2240, offset_2);
            GibCursor after_tag_1459 = loc_831 + 1;

            *(uintptr_t *) after_tag_1459 = ran_776;

            GibCursor writecur_1463 = after_tag_1459 + 8;

            *(GibInt *) writecur_1463 = m_60_227_362;

            GibCursor writecur_1464 = writecur_1463 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorProd) {pvrtmp_2245, loc_831,
                                                      pvrtmp_2247};
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd loop(GibCursor end_r_835,
                                              GibCursor end_r_836,
                                              GibCursor loc_834,
                                              GibCursor tr_61_228_367,
                                              GibInt n_62_229_368)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_834 + 26 > end_r_836) {
        gib_grow_region(&loc_834, &end_r_836);
    }

    GibBool fltIf_315_369 = n_62_229_368 == 0;

    if (fltIf_315_369) {
        if (loc_834 + 18 > end_r_836) {
            gib_grow_region(&loc_834, &end_r_836);
        }
        gib_indirection_barrier(loc_834, end_r_836, tr_61_228_367, end_r_835,
                                SearchTree_T);

        GibCursor end_1471 = loc_834 + 9;

        return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_835, end_r_836,
                                                           loc_834, end_1471};
    } else {
        GibInt fltPrm_316_370 = rand();
        GibInt j_63_230_371 = fltPrm_316_370 % 20;
        GibInt fltPrm_318_372 = j_63_230_371 % 2;
        GibBool fltIf_317_373 = 0 == fltPrm_318_372;

        printf("%ld\n", j_63_230_371);

        if (fltIf_317_373) {
            gib_shadowstack_push(rstack, tr_61_228_367, end_r_835, Stk,
                                 SearchTree_T);
            gib_shadowstack_push(wstack, loc_834, end_r_836, Stk, SearchTree_T);

            GibChunk region_2260 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_902 = region_2260.start;
            GibCursor end_r_902 = region_2260.end;

            frame = gib_shadowstack_pop(wstack);
            loc_834 = frame->ptr;
            end_r_836 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tr_61_228_367 = frame->ptr;
            end_r_835 = frame->endptr;
            gib_shadowstack_push(wstack, loc_834, end_r_836, Stk, SearchTree_T);

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_9 =
                                                      tree_insert(end_r_835, end_r_902, r_902, tr_61_228_367, j_63_230_371);
            GibCursor pvrtmp_2261 = tmp_struct_9.field0;
            GibCursor pvrtmp_2262 = tmp_struct_9.field1;
            GibCursor pvrtmp_2263 = tmp_struct_9.field2;
            GibCursor pvrtmp_2264 = tmp_struct_9.field3;

            frame = gib_shadowstack_pop(wstack);
            loc_834 = frame->ptr;
            end_r_836 = frame->endptr;

            GibInt fltAppE_320_375 = n_62_229_368 - 1;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_10 =
                                                      loop(pvrtmp_2262, end_r_836, loc_834, pvrtmp_2263, fltAppE_320_375);
            GibCursor pvrtmp_2269 = tmp_struct_10.field0;
            GibCursor pvrtmp_2270 = tmp_struct_10.field1;
            GibCursor pvrtmp_2271 = tmp_struct_10.field2;
            GibCursor pvrtmp_2272 = tmp_struct_10.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2261,
                                                               pvrtmp_2270,
                                                               pvrtmp_2271,
                                                               pvrtmp_2272};
        } else {
            GibInt fltAppE_322_376 = j_63_230_371 - 1;

            gib_shadowstack_push(rstack, tr_61_228_367, end_r_835, Stk,
                                 SearchTree_T);
            gib_shadowstack_push(wstack, loc_834, end_r_836, Stk, SearchTree_T);

            GibChunk region_2279 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_911 = region_2279.start;
            GibCursor end_r_911 = region_2279.end;

            frame = gib_shadowstack_pop(wstack);
            loc_834 = frame->ptr;
            end_r_836 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tr_61_228_367 = frame->ptr;
            end_r_835 = frame->endptr;
            gib_shadowstack_push(wstack, loc_834, end_r_836, Stk, SearchTree_T);

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_11 =
                                                      tree_delete(end_r_835, end_r_911, r_911, tr_61_228_367, fltAppE_322_376);
            GibCursor pvrtmp_2280 = tmp_struct_11.field0;
            GibCursor pvrtmp_2281 = tmp_struct_11.field1;
            GibCursor pvrtmp_2282 = tmp_struct_11.field2;
            GibCursor pvrtmp_2283 = tmp_struct_11.field3;

            frame = gib_shadowstack_pop(wstack);
            loc_834 = frame->ptr;
            end_r_836 = frame->endptr;

            GibInt fltAppE_323_378 = n_62_229_368 - 1;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_12 =
                                                      loop(pvrtmp_2281, end_r_836, loc_834, pvrtmp_2282, fltAppE_323_378);
            GibCursor pvrtmp_2288 = tmp_struct_12.field0;
            GibCursor pvrtmp_2289 = tmp_struct_12.field1;
            GibCursor pvrtmp_2290 = tmp_struct_12.field2;
            GibCursor pvrtmp_2291 = tmp_struct_12.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2280,
                                                               pvrtmp_2289,
                                                               pvrtmp_2290,
                                                               pvrtmp_2291};
        }
    }
}
GibCursorGibCursorGibIntProd countnodes(GibCursor end_r_838,
                                        GibCursor tr_64_231_379)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2298 = *(GibPackedTag *) tr_64_231_379;
    GibCursor tmpcur_2299 = tr_64_231_379 + 1;


  switch_2325:
    ;
    switch (tmpval_2298) {

      case 0:
        {
            GibCursor jump_1209 = tr_64_231_379 + 1;

            return (GibCursorGibCursorGibIntProd) {end_r_838, jump_1209, 0};
            break;
        }

      case 1:
        {
            GibInt tmpval_2300 = *(GibInt *) tmpcur_2299;
            GibCursor tmpcur_2301 = tmpcur_2299 + sizeof(GibInt);
            GibCursor jump_1210 = tmpcur_2299 + 8;

            return (GibCursorGibCursorGibIntProd) {end_r_838, jump_1210, 1};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_18 = *(uintptr_t *) tmpcur_2299;
            GibCursor tmpcur_2302 = GIB_UNTAG(tagged_tmpcur_18);
            GibCursor tmpaftercur_2303 = tmpcur_2299 + 8;
            uint16_t tmptag_2304 = GIB_GET_TAG(tagged_tmpcur_18);
            GibCursor end_from_tagged_absran_777 = tmpcur_2302 + tmptag_2304;
            GibInt tmpval_2305 = *(GibInt *) tmpaftercur_2303;
            GibCursor tmpcur_2306 = tmpaftercur_2303 + sizeof(GibInt);

            gib_shadowstack_push(rstack, tmpcur_2302, end_r_838, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibIntProd tmp_struct_16 =
                                          countnodes(end_r_838, tmpcur_2306);
            GibCursor pvrtmp_2307 = tmp_struct_16.field0;
            GibCursor pvrtmp_2308 = tmp_struct_16.field1;
            GibInt pvrtmp_2309 = tmp_struct_16.field2;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_2302 = frame->ptr;
            end_r_838 = frame->endptr;

            GibCursorGibCursorGibIntProd tmp_struct_17 =
                                          countnodes(end_from_tagged_absran_777, tmpcur_2302);
            GibCursor pvrtmp_2310 = tmp_struct_17.field0;
            GibCursor pvrtmp_2311 = tmp_struct_17.field1;
            GibInt pvrtmp_2312 = tmp_struct_17.field2;
            GibInt fltPrm_324_386 = pvrtmp_2309 + pvrtmp_2312;
            GibInt tailprim_1215 = 1 + fltPrm_324_386;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_2310, pvrtmp_2311,
                                                   tailprim_1215};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_20 = *(uintptr_t *) tmpcur_2299;
            GibCursor tmpcur_2313 = GIB_UNTAG(tagged_tmpcur_20);
            GibCursor tmpaftercur_2314 = tmpcur_2299 + 8;
            uint16_t tmptag_2315 = GIB_GET_TAG(tagged_tmpcur_20);
            GibCursor end_from_tagged_indr_1289 = tmpcur_2313 + tmptag_2315;
            GibCursor jump_1291 = tmpcur_2299 + 8;
            GibCursorGibCursorGibIntProd tmp_struct_19 =
                                          countnodes(end_from_tagged_indr_1289, tmpcur_2313);
            GibCursor pvrtmp_2316 = tmp_struct_19.field0;
            GibCursor pvrtmp_2317 = tmp_struct_19.field1;
            GibInt pvrtmp_2318 = tmp_struct_19.field2;

            return (GibCursorGibCursorGibIntProd) {end_r_838, jump_1291,
                                                   pvrtmp_2318};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_22 = *(uintptr_t *) tmpcur_2299;
            GibCursor tmpcur_2319 = GIB_UNTAG(tagged_tmpcur_22);
            GibCursor tmpaftercur_2320 = tmpcur_2299 + 8;
            uint16_t tmptag_2321 = GIB_GET_TAG(tagged_tmpcur_22);
            GibCursor end_from_tagged_indr_1289 = tmpcur_2319 + tmptag_2321;
            GibCursorGibCursorGibIntProd tmp_struct_21 =
                                          countnodes(end_from_tagged_indr_1289, tmpcur_2319);
            GibCursor pvrtmp_2322 = tmp_struct_21.field0;
            GibCursor pvrtmp_2323 = tmp_struct_21.field1;
            GibInt pvrtmp_2324 = tmp_struct_21.field2;

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
GibCursorGibCursorGibCursorGibCursorProd tree_delete(GibCursor end_r_841,
                                                     GibCursor end_r_842,
                                                     GibCursor loc_840,
                                                     GibCursor tr_69_236_387,
                                                     GibInt n_70_237_388)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_840 + 26 > end_r_842) {
        gib_grow_region(&loc_840, &end_r_842);
    }

    GibPackedTag tmpval_2326 = *(GibPackedTag *) tr_69_236_387;
    GibCursor tmpcur_2327 = tr_69_236_387 + 1;


  switch_2417:
    ;
    switch (tmpval_2326) {

      case 0:
        {
            *(GibPackedTag *) loc_840 = 0;

            GibCursor writetag_1504 = loc_840 + 1;
            GibCursor after_tag_1505 = loc_840 + 1;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_841,
                                                               end_r_842,
                                                               loc_840,
                                                               after_tag_1505};
            break;
        }

      case 1:
        {
            GibInt tmpval_2332 = *(GibInt *) tmpcur_2327;
            GibCursor tmpcur_2333 = tmpcur_2327 + sizeof(GibInt);
            GibBool fltIf_327_390 = tmpval_2332 == n_70_237_388;

            if (fltIf_327_390) {
                *(GibPackedTag *) loc_840 = 0;

                GibCursor writetag_1513 = loc_840 + 1;
                GibCursor after_tag_1514 = loc_840 + 1;

                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_841,
                                                                   end_r_842,
                                                                   loc_840,
                                                                   after_tag_1514};
            } else {
                *(GibPackedTag *) loc_840 = 1;

                GibCursor writetag_1520 = loc_840 + 1;
                GibCursor after_tag_1521 = loc_840 + 1;

                *(GibInt *) after_tag_1521 = tmpval_2332;

                GibCursor writecur_1525 = after_tag_1521 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_841,
                                                                   end_r_842,
                                                                   loc_840,
                                                                   writecur_1525};
            }
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_39 = *(uintptr_t *) tmpcur_2327;
            GibCursor tmpcur_2342 = GIB_UNTAG(tagged_tmpcur_39);
            GibCursor tmpaftercur_2343 = tmpcur_2327 + 8;
            uint16_t tmptag_2344 = GIB_GET_TAG(tagged_tmpcur_39);
            GibCursor end_from_tagged_absran_783 = tmpcur_2342 + tmptag_2344;
            GibInt tmpval_2345 = *(GibInt *) tmpaftercur_2343;
            GibCursor tmpcur_2346 = tmpaftercur_2343 + sizeof(GibInt);
            GibBool fltIf_328_394 = tmpval_2345 == n_70_237_388;

            if (fltIf_328_394) {
                gib_shadowstack_push(rstack, tmpcur_2342, end_r_841, Stk,
                                     SearchTree_T);
                gib_shadowstack_push(rstack, tmpcur_2346, end_r_841, Stk,
                                     SearchTree_T);
                gib_shadowstack_push(wstack, loc_840, end_r_842, Stk,
                                     SearchTree_T);

                GibCursorGibIntProd tmp_struct_23 =
                                     min_tree(end_from_tagged_absran_783, tmpcur_2342);
                GibCursor pvrtmp_2347 = tmp_struct_23.field0;
                GibInt pvrtmp_2348 = tmp_struct_23.field1;

                frame = gib_shadowstack_pop(wstack);
                loc_840 = frame->ptr;
                end_r_842 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                tmpcur_2346 = frame->ptr;
                end_r_841 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                tmpcur_2342 = frame->ptr;
                end_r_841 = frame->endptr;

                GibCursor loc_945 = loc_840 + 17;

                *(GibPackedTag *) loc_840 = 3;

                GibCursor writetag_1539 = loc_840 + 1;

                if (loc_945 + 18 > end_r_842) {
                    gib_grow_region(&loc_945, &end_r_842);
                }
                gib_indirection_barrier(loc_945, end_r_842, tmpcur_2346,
                                        end_r_841, SearchTree_T);

                GibCursor end_1534 = loc_945 + 9;

                gib_shadowstack_push(rstack, loc_840, end_r_842, Stk,
                                     SearchTree_T);

                GibCursorGibCursorGibCursorGibCursorProd tmp_struct_24 =
                                                          tree_delete(end_from_tagged_absran_783, end_r_842, end_1534, tmpcur_2342, pvrtmp_2348);
                GibCursor pvrtmp_2351 = tmp_struct_24.field0;
                GibCursor pvrtmp_2352 = tmp_struct_24.field1;
                GibCursor pvrtmp_2353 = tmp_struct_24.field2;
                GibCursor pvrtmp_2354 = tmp_struct_24.field3;

                frame = gib_shadowstack_pop(rstack);
                loc_840 = frame->ptr;
                end_r_842 = frame->endptr;

                uint16_t offset_25 = end_r_842 - end_1534;
                uintptr_t ran_786 = GIB_STORE_TAG(end_1534, offset_25);
                GibCursor after_tag_1540 = loc_840 + 1;

                *(uintptr_t *) after_tag_1540 = ran_786;

                GibCursor writecur_1544 = after_tag_1540 + 8;

                *(GibInt *) writecur_1544 = pvrtmp_2348;

                GibCursor writecur_1545 = writecur_1544 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2351,
                                                                   pvrtmp_2352,
                                                                   loc_840,
                                                                   pvrtmp_2354};
            } else {
                GibBool fltIf_331_398 = tmpval_2345 < n_70_237_388;

                if (fltIf_331_398) {
                    GibCursor loc_961 = loc_840 + 17;

                    *(GibPackedTag *) loc_840 = 3;

                    GibCursor writetag_1557 = loc_840 + 1;

                    if (loc_961 + 18 > end_r_842) {
                        gib_grow_region(&loc_961, &end_r_842);
                    }
                    gib_indirection_barrier(loc_961, end_r_842, tmpcur_2346,
                                            end_r_841, SearchTree_T);

                    GibCursor end_1552 = loc_961 + 9;

                    gib_shadowstack_push(rstack, loc_840, end_r_842, Stk,
                                         SearchTree_T);

                    GibCursorGibCursorGibCursorGibCursorProd tmp_struct_29 =
                                                              tree_delete(end_from_tagged_absran_783, end_r_842, end_1552, tmpcur_2342, n_70_237_388);
                    GibCursor pvrtmp_2365 = tmp_struct_29.field0;
                    GibCursor pvrtmp_2366 = tmp_struct_29.field1;
                    GibCursor pvrtmp_2367 = tmp_struct_29.field2;
                    GibCursor pvrtmp_2368 = tmp_struct_29.field3;

                    frame = gib_shadowstack_pop(rstack);
                    loc_840 = frame->ptr;
                    end_r_842 = frame->endptr;

                    uint16_t offset_30 = end_r_842 - end_1552;
                    uintptr_t ran_787 = GIB_STORE_TAG(end_1552, offset_30);
                    GibCursor after_tag_1558 = loc_840 + 1;

                    *(uintptr_t *) after_tag_1558 = ran_787;

                    GibCursor writecur_1562 = after_tag_1558 + 8;

                    *(GibInt *) writecur_1562 = tmpval_2345;

                    GibCursor writecur_1563 = writecur_1562 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2365,
                                                                       pvrtmp_2366,
                                                                       loc_840,
                                                                       pvrtmp_2368};
                } else {
                    GibCursor loc_977 = loc_840 + 17;

                    *(GibPackedTag *) loc_840 = 3;

                    GibCursor writetag_1575 = loc_840 + 1;

                    gib_shadowstack_push(rstack, loc_840, end_r_842, Stk,
                                         SearchTree_T);
                    gib_shadowstack_push(rstack, tmpcur_2342, end_r_841, Stk,
                                         SearchTree_T);

                    GibCursorGibCursorGibCursorGibCursorProd tmp_struct_34 =
                                                              tree_delete(end_r_841, end_r_842, loc_977, tmpcur_2346, n_70_237_388);
                    GibCursor pvrtmp_2377 = tmp_struct_34.field0;
                    GibCursor pvrtmp_2378 = tmp_struct_34.field1;
                    GibCursor pvrtmp_2379 = tmp_struct_34.field2;
                    GibCursor pvrtmp_2380 = tmp_struct_34.field3;

                    frame = gib_shadowstack_pop(rstack);
                    tmpcur_2342 = frame->ptr;
                    end_r_841 = frame->endptr;
                    frame = gib_shadowstack_pop(rstack);
                    loc_840 = frame->ptr;
                    end_r_842 = frame->endptr;
                    if (pvrtmp_2380 + 18 > pvrtmp_2378) {
                        gib_grow_region(&pvrtmp_2380, &pvrtmp_2378);
                    }
                    gib_indirection_barrier(pvrtmp_2380, pvrtmp_2378,
                                            tmpcur_2342,
                                            end_from_tagged_absran_783,
                                            SearchTree_T);

                    GibCursor end_1573 = pvrtmp_2380 + 9;
                    uint16_t offset_35 = pvrtmp_2378 - pvrtmp_2380;
                    uintptr_t ran_788 = GIB_STORE_TAG(pvrtmp_2380, offset_35);
                    GibCursor after_tag_1576 = loc_840 + 1;

                    *(uintptr_t *) after_tag_1576 = ran_788;

                    GibCursor writecur_1580 = after_tag_1576 + 8;

                    *(GibInt *) writecur_1580 = tmpval_2345;

                    GibCursor writecur_1581 = writecur_1580 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2377,
                                                                       pvrtmp_2378,
                                                                       loc_840,
                                                                       end_1573};
                }
            }
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_41 = *(uintptr_t *) tmpcur_2327;
            GibCursor tmpcur_2391 = GIB_UNTAG(tagged_tmpcur_41);
            GibCursor tmpaftercur_2392 = tmpcur_2327 + 8;
            uint16_t tmptag_2393 = GIB_GET_TAG(tagged_tmpcur_41);
            GibCursor end_from_tagged_indr_1295 = tmpcur_2391 + tmptag_2393;
            GibCursor jump_1297 = tmpcur_2327 + 8;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_40 =
                                                      tree_delete(end_from_tagged_indr_1295, end_r_842, loc_840, tmpcur_2391, n_70_237_388);
            GibCursor pvrtmp_2394 = tmp_struct_40.field0;
            GibCursor pvrtmp_2395 = tmp_struct_40.field1;
            GibCursor pvrtmp_2396 = tmp_struct_40.field2;
            GibCursor pvrtmp_2397 = tmp_struct_40.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_841,
                                                               pvrtmp_2395,
                                                               pvrtmp_2396,
                                                               pvrtmp_2397};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_43 = *(uintptr_t *) tmpcur_2327;
            GibCursor tmpcur_2404 = GIB_UNTAG(tagged_tmpcur_43);
            GibCursor tmpaftercur_2405 = tmpcur_2327 + 8;
            uint16_t tmptag_2406 = GIB_GET_TAG(tagged_tmpcur_43);
            GibCursor end_from_tagged_indr_1295 = tmpcur_2404 + tmptag_2406;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_42 =
                                                      tree_delete(end_from_tagged_indr_1295, end_r_842, loc_840, tmpcur_2404, n_70_237_388);
            GibCursor pvrtmp_2407 = tmp_struct_42.field0;
            GibCursor pvrtmp_2408 = tmp_struct_42.field1;
            GibCursor pvrtmp_2409 = tmp_struct_42.field2;
            GibCursor pvrtmp_2410 = tmp_struct_42.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2407,
                                                               pvrtmp_2408,
                                                               pvrtmp_2409,
                                                               pvrtmp_2410};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2326");
            exit(1);
        }
    }
}
GibCursorGibIntProd min_tree(GibCursor end_r_844, GibCursor tr_76_243_403)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2418 = *(GibPackedTag *) tr_76_243_403;
    GibCursor tmpcur_2419 = tr_76_243_403 + 1;


  switch_2439:
    ;
    switch (tmpval_2418) {

      case 0:
        {
            return (GibCursorGibIntProd) {end_r_844, 0};
            break;
        }

      case 1:
        {
            GibInt tmpval_2420 = *(GibInt *) tmpcur_2419;
            GibCursor tmpcur_2421 = tmpcur_2419 + sizeof(GibInt);

            return (GibCursorGibIntProd) {end_r_844, tmpval_2420};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_48 = *(uintptr_t *) tmpcur_2419;
            GibCursor tmpcur_2422 = GIB_UNTAG(tagged_tmpcur_48);
            GibCursor tmpaftercur_2423 = tmpcur_2419 + 8;
            uint16_t tmptag_2424 = GIB_GET_TAG(tagged_tmpcur_48);
            GibCursor end_from_tagged_absran_792 = tmpcur_2422 + tmptag_2424;
            GibInt tmpval_2425 = *(GibInt *) tmpaftercur_2423;
            GibCursor tmpcur_2426 = tmpaftercur_2423 + sizeof(GibInt);
            GibCursorGibIntProd tmp_struct_47 =
                                 caseFn_218(end_r_844, tmpcur_2426, tmpval_2425);
            GibCursor pvrtmp_2427 = tmp_struct_47.field0;
            GibInt pvrtmp_2428 = tmp_struct_47.field1;

            return (GibCursorGibIntProd) {pvrtmp_2427, pvrtmp_2428};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_50 = *(uintptr_t *) tmpcur_2419;
            GibCursor tmpcur_2429 = GIB_UNTAG(tagged_tmpcur_50);
            GibCursor tmpaftercur_2430 = tmpcur_2419 + 8;
            uint16_t tmptag_2431 = GIB_GET_TAG(tagged_tmpcur_50);
            GibCursor end_from_tagged_indr_1300 = tmpcur_2429 + tmptag_2431;
            GibCursor jump_1302 = tmpcur_2419 + 8;
            GibCursorGibIntProd tmp_struct_49 =
                                 min_tree(end_from_tagged_indr_1300, tmpcur_2429);
            GibCursor pvrtmp_2432 = tmp_struct_49.field0;
            GibInt pvrtmp_2433 = tmp_struct_49.field1;

            return (GibCursorGibIntProd) {end_r_844, pvrtmp_2433};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_52 = *(uintptr_t *) tmpcur_2419;
            GibCursor tmpcur_2434 = GIB_UNTAG(tagged_tmpcur_52);
            GibCursor tmpaftercur_2435 = tmpcur_2419 + 8;
            uint16_t tmptag_2436 = GIB_GET_TAG(tagged_tmpcur_52);
            GibCursor end_from_tagged_indr_1300 = tmpcur_2434 + tmptag_2436;
            GibCursorGibIntProd tmp_struct_51 =
                                 min_tree(end_from_tagged_indr_1300, tmpcur_2434);
            GibCursor pvrtmp_2437 = tmp_struct_51.field0;
            GibInt pvrtmp_2438 = tmp_struct_51.field1;

            return (GibCursorGibIntProd) {pvrtmp_2437, pvrtmp_2438};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2418");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd tree_insert(GibCursor end_r_847,
                                                     GibCursor end_r_848,
                                                     GibCursor loc_846,
                                                     GibCursor tr_85_248_408,
                                                     GibInt n_86_249_409)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_846 + 26 > end_r_848) {
        gib_grow_region(&loc_846, &end_r_848);
    }

    GibPackedTag tmpval_2440 = *(GibPackedTag *) tr_85_248_408;
    GibCursor tmpcur_2441 = tr_85_248_408 + 1;


  switch_2535:
    ;
    switch (tmpval_2440) {

      case 0:
        {
            *(GibPackedTag *) loc_846 = 1;

            GibCursor writetag_1614 = loc_846 + 1;
            GibCursor after_tag_1615 = loc_846 + 1;

            *(GibInt *) after_tag_1615 = n_86_249_409;

            GibCursor writecur_1619 = after_tag_1615 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_847,
                                                               end_r_848,
                                                               loc_846,
                                                               writecur_1619};
            break;
        }

      case 1:
        {
            GibInt tmpval_2446 = *(GibInt *) tmpcur_2441;
            GibCursor tmpcur_2447 = tmpcur_2441 + sizeof(GibInt);
            GibBool fltIf_336_411 = n_86_249_409 == tmpval_2446;

            if (fltIf_336_411) {
                *(GibPackedTag *) loc_846 = 1;

                GibCursor writetag_1624 = loc_846 + 1;
                GibCursor after_tag_1625 = loc_846 + 1;

                *(GibInt *) after_tag_1625 = tmpval_2446;

                GibCursor writecur_1629 = after_tag_1625 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_847,
                                                                   end_r_848,
                                                                   loc_846,
                                                                   writecur_1629};
            } else {
                GibBool fltIf_337_412 = n_86_249_409 < tmpval_2446;

                if (fltIf_337_412) {
                    GibCursor loc_1014 = loc_846 + 17;

                    *(GibPackedTag *) loc_846 = 3;

                    GibCursor writetag_1647 = loc_846 + 1;

                    *(GibPackedTag *) loc_1014 = 1;

                    GibCursor writetag_1632 = loc_1014 + 1;
                    GibCursor after_tag_1633 = loc_1014 + 1;

                    *(GibInt *) after_tag_1633 = n_86_249_409;

                    GibCursor writecur_1637 = after_tag_1633 + sizeof(GibInt);

                    *(GibPackedTag *) writecur_1637 = 0;

                    GibCursor writetag_1640 = writecur_1637 + 1;
                    GibCursor after_tag_1641 = writecur_1637 + 1;
                    uint16_t offset_53 = end_r_848 - writecur_1637;
                    uintptr_t ran_795 = GIB_STORE_TAG(writecur_1637, offset_53);
                    GibCursor after_tag_1648 = loc_846 + 1;

                    *(uintptr_t *) after_tag_1648 = ran_795;

                    GibCursor writecur_1652 = after_tag_1648 + 8;

                    *(GibInt *) writecur_1652 = tmpval_2446;

                    GibCursor writecur_1653 = writecur_1652 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_847,
                                                                       end_r_848,
                                                                       loc_846,
                                                                       after_tag_1641};
                } else {
                    GibCursor loc_1030 = loc_846 + 17;

                    *(GibPackedTag *) loc_846 = 3;

                    GibCursor writetag_1674 = loc_846 + 1;

                    *(GibPackedTag *) loc_1030 = 0;

                    GibCursor writetag_1659 = loc_1030 + 1;
                    GibCursor after_tag_1660 = loc_1030 + 1;

                    *(GibPackedTag *) after_tag_1660 = 1;

                    GibCursor writetag_1666 = after_tag_1660 + 1;
                    GibCursor after_tag_1667 = after_tag_1660 + 1;

                    *(GibInt *) after_tag_1667 = n_86_249_409;

                    GibCursor writecur_1671 = after_tag_1667 + sizeof(GibInt);
                    uint16_t offset_54 = end_r_848 - after_tag_1660;
                    uintptr_t ran_796 = GIB_STORE_TAG(after_tag_1660,
                                                      offset_54);
                    GibCursor after_tag_1675 = loc_846 + 1;

                    *(uintptr_t *) after_tag_1675 = ran_796;

                    GibCursor writecur_1679 = after_tag_1675 + 8;

                    *(GibInt *) writecur_1679 = tmpval_2446;

                    GibCursor writecur_1680 = writecur_1679 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_847,
                                                                       end_r_848,
                                                                       loc_846,
                                                                       writecur_1671};
                }
            }
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_72 = *(uintptr_t *) tmpcur_2441;
            GibCursor tmpcur_2468 = GIB_UNTAG(tagged_tmpcur_72);
            GibCursor tmpaftercur_2469 = tmpcur_2441 + 8;
            uint16_t tmptag_2470 = GIB_GET_TAG(tagged_tmpcur_72);
            GibCursor end_from_tagged_absran_800 = tmpcur_2468 + tmptag_2470;
            GibInt tmpval_2471 = *(GibInt *) tmpaftercur_2469;
            GibCursor tmpcur_2472 = tmpaftercur_2469 + sizeof(GibInt);
            GibBool fltIf_342_420 = tmpval_2471 == n_86_249_409;

            if (fltIf_342_420) {
                GibCursor loc_1050 = loc_846 + 17;

                *(GibPackedTag *) loc_846 = 3;

                GibCursor writetag_1695 = loc_846 + 1;

                if (loc_1050 + 18 > end_r_848) {
                    gib_grow_region(&loc_1050, &end_r_848);
                }
                gib_indirection_barrier(loc_1050, end_r_848, tmpcur_2472,
                                        end_r_847, SearchTree_T);

                GibCursor end_1690 = loc_1050 + 9;

                if (end_1690 + 18 > end_r_848) {
                    gib_grow_region(&end_1690, &end_r_848);
                }
                gib_indirection_barrier(end_1690, end_r_848, tmpcur_2468,
                                        end_from_tagged_absran_800,
                                        SearchTree_T);

                GibCursor end_1693 = end_1690 + 9;
                uint16_t offset_55 = end_r_848 - end_1690;
                uintptr_t ran_803 = GIB_STORE_TAG(end_1690, offset_55);
                GibCursor after_tag_1696 = loc_846 + 1;

                *(uintptr_t *) after_tag_1696 = ran_803;

                GibCursor writecur_1700 = after_tag_1696 + 8;

                *(GibInt *) writecur_1700 = tmpval_2471;

                GibCursor writecur_1701 = writecur_1700 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_847,
                                                                   end_r_848,
                                                                   loc_846,
                                                                   end_1693};
            } else {
                GibBool fltIf_345_423 = tmpval_2471 < n_86_249_409;

                if (fltIf_345_423) {
                    GibCursor loc_1066 = loc_846 + 17;

                    *(GibPackedTag *) loc_846 = 3;

                    GibCursor writetag_1713 = loc_846 + 1;

                    if (loc_1066 + 18 > end_r_848) {
                        gib_grow_region(&loc_1066, &end_r_848);
                    }
                    gib_indirection_barrier(loc_1066, end_r_848, tmpcur_2472,
                                            end_r_847, SearchTree_T);

                    GibCursor end_1708 = loc_1066 + 9;

                    gib_shadowstack_push(rstack, loc_846, end_r_848, Stk,
                                         SearchTree_T);

                    GibCursorGibCursorGibCursorGibCursorProd tmp_struct_62 =
                                                              tree_insert(end_from_tagged_absran_800, end_r_848, end_1708, tmpcur_2468, n_86_249_409);
                    GibCursor pvrtmp_2483 = tmp_struct_62.field0;
                    GibCursor pvrtmp_2484 = tmp_struct_62.field1;
                    GibCursor pvrtmp_2485 = tmp_struct_62.field2;
                    GibCursor pvrtmp_2486 = tmp_struct_62.field3;

                    frame = gib_shadowstack_pop(rstack);
                    loc_846 = frame->ptr;
                    end_r_848 = frame->endptr;

                    uint16_t offset_63 = end_r_848 - end_1708;
                    uintptr_t ran_804 = GIB_STORE_TAG(end_1708, offset_63);
                    GibCursor after_tag_1714 = loc_846 + 1;

                    *(uintptr_t *) after_tag_1714 = ran_804;

                    GibCursor writecur_1718 = after_tag_1714 + 8;

                    *(GibInt *) writecur_1718 = tmpval_2471;

                    GibCursor writecur_1719 = writecur_1718 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2483,
                                                                       pvrtmp_2484,
                                                                       loc_846,
                                                                       pvrtmp_2486};
                } else {
                    GibCursor loc_1082 = loc_846 + 17;

                    *(GibPackedTag *) loc_846 = 3;

                    GibCursor writetag_1731 = loc_846 + 1;

                    gib_shadowstack_push(rstack, loc_846, end_r_848, Stk,
                                         SearchTree_T);
                    gib_shadowstack_push(rstack, tmpcur_2468, end_r_847, Stk,
                                         SearchTree_T);

                    GibCursorGibCursorGibCursorGibCursorProd tmp_struct_67 =
                                                              tree_insert(end_r_847, end_r_848, loc_1082, tmpcur_2472, n_86_249_409);
                    GibCursor pvrtmp_2495 = tmp_struct_67.field0;
                    GibCursor pvrtmp_2496 = tmp_struct_67.field1;
                    GibCursor pvrtmp_2497 = tmp_struct_67.field2;
                    GibCursor pvrtmp_2498 = tmp_struct_67.field3;

                    frame = gib_shadowstack_pop(rstack);
                    tmpcur_2468 = frame->ptr;
                    end_r_847 = frame->endptr;
                    frame = gib_shadowstack_pop(rstack);
                    loc_846 = frame->ptr;
                    end_r_848 = frame->endptr;
                    if (pvrtmp_2498 + 18 > pvrtmp_2496) {
                        gib_grow_region(&pvrtmp_2498, &pvrtmp_2496);
                    }
                    gib_indirection_barrier(pvrtmp_2498, pvrtmp_2496,
                                            tmpcur_2468,
                                            end_from_tagged_absran_800,
                                            SearchTree_T);

                    GibCursor end_1729 = pvrtmp_2498 + 9;
                    uint16_t offset_68 = pvrtmp_2496 - pvrtmp_2498;
                    uintptr_t ran_805 = GIB_STORE_TAG(pvrtmp_2498, offset_68);
                    GibCursor after_tag_1732 = loc_846 + 1;

                    *(uintptr_t *) after_tag_1732 = ran_805;

                    GibCursor writecur_1736 = after_tag_1732 + 8;

                    *(GibInt *) writecur_1736 = tmpval_2471;

                    GibCursor writecur_1737 = writecur_1736 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2495,
                                                                       pvrtmp_2496,
                                                                       loc_846,
                                                                       end_1729};
                }
            }
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_74 = *(uintptr_t *) tmpcur_2441;
            GibCursor tmpcur_2509 = GIB_UNTAG(tagged_tmpcur_74);
            GibCursor tmpaftercur_2510 = tmpcur_2441 + 8;
            uint16_t tmptag_2511 = GIB_GET_TAG(tagged_tmpcur_74);
            GibCursor end_from_tagged_indr_1305 = tmpcur_2509 + tmptag_2511;
            GibCursor jump_1307 = tmpcur_2441 + 8;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_73 =
                                                      tree_insert(end_from_tagged_indr_1305, end_r_848, loc_846, tmpcur_2509, n_86_249_409);
            GibCursor pvrtmp_2512 = tmp_struct_73.field0;
            GibCursor pvrtmp_2513 = tmp_struct_73.field1;
            GibCursor pvrtmp_2514 = tmp_struct_73.field2;
            GibCursor pvrtmp_2515 = tmp_struct_73.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_847,
                                                               pvrtmp_2513,
                                                               pvrtmp_2514,
                                                               pvrtmp_2515};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_76 = *(uintptr_t *) tmpcur_2441;
            GibCursor tmpcur_2522 = GIB_UNTAG(tagged_tmpcur_76);
            GibCursor tmpaftercur_2523 = tmpcur_2441 + 8;
            uint16_t tmptag_2524 = GIB_GET_TAG(tagged_tmpcur_76);
            GibCursor end_from_tagged_indr_1305 = tmpcur_2522 + tmptag_2524;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_75 =
                                                      tree_insert(end_from_tagged_indr_1305, end_r_848, loc_846, tmpcur_2522, n_86_249_409);
            GibCursor pvrtmp_2525 = tmp_struct_75.field0;
            GibCursor pvrtmp_2526 = tmp_struct_75.field1;
            GibCursor pvrtmp_2527 = tmp_struct_75.field2;
            GibCursor pvrtmp_2528 = tmp_struct_75.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2525,
                                                               pvrtmp_2526,
                                                               pvrtmp_2527,
                                                               pvrtmp_2528};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2440");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_SearchTree(GibCursor end_r_851,
                                                                   GibCursor end_r_852,
                                                                   GibCursor loc_850,
                                                                   GibCursor arg_176_259_428)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_850 + 26 > end_r_852) {
        gib_grow_region(&loc_850, &end_r_852);
    }

    GibPackedTag tmpval_2536 = *(GibPackedTag *) arg_176_259_428;
    GibCursor tmpcur_2537 = arg_176_259_428 + 1;


  switch_2603:
    ;
    switch (tmpval_2536) {

      case 0:
        {
            GibCursor jump_1243 = arg_176_259_428 + 1;

            *(GibPackedTag *) loc_850 = 0;

            GibCursor writetag_1754 = loc_850 + 1;
            GibCursor after_tag_1755 = loc_850 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_851,
                                                                        end_r_852,
                                                                        jump_1243,
                                                                        loc_850,
                                                                        after_tag_1755};
            break;
        }

      case 1:
        {
            GibInt tmpval_2542 = *(GibInt *) tmpcur_2537;
            GibCursor tmpcur_2543 = tmpcur_2537 + sizeof(GibInt);
            GibCursor jump_1245 = tmpcur_2537 + 8;

            *(GibPackedTag *) loc_850 = 1;

            GibCursor writetag_1763 = loc_850 + 1;
            GibCursor after_tag_1764 = loc_850 + 1;

            *(GibInt *) after_tag_1764 = tmpval_2542;

            GibCursor writecur_1768 = after_tag_1764 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_851,
                                                                        end_r_852,
                                                                        jump_1245,
                                                                        loc_850,
                                                                        writecur_1768};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_83 = *(uintptr_t *) tmpcur_2537;
            GibCursor tmpcur_2548 = GIB_UNTAG(tagged_tmpcur_83);
            GibCursor tmpaftercur_2549 = tmpcur_2537 + 8;
            uint16_t tmptag_2550 = GIB_GET_TAG(tagged_tmpcur_83);
            GibCursor end_from_tagged_absran_810 = tmpcur_2548 + tmptag_2550;
            GibInt tmpval_2551 = *(GibInt *) tmpaftercur_2549;
            GibCursor tmpcur_2552 = tmpaftercur_2549 + sizeof(GibInt);
            GibCursor loc_1114 = loc_850 + 17;

            *(GibPackedTag *) loc_850 = 3;

            GibCursor writetag_1780 = loc_850 + 1;

            gib_shadowstack_push(rstack, loc_850, end_r_852, Stk, SearchTree_T);
            gib_shadowstack_push(rstack, tmpcur_2548, end_r_851, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_80 =
                                                               _copy_SearchTree(end_r_851, end_r_852, loc_1114, tmpcur_2552);
            GibCursor pvrtmp_2553 = tmp_struct_80.field0;
            GibCursor pvrtmp_2554 = tmp_struct_80.field1;
            GibCursor pvrtmp_2555 = tmp_struct_80.field2;
            GibCursor pvrtmp_2556 = tmp_struct_80.field3;
            GibCursor pvrtmp_2557 = tmp_struct_80.field4;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_2548 = frame->ptr;
            end_r_851 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_850 = frame->ptr;
            end_r_852 = frame->endptr;
            gib_shadowstack_push(rstack, loc_850, pvrtmp_2554, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_81 =
                                                               _copy_SearchTree(end_from_tagged_absran_810, pvrtmp_2554, pvrtmp_2557, tmpcur_2548);
            GibCursor pvrtmp_2562 = tmp_struct_81.field0;
            GibCursor pvrtmp_2563 = tmp_struct_81.field1;
            GibCursor pvrtmp_2564 = tmp_struct_81.field2;
            GibCursor pvrtmp_2565 = tmp_struct_81.field3;
            GibCursor pvrtmp_2566 = tmp_struct_81.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_850 = frame->ptr;
            pvrtmp_2554 = frame->endptr;

            uint16_t offset_82 = pvrtmp_2554 - pvrtmp_2557;
            uintptr_t ran_813 = GIB_STORE_TAG(pvrtmp_2557, offset_82);
            GibCursor after_tag_1781 = loc_850 + 1;

            *(uintptr_t *) after_tag_1781 = ran_813;

            GibCursor writecur_1785 = after_tag_1781 + 8;

            *(GibInt *) writecur_1785 = tmpval_2551;

            GibCursor writecur_1786 = writecur_1785 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2562,
                                                                        pvrtmp_2563,
                                                                        pvrtmp_2564,
                                                                        loc_850,
                                                                        pvrtmp_2566};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_85 = *(uintptr_t *) tmpcur_2537;
            GibCursor tmpcur_2575 = GIB_UNTAG(tagged_tmpcur_85);
            GibCursor tmpaftercur_2576 = tmpcur_2537 + 8;
            uint16_t tmptag_2577 = GIB_GET_TAG(tagged_tmpcur_85);
            GibCursor end_from_tagged_indr_1310 = tmpcur_2575 + tmptag_2577;
            GibCursor jump_1312 = tmpcur_2537 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_84 =
                                                               _copy_SearchTree(end_from_tagged_indr_1310, end_r_852, loc_850, tmpcur_2575);
            GibCursor pvrtmp_2578 = tmp_struct_84.field0;
            GibCursor pvrtmp_2579 = tmp_struct_84.field1;
            GibCursor pvrtmp_2580 = tmp_struct_84.field2;
            GibCursor pvrtmp_2581 = tmp_struct_84.field3;
            GibCursor pvrtmp_2582 = tmp_struct_84.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_851,
                                                                        pvrtmp_2579,
                                                                        jump_1312,
                                                                        pvrtmp_2581,
                                                                        pvrtmp_2582};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_87 = *(uintptr_t *) tmpcur_2537;
            GibCursor tmpcur_2589 = GIB_UNTAG(tagged_tmpcur_87);
            GibCursor tmpaftercur_2590 = tmpcur_2537 + 8;
            uint16_t tmptag_2591 = GIB_GET_TAG(tagged_tmpcur_87);
            GibCursor end_from_tagged_indr_1310 = tmpcur_2589 + tmptag_2591;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_86 =
                                                               _copy_SearchTree(end_from_tagged_indr_1310, end_r_852, loc_850, tmpcur_2589);
            GibCursor pvrtmp_2592 = tmp_struct_86.field0;
            GibCursor pvrtmp_2593 = tmp_struct_86.field1;
            GibCursor pvrtmp_2594 = tmp_struct_86.field2;
            GibCursor pvrtmp_2595 = tmp_struct_86.field3;
            GibCursor pvrtmp_2596 = tmp_struct_86.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2592,
                                                                        pvrtmp_2593,
                                                                        pvrtmp_2594,
                                                                        pvrtmp_2595,
                                                                        pvrtmp_2596};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2536");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_SearchTree(GibCursor end_r_855,
                                                                                GibCursor end_r_856,
                                                                                GibCursor loc_854,
                                                                                GibCursor arg_185_268_437)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2604 = *(GibPackedTag *) arg_185_268_437;
    GibCursor tmpcur_2605 = arg_185_268_437 + 1;


  switch_2671:
    ;
    switch (tmpval_2604) {

      case 0:
        {
            GibCursor jump_1252 = arg_185_268_437 + 1;

            *(GibPackedTag *) loc_854 = 0;

            GibCursor writetag_1803 = loc_854 + 1;
            GibCursor after_tag_1804 = loc_854 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_855,
                                                                        end_r_856,
                                                                        jump_1252,
                                                                        loc_854,
                                                                        after_tag_1804};
            break;
        }

      case 1:
        {
            GibInt tmpval_2610 = *(GibInt *) tmpcur_2605;
            GibCursor tmpcur_2611 = tmpcur_2605 + sizeof(GibInt);
            GibCursor jump_1254 = tmpcur_2605 + 8;

            *(GibPackedTag *) loc_854 = 1;

            GibCursor writetag_1812 = loc_854 + 1;
            GibCursor after_tag_1813 = loc_854 + 1;

            *(GibInt *) after_tag_1813 = tmpval_2610;

            GibCursor writecur_1817 = after_tag_1813 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_855,
                                                                        end_r_856,
                                                                        jump_1254,
                                                                        loc_854,
                                                                        writecur_1817};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_93 = *(uintptr_t *) tmpcur_2605;
            GibCursor tmpcur_2616 = GIB_UNTAG(tagged_tmpcur_93);
            GibCursor tmpaftercur_2617 = tmpcur_2605 + 8;
            uint16_t tmptag_2618 = GIB_GET_TAG(tagged_tmpcur_93);
            GibCursor end_from_tagged_absran_815 = tmpcur_2616 + tmptag_2618;
            GibInt tmpval_2619 = *(GibInt *) tmpaftercur_2617;
            GibCursor tmpcur_2620 = tmpaftercur_2617 + sizeof(GibInt);
            GibCursor loc_1141 = loc_854 + 9;

            *(GibPackedTag *) loc_854 = 2;

            GibCursor writetag_1829 = loc_854 + 1;
            GibCursor after_tag_1830 = loc_854 + 1;

            *(GibInt *) after_tag_1830 = tmpval_2619;

            GibCursor writecur_1834 = after_tag_1830 + sizeof(GibInt);

            gib_shadowstack_push(rstack, loc_854, end_r_856, Stk, SearchTree_T);
            gib_shadowstack_push(rstack, tmpcur_2616, end_r_855, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_91 =
                                                               _copy_without_ptrs_SearchTree(end_r_855, end_r_856, loc_1141, tmpcur_2620);
            GibCursor pvrtmp_2621 = tmp_struct_91.field0;
            GibCursor pvrtmp_2622 = tmp_struct_91.field1;
            GibCursor pvrtmp_2623 = tmp_struct_91.field2;
            GibCursor pvrtmp_2624 = tmp_struct_91.field3;
            GibCursor pvrtmp_2625 = tmp_struct_91.field4;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_2616 = frame->ptr;
            end_r_855 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_854 = frame->ptr;
            end_r_856 = frame->endptr;
            gib_shadowstack_push(rstack, loc_854, pvrtmp_2622, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_92 =
                                                               _copy_without_ptrs_SearchTree(end_from_tagged_absran_815, pvrtmp_2622, pvrtmp_2625, tmpcur_2616);
            GibCursor pvrtmp_2630 = tmp_struct_92.field0;
            GibCursor pvrtmp_2631 = tmp_struct_92.field1;
            GibCursor pvrtmp_2632 = tmp_struct_92.field2;
            GibCursor pvrtmp_2633 = tmp_struct_92.field3;
            GibCursor pvrtmp_2634 = tmp_struct_92.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_854 = frame->ptr;
            pvrtmp_2622 = frame->endptr;
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2630,
                                                                        pvrtmp_2631,
                                                                        pvrtmp_2632,
                                                                        loc_854,
                                                                        pvrtmp_2634};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_95 = *(uintptr_t *) tmpcur_2605;
            GibCursor tmpcur_2643 = GIB_UNTAG(tagged_tmpcur_95);
            GibCursor tmpaftercur_2644 = tmpcur_2605 + 8;
            uint16_t tmptag_2645 = GIB_GET_TAG(tagged_tmpcur_95);
            GibCursor end_from_tagged_indr_1316 = tmpcur_2643 + tmptag_2645;
            GibCursor jump_1318 = tmpcur_2605 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_94 =
                                                               _copy_without_ptrs_SearchTree(end_from_tagged_indr_1316, end_r_856, loc_854, tmpcur_2643);
            GibCursor pvrtmp_2646 = tmp_struct_94.field0;
            GibCursor pvrtmp_2647 = tmp_struct_94.field1;
            GibCursor pvrtmp_2648 = tmp_struct_94.field2;
            GibCursor pvrtmp_2649 = tmp_struct_94.field3;
            GibCursor pvrtmp_2650 = tmp_struct_94.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_855,
                                                                        pvrtmp_2647,
                                                                        jump_1318,
                                                                        pvrtmp_2649,
                                                                        pvrtmp_2650};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_97 = *(uintptr_t *) tmpcur_2605;
            GibCursor tmpcur_2657 = GIB_UNTAG(tagged_tmpcur_97);
            GibCursor tmpaftercur_2658 = tmpcur_2605 + 8;
            uint16_t tmptag_2659 = GIB_GET_TAG(tagged_tmpcur_97);
            GibCursor end_from_tagged_indr_1316 = tmpcur_2657 + tmptag_2659;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_96 =
                                                               _copy_without_ptrs_SearchTree(end_from_tagged_indr_1316, end_r_856, loc_854, tmpcur_2657);
            GibCursor pvrtmp_2660 = tmp_struct_96.field0;
            GibCursor pvrtmp_2661 = tmp_struct_96.field1;
            GibCursor pvrtmp_2662 = tmp_struct_96.field2;
            GibCursor pvrtmp_2663 = tmp_struct_96.field3;
            GibCursor pvrtmp_2664 = tmp_struct_96.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2660,
                                                                        pvrtmp_2661,
                                                                        pvrtmp_2662,
                                                                        pvrtmp_2663,
                                                                        pvrtmp_2664};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2604");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_SearchTree(GibCursor end_r_858,
                                            GibCursor arg_194_277_446)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2672 = *(GibPackedTag *) arg_194_277_446;
    GibCursor tmpcur_2673 = arg_194_277_446 + 1;


  switch_2695:
    ;
    switch (tmpval_2672) {

      case 0:
        {
            GibCursor jump_1261 = arg_194_277_446 + 1;

            return (GibCursorGibCursorProd) {end_r_858, jump_1261};
            break;
        }

      case 1:
        {
            GibInt tmpval_2674 = *(GibInt *) tmpcur_2673;
            GibCursor tmpcur_2675 = tmpcur_2673 + sizeof(GibInt);
            GibCursor jump_1263 = tmpcur_2673 + 8;

            return (GibCursorGibCursorProd) {end_r_858, jump_1263};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_100 = *(uintptr_t *) tmpcur_2673;
            GibCursor tmpcur_2676 = GIB_UNTAG(tagged_tmpcur_100);
            GibCursor tmpaftercur_2677 = tmpcur_2673 + 8;
            uint16_t tmptag_2678 = GIB_GET_TAG(tagged_tmpcur_100);
            GibCursor end_from_tagged_absran_818 = tmpcur_2676 + tmptag_2678;
            GibInt tmpval_2679 = *(GibInt *) tmpaftercur_2677;
            GibCursor tmpcur_2680 = tmpaftercur_2677 + sizeof(GibInt);

            gib_shadowstack_push(rstack, tmpcur_2676, end_r_858, Stk,
                                 SearchTree_T);

            GibCursorGibCursorProd tmp_struct_98 =
                                    _traverse_SearchTree(end_r_858, tmpcur_2680);
            GibCursor pvrtmp_2681 = tmp_struct_98.field0;
            GibCursor pvrtmp_2682 = tmp_struct_98.field1;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_2676 = frame->ptr;
            end_r_858 = frame->endptr;

            GibCursorGibCursorProd tmp_struct_99 =
                                    _traverse_SearchTree(end_from_tagged_absran_818, tmpcur_2676);
            GibCursor pvrtmp_2683 = tmp_struct_99.field0;
            GibCursor pvrtmp_2684 = tmp_struct_99.field1;

            return (GibCursorGibCursorProd) {pvrtmp_2683, pvrtmp_2684};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_102 = *(uintptr_t *) tmpcur_2673;
            GibCursor tmpcur_2685 = GIB_UNTAG(tagged_tmpcur_102);
            GibCursor tmpaftercur_2686 = tmpcur_2673 + 8;
            uint16_t tmptag_2687 = GIB_GET_TAG(tagged_tmpcur_102);
            GibCursor end_from_tagged_indr_1322 = tmpcur_2685 + tmptag_2687;
            GibCursor jump_1324 = tmpcur_2673 + 8;
            GibCursorGibCursorProd tmp_struct_101 =
                                    _traverse_SearchTree(end_from_tagged_indr_1322, tmpcur_2685);
            GibCursor pvrtmp_2688 = tmp_struct_101.field0;
            GibCursor pvrtmp_2689 = tmp_struct_101.field1;

            return (GibCursorGibCursorProd) {end_r_858, jump_1324};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_104 = *(uintptr_t *) tmpcur_2673;
            GibCursor tmpcur_2690 = GIB_UNTAG(tagged_tmpcur_104);
            GibCursor tmpaftercur_2691 = tmpcur_2673 + 8;
            uint16_t tmptag_2692 = GIB_GET_TAG(tagged_tmpcur_104);
            GibCursor end_from_tagged_indr_1322 = tmpcur_2690 + tmptag_2692;
            GibCursorGibCursorProd tmp_struct_103 =
                                    _traverse_SearchTree(end_from_tagged_indr_1322, tmpcur_2690);
            GibCursor pvrtmp_2693 = tmp_struct_103.field0;
            GibCursor pvrtmp_2694 = tmp_struct_103.field1;

            return (GibCursorGibCursorProd) {pvrtmp_2693, pvrtmp_2694};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2672");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_SearchTree(GibCursor end_r_860,
                                         GibCursor arg_203_284_453)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2696 = *(GibPackedTag *) arg_203_284_453;
    GibCursor tmpcur_2697 = arg_203_284_453 + 1;


  switch_2719:
    ;
    switch (tmpval_2696) {

      case 0:
        {
            GibCursor jump_1270 = arg_203_284_453 + 1;
            unsigned char wildcard_204_285_454 = gib_print_symbol(2181);
            unsigned char wildcard_205_286_455 = gib_print_symbol(2180);

            return (GibCursorGibCursorProd) {end_r_860, jump_1270};
            break;
        }

      case 1:
        {
            GibInt tmpval_2698 = *(GibInt *) tmpcur_2697;
            GibCursor tmpcur_2699 = tmpcur_2697 + sizeof(GibInt);
            GibCursor jump_1272 = tmpcur_2697 + 8;
            unsigned char wildcard_208_288_457 = gib_print_symbol(2183);
            unsigned char y_207_289_458 = printf("%ld", tmpval_2698);
            unsigned char wildcard_209_290_459 = gib_print_symbol(2180);

            return (GibCursorGibCursorProd) {end_r_860, jump_1272};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_107 = *(uintptr_t *) tmpcur_2697;
            GibCursor tmpcur_2700 = GIB_UNTAG(tagged_tmpcur_107);
            GibCursor tmpaftercur_2701 = tmpcur_2697 + 8;
            uint16_t tmptag_2702 = GIB_GET_TAG(tagged_tmpcur_107);
            GibCursor end_from_tagged_absran_821 = tmpcur_2700 + tmptag_2702;
            GibInt tmpval_2703 = *(GibInt *) tmpaftercur_2701;
            GibCursor tmpcur_2704 = tmpaftercur_2701 + sizeof(GibInt);
            unsigned char wildcard_216_294_463 = gib_print_symbol(2182);
            unsigned char y_213_295_464 = printf("%ld", tmpval_2703);

            gib_shadowstack_push(rstack, tmpcur_2700, end_r_860, Stk,
                                 SearchTree_T);

            GibCursorGibCursorProd tmp_struct_105 =
                                    _print_SearchTree(end_r_860, tmpcur_2704);
            GibCursor pvrtmp_2705 = tmp_struct_105.field0;
            GibCursor pvrtmp_2706 = tmp_struct_105.field1;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_2700 = frame->ptr;
            end_r_860 = frame->endptr;

            GibCursorGibCursorProd tmp_struct_106 =
                                    _print_SearchTree(end_from_tagged_absran_821, tmpcur_2700);
            GibCursor pvrtmp_2707 = tmp_struct_106.field0;
            GibCursor pvrtmp_2708 = tmp_struct_106.field1;
            unsigned char wildcard_217_298_467 = gib_print_symbol(2180);

            return (GibCursorGibCursorProd) {pvrtmp_2707, pvrtmp_2708};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_109 = *(uintptr_t *) tmpcur_2697;
            GibCursor tmpcur_2709 = GIB_UNTAG(tagged_tmpcur_109);
            GibCursor tmpaftercur_2710 = tmpcur_2697 + 8;
            uint16_t tmptag_2711 = GIB_GET_TAG(tagged_tmpcur_109);
            GibCursor end_from_tagged_indr_1328 = tmpcur_2709 + tmptag_2711;
            GibCursor jump_1330 = tmpcur_2697 + 8;
            unsigned char wildcard_1333 = gib_print_symbol(2185);
            GibCursorGibCursorProd tmp_struct_108 =
                                    _print_SearchTree(end_from_tagged_indr_1328, tmpcur_2709);
            GibCursor pvrtmp_2712 = tmp_struct_108.field0;
            GibCursor pvrtmp_2713 = tmp_struct_108.field1;

            return (GibCursorGibCursorProd) {end_r_860, jump_1330};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_111 = *(uintptr_t *) tmpcur_2697;
            GibCursor tmpcur_2714 = GIB_UNTAG(tagged_tmpcur_111);
            GibCursor tmpaftercur_2715 = tmpcur_2697 + 8;
            uint16_t tmptag_2716 = GIB_GET_TAG(tagged_tmpcur_111);
            GibCursor end_from_tagged_indr_1328 = tmpcur_2714 + tmptag_2716;
            unsigned char wildcard_1333 = gib_print_symbol(2184);
            GibCursorGibCursorProd tmp_struct_110 =
                                    _print_SearchTree(end_from_tagged_indr_1328, tmpcur_2714);
            GibCursor pvrtmp_2717 = tmp_struct_110.field0;
            GibCursor pvrtmp_2718 = tmp_struct_110.field1;

            return (GibCursorGibCursorProd) {pvrtmp_2717, pvrtmp_2718};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2696");
            exit(1);
        }
    }
}
GibCursorGibIntProd caseFn_218(GibCursor end_r_862, GibCursor l_79_219_299_468,
                               GibInt n_78_220_300_469)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2720 = *(GibPackedTag *) l_79_219_299_468;
    GibCursor tmpcur_2721 = l_79_219_299_468 + 1;


  switch_2741:
    ;
    switch (tmpval_2720) {

      case 0:
        {
            return (GibCursorGibIntProd) {end_r_862, n_78_220_300_469};
            break;
        }

      case 1:
        {
            GibInt tmpval_2722 = *(GibInt *) tmpcur_2721;
            GibCursor tmpcur_2723 = tmpcur_2721 + sizeof(GibInt);

            return (GibCursorGibIntProd) {end_r_862, tmpval_2722};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_113 = *(uintptr_t *) tmpcur_2721;
            GibCursor tmpcur_2724 = GIB_UNTAG(tagged_tmpcur_113);
            GibCursor tmpaftercur_2725 = tmpcur_2721 + 8;
            uint16_t tmptag_2726 = GIB_GET_TAG(tagged_tmpcur_113);
            GibCursor end_from_tagged_absran_824 = tmpcur_2724 + tmptag_2726;
            GibInt tmpval_2727 = *(GibInt *) tmpaftercur_2725;
            GibCursor tmpcur_2728 = tmpaftercur_2725 + sizeof(GibInt);
            GibCursorGibIntProd tmp_struct_112 =
                                 min_tree(end_r_862, tmpcur_2728);
            GibCursor pvrtmp_2729 = tmp_struct_112.field0;
            GibInt pvrtmp_2730 = tmp_struct_112.field1;

            return (GibCursorGibIntProd) {pvrtmp_2729, pvrtmp_2730};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_115 = *(uintptr_t *) tmpcur_2721;
            GibCursor tmpcur_2731 = GIB_UNTAG(tagged_tmpcur_115);
            GibCursor tmpaftercur_2732 = tmpcur_2721 + 8;
            uint16_t tmptag_2733 = GIB_GET_TAG(tagged_tmpcur_115);
            GibCursor end_from_tagged_indr_1334 = tmpcur_2731 + tmptag_2733;
            GibCursor jump_1336 = tmpcur_2721 + 8;
            GibCursorGibIntProd tmp_struct_114 =
                                 caseFn_218(end_from_tagged_indr_1334, tmpcur_2731, n_78_220_300_469);
            GibCursor pvrtmp_2734 = tmp_struct_114.field0;
            GibInt pvrtmp_2735 = tmp_struct_114.field1;

            return (GibCursorGibIntProd) {end_r_862, pvrtmp_2735};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_117 = *(uintptr_t *) tmpcur_2721;
            GibCursor tmpcur_2736 = GIB_UNTAG(tagged_tmpcur_117);
            GibCursor tmpaftercur_2737 = tmpcur_2721 + 8;
            uint16_t tmptag_2738 = GIB_GET_TAG(tagged_tmpcur_117);
            GibCursor end_from_tagged_indr_1334 = tmpcur_2736 + tmptag_2738;
            GibCursorGibIntProd tmp_struct_116 =
                                 caseFn_218(end_from_tagged_indr_1334, tmpcur_2736, n_78_220_300_469);
            GibCursor pvrtmp_2739 = tmp_struct_116.field0;
            GibInt pvrtmp_2740 = tmp_struct_116.field1;

            return (GibCursorGibIntProd) {pvrtmp_2739, pvrtmp_2740};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2720");
            exit(1);
        }
    }
}
int gib_main_expr(void)
{


    for (int i = 0; i < 1000000; i++) {
        GibInt fltPrm_316_370 = rand();
        GibInt j_63_230_371 = fltPrm_316_370 % 100;
        printf("%ld\n", j_63_230_371);
    }
    fflush(stdout);
    exit(1);

    info_table_initialize();
    symbol_table_initialize();

    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibChunk region_2186 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_876 = region_2186.start;
    GibCursor end_r_876 = region_2186.end;
    GibChunk region_2187 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_875 = region_2187.start;
    GibCursor end_r_875 = region_2187.end;
    GibInt m_54_221_350 = gib_get_size_param();
    GibInt fltPrm_305_351 = gib_expll(2, 3);
    GibInt total_nodes_55_222_352 = fltPrm_305_351 - 1;
    GibCursor pvrtmp_2197;
    GibCursor pvrtmp_2198;
    GibCursor pvrtmp_2199;
    GibVector *times_122 = gib_vector_alloc(gib_get_iters_param(),
                                            sizeof(double));
    struct timespec begin_pvrtmp_2197;
    struct timespec end_pvrtmp_2197;

    clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_2197);
    {
        GibCursorGibCursorGibCursorProd tmp_struct_118 =
                                         helper(end_r_876, r_876, 0, total_nodes_55_222_352);
        GibCursor pvrtmp_2188 = tmp_struct_118.field0;
        GibCursor pvrtmp_2189 = tmp_struct_118.field1;
        GibCursor pvrtmp_2190 = tmp_struct_118.field2;

        pvrtmp_2197 = pvrtmp_2188;
        pvrtmp_2198 = pvrtmp_2189;
        pvrtmp_2199 = pvrtmp_2190;
    }
    clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_2197);

    double selftimed_121 = gib_difftimespecs(&begin_pvrtmp_2197,
                                             &end_pvrtmp_2197);

    gib_vector_free(times_122);
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("SELFTIMED: %e\n", gib_difftimespecs(&begin_pvrtmp_2197,
                                                &end_pvrtmp_2197));
    gib_shadowstack_push(rstack, r_876, end_r_876, Stk, SearchTree_T);
    frame = gib_shadowstack_pop(rstack);
    r_876 = frame->ptr;
    end_r_876 = frame->endptr;

    GibCursor pvrtmp_2217;
    GibCursor pvrtmp_2218;
    GibCursor pvrtmp_2219;
    GibVector *times_128 = gib_vector_alloc(gib_get_iters_param(),
                                            sizeof(double));
    struct timespec begin_pvrtmp_2217;
    struct timespec end_pvrtmp_2217;

    for (long long iters_pvrtmp_2217 = 0; iters_pvrtmp_2217 <
         gib_get_iters_param(); iters_pvrtmp_2217++) {
        if (iters_pvrtmp_2217 != gib_get_iters_param() - 1)
            gib_list_bumpalloc_save_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_2217);

        GibInt fltAppE_306_354 = gib_get_size_param();
        GibCursorGibCursorGibCursorGibCursorProd tmp_struct_124 =
                                                  loop(end_r_876, end_r_875, r_875, pvrtmp_2198, fltAppE_306_354);
        GibCursor pvrtmp_2207 = tmp_struct_124.field0;
        GibCursor pvrtmp_2208 = tmp_struct_124.field1;
        GibCursor pvrtmp_2209 = tmp_struct_124.field2;
        GibCursor pvrtmp_2210 = tmp_struct_124.field3;

        pvrtmp_2217 = pvrtmp_2208;
        pvrtmp_2218 = pvrtmp_2209;
        pvrtmp_2219 = pvrtmp_2210;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_2217);
        if (iters_pvrtmp_2217 != gib_get_iters_param() - 1)
            gib_list_bumpalloc_restore_state();

        double itertime_125 = gib_difftimespecs(&begin_pvrtmp_2217,
                                                &end_pvrtmp_2217);

        printf("itertime: %lf\n", itertime_125);
        gib_vector_inplace_update(times_128, iters_pvrtmp_2217, &itertime_125);
    }
    gib_vector_inplace_sort(times_128, gib_compare_doubles);

    double *tmp_129 = (double *) gib_vector_nth(times_128,
                                                gib_get_iters_param() / 2);
    double selftimed_127 = *tmp_129;
    double batchtime_126 = gib_sum_timing_array(times_128);

    gib_print_timing_array(times_128);
    gib_vector_free(times_128);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_126);
    printf("SELFTIMED: %e\n", selftimed_127);

    GibCursorGibCursorGibIntProd tmp_struct_130 =
                                  countnodes(end_r_875, pvrtmp_2218);
    GibCursor pvrtmp_2227 = tmp_struct_130.field0;
    GibCursor pvrtmp_2228 = tmp_struct_130.field1;
    GibInt pvrtmp_2229 = tmp_struct_130.field2;

    printf("%ld", pvrtmp_2229);
    printf("\n");
    return 0;
}
