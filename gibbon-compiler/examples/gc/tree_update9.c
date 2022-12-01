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
GibCursorGibCursorGibCursorProd helper(GibCursor end_r_847, GibCursor loc_846,
                                       GibInt s_55_231_363,
                                       GibInt e_56_232_364);
GibCursorGibCursorGibCursorGibCursorGibCursorProd loop(GibCursor end_r_850,
                                                       GibCursor end_r_851,
                                                       GibCursor loc_849,
                                                       GibCursor tr_58_234_374,
                                                       GibInt n_59_235_375);
GibCursorGibCursorGibIntProd countnodes(GibCursor end_r_853,
                                        GibCursor tr_89_238_388);
GibCursorGibCursorGibIntProd sum_tree(GibCursor end_r_855,
                                      GibCursor tr_62_243_396);
GibCursorGibCursorGibCursorGibCursorProd tree_delete(GibCursor end_r_858,
                                                     GibCursor end_r_859,
                                                     GibCursor loc_857,
                                                     GibCursor tr_67_248_404,
                                                     GibInt n_68_249_405);
GibCursorGibIntProd min_tree(GibCursor end_r_861, GibCursor tr_74_255_420);
GibCursorGibCursorGibCursorGibCursorProd tree_insert(GibCursor end_r_864,
                                                     GibCursor end_r_865,
                                                     GibCursor loc_863,
                                                     GibCursor tr_83_260_425,
                                                     GibInt n_84_261_426);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_SearchTree(GibCursor end_r_868, GibCursor end_r_869, GibCursor loc_867,
                 GibCursor arg_182_266_441);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_SearchTree(GibCursor end_r_872, GibCursor end_r_873,
                              GibCursor loc_871, GibCursor arg_191_275_450);
GibCursorGibCursorProd _traverse_SearchTree(GibCursor end_r_875,
                                            GibCursor arg_200_284_459);
GibCursorGibCursorProd _print_SearchTree(GibCursor end_r_877,
                                         GibCursor arg_209_291_466);
GibCursorGibIntProd caseFn_224(GibCursor end_r_879, GibCursor l_77_225_306_481,
                               GibInt n_76_226_307_482);
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
    gib_add_symbol(2210, ")");
    gib_add_symbol(2211, "(Null ");
    gib_add_symbol(2212, "(Node ");
    gib_add_symbol(2213, "(Leaf ");
    gib_add_symbol(2214, " ->r ");
    gib_add_symbol(2215, " ->i ");
}
GibCursorGibCursorGibCursorProd helper(GibCursor end_r_847, GibCursor loc_846,
                                       GibInt s_55_231_363, GibInt e_56_232_364)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    
    if (loc_846 + 26 > end_r_847) {
        gib_grow_region(&loc_846, &end_r_847);
    }
    
    GibBool fltIf_314_365 = e_56_232_364 < s_55_231_363;
    
    if (fltIf_314_365) {
        *(GibPackedTag *) loc_846 = 0;
        
        GibCursor writetag_1478 = loc_846 + 1;
        GibCursor after_tag_1479 = loc_846 + 1;
        
        return (GibCursorGibCursorGibCursorProd) {end_r_847, loc_846,
                                                  after_tag_1479};
    } else {
        GibBool fltIf_315_366 = s_55_231_363 == e_56_232_364;
        
        if (fltIf_315_366) {
            *(GibPackedTag *) loc_846 = 1;
            
            GibCursor writetag_1485 = loc_846 + 1;
            GibCursor after_tag_1486 = loc_846 + 1;
            
            *(GibInt *) after_tag_1486 = s_55_231_363;
            
            GibCursor writecur_1490 = after_tag_1486 + sizeof(GibInt);
            
            return (GibCursorGibCursorGibCursorProd) {end_r_847, loc_846,
                                                      writecur_1490};
        } else {
            GibInt fltPrm_317_367 = e_56_232_364 - s_55_231_363;
            GibInt fltPrm_316_368 = fltPrm_317_367 / 2;
            GibInt m_57_233_369 = fltPrm_316_368 + s_55_231_363;
            GibInt fltAppE_319_370 = m_57_233_369 - 1;
            GibCursor loc_902 = loc_846 + 17;
            
            *(GibPackedTag *) loc_846 = 3;
            
            GibCursor writetag_1497 = loc_846 + 1;
            
            gib_shadowstack_push(rstack, loc_846, end_r_847, Stk, SearchTree_T);
            
            GibCursorGibCursorGibCursorProd tmp_struct_0 =
                                             helper(end_r_847, loc_902, s_55_231_363, fltAppE_319_370);
            GibCursor pvrtmp_2269 = tmp_struct_0.field0;
            GibCursor pvrtmp_2270 = tmp_struct_0.field1;
            GibCursor pvrtmp_2271 = tmp_struct_0.field2;
            
            frame = gib_shadowstack_pop(rstack);
            loc_846 = frame->ptr;
            end_r_847 = frame->endptr;
            
            GibInt fltAppE_321_372 = m_57_233_369 + 1;
            
            gib_shadowstack_push(rstack, loc_846, pvrtmp_2269, Stk,
                                 SearchTree_T);
            
            GibCursorGibCursorGibCursorProd tmp_struct_1 =
                                             helper(pvrtmp_2269, pvrtmp_2271, fltAppE_321_372, e_56_232_364);
            GibCursor pvrtmp_2276 = tmp_struct_1.field0;
            GibCursor pvrtmp_2277 = tmp_struct_1.field1;
            GibCursor pvrtmp_2278 = tmp_struct_1.field2;
            
            frame = gib_shadowstack_pop(rstack);
            loc_846 = frame->ptr;
            pvrtmp_2269 = frame->endptr;
            
            uint16_t offset_2 = pvrtmp_2269 - pvrtmp_2271;
            uintptr_t ran_791 = GIB_STORE_TAG(pvrtmp_2271, offset_2);
            GibCursor after_tag_1498 = loc_846 + 1;
            
            *(uintptr_t *) after_tag_1498 = ran_791;
            
            GibCursor writecur_1502 = after_tag_1498 + 8;
            
            *(GibInt *) writecur_1502 = m_57_233_369;
            
            GibCursor writecur_1503 = writecur_1502 + sizeof(GibInt);
            
            return (GibCursorGibCursorGibCursorProd) {pvrtmp_2276, loc_846,
                                                      pvrtmp_2278};
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd loop(GibCursor end_r_850,
                                                       GibCursor end_r_851,
                                                       GibCursor loc_849,
                                                       GibCursor tr_58_234_374,
                                                       GibInt n_59_235_375)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    
    if (loc_849 + 26 > end_r_851) {
        gib_grow_region(&loc_849, &end_r_851);
    }
    gib_shadowstack_push(rstack, tr_58_234_374, end_r_850, Stk, SearchTree_T);
    gib_shadowstack_push(wstack, loc_849, end_r_851, Stk, SearchTree_T);
    
    GibCursorGibCursorGibIntProd tmp_struct_6 =
                                  countnodes(end_r_850, tr_58_234_374);
    GibCursor pvrtmp_2287 = tmp_struct_6.field0;
    GibCursor pvrtmp_2288 = tmp_struct_6.field1;
    GibInt pvrtmp_2289 = tmp_struct_6.field2;
    
    frame = gib_shadowstack_pop(wstack);
    loc_849 = frame->ptr;
    end_r_851 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    tr_58_234_374 = frame->ptr;
    end_r_850 = frame->endptr;
    
    unsigned char __60_236_377 = printf("%ld", pvrtmp_2289);
    GibBool fltIf_323_378 = n_59_235_375 == 0;
    
    if (fltIf_323_378) {
        if (loc_849 + 18 > end_r_851) {
            gib_grow_region(&loc_849, &end_r_851);
        }
        gib_indirection_barrier(loc_849, end_r_851, tr_58_234_374, end_r_850,
                                SearchTree_T);
        
        GibCursor end_1512 = loc_849 + 9;
        
        return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2287,
                                                                    end_r_851,
                                                                    pvrtmp_2288,
                                                                    loc_849,
                                                                    end_1512};
    } else {
        GibInt fltPrm_324_379 = rand();
        GibInt j_61_237_380 = fltPrm_324_379 % 1000;
        GibInt fltPrm_326_381 = j_61_237_380 % 2;
        GibBool fltIf_325_382 = 0 == fltPrm_326_381;
        
        if (fltIf_325_382) {
            gib_shadowstack_push(rstack, tr_58_234_374, end_r_850, Stk,
                                 SearchTree_T);
            gib_shadowstack_push(wstack, loc_849, end_r_851, Stk, SearchTree_T);
            
            GibChunk region_2294 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_921 = region_2294.start;
            GibCursor end_r_921 = region_2294.end;
            
            frame = gib_shadowstack_pop(wstack);
            loc_849 = frame->ptr;
            end_r_851 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tr_58_234_374 = frame->ptr;
            end_r_850 = frame->endptr;
            gib_shadowstack_push(wstack, loc_849, end_r_851, Stk, SearchTree_T);
            
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_10 =
                                                      tree_insert(end_r_850, end_r_921, r_921, tr_58_234_374, j_61_237_380);
            GibCursor pvrtmp_2295 = tmp_struct_10.field0;
            GibCursor pvrtmp_2296 = tmp_struct_10.field1;
            GibCursor pvrtmp_2297 = tmp_struct_10.field2;
            GibCursor pvrtmp_2298 = tmp_struct_10.field3;
            
            frame = gib_shadowstack_pop(wstack);
            loc_849 = frame->ptr;
            end_r_851 = frame->endptr;
            
            GibInt fltAppE_328_384 = n_59_235_375 - 1;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_11 =
                                                               loop(pvrtmp_2296, end_r_851, loc_849, pvrtmp_2297, fltAppE_328_384);
            GibCursor pvrtmp_2303 = tmp_struct_11.field0;
            GibCursor pvrtmp_2304 = tmp_struct_11.field1;
            GibCursor pvrtmp_2305 = tmp_struct_11.field2;
            GibCursor pvrtmp_2306 = tmp_struct_11.field3;
            GibCursor pvrtmp_2307 = tmp_struct_11.field4;
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2295,
                                                                        pvrtmp_2304,
                                                                        pvrtmp_2288,
                                                                        pvrtmp_2306,
                                                                        pvrtmp_2307};
        } else {
            GibInt fltAppE_330_385 = j_61_237_380 - 1;
            
            gib_shadowstack_push(rstack, tr_58_234_374, end_r_850, Stk,
                                 SearchTree_T);
            gib_shadowstack_push(wstack, loc_849, end_r_851, Stk, SearchTree_T);
            
            GibChunk region_2314 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_930 = region_2314.start;
            GibCursor end_r_930 = region_2314.end;
            
            frame = gib_shadowstack_pop(wstack);
            loc_849 = frame->ptr;
            end_r_851 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tr_58_234_374 = frame->ptr;
            end_r_850 = frame->endptr;
            gib_shadowstack_push(wstack, loc_849, end_r_851, Stk, SearchTree_T);
            
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_12 =
                                                      tree_delete(end_r_850, end_r_930, r_930, tr_58_234_374, fltAppE_330_385);
            GibCursor pvrtmp_2315 = tmp_struct_12.field0;
            GibCursor pvrtmp_2316 = tmp_struct_12.field1;
            GibCursor pvrtmp_2317 = tmp_struct_12.field2;
            GibCursor pvrtmp_2318 = tmp_struct_12.field3;
            
            frame = gib_shadowstack_pop(wstack);
            loc_849 = frame->ptr;
            end_r_851 = frame->endptr;
            
            GibInt fltAppE_331_387 = n_59_235_375 - 1;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_13 =
                                                               loop(pvrtmp_2316, end_r_851, loc_849, pvrtmp_2317, fltAppE_331_387);
            GibCursor pvrtmp_2323 = tmp_struct_13.field0;
            GibCursor pvrtmp_2324 = tmp_struct_13.field1;
            GibCursor pvrtmp_2325 = tmp_struct_13.field2;
            GibCursor pvrtmp_2326 = tmp_struct_13.field3;
            GibCursor pvrtmp_2327 = tmp_struct_13.field4;
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2315,
                                                                        pvrtmp_2324,
                                                                        pvrtmp_2288,
                                                                        pvrtmp_2326,
                                                                        pvrtmp_2327};
        }
    }
}
GibCursorGibCursorGibIntProd countnodes(GibCursor end_r_853,
                                        GibCursor tr_89_238_388)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2334 = *(GibPackedTag *) tr_89_238_388;
    GibCursor tmpcur_2335 = tr_89_238_388 + 1;
    
    
  switch_2361:
    ;
    switch (tmpval_2334) {
        
      case 0:
        {
            GibCursor jump_1224 = tr_89_238_388 + 1;
            
            return (GibCursorGibCursorGibIntProd) {end_r_853, jump_1224, 0};
            break;
        }
        
      case 1:
        {
            GibInt tmpval_2336 = *(GibInt *) tmpcur_2335;
            GibCursor tmpcur_2337 = tmpcur_2335 + sizeof(GibInt);
            GibCursor jump_1225 = tmpcur_2335 + 8;
            
            return (GibCursorGibCursorGibIntProd) {end_r_853, jump_1225, 1};
            break;
        }
        
      case 3:
        {
            uintptr_t tagged_tmpcur_19 = *(uintptr_t *) tmpcur_2335;
            GibCursor tmpcur_2338 = GIB_UNTAG(tagged_tmpcur_19);
            GibCursor tmpaftercur_2339 = tmpcur_2335 + 8;
            uint16_t tmptag_2340 = GIB_GET_TAG(tagged_tmpcur_19);
            GibCursor end_from_tagged_absran_792 = tmpcur_2338 + tmptag_2340;
            GibInt tmpval_2341 = *(GibInt *) tmpaftercur_2339;
            GibCursor tmpcur_2342 = tmpaftercur_2339 + sizeof(GibInt);
            
            gib_shadowstack_push(rstack, tmpcur_2338, end_r_853, Stk,
                                 SearchTree_T);
            
            GibCursorGibCursorGibIntProd tmp_struct_17 =
                                          countnodes(end_r_853, tmpcur_2342);
            GibCursor pvrtmp_2343 = tmp_struct_17.field0;
            GibCursor pvrtmp_2344 = tmp_struct_17.field1;
            GibInt pvrtmp_2345 = tmp_struct_17.field2;
            
            frame = gib_shadowstack_pop(rstack);
            tmpcur_2338 = frame->ptr;
            end_r_853 = frame->endptr;
            
            GibCursorGibCursorGibIntProd tmp_struct_18 =
                                          countnodes(end_from_tagged_absran_792, tmpcur_2338);
            GibCursor pvrtmp_2346 = tmp_struct_18.field0;
            GibCursor pvrtmp_2347 = tmp_struct_18.field1;
            GibInt pvrtmp_2348 = tmp_struct_18.field2;
            GibInt fltPrm_332_395 = pvrtmp_2345 + pvrtmp_2348;
            GibInt tailprim_1230 = 1 + fltPrm_332_395;
            
            return (GibCursorGibCursorGibIntProd) {pvrtmp_2346, pvrtmp_2347,
                                                   tailprim_1230};
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_21 = *(uintptr_t *) tmpcur_2335;
            GibCursor tmpcur_2349 = GIB_UNTAG(tagged_tmpcur_21);
            GibCursor tmpaftercur_2350 = tmpcur_2335 + 8;
            uint16_t tmptag_2351 = GIB_GET_TAG(tagged_tmpcur_21);
            GibCursor end_from_tagged_indr_1312 = tmpcur_2349 + tmptag_2351;
            GibCursor jump_1314 = tmpcur_2335 + 8;
            GibCursorGibCursorGibIntProd tmp_struct_20 =
                                          countnodes(end_from_tagged_indr_1312, tmpcur_2349);
            GibCursor pvrtmp_2352 = tmp_struct_20.field0;
            GibCursor pvrtmp_2353 = tmp_struct_20.field1;
            GibInt pvrtmp_2354 = tmp_struct_20.field2;
            
            return (GibCursorGibCursorGibIntProd) {end_r_853, jump_1314,
                                                   pvrtmp_2354};
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_23 = *(uintptr_t *) tmpcur_2335;
            GibCursor tmpcur_2355 = GIB_UNTAG(tagged_tmpcur_23);
            GibCursor tmpaftercur_2356 = tmpcur_2335 + 8;
            uint16_t tmptag_2357 = GIB_GET_TAG(tagged_tmpcur_23);
            GibCursor end_from_tagged_indr_1312 = tmpcur_2355 + tmptag_2357;
            GibCursorGibCursorGibIntProd tmp_struct_22 =
                                          countnodes(end_from_tagged_indr_1312, tmpcur_2355);
            GibCursor pvrtmp_2358 = tmp_struct_22.field0;
            GibCursor pvrtmp_2359 = tmp_struct_22.field1;
            GibInt pvrtmp_2360 = tmp_struct_22.field2;
            
            return (GibCursorGibCursorGibIntProd) {pvrtmp_2358, pvrtmp_2359,
                                                   pvrtmp_2360};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2334");
            exit(1);
        }
    }
}
GibCursorGibCursorGibIntProd sum_tree(GibCursor end_r_855,
                                      GibCursor tr_62_243_396)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2362 = *(GibPackedTag *) tr_62_243_396;
    GibCursor tmpcur_2363 = tr_62_243_396 + 1;
    
    
  switch_2389:
    ;
    switch (tmpval_2362) {
        
      case 0:
        {
            GibCursor jump_1232 = tr_62_243_396 + 1;
            
            return (GibCursorGibCursorGibIntProd) {end_r_855, jump_1232, 0};
            break;
        }
        
      case 1:
        {
            GibInt tmpval_2364 = *(GibInt *) tmpcur_2363;
            GibCursor tmpcur_2365 = tmpcur_2363 + sizeof(GibInt);
            GibCursor jump_1233 = tmpcur_2363 + 8;
            
            return (GibCursorGibCursorGibIntProd) {end_r_855, jump_1233,
                                                   tmpval_2364};
            break;
        }
        
      case 3:
        {
            uintptr_t tagged_tmpcur_26 = *(uintptr_t *) tmpcur_2363;
            GibCursor tmpcur_2366 = GIB_UNTAG(tagged_tmpcur_26);
            GibCursor tmpaftercur_2367 = tmpcur_2363 + 8;
            uint16_t tmptag_2368 = GIB_GET_TAG(tagged_tmpcur_26);
            GibCursor end_from_tagged_absran_795 = tmpcur_2366 + tmptag_2368;
            GibInt tmpval_2369 = *(GibInt *) tmpaftercur_2367;
            GibCursor tmpcur_2370 = tmpaftercur_2367 + sizeof(GibInt);
            
            gib_shadowstack_push(rstack, tmpcur_2366, end_r_855, Stk,
                                 SearchTree_T);
            
            GibCursorGibCursorGibIntProd tmp_struct_24 =
                                          sum_tree(end_r_855, tmpcur_2370);
            GibCursor pvrtmp_2371 = tmp_struct_24.field0;
            GibCursor pvrtmp_2372 = tmp_struct_24.field1;
            GibInt pvrtmp_2373 = tmp_struct_24.field2;
            
            frame = gib_shadowstack_pop(rstack);
            tmpcur_2366 = frame->ptr;
            end_r_855 = frame->endptr;
            
            GibCursorGibCursorGibIntProd tmp_struct_25 =
                                          sum_tree(end_from_tagged_absran_795, tmpcur_2366);
            GibCursor pvrtmp_2374 = tmp_struct_25.field0;
            GibCursor pvrtmp_2375 = tmp_struct_25.field1;
            GibInt pvrtmp_2376 = tmp_struct_25.field2;
            GibInt fltPrm_335_403 = pvrtmp_2373 + pvrtmp_2376;
            GibInt tailprim_1238 = tmpval_2369 + fltPrm_335_403;
            
            return (GibCursorGibCursorGibIntProd) {pvrtmp_2374, pvrtmp_2375,
                                                   tailprim_1238};
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_28 = *(uintptr_t *) tmpcur_2363;
            GibCursor tmpcur_2377 = GIB_UNTAG(tagged_tmpcur_28);
            GibCursor tmpaftercur_2378 = tmpcur_2363 + 8;
            uint16_t tmptag_2379 = GIB_GET_TAG(tagged_tmpcur_28);
            GibCursor end_from_tagged_indr_1318 = tmpcur_2377 + tmptag_2379;
            GibCursor jump_1320 = tmpcur_2363 + 8;
            GibCursorGibCursorGibIntProd tmp_struct_27 =
                                          sum_tree(end_from_tagged_indr_1318, tmpcur_2377);
            GibCursor pvrtmp_2380 = tmp_struct_27.field0;
            GibCursor pvrtmp_2381 = tmp_struct_27.field1;
            GibInt pvrtmp_2382 = tmp_struct_27.field2;
            
            return (GibCursorGibCursorGibIntProd) {end_r_855, jump_1320,
                                                   pvrtmp_2382};
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_30 = *(uintptr_t *) tmpcur_2363;
            GibCursor tmpcur_2383 = GIB_UNTAG(tagged_tmpcur_30);
            GibCursor tmpaftercur_2384 = tmpcur_2363 + 8;
            uint16_t tmptag_2385 = GIB_GET_TAG(tagged_tmpcur_30);
            GibCursor end_from_tagged_indr_1318 = tmpcur_2383 + tmptag_2385;
            GibCursorGibCursorGibIntProd tmp_struct_29 =
                                          sum_tree(end_from_tagged_indr_1318, tmpcur_2383);
            GibCursor pvrtmp_2386 = tmp_struct_29.field0;
            GibCursor pvrtmp_2387 = tmp_struct_29.field1;
            GibInt pvrtmp_2388 = tmp_struct_29.field2;
            
            return (GibCursorGibCursorGibIntProd) {pvrtmp_2386, pvrtmp_2387,
                                                   pvrtmp_2388};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2362");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd tree_delete(GibCursor end_r_858,
                                                     GibCursor end_r_859,
                                                     GibCursor loc_857,
                                                     GibCursor tr_67_248_404,
                                                     GibInt n_68_249_405)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    
    if (loc_857 + 26 > end_r_859) {
        gib_grow_region(&loc_857, &end_r_859);
    }
    
    GibPackedTag tmpval_2390 = *(GibPackedTag *) tr_67_248_404;
    GibCursor tmpcur_2391 = tr_67_248_404 + 1;
    
    
  switch_2481:
    ;
    switch (tmpval_2390) {
        
      case 0:
        {
            *(GibPackedTag *) loc_857 = 1;
            
            GibCursor writetag_1563 = loc_857 + 1;
            GibCursor after_tag_1564 = loc_857 + 1;
            
            *(GibInt *) after_tag_1564 = n_68_249_405;
            
            GibCursor writecur_1568 = after_tag_1564 + sizeof(GibInt);
            
            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_858,
                                                               end_r_859,
                                                               loc_857,
                                                               writecur_1568};
            break;
        }
        
      case 1:
        {
            GibInt tmpval_2396 = *(GibInt *) tmpcur_2391;
            GibCursor tmpcur_2397 = tmpcur_2391 + sizeof(GibInt);
            GibBool fltIf_338_407 = tmpval_2396 == n_68_249_405;
            
            if (fltIf_338_407) {
                *(GibPackedTag *) loc_857 = 0;
                
                GibCursor writetag_1573 = loc_857 + 1;
                GibCursor after_tag_1574 = loc_857 + 1;
                
                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_858,
                                                                   end_r_859,
                                                                   loc_857,
                                                                   after_tag_1574};
            } else {
                *(GibPackedTag *) loc_857 = 1;
                
                GibCursor writetag_1580 = loc_857 + 1;
                GibCursor after_tag_1581 = loc_857 + 1;
                
                *(GibInt *) after_tag_1581 = tmpval_2396;
                
                GibCursor writecur_1585 = after_tag_1581 + sizeof(GibInt);
                
                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_858,
                                                                   end_r_859,
                                                                   loc_857,
                                                                   writecur_1585};
            }
            break;
        }
        
      case 3:
        {
            uintptr_t tagged_tmpcur_47 = *(uintptr_t *) tmpcur_2391;
            GibCursor tmpcur_2406 = GIB_UNTAG(tagged_tmpcur_47);
            GibCursor tmpaftercur_2407 = tmpcur_2391 + 8;
            uint16_t tmptag_2408 = GIB_GET_TAG(tagged_tmpcur_47);
            GibCursor end_from_tagged_absran_801 = tmpcur_2406 + tmptag_2408;
            GibInt tmpval_2409 = *(GibInt *) tmpaftercur_2407;
            GibCursor tmpcur_2410 = tmpaftercur_2407 + sizeof(GibInt);
            GibBool fltIf_339_411 = tmpval_2409 == n_68_249_405;
            
            if (fltIf_339_411) {
                gib_shadowstack_push(rstack, tmpcur_2406, end_r_858, Stk,
                                     SearchTree_T);
                gib_shadowstack_push(rstack, tmpcur_2410, end_r_858, Stk,
                                     SearchTree_T);
                gib_shadowstack_push(wstack, loc_857, end_r_859, Stk,
                                     SearchTree_T);
                
                GibCursorGibIntProd tmp_struct_31 =
                                     min_tree(end_from_tagged_absran_801, tmpcur_2406);
                GibCursor pvrtmp_2411 = tmp_struct_31.field0;
                GibInt pvrtmp_2412 = tmp_struct_31.field1;
                
                frame = gib_shadowstack_pop(wstack);
                loc_857 = frame->ptr;
                end_r_859 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                tmpcur_2410 = frame->ptr;
                end_r_858 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                tmpcur_2406 = frame->ptr;
                end_r_858 = frame->endptr;
                
                GibCursor loc_977 = loc_857 + 17;
                
                *(GibPackedTag *) loc_857 = 3;
                
                GibCursor writetag_1599 = loc_857 + 1;
                
                if (loc_977 + 18 > end_r_859) {
                    gib_grow_region(&loc_977, &end_r_859);
                }
                gib_indirection_barrier(loc_977, end_r_859, tmpcur_2410,
                                        end_r_858, SearchTree_T);
                
                GibCursor end_1594 = loc_977 + 9;
                
                gib_shadowstack_push(rstack, loc_857, end_r_859, Stk,
                                     SearchTree_T);
                
                GibCursorGibCursorGibCursorGibCursorProd tmp_struct_32 =
                                                          tree_delete(end_from_tagged_absran_801, end_r_859, end_1594, tmpcur_2406, pvrtmp_2412);
                GibCursor pvrtmp_2415 = tmp_struct_32.field0;
                GibCursor pvrtmp_2416 = tmp_struct_32.field1;
                GibCursor pvrtmp_2417 = tmp_struct_32.field2;
                GibCursor pvrtmp_2418 = tmp_struct_32.field3;
                
                frame = gib_shadowstack_pop(rstack);
                loc_857 = frame->ptr;
                end_r_859 = frame->endptr;
                
                uint16_t offset_33 = end_r_859 - end_1594;
                uintptr_t ran_804 = GIB_STORE_TAG(end_1594, offset_33);
                GibCursor after_tag_1600 = loc_857 + 1;
                
                *(uintptr_t *) after_tag_1600 = ran_804;
                
                GibCursor writecur_1604 = after_tag_1600 + 8;
                
                *(GibInt *) writecur_1604 = pvrtmp_2412;
                
                GibCursor writecur_1605 = writecur_1604 + sizeof(GibInt);
                
                return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2415,
                                                                   pvrtmp_2416,
                                                                   loc_857,
                                                                   pvrtmp_2418};
            } else {
                GibBool fltIf_342_415 = tmpval_2409 < n_68_249_405;
                
                if (fltIf_342_415) {
                    GibCursor loc_993 = loc_857 + 17;
                    
                    *(GibPackedTag *) loc_857 = 3;
                    
                    GibCursor writetag_1617 = loc_857 + 1;
                    
                    if (loc_993 + 18 > end_r_859) {
                        gib_grow_region(&loc_993, &end_r_859);
                    }
                    gib_indirection_barrier(loc_993, end_r_859, tmpcur_2410,
                                            end_r_858, SearchTree_T);
                    
                    GibCursor end_1612 = loc_993 + 9;
                    
                    gib_shadowstack_push(rstack, loc_857, end_r_859, Stk,
                                         SearchTree_T);
                    
                    GibCursorGibCursorGibCursorGibCursorProd tmp_struct_37 =
                                                              tree_delete(end_from_tagged_absran_801, end_r_859, end_1612, tmpcur_2406, n_68_249_405);
                    GibCursor pvrtmp_2429 = tmp_struct_37.field0;
                    GibCursor pvrtmp_2430 = tmp_struct_37.field1;
                    GibCursor pvrtmp_2431 = tmp_struct_37.field2;
                    GibCursor pvrtmp_2432 = tmp_struct_37.field3;
                    
                    frame = gib_shadowstack_pop(rstack);
                    loc_857 = frame->ptr;
                    end_r_859 = frame->endptr;
                    
                    uint16_t offset_38 = end_r_859 - end_1612;
                    uintptr_t ran_805 = GIB_STORE_TAG(end_1612, offset_38);
                    GibCursor after_tag_1618 = loc_857 + 1;
                    
                    *(uintptr_t *) after_tag_1618 = ran_805;
                    
                    GibCursor writecur_1622 = after_tag_1618 + 8;
                    
                    *(GibInt *) writecur_1622 = tmpval_2409;
                    
                    GibCursor writecur_1623 = writecur_1622 + sizeof(GibInt);
                    
                    return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2429,
                                                                       pvrtmp_2430,
                                                                       loc_857,
                                                                       pvrtmp_2432};
                } else {
                    GibCursor loc_1009 = loc_857 + 17;
                    
                    *(GibPackedTag *) loc_857 = 3;
                    
                    GibCursor writetag_1635 = loc_857 + 1;
                    
                    gib_shadowstack_push(rstack, loc_857, end_r_859, Stk,
                                         SearchTree_T);
                    gib_shadowstack_push(rstack, tmpcur_2406, end_r_858, Stk,
                                         SearchTree_T);
                    
                    GibCursorGibCursorGibCursorGibCursorProd tmp_struct_42 =
                                                              tree_delete(end_r_858, end_r_859, loc_1009, tmpcur_2410, n_68_249_405);
                    GibCursor pvrtmp_2441 = tmp_struct_42.field0;
                    GibCursor pvrtmp_2442 = tmp_struct_42.field1;
                    GibCursor pvrtmp_2443 = tmp_struct_42.field2;
                    GibCursor pvrtmp_2444 = tmp_struct_42.field3;
                    
                    frame = gib_shadowstack_pop(rstack);
                    tmpcur_2406 = frame->ptr;
                    end_r_858 = frame->endptr;
                    frame = gib_shadowstack_pop(rstack);
                    loc_857 = frame->ptr;
                    end_r_859 = frame->endptr;
                    if (pvrtmp_2444 + 18 > pvrtmp_2442) {
                        gib_grow_region(&pvrtmp_2444, &pvrtmp_2442);
                    }
                    gib_indirection_barrier(pvrtmp_2444, pvrtmp_2442,
                                            tmpcur_2406,
                                            end_from_tagged_absran_801,
                                            SearchTree_T);
                    
                    GibCursor end_1633 = pvrtmp_2444 + 9;
                    uint16_t offset_43 = pvrtmp_2442 - pvrtmp_2444;
                    uintptr_t ran_806 = GIB_STORE_TAG(pvrtmp_2444, offset_43);
                    GibCursor after_tag_1636 = loc_857 + 1;
                    
                    *(uintptr_t *) after_tag_1636 = ran_806;
                    
                    GibCursor writecur_1640 = after_tag_1636 + 8;
                    
                    *(GibInt *) writecur_1640 = tmpval_2409;
                    
                    GibCursor writecur_1641 = writecur_1640 + sizeof(GibInt);
                    
                    return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2441,
                                                                       pvrtmp_2442,
                                                                       loc_857,
                                                                       end_1633};
                }
            }
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_49 = *(uintptr_t *) tmpcur_2391;
            GibCursor tmpcur_2455 = GIB_UNTAG(tagged_tmpcur_49);
            GibCursor tmpaftercur_2456 = tmpcur_2391 + 8;
            uint16_t tmptag_2457 = GIB_GET_TAG(tagged_tmpcur_49);
            GibCursor end_from_tagged_indr_1324 = tmpcur_2455 + tmptag_2457;
            GibCursor jump_1326 = tmpcur_2391 + 8;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_48 =
                                                      tree_delete(end_from_tagged_indr_1324, end_r_859, loc_857, tmpcur_2455, n_68_249_405);
            GibCursor pvrtmp_2458 = tmp_struct_48.field0;
            GibCursor pvrtmp_2459 = tmp_struct_48.field1;
            GibCursor pvrtmp_2460 = tmp_struct_48.field2;
            GibCursor pvrtmp_2461 = tmp_struct_48.field3;
            
            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_858,
                                                               pvrtmp_2459,
                                                               pvrtmp_2460,
                                                               pvrtmp_2461};
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_51 = *(uintptr_t *) tmpcur_2391;
            GibCursor tmpcur_2468 = GIB_UNTAG(tagged_tmpcur_51);
            GibCursor tmpaftercur_2469 = tmpcur_2391 + 8;
            uint16_t tmptag_2470 = GIB_GET_TAG(tagged_tmpcur_51);
            GibCursor end_from_tagged_indr_1324 = tmpcur_2468 + tmptag_2470;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_50 =
                                                      tree_delete(end_from_tagged_indr_1324, end_r_859, loc_857, tmpcur_2468, n_68_249_405);
            GibCursor pvrtmp_2471 = tmp_struct_50.field0;
            GibCursor pvrtmp_2472 = tmp_struct_50.field1;
            GibCursor pvrtmp_2473 = tmp_struct_50.field2;
            GibCursor pvrtmp_2474 = tmp_struct_50.field3;
            
            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2471,
                                                               pvrtmp_2472,
                                                               pvrtmp_2473,
                                                               pvrtmp_2474};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2390");
            exit(1);
        }
    }
}
GibCursorGibIntProd min_tree(GibCursor end_r_861, GibCursor tr_74_255_420)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2482 = *(GibPackedTag *) tr_74_255_420;
    GibCursor tmpcur_2483 = tr_74_255_420 + 1;
    
    
  switch_2503:
    ;
    switch (tmpval_2482) {
        
      case 0:
        {
            return (GibCursorGibIntProd) {end_r_861, 0};
            break;
        }
        
      case 1:
        {
            GibInt tmpval_2484 = *(GibInt *) tmpcur_2483;
            GibCursor tmpcur_2485 = tmpcur_2483 + sizeof(GibInt);
            
            return (GibCursorGibIntProd) {end_r_861, tmpval_2484};
            break;
        }
        
      case 3:
        {
            uintptr_t tagged_tmpcur_56 = *(uintptr_t *) tmpcur_2483;
            GibCursor tmpcur_2486 = GIB_UNTAG(tagged_tmpcur_56);
            GibCursor tmpaftercur_2487 = tmpcur_2483 + 8;
            uint16_t tmptag_2488 = GIB_GET_TAG(tagged_tmpcur_56);
            GibCursor end_from_tagged_absran_810 = tmpcur_2486 + tmptag_2488;
            GibInt tmpval_2489 = *(GibInt *) tmpaftercur_2487;
            GibCursor tmpcur_2490 = tmpaftercur_2487 + sizeof(GibInt);
            GibCursorGibIntProd tmp_struct_55 =
                                 caseFn_224(end_r_861, tmpcur_2490, tmpval_2489);
            GibCursor pvrtmp_2491 = tmp_struct_55.field0;
            GibInt pvrtmp_2492 = tmp_struct_55.field1;
            
            return (GibCursorGibIntProd) {pvrtmp_2491, pvrtmp_2492};
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_58 = *(uintptr_t *) tmpcur_2483;
            GibCursor tmpcur_2493 = GIB_UNTAG(tagged_tmpcur_58);
            GibCursor tmpaftercur_2494 = tmpcur_2483 + 8;
            uint16_t tmptag_2495 = GIB_GET_TAG(tagged_tmpcur_58);
            GibCursor end_from_tagged_indr_1329 = tmpcur_2493 + tmptag_2495;
            GibCursor jump_1331 = tmpcur_2483 + 8;
            GibCursorGibIntProd tmp_struct_57 =
                                 min_tree(end_from_tagged_indr_1329, tmpcur_2493);
            GibCursor pvrtmp_2496 = tmp_struct_57.field0;
            GibInt pvrtmp_2497 = tmp_struct_57.field1;
            
            return (GibCursorGibIntProd) {end_r_861, pvrtmp_2497};
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_60 = *(uintptr_t *) tmpcur_2483;
            GibCursor tmpcur_2498 = GIB_UNTAG(tagged_tmpcur_60);
            GibCursor tmpaftercur_2499 = tmpcur_2483 + 8;
            uint16_t tmptag_2500 = GIB_GET_TAG(tagged_tmpcur_60);
            GibCursor end_from_tagged_indr_1329 = tmpcur_2498 + tmptag_2500;
            GibCursorGibIntProd tmp_struct_59 =
                                 min_tree(end_from_tagged_indr_1329, tmpcur_2498);
            GibCursor pvrtmp_2501 = tmp_struct_59.field0;
            GibInt pvrtmp_2502 = tmp_struct_59.field1;
            
            return (GibCursorGibIntProd) {pvrtmp_2501, pvrtmp_2502};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2482");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd tree_insert(GibCursor end_r_864,
                                                     GibCursor end_r_865,
                                                     GibCursor loc_863,
                                                     GibCursor tr_83_260_425,
                                                     GibInt n_84_261_426)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    
    if (loc_863 + 26 > end_r_865) {
        gib_grow_region(&loc_863, &end_r_865);
    }
    
    GibPackedTag tmpval_2504 = *(GibPackedTag *) tr_83_260_425;
    GibCursor tmpcur_2505 = tr_83_260_425 + 1;
    
    
  switch_2587:
    ;
    switch (tmpval_2504) {
        
      case 0:
        {
            *(GibPackedTag *) loc_863 = 1;
            
            GibCursor writetag_1674 = loc_863 + 1;
            GibCursor after_tag_1675 = loc_863 + 1;
            
            *(GibInt *) after_tag_1675 = n_84_261_426;
            
            GibCursor writecur_1679 = after_tag_1675 + sizeof(GibInt);
            
            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_864,
                                                               end_r_865,
                                                               loc_863,
                                                               writecur_1679};
            break;
        }
        
      case 1:
        {
            GibInt tmpval_2510 = *(GibInt *) tmpcur_2505;
            GibCursor tmpcur_2511 = tmpcur_2505 + sizeof(GibInt);
            GibBool fltIf_347_428 = n_84_261_426 < tmpval_2510;
            
            if (fltIf_347_428) {
                GibCursor loc_1043 = loc_863 + 17;
                
                *(GibPackedTag *) loc_863 = 3;
                
                GibCursor writetag_1699 = loc_863 + 1;
                
                *(GibPackedTag *) loc_1043 = 1;
                
                GibCursor writetag_1684 = loc_1043 + 1;
                GibCursor after_tag_1685 = loc_1043 + 1;
                
                *(GibInt *) after_tag_1685 = n_84_261_426;
                
                GibCursor writecur_1689 = after_tag_1685 + sizeof(GibInt);
                
                *(GibPackedTag *) writecur_1689 = 0;
                
                GibCursor writetag_1692 = writecur_1689 + 1;
                GibCursor after_tag_1693 = writecur_1689 + 1;
                uint16_t offset_61 = end_r_865 - writecur_1689;
                uintptr_t ran_813 = GIB_STORE_TAG(writecur_1689, offset_61);
                GibCursor after_tag_1700 = loc_863 + 1;
                
                *(uintptr_t *) after_tag_1700 = ran_813;
                
                GibCursor writecur_1704 = after_tag_1700 + 8;
                
                *(GibInt *) writecur_1704 = tmpval_2510;
                
                GibCursor writecur_1705 = writecur_1704 + sizeof(GibInt);
                
                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_864,
                                                                   end_r_865,
                                                                   loc_863,
                                                                   after_tag_1693};
            } else {
                GibCursor loc_1059 = loc_863 + 17;
                
                *(GibPackedTag *) loc_863 = 3;
                
                GibCursor writetag_1726 = loc_863 + 1;
                
                *(GibPackedTag *) loc_1059 = 0;
                
                GibCursor writetag_1711 = loc_1059 + 1;
                GibCursor after_tag_1712 = loc_1059 + 1;
                
                *(GibPackedTag *) after_tag_1712 = 1;
                
                GibCursor writetag_1718 = after_tag_1712 + 1;
                GibCursor after_tag_1719 = after_tag_1712 + 1;
                
                *(GibInt *) after_tag_1719 = n_84_261_426;
                
                GibCursor writecur_1723 = after_tag_1719 + sizeof(GibInt);
                uint16_t offset_62 = end_r_865 - after_tag_1712;
                uintptr_t ran_814 = GIB_STORE_TAG(after_tag_1712, offset_62);
                GibCursor after_tag_1727 = loc_863 + 1;
                
                *(uintptr_t *) after_tag_1727 = ran_814;
                
                GibCursor writecur_1731 = after_tag_1727 + 8;
                
                *(GibInt *) writecur_1731 = tmpval_2510;
                
                GibCursor writecur_1732 = writecur_1731 + sizeof(GibInt);
                
                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_864,
                                                                   end_r_865,
                                                                   loc_863,
                                                                   writecur_1723};
            }
            break;
        }
        
      case 3:
        {
            uintptr_t tagged_tmpcur_73 = *(uintptr_t *) tmpcur_2505;
            GibCursor tmpcur_2528 = GIB_UNTAG(tagged_tmpcur_73);
            GibCursor tmpaftercur_2529 = tmpcur_2505 + 8;
            uint16_t tmptag_2530 = GIB_GET_TAG(tagged_tmpcur_73);
            GibCursor end_from_tagged_absran_817 = tmpcur_2528 + tmptag_2530;
            GibInt tmpval_2531 = *(GibInt *) tmpaftercur_2529;
            GibCursor tmpcur_2532 = tmpaftercur_2529 + sizeof(GibInt);
            GibBool fltIf_352_436 = tmpval_2531 < n_84_261_426;
            
            if (fltIf_352_436) {
                GibCursor loc_1079 = loc_863 + 17;
                
                *(GibPackedTag *) loc_863 = 3;
                
                GibCursor writetag_1747 = loc_863 + 1;
                
                if (loc_1079 + 18 > end_r_865) {
                    gib_grow_region(&loc_1079, &end_r_865);
                }
                gib_indirection_barrier(loc_1079, end_r_865, tmpcur_2532,
                                        end_r_864, SearchTree_T);
                
                GibCursor end_1742 = loc_1079 + 9;
                
                gib_shadowstack_push(rstack, loc_863, end_r_865, Stk,
                                     SearchTree_T);
                
                GibCursorGibCursorGibCursorGibCursorProd tmp_struct_63 =
                                                          tree_insert(end_from_tagged_absran_817, end_r_865, end_1742, tmpcur_2528, n_84_261_426);
                GibCursor pvrtmp_2535 = tmp_struct_63.field0;
                GibCursor pvrtmp_2536 = tmp_struct_63.field1;
                GibCursor pvrtmp_2537 = tmp_struct_63.field2;
                GibCursor pvrtmp_2538 = tmp_struct_63.field3;
                
                frame = gib_shadowstack_pop(rstack);
                loc_863 = frame->ptr;
                end_r_865 = frame->endptr;
                
                uint16_t offset_64 = end_r_865 - end_1742;
                uintptr_t ran_820 = GIB_STORE_TAG(end_1742, offset_64);
                GibCursor after_tag_1748 = loc_863 + 1;
                
                *(uintptr_t *) after_tag_1748 = ran_820;
                
                GibCursor writecur_1752 = after_tag_1748 + 8;
                
                *(GibInt *) writecur_1752 = tmpval_2531;
                
                GibCursor writecur_1753 = writecur_1752 + sizeof(GibInt);
                
                return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2535,
                                                                   pvrtmp_2536,
                                                                   loc_863,
                                                                   pvrtmp_2538};
            } else {
                GibCursor loc_1095 = loc_863 + 17;
                
                *(GibPackedTag *) loc_863 = 3;
                
                GibCursor writetag_1765 = loc_863 + 1;
                
                gib_shadowstack_push(rstack, loc_863, end_r_865, Stk,
                                     SearchTree_T);
                gib_shadowstack_push(rstack, tmpcur_2528, end_r_864, Stk,
                                     SearchTree_T);
                
                GibCursorGibCursorGibCursorGibCursorProd tmp_struct_68 =
                                                          tree_insert(end_r_864, end_r_865, loc_1095, tmpcur_2532, n_84_261_426);
                GibCursor pvrtmp_2547 = tmp_struct_68.field0;
                GibCursor pvrtmp_2548 = tmp_struct_68.field1;
                GibCursor pvrtmp_2549 = tmp_struct_68.field2;
                GibCursor pvrtmp_2550 = tmp_struct_68.field3;
                
                frame = gib_shadowstack_pop(rstack);
                tmpcur_2528 = frame->ptr;
                end_r_864 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                loc_863 = frame->ptr;
                end_r_865 = frame->endptr;
                if (pvrtmp_2550 + 18 > pvrtmp_2548) {
                    gib_grow_region(&pvrtmp_2550, &pvrtmp_2548);
                }
                gib_indirection_barrier(pvrtmp_2550, pvrtmp_2548, tmpcur_2528,
                                        end_from_tagged_absran_817,
                                        SearchTree_T);
                
                GibCursor end_1763 = pvrtmp_2550 + 9;
                uint16_t offset_69 = pvrtmp_2548 - pvrtmp_2550;
                uintptr_t ran_821 = GIB_STORE_TAG(pvrtmp_2550, offset_69);
                GibCursor after_tag_1766 = loc_863 + 1;
                
                *(uintptr_t *) after_tag_1766 = ran_821;
                
                GibCursor writecur_1770 = after_tag_1766 + 8;
                
                *(GibInt *) writecur_1770 = tmpval_2531;
                
                GibCursor writecur_1771 = writecur_1770 + sizeof(GibInt);
                
                return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2547,
                                                                   pvrtmp_2548,
                                                                   loc_863,
                                                                   end_1763};
            }
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_75 = *(uintptr_t *) tmpcur_2505;
            GibCursor tmpcur_2561 = GIB_UNTAG(tagged_tmpcur_75);
            GibCursor tmpaftercur_2562 = tmpcur_2505 + 8;
            uint16_t tmptag_2563 = GIB_GET_TAG(tagged_tmpcur_75);
            GibCursor end_from_tagged_indr_1334 = tmpcur_2561 + tmptag_2563;
            GibCursor jump_1336 = tmpcur_2505 + 8;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_74 =
                                                      tree_insert(end_from_tagged_indr_1334, end_r_865, loc_863, tmpcur_2561, n_84_261_426);
            GibCursor pvrtmp_2564 = tmp_struct_74.field0;
            GibCursor pvrtmp_2565 = tmp_struct_74.field1;
            GibCursor pvrtmp_2566 = tmp_struct_74.field2;
            GibCursor pvrtmp_2567 = tmp_struct_74.field3;
            
            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_864,
                                                               pvrtmp_2565,
                                                               pvrtmp_2566,
                                                               pvrtmp_2567};
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_77 = *(uintptr_t *) tmpcur_2505;
            GibCursor tmpcur_2574 = GIB_UNTAG(tagged_tmpcur_77);
            GibCursor tmpaftercur_2575 = tmpcur_2505 + 8;
            uint16_t tmptag_2576 = GIB_GET_TAG(tagged_tmpcur_77);
            GibCursor end_from_tagged_indr_1334 = tmpcur_2574 + tmptag_2576;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_76 =
                                                      tree_insert(end_from_tagged_indr_1334, end_r_865, loc_863, tmpcur_2574, n_84_261_426);
            GibCursor pvrtmp_2577 = tmp_struct_76.field0;
            GibCursor pvrtmp_2578 = tmp_struct_76.field1;
            GibCursor pvrtmp_2579 = tmp_struct_76.field2;
            GibCursor pvrtmp_2580 = tmp_struct_76.field3;
            
            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2577,
                                                               pvrtmp_2578,
                                                               pvrtmp_2579,
                                                               pvrtmp_2580};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2504");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_SearchTree(GibCursor end_r_868,
                                                                   GibCursor end_r_869,
                                                                   GibCursor loc_867,
                                                                   GibCursor arg_182_266_441)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    
    if (loc_867 + 26 > end_r_869) {
        gib_grow_region(&loc_867, &end_r_869);
    }
    
    GibPackedTag tmpval_2588 = *(GibPackedTag *) arg_182_266_441;
    GibCursor tmpcur_2589 = arg_182_266_441 + 1;
    
    
  switch_2655:
    ;
    switch (tmpval_2588) {
        
      case 0:
        {
            GibCursor jump_1264 = arg_182_266_441 + 1;
            
            *(GibPackedTag *) loc_867 = 0;
            
            GibCursor writetag_1788 = loc_867 + 1;
            GibCursor after_tag_1789 = loc_867 + 1;
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_868,
                                                                        end_r_869,
                                                                        jump_1264,
                                                                        loc_867,
                                                                        after_tag_1789};
            break;
        }
        
      case 1:
        {
            GibInt tmpval_2594 = *(GibInt *) tmpcur_2589;
            GibCursor tmpcur_2595 = tmpcur_2589 + sizeof(GibInt);
            GibCursor jump_1266 = tmpcur_2589 + 8;
            
            *(GibPackedTag *) loc_867 = 1;
            
            GibCursor writetag_1797 = loc_867 + 1;
            GibCursor after_tag_1798 = loc_867 + 1;
            
            *(GibInt *) after_tag_1798 = tmpval_2594;
            
            GibCursor writecur_1802 = after_tag_1798 + sizeof(GibInt);
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_868,
                                                                        end_r_869,
                                                                        jump_1266,
                                                                        loc_867,
                                                                        writecur_1802};
            break;
        }
        
      case 3:
        {
            uintptr_t tagged_tmpcur_84 = *(uintptr_t *) tmpcur_2589;
            GibCursor tmpcur_2600 = GIB_UNTAG(tagged_tmpcur_84);
            GibCursor tmpaftercur_2601 = tmpcur_2589 + 8;
            uint16_t tmptag_2602 = GIB_GET_TAG(tagged_tmpcur_84);
            GibCursor end_from_tagged_absran_825 = tmpcur_2600 + tmptag_2602;
            GibInt tmpval_2603 = *(GibInt *) tmpaftercur_2601;
            GibCursor tmpcur_2604 = tmpaftercur_2601 + sizeof(GibInt);
            GibCursor loc_1126 = loc_867 + 17;
            
            *(GibPackedTag *) loc_867 = 3;
            
            GibCursor writetag_1814 = loc_867 + 1;
            
            gib_shadowstack_push(rstack, loc_867, end_r_869, Stk, SearchTree_T);
            gib_shadowstack_push(rstack, tmpcur_2600, end_r_868, Stk,
                                 SearchTree_T);
            
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_81 =
                                                               _copy_SearchTree(end_r_868, end_r_869, loc_1126, tmpcur_2604);
            GibCursor pvrtmp_2605 = tmp_struct_81.field0;
            GibCursor pvrtmp_2606 = tmp_struct_81.field1;
            GibCursor pvrtmp_2607 = tmp_struct_81.field2;
            GibCursor pvrtmp_2608 = tmp_struct_81.field3;
            GibCursor pvrtmp_2609 = tmp_struct_81.field4;
            
            frame = gib_shadowstack_pop(rstack);
            tmpcur_2600 = frame->ptr;
            end_r_868 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_867 = frame->ptr;
            end_r_869 = frame->endptr;
            gib_shadowstack_push(rstack, loc_867, pvrtmp_2606, Stk,
                                 SearchTree_T);
            
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_82 =
                                                               _copy_SearchTree(end_from_tagged_absran_825, pvrtmp_2606, pvrtmp_2609, tmpcur_2600);
            GibCursor pvrtmp_2614 = tmp_struct_82.field0;
            GibCursor pvrtmp_2615 = tmp_struct_82.field1;
            GibCursor pvrtmp_2616 = tmp_struct_82.field2;
            GibCursor pvrtmp_2617 = tmp_struct_82.field3;
            GibCursor pvrtmp_2618 = tmp_struct_82.field4;
            
            frame = gib_shadowstack_pop(rstack);
            loc_867 = frame->ptr;
            pvrtmp_2606 = frame->endptr;
            
            uint16_t offset_83 = pvrtmp_2606 - pvrtmp_2609;
            uintptr_t ran_828 = GIB_STORE_TAG(pvrtmp_2609, offset_83);
            GibCursor after_tag_1815 = loc_867 + 1;
            
            *(uintptr_t *) after_tag_1815 = ran_828;
            
            GibCursor writecur_1819 = after_tag_1815 + 8;
            
            *(GibInt *) writecur_1819 = tmpval_2603;
            
            GibCursor writecur_1820 = writecur_1819 + sizeof(GibInt);
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2614,
                                                                        pvrtmp_2615,
                                                                        pvrtmp_2616,
                                                                        loc_867,
                                                                        pvrtmp_2618};
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_86 = *(uintptr_t *) tmpcur_2589;
            GibCursor tmpcur_2627 = GIB_UNTAG(tagged_tmpcur_86);
            GibCursor tmpaftercur_2628 = tmpcur_2589 + 8;
            uint16_t tmptag_2629 = GIB_GET_TAG(tagged_tmpcur_86);
            GibCursor end_from_tagged_indr_1339 = tmpcur_2627 + tmptag_2629;
            GibCursor jump_1341 = tmpcur_2589 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_85 =
                                                               _copy_SearchTree(end_from_tagged_indr_1339, end_r_869, loc_867, tmpcur_2627);
            GibCursor pvrtmp_2630 = tmp_struct_85.field0;
            GibCursor pvrtmp_2631 = tmp_struct_85.field1;
            GibCursor pvrtmp_2632 = tmp_struct_85.field2;
            GibCursor pvrtmp_2633 = tmp_struct_85.field3;
            GibCursor pvrtmp_2634 = tmp_struct_85.field4;
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_868,
                                                                        pvrtmp_2631,
                                                                        jump_1341,
                                                                        pvrtmp_2633,
                                                                        pvrtmp_2634};
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_88 = *(uintptr_t *) tmpcur_2589;
            GibCursor tmpcur_2641 = GIB_UNTAG(tagged_tmpcur_88);
            GibCursor tmpaftercur_2642 = tmpcur_2589 + 8;
            uint16_t tmptag_2643 = GIB_GET_TAG(tagged_tmpcur_88);
            GibCursor end_from_tagged_indr_1339 = tmpcur_2641 + tmptag_2643;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_87 =
                                                               _copy_SearchTree(end_from_tagged_indr_1339, end_r_869, loc_867, tmpcur_2641);
            GibCursor pvrtmp_2644 = tmp_struct_87.field0;
            GibCursor pvrtmp_2645 = tmp_struct_87.field1;
            GibCursor pvrtmp_2646 = tmp_struct_87.field2;
            GibCursor pvrtmp_2647 = tmp_struct_87.field3;
            GibCursor pvrtmp_2648 = tmp_struct_87.field4;
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2644,
                                                                        pvrtmp_2645,
                                                                        pvrtmp_2646,
                                                                        pvrtmp_2647,
                                                                        pvrtmp_2648};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2588");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_SearchTree(GibCursor end_r_872,
                                                                                GibCursor end_r_873,
                                                                                GibCursor loc_871,
                                                                                GibCursor arg_191_275_450)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2656 = *(GibPackedTag *) arg_191_275_450;
    GibCursor tmpcur_2657 = arg_191_275_450 + 1;
    
    
  switch_2723:
    ;
    switch (tmpval_2656) {
        
      case 0:
        {
            GibCursor jump_1273 = arg_191_275_450 + 1;
            
            *(GibPackedTag *) loc_871 = 0;
            
            GibCursor writetag_1837 = loc_871 + 1;
            GibCursor after_tag_1838 = loc_871 + 1;
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_872,
                                                                        end_r_873,
                                                                        jump_1273,
                                                                        loc_871,
                                                                        after_tag_1838};
            break;
        }
        
      case 1:
        {
            GibInt tmpval_2662 = *(GibInt *) tmpcur_2657;
            GibCursor tmpcur_2663 = tmpcur_2657 + sizeof(GibInt);
            GibCursor jump_1275 = tmpcur_2657 + 8;
            
            *(GibPackedTag *) loc_871 = 1;
            
            GibCursor writetag_1846 = loc_871 + 1;
            GibCursor after_tag_1847 = loc_871 + 1;
            
            *(GibInt *) after_tag_1847 = tmpval_2662;
            
            GibCursor writecur_1851 = after_tag_1847 + sizeof(GibInt);
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_872,
                                                                        end_r_873,
                                                                        jump_1275,
                                                                        loc_871,
                                                                        writecur_1851};
            break;
        }
        
      case 3:
        {
            uintptr_t tagged_tmpcur_94 = *(uintptr_t *) tmpcur_2657;
            GibCursor tmpcur_2668 = GIB_UNTAG(tagged_tmpcur_94);
            GibCursor tmpaftercur_2669 = tmpcur_2657 + 8;
            uint16_t tmptag_2670 = GIB_GET_TAG(tagged_tmpcur_94);
            GibCursor end_from_tagged_absran_830 = tmpcur_2668 + tmptag_2670;
            GibInt tmpval_2671 = *(GibInt *) tmpaftercur_2669;
            GibCursor tmpcur_2672 = tmpaftercur_2669 + sizeof(GibInt);
            GibCursor loc_1153 = loc_871 + 9;
            
            *(GibPackedTag *) loc_871 = 2;
            
            GibCursor writetag_1863 = loc_871 + 1;
            GibCursor after_tag_1864 = loc_871 + 1;
            
            *(GibInt *) after_tag_1864 = tmpval_2671;
            
            GibCursor writecur_1868 = after_tag_1864 + sizeof(GibInt);
            
            gib_shadowstack_push(rstack, loc_871, end_r_873, Stk, SearchTree_T);
            gib_shadowstack_push(rstack, tmpcur_2668, end_r_872, Stk,
                                 SearchTree_T);
            
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_92 =
                                                               _copy_without_ptrs_SearchTree(end_r_872, end_r_873, loc_1153, tmpcur_2672);
            GibCursor pvrtmp_2673 = tmp_struct_92.field0;
            GibCursor pvrtmp_2674 = tmp_struct_92.field1;
            GibCursor pvrtmp_2675 = tmp_struct_92.field2;
            GibCursor pvrtmp_2676 = tmp_struct_92.field3;
            GibCursor pvrtmp_2677 = tmp_struct_92.field4;
            
            frame = gib_shadowstack_pop(rstack);
            tmpcur_2668 = frame->ptr;
            end_r_872 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_871 = frame->ptr;
            end_r_873 = frame->endptr;
            gib_shadowstack_push(rstack, loc_871, pvrtmp_2674, Stk,
                                 SearchTree_T);
            
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_93 =
                                                               _copy_without_ptrs_SearchTree(end_from_tagged_absran_830, pvrtmp_2674, pvrtmp_2677, tmpcur_2668);
            GibCursor pvrtmp_2682 = tmp_struct_93.field0;
            GibCursor pvrtmp_2683 = tmp_struct_93.field1;
            GibCursor pvrtmp_2684 = tmp_struct_93.field2;
            GibCursor pvrtmp_2685 = tmp_struct_93.field3;
            GibCursor pvrtmp_2686 = tmp_struct_93.field4;
            
            frame = gib_shadowstack_pop(rstack);
            loc_871 = frame->ptr;
            pvrtmp_2674 = frame->endptr;
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2682,
                                                                        pvrtmp_2683,
                                                                        pvrtmp_2684,
                                                                        loc_871,
                                                                        pvrtmp_2686};
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_96 = *(uintptr_t *) tmpcur_2657;
            GibCursor tmpcur_2695 = GIB_UNTAG(tagged_tmpcur_96);
            GibCursor tmpaftercur_2696 = tmpcur_2657 + 8;
            uint16_t tmptag_2697 = GIB_GET_TAG(tagged_tmpcur_96);
            GibCursor end_from_tagged_indr_1345 = tmpcur_2695 + tmptag_2697;
            GibCursor jump_1347 = tmpcur_2657 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_95 =
                                                               _copy_without_ptrs_SearchTree(end_from_tagged_indr_1345, end_r_873, loc_871, tmpcur_2695);
            GibCursor pvrtmp_2698 = tmp_struct_95.field0;
            GibCursor pvrtmp_2699 = tmp_struct_95.field1;
            GibCursor pvrtmp_2700 = tmp_struct_95.field2;
            GibCursor pvrtmp_2701 = tmp_struct_95.field3;
            GibCursor pvrtmp_2702 = tmp_struct_95.field4;
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_872,
                                                                        pvrtmp_2699,
                                                                        jump_1347,
                                                                        pvrtmp_2701,
                                                                        pvrtmp_2702};
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_98 = *(uintptr_t *) tmpcur_2657;
            GibCursor tmpcur_2709 = GIB_UNTAG(tagged_tmpcur_98);
            GibCursor tmpaftercur_2710 = tmpcur_2657 + 8;
            uint16_t tmptag_2711 = GIB_GET_TAG(tagged_tmpcur_98);
            GibCursor end_from_tagged_indr_1345 = tmpcur_2709 + tmptag_2711;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_97 =
                                                               _copy_without_ptrs_SearchTree(end_from_tagged_indr_1345, end_r_873, loc_871, tmpcur_2709);
            GibCursor pvrtmp_2712 = tmp_struct_97.field0;
            GibCursor pvrtmp_2713 = tmp_struct_97.field1;
            GibCursor pvrtmp_2714 = tmp_struct_97.field2;
            GibCursor pvrtmp_2715 = tmp_struct_97.field3;
            GibCursor pvrtmp_2716 = tmp_struct_97.field4;
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2712,
                                                                        pvrtmp_2713,
                                                                        pvrtmp_2714,
                                                                        pvrtmp_2715,
                                                                        pvrtmp_2716};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2656");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_SearchTree(GibCursor end_r_875,
                                            GibCursor arg_200_284_459)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2724 = *(GibPackedTag *) arg_200_284_459;
    GibCursor tmpcur_2725 = arg_200_284_459 + 1;
    
    
  switch_2747:
    ;
    switch (tmpval_2724) {
        
      case 0:
        {
            GibCursor jump_1282 = arg_200_284_459 + 1;
            
            return (GibCursorGibCursorProd) {end_r_875, jump_1282};
            break;
        }
        
      case 1:
        {
            GibInt tmpval_2726 = *(GibInt *) tmpcur_2725;
            GibCursor tmpcur_2727 = tmpcur_2725 + sizeof(GibInt);
            GibCursor jump_1284 = tmpcur_2725 + 8;
            
            return (GibCursorGibCursorProd) {end_r_875, jump_1284};
            break;
        }
        
      case 3:
        {
            uintptr_t tagged_tmpcur_101 = *(uintptr_t *) tmpcur_2725;
            GibCursor tmpcur_2728 = GIB_UNTAG(tagged_tmpcur_101);
            GibCursor tmpaftercur_2729 = tmpcur_2725 + 8;
            uint16_t tmptag_2730 = GIB_GET_TAG(tagged_tmpcur_101);
            GibCursor end_from_tagged_absran_833 = tmpcur_2728 + tmptag_2730;
            GibInt tmpval_2731 = *(GibInt *) tmpaftercur_2729;
            GibCursor tmpcur_2732 = tmpaftercur_2729 + sizeof(GibInt);
            
            gib_shadowstack_push(rstack, tmpcur_2728, end_r_875, Stk,
                                 SearchTree_T);
            
            GibCursorGibCursorProd tmp_struct_99 =
                                    _traverse_SearchTree(end_r_875, tmpcur_2732);
            GibCursor pvrtmp_2733 = tmp_struct_99.field0;
            GibCursor pvrtmp_2734 = tmp_struct_99.field1;
            
            frame = gib_shadowstack_pop(rstack);
            tmpcur_2728 = frame->ptr;
            end_r_875 = frame->endptr;
            
            GibCursorGibCursorProd tmp_struct_100 =
                                    _traverse_SearchTree(end_from_tagged_absran_833, tmpcur_2728);
            GibCursor pvrtmp_2735 = tmp_struct_100.field0;
            GibCursor pvrtmp_2736 = tmp_struct_100.field1;
            
            return (GibCursorGibCursorProd) {pvrtmp_2735, pvrtmp_2736};
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_103 = *(uintptr_t *) tmpcur_2725;
            GibCursor tmpcur_2737 = GIB_UNTAG(tagged_tmpcur_103);
            GibCursor tmpaftercur_2738 = tmpcur_2725 + 8;
            uint16_t tmptag_2739 = GIB_GET_TAG(tagged_tmpcur_103);
            GibCursor end_from_tagged_indr_1351 = tmpcur_2737 + tmptag_2739;
            GibCursor jump_1353 = tmpcur_2725 + 8;
            GibCursorGibCursorProd tmp_struct_102 =
                                    _traverse_SearchTree(end_from_tagged_indr_1351, tmpcur_2737);
            GibCursor pvrtmp_2740 = tmp_struct_102.field0;
            GibCursor pvrtmp_2741 = tmp_struct_102.field1;
            
            return (GibCursorGibCursorProd) {end_r_875, jump_1353};
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_105 = *(uintptr_t *) tmpcur_2725;
            GibCursor tmpcur_2742 = GIB_UNTAG(tagged_tmpcur_105);
            GibCursor tmpaftercur_2743 = tmpcur_2725 + 8;
            uint16_t tmptag_2744 = GIB_GET_TAG(tagged_tmpcur_105);
            GibCursor end_from_tagged_indr_1351 = tmpcur_2742 + tmptag_2744;
            GibCursorGibCursorProd tmp_struct_104 =
                                    _traverse_SearchTree(end_from_tagged_indr_1351, tmpcur_2742);
            GibCursor pvrtmp_2745 = tmp_struct_104.field0;
            GibCursor pvrtmp_2746 = tmp_struct_104.field1;
            
            return (GibCursorGibCursorProd) {pvrtmp_2745, pvrtmp_2746};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2724");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_SearchTree(GibCursor end_r_877,
                                         GibCursor arg_209_291_466)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2748 = *(GibPackedTag *) arg_209_291_466;
    GibCursor tmpcur_2749 = arg_209_291_466 + 1;
    
    
  switch_2771:
    ;
    switch (tmpval_2748) {
        
      case 0:
        {
            GibCursor jump_1291 = arg_209_291_466 + 1;
            unsigned char wildcard_210_292_467 = gib_print_symbol(2211);
            unsigned char wildcard_211_293_468 = gib_print_symbol(2210);
            
            return (GibCursorGibCursorProd) {end_r_877, jump_1291};
            break;
        }
        
      case 1:
        {
            GibInt tmpval_2750 = *(GibInt *) tmpcur_2749;
            GibCursor tmpcur_2751 = tmpcur_2749 + sizeof(GibInt);
            GibCursor jump_1293 = tmpcur_2749 + 8;
            unsigned char wildcard_214_295_470 = gib_print_symbol(2213);
            unsigned char y_213_296_471 = printf("%ld", tmpval_2750);
            unsigned char wildcard_215_297_472 = gib_print_symbol(2210);
            
            return (GibCursorGibCursorProd) {end_r_877, jump_1293};
            break;
        }
        
      case 3:
        {
            uintptr_t tagged_tmpcur_108 = *(uintptr_t *) tmpcur_2749;
            GibCursor tmpcur_2752 = GIB_UNTAG(tagged_tmpcur_108);
            GibCursor tmpaftercur_2753 = tmpcur_2749 + 8;
            uint16_t tmptag_2754 = GIB_GET_TAG(tagged_tmpcur_108);
            GibCursor end_from_tagged_absran_836 = tmpcur_2752 + tmptag_2754;
            GibInt tmpval_2755 = *(GibInt *) tmpaftercur_2753;
            GibCursor tmpcur_2756 = tmpaftercur_2753 + sizeof(GibInt);
            unsigned char wildcard_222_301_476 = gib_print_symbol(2212);
            unsigned char y_219_302_477 = printf("%ld", tmpval_2755);
            
            gib_shadowstack_push(rstack, tmpcur_2752, end_r_877, Stk,
                                 SearchTree_T);
            
            GibCursorGibCursorProd tmp_struct_106 =
                                    _print_SearchTree(end_r_877, tmpcur_2756);
            GibCursor pvrtmp_2757 = tmp_struct_106.field0;
            GibCursor pvrtmp_2758 = tmp_struct_106.field1;
            
            frame = gib_shadowstack_pop(rstack);
            tmpcur_2752 = frame->ptr;
            end_r_877 = frame->endptr;
            
            GibCursorGibCursorProd tmp_struct_107 =
                                    _print_SearchTree(end_from_tagged_absran_836, tmpcur_2752);
            GibCursor pvrtmp_2759 = tmp_struct_107.field0;
            GibCursor pvrtmp_2760 = tmp_struct_107.field1;
            unsigned char wildcard_223_305_480 = gib_print_symbol(2210);
            
            return (GibCursorGibCursorProd) {pvrtmp_2759, pvrtmp_2760};
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_110 = *(uintptr_t *) tmpcur_2749;
            GibCursor tmpcur_2761 = GIB_UNTAG(tagged_tmpcur_110);
            GibCursor tmpaftercur_2762 = tmpcur_2749 + 8;
            uint16_t tmptag_2763 = GIB_GET_TAG(tagged_tmpcur_110);
            GibCursor end_from_tagged_indr_1357 = tmpcur_2761 + tmptag_2763;
            GibCursor jump_1359 = tmpcur_2749 + 8;
            unsigned char wildcard_1362 = gib_print_symbol(2215);
            GibCursorGibCursorProd tmp_struct_109 =
                                    _print_SearchTree(end_from_tagged_indr_1357, tmpcur_2761);
            GibCursor pvrtmp_2764 = tmp_struct_109.field0;
            GibCursor pvrtmp_2765 = tmp_struct_109.field1;
            
            return (GibCursorGibCursorProd) {end_r_877, jump_1359};
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_112 = *(uintptr_t *) tmpcur_2749;
            GibCursor tmpcur_2766 = GIB_UNTAG(tagged_tmpcur_112);
            GibCursor tmpaftercur_2767 = tmpcur_2749 + 8;
            uint16_t tmptag_2768 = GIB_GET_TAG(tagged_tmpcur_112);
            GibCursor end_from_tagged_indr_1357 = tmpcur_2766 + tmptag_2768;
            unsigned char wildcard_1362 = gib_print_symbol(2214);
            GibCursorGibCursorProd tmp_struct_111 =
                                    _print_SearchTree(end_from_tagged_indr_1357, tmpcur_2766);
            GibCursor pvrtmp_2769 = tmp_struct_111.field0;
            GibCursor pvrtmp_2770 = tmp_struct_111.field1;
            
            return (GibCursorGibCursorProd) {pvrtmp_2769, pvrtmp_2770};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2748");
            exit(1);
        }
    }
}
GibCursorGibIntProd caseFn_224(GibCursor end_r_879, GibCursor l_77_225_306_481,
                               GibInt n_76_226_307_482)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2772 = *(GibPackedTag *) l_77_225_306_481;
    GibCursor tmpcur_2773 = l_77_225_306_481 + 1;
    
    
  switch_2795:
    ;
    switch (tmpval_2772) {
        
      case 0:
        {
            return (GibCursorGibIntProd) {end_r_879, n_76_226_307_482};
            break;
        }
        
      case 1:
        {
            GibInt tmpval_2774 = *(GibInt *) tmpcur_2773;
            GibCursor tmpcur_2775 = tmpcur_2773 + sizeof(GibInt);
            GibCursorGibIntProd tmp_struct_113 =
                                 min_tree(end_r_879, l_77_225_306_481);
            GibCursor pvrtmp_2776 = tmp_struct_113.field0;
            GibInt pvrtmp_2777 = tmp_struct_113.field1;
            
            return (GibCursorGibIntProd) {pvrtmp_2776, pvrtmp_2777};
            break;
        }
        
      case 3:
        {
            uintptr_t tagged_tmpcur_115 = *(uintptr_t *) tmpcur_2773;
            GibCursor tmpcur_2778 = GIB_UNTAG(tagged_tmpcur_115);
            GibCursor tmpaftercur_2779 = tmpcur_2773 + 8;
            uint16_t tmptag_2780 = GIB_GET_TAG(tagged_tmpcur_115);
            GibCursor end_from_tagged_absran_839 = tmpcur_2778 + tmptag_2780;
            GibInt tmpval_2781 = *(GibInt *) tmpaftercur_2779;
            GibCursor tmpcur_2782 = tmpaftercur_2779 + sizeof(GibInt);
            GibCursorGibIntProd tmp_struct_114 =
                                 min_tree(end_r_879, l_77_225_306_481);
            GibCursor pvrtmp_2783 = tmp_struct_114.field0;
            GibInt pvrtmp_2784 = tmp_struct_114.field1;
            
            return (GibCursorGibIntProd) {pvrtmp_2783, pvrtmp_2784};
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_117 = *(uintptr_t *) tmpcur_2773;
            GibCursor tmpcur_2785 = GIB_UNTAG(tagged_tmpcur_117);
            GibCursor tmpaftercur_2786 = tmpcur_2773 + 8;
            uint16_t tmptag_2787 = GIB_GET_TAG(tagged_tmpcur_117);
            GibCursor end_from_tagged_indr_1363 = tmpcur_2785 + tmptag_2787;
            GibCursor jump_1365 = tmpcur_2773 + 8;
            GibCursorGibIntProd tmp_struct_116 =
                                 caseFn_224(end_from_tagged_indr_1363, tmpcur_2785, n_76_226_307_482);
            GibCursor pvrtmp_2788 = tmp_struct_116.field0;
            GibInt pvrtmp_2789 = tmp_struct_116.field1;
            
            return (GibCursorGibIntProd) {end_r_879, pvrtmp_2789};
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_119 = *(uintptr_t *) tmpcur_2773;
            GibCursor tmpcur_2790 = GIB_UNTAG(tagged_tmpcur_119);
            GibCursor tmpaftercur_2791 = tmpcur_2773 + 8;
            uint16_t tmptag_2792 = GIB_GET_TAG(tagged_tmpcur_119);
            GibCursor end_from_tagged_indr_1363 = tmpcur_2790 + tmptag_2792;
            GibCursorGibIntProd tmp_struct_118 =
                                 caseFn_224(end_from_tagged_indr_1363, tmpcur_2790, n_76_226_307_482);
            GibCursor pvrtmp_2793 = tmp_struct_118.field0;
            GibInt pvrtmp_2794 = tmp_struct_118.field1;
            
            return (GibCursorGibIntProd) {pvrtmp_2793, pvrtmp_2794};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2772");
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
    GibChunk region_2216 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_893 = region_2216.start;
    GibCursor end_r_893 = region_2216.end;
    GibChunk region_2217 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_892 = region_2217.start;
    GibCursor end_r_892 = region_2217.end;
    GibInt m_51_227_357 = gib_get_size_param();
    GibInt fltPrm_312_358 = gib_expll(2, 2);
    GibInt total_nodes_52_228_359 = fltPrm_312_358 - 1;
    GibCursor pvrtmp_2227;
    GibCursor pvrtmp_2228;
    GibCursor pvrtmp_2229;
    GibVector *times_124 = gib_vector_alloc(gib_get_iters_param(),
                                            sizeof(double));
    struct timespec begin_pvrtmp_2227;
    struct timespec end_pvrtmp_2227;
    
    clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_2227);
    {
        GibCursorGibCursorGibCursorProd tmp_struct_120 =
                                         helper(end_r_893, r_893, 0, total_nodes_52_228_359);
        GibCursor pvrtmp_2218 = tmp_struct_120.field0;
        GibCursor pvrtmp_2219 = tmp_struct_120.field1;
        GibCursor pvrtmp_2220 = tmp_struct_120.field2;
        
        pvrtmp_2227 = pvrtmp_2218;
        pvrtmp_2228 = pvrtmp_2219;
        pvrtmp_2229 = pvrtmp_2220;
    }
    clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_2227);
    
    double selftimed_123 = gib_difftimespecs(&begin_pvrtmp_2227,
                                             &end_pvrtmp_2227);
    
    gib_vector_free(times_124);
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("SELFTIMED: %e\n", gib_difftimespecs(&begin_pvrtmp_2227,
                                                &end_pvrtmp_2227));
    gib_shadowstack_push(rstack, r_893, end_r_893, Stk, SearchTree_T);
    frame = gib_shadowstack_pop(rstack);
    r_893 = frame->ptr;
    end_r_893 = frame->endptr;
    
    GibCursor pvrtmp_2248;
    GibCursor pvrtmp_2249;
    GibCursor pvrtmp_2250;
    GibVector *times_130 = gib_vector_alloc(gib_get_iters_param(),
                                            sizeof(double));
    struct timespec begin_pvrtmp_2248;
    struct timespec end_pvrtmp_2248;
    
    for (long long iters_pvrtmp_2248 = 0; iters_pvrtmp_2248 <
         gib_get_iters_param(); iters_pvrtmp_2248++) {
        if (iters_pvrtmp_2248 != gib_get_iters_param() - 1)
            gib_list_bumpalloc_save_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_2248);
        
        GibInt fltAppE_313_361 = gib_get_size_param();
        GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_126 =
                                                           loop(end_r_893, end_r_892, r_892, pvrtmp_2228, fltAppE_313_361);
        GibCursor pvrtmp_2237 = tmp_struct_126.field0;
        GibCursor pvrtmp_2238 = tmp_struct_126.field1;
        GibCursor pvrtmp_2239 = tmp_struct_126.field2;
        GibCursor pvrtmp_2240 = tmp_struct_126.field3;
        GibCursor pvrtmp_2241 = tmp_struct_126.field4;
        
        pvrtmp_2248 = pvrtmp_2238;
        pvrtmp_2249 = pvrtmp_2240;
        pvrtmp_2250 = pvrtmp_2241;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_2248);
        if (iters_pvrtmp_2248 != gib_get_iters_param() - 1)
            gib_list_bumpalloc_restore_state();
        
        double itertime_127 = gib_difftimespecs(&begin_pvrtmp_2248,
                                                &end_pvrtmp_2248);
        
        printf("itertime: %lf\n", itertime_127);
        gib_vector_inplace_update(times_130, iters_pvrtmp_2248, &itertime_127);
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
    
    GibCursorGibCursorGibIntProd tmp_struct_132 =
                                  sum_tree(end_r_892, pvrtmp_2249);
    GibCursor pvrtmp_2258 = tmp_struct_132.field0;
    GibCursor pvrtmp_2259 = tmp_struct_132.field1;
    GibInt pvrtmp_2260 = tmp_struct_132.field2;
    
    printf("%ld", pvrtmp_2260);
    printf("\n");
    return 0;
}