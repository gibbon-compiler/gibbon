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

// Convenience macros since we don't really need the arrays of nurseries and
// shadowstacks since mutators are still sequential.
// #define DEFAULT_NURSERY gib_global_nurseries
#define DEFAULT_NURSERY (&(gib_global_nurseries[0]))
#define DEFAULT_READ_SHADOWSTACK (&(gib_global_read_shadowstacks[0]))
#define DEFAULT_WRITE_SHADOWSTACK (&(gib_global_write_shadowstacks[0]))


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
            GibBoxedTag field0;
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
GibCursorGibCursorGibCursorGibCursorProd add1(GibCursor end_r_606,  // input region
                                              GibCursor end_r_607, // output region
                                              GibCursor loc_605,  // output location
                                              GibCursor tr_25_168_265 // input location
                                             );
GibCursorGibIntProd sumtree(GibCursor end_r_598, GibCursor tr_29_163_260);
GibCursorGibCursorGibCursorProd buildtree(GibCursor end_r_600,
                                          GibCursor loc_599,
                                          GibInt n_35_169_266);
GibCursorGibCursorGibCursorGibCursorProd reverse(GibCursor end_r_615, // input region (xs)
                                                 GibCursor end_r_616, // input region (ys)
                                                 GibCursor end_r_617, // output region
                                                 GibCursor loc_614, // output location
                                                 GibCursor xs_36_179_284, // input location
                                                 GibCursor ys_37_180_285 // input location
                                                );
GibInt do_reverse(GibInt n_19_183_289);
GibInt do_tree(GibInt n_22_186_293);
GibCursorGibIntProd sum_list(GibCursor end_r_619, GibCursor xs_40_189_296);
GibCursorGibCursorGibCursorProd build_list(GibCursor end_r_621,
                                           GibCursor loc_620,
                                           GibInt n_43_192_300,
                                           GibInt n_new);
GibCursorGibCursorGibCursorGibCursorProd _copy_Tree(GibCursor end_r_624,
                                                    GibCursor end_r_625,
                                                    GibCursor loc_623,
                                                    GibCursor arg_112_193_304);
GibCursorProd _traverse_Tree(GibCursor end_r_631, GibCursor arg_126_207_318);
GibCursorProd _print_Tree(GibCursor end_r_633, GibCursor arg_133_213_324);
GibCursorGibCursorGibCursorGibCursorProd _copy_List(GibCursor end_r_636,
                                                    GibCursor end_r_637,
                                                    GibCursor loc_635,
                                                    GibCursor arg_144_224_335);
GibCursorProd _print_List(GibCursor end_r_645, GibCursor arg_159_238_349);
typedef enum {
            GibInt_T,
            GibFloat_T,
            GibSym_T,
            GibBool_T,
            GibVector_T,
            GibList_T,
            GibCursor_T,
            List_T,
            Tree_T,
        } GibDatatype;
void info_table_initialize(void)
{
    int error = gib_info_table_initialize();

    if (error < 0) {
        fprintf(stderr, "Couldn't initialize info table, errorno=%d", error);
        exit(1);
    }
    gib_info_table_insert_scalar(GibInt_T, sizeof(GibInt));
    gib_info_table_insert_scalar(GibFloat_T, sizeof(GibFloat));
    gib_info_table_insert_scalar(GibSym_T, sizeof(GibSym));
    gib_info_table_insert_scalar(GibBool_T, sizeof(GibBool));
    gib_info_table_insert_scalar(GibVector_T, sizeof(GibVector));
    gib_info_table_insert_scalar(GibList_T, sizeof(GibList));

    GibDatatype field_tys[2];

    field_tys[0] = GibInt_T;
    field_tys[1] = List_T;
    error = gib_info_table_insert_packed_dcon(List_T, 1, 8, 1, 1, field_tys, 2);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, List_T, 1);
        exit(1);
    }
    error = gib_info_table_insert_packed_dcon(List_T, 0, 0, 0, 0, field_tys, 0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, List_T, 0);
        exit(1);
    }
    field_tys[0] = GibInt_T;
    error = gib_info_table_insert_packed_dcon(Tree_T, 0, 8, 1, 0, field_tys, 1);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, Tree_T, 0);
        exit(1);
    }
    field_tys[0] = Tree_T;
    field_tys[1] = Tree_T;
    error = gib_info_table_insert_packed_dcon(Tree_T, 1, 0, 0, 2, field_tys, 2);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, Tree_T, 1);
        exit(1);
    }
}
void symbol_table_initialize(void)
{
    gib_add_symbol(1286, ")");
    gib_add_symbol(1287, "(Node ");
    gib_add_symbol(1288, "(Nil ");
    gib_add_symbol(1289, "(Leaf ");
    gib_add_symbol(1290, "(Cons ");
}
GibInt do_reverse(GibInt n_19_183_289)
{
    GibChunk region_1380 =
        gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_721 = region_1380.start;
    GibCursor end_r_721 = region_1380.end;

    GibCursorGibCursorGibCursorProd tmp_struct_16 =
        build_list(end_r_721, r_721, n_19_183_289, n_19_183_289);
    GibCursor pvrtmp_1384 = tmp_struct_16.field0;
    GibCursor pvrtmp_1385 = tmp_struct_16.field1;
    GibCursor pvrtmp_1386 = tmp_struct_16.field2;

    GibChunk region_1378 =
        gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_720 = region_1378.start;
    GibCursor end_r_720 = region_1378.end;

    *(GibBoxedTag *) r_720 = 0;
    GibCursor writetag_1010 = r_720 + 1;

    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;

    // printf("input:");
    // _print_List(NULL, pvrtmp_1385);
    // printf("\n");

    gib_shadowstack_push(rstack, r_720, end_r_720, List_T);

    GibChunk region_1382 =
        gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_719 = region_1382.start;
    GibCursor end_r_719 = region_1382.end;

    GibShadowstackFrame *frame;
    frame = gib_shadowstack_pop(rstack);
    r_720 = frame->ptr;
    end_r_720 = frame->endptr;

    GibVector *timings = gib_vector_alloc(gib_get_iters_param(), sizeof(double));
    struct timespec begin;
    struct timespec end;

    GibCursorGibCursorGibCursorGibCursorProd tmp_struct_17;

    for (int i = 0; i < gib_get_iters_param(); i++) {
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin);
        tmp_struct_17 = reverse(pvrtmp_1384, end_r_720, end_r_719, r_719, pvrtmp_1385, r_720);
        clock_gettime(CLOCK_MONOTONIC_RAW, &end);
        double itertime = gib_difftimespecs(&begin, &end);
        gib_vector_inplace_update(timings, i, &itertime);
    }

    /*
    gib_vector_inplace_sort(timings, gib_compare_doubles);
    double *tmp_34 = (double *) gib_vector_nth(timings, gib_get_iters_param() / 2);
    double selftimed = *tmp_34;
    double batchtime = gib_sum_timing_array(timings);
    gib_print_timing_array(timings);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime);
    printf("SELFTIMED: %e\n", selftimed);
    */

    GibCursor pvrtmp_1393 = tmp_struct_17.field0;
    GibCursor pvrtmp_1394 = tmp_struct_17.field1;
    GibCursor pvrtmp_1395 = tmp_struct_17.field2;
    GibCursor pvrtmp_1396 = tmp_struct_17.field3;

    // printf("reversed:");
    // _print_List(NULL, pvrtmp_1395);
    // printf("\n");

    GibCursorGibIntProd tmp_struct_18 =  sum_list(pvrtmp_1393, pvrtmp_1395);
    GibCursor pvrtmp_1401 = tmp_struct_18.field0;
    GibInt pvrtmp_1402 = tmp_struct_18.field1;

    gib_vector_free(timings);

    return pvrtmp_1402;
}
GibCursorGibCursorGibCursorGibCursorProd reverse(GibCursor end_r_615, // input region (xs)
                                                 GibCursor end_r_616, // input region (ys)
                                                 GibCursor end_r_617, // output region
                                                 GibCursor loc_614, // output location
                                                 GibCursor xs_36_179_284, // input location
                                                 GibCursor ys_37_180_285 // input location
                                                )
{
    // Bounds checking.
    if (loc_614 + 32 > end_r_617) {
        gib_grow_region(&loc_614, &end_r_617);
    }

    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    GibBoxedTag tmpval_1355 = *(GibBoxedTag *) xs_36_179_284;
    GibCursor tmpcur_1356 = xs_36_179_284 + 1;

  switch_1377:
    ;
    switch (tmpval_1355) {

      case 0:
        {
            GibCursor jump_882 = xs_36_179_284 + 1;
            // gib_bump_refcount(end_r_617, end_r_616);
            *(GibBoxedTag *) loc_614 = GIB_INDIRECTION_TAG;
            GibCursor writetag_996 = loc_614 + 1;
            *(GibCursor *) writetag_996 = ys_37_180_285;
            GibCursor writecur_997 = writetag_996 + 8;

            // printf("(1) in list empty:\n");
            // _print_List(NULL, xs_36_179_284);
            // printf("\n");
            // _print_List(NULL, ys_37_180_285);
            // printf("\n");

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_617,
                                                               jump_882,
                                                               loc_614,
                                                               writecur_997};
            break;
        }

      case 1:
        {
            GibInt tmpval_1361 = *(GibInt *) tmpcur_1356;
            GibCursor tmpcur_1362 = tmpcur_1356 + sizeof(GibInt);

            // printf("(1) before GC:\n");
            // _print_List(NULL, tmpcur_1362);
            // printf("\n");
            // _print_List(NULL, ys_37_180_285);
            // printf("\n");

            // Only are function arguments are live at this point. The caller
            // would have already pushed them to the shadowstack. We can
            // allocate the region directly.

            // Push to shadow stack.
            // xs, ys, output
            gib_shadowstack_push(rstack, tmpcur_1362, end_r_615, List_T);
            gib_shadowstack_push(rstack, ys_37_180_285, end_r_616, List_T);
            gib_shadowstack_push(wstack, loc_614, end_r_617, List_T);
            // Pushed.

            GibChunk region_1353 =
                gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_705 = region_1353.start;
            GibCursor end_r_705 = region_1353.end;

            // Restore from shadow stack.
            frame = gib_shadowstack_pop(wstack);
            loc_614 = frame->ptr;
            end_r_617 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            ys_37_180_285 = frame->ptr;
            end_r_616 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tmpcur_1362 = frame->ptr;
            end_r_615 = frame->endptr;
            // Restored.

            // printf("(1) after GC:\n");
            // _print_List(NULL, tmpcur_1362);
            // printf("\n");
            // _print_List(NULL, ys_37_180_285);
            // printf("\n");

            GibCursor loc_693 = r_705 + 1;
            GibCursor loc_694 = loc_693 + 8;

            // GibCursor jump_883 = tmpcur_1356 + 8;
            // gib_bump_refcount(end_r_705, end_r_616);
            *(GibBoxedTag *) loc_694 = GIB_INDIRECTION_TAG;
            GibCursor writetag_1001 = loc_694 + 1;
            *(GibCursor *) writetag_1001 = ys_37_180_285;
            GibCursor writecur_1002 = writetag_1001 + 8;

            *(GibBoxedTag *) r_705 = 1;
            GibCursor writetag_1004 = r_705 + 1;
            *(GibInt *) writetag_1004 = tmpval_1361;
            GibCursor writecur_1005 = writetag_1004 + sizeof(GibInt);

            // printf("(2) before GC:\n");
            // _print_List(NULL, tmpcur_1362);
            // printf("\n");
            // _print_List(NULL, r_705);
            // printf("\n");

            // // Push to shadow stack.
            // // xs, ys, output
            // gib_shadowstack_push(rstack, tmpcur_1362, end_r_615, List_T);
            // gib_shadowstack_push(rstack, r_705, end_r_705, List_T);
            // gib_shadowstack_push(wstack, loc_614, end_r_617, List_T);
            // // Pushed.

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_12 =
                reverse(end_r_615, end_r_705, end_r_617, loc_614, tmpcur_1362, r_705);

            // // Popping is sufficient, don't need to restore anything because
            // // all of these cursors are unused after this point.
            // gib_shadowstack_pop(wstack);
            // gib_shadowstack_pop(rstack);
            // gib_shadowstack_pop(rstack);
            // // Popped.

            // printf("(2) after GC:\n");
            // _print_List(NULL, tmpcur_1362);
            // printf("\n");
            // _print_List(NULL, r_705);
            // printf("\n");

            GibCursor pvrtmp_1367 = tmp_struct_12.field0;
            GibCursor pvrtmp_1368 = tmp_struct_12.field1;
            GibCursor pvrtmp_1369 = tmp_struct_12.field2;
            GibCursor pvrtmp_1370 = tmp_struct_12.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_1367,
                                                               pvrtmp_1368,
                                                               pvrtmp_1369,
                                                               pvrtmp_1370};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_1630 = *(uintptr_t *) tmpcur_1356;
            GibCursor tmpcur_1630 = GIB_UNTAG(tagged_tmpcur_1630);
            GibCursor tmpaftercur_1631 = tmpcur_1356 + 8;
            GibBoxedTag tagtmp_1632 = *(GibBoxedTag *) tmpcur_1630;
            GibCursor tailtmp_1633 = tmpcur_1630 + 1;
            tmpval_1355 = tagtmp_1632;
            tmpcur_1356 = tailtmp_1633;
            goto switch_1377;
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            GibCursor tmpcur_1630 = *(GibCursor *) tmpcur_1356;
            GibCursor tmpaftercur_1631 = tmpcur_1356 + 8;
            GibBoxedTag tagtmp_1632 = *(GibBoxedTag *) tmpcur_1630;
            GibCursor tailtmp_1633 = tmpcur_1630 + 1;
            tmpval_1355 = tagtmp_1632;
            tmpcur_1356 = tailtmp_1633;
            goto switch_1377;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1355");
            exit(1);
        }
    }
}
GibCursorGibIntProd sum_list(GibCursor end_r_619, GibCursor xs_40_189_296)
{
    GibBoxedTag tmpval_1424 = *(GibBoxedTag *) xs_40_189_296;
    GibCursor tmpcur_1425 = xs_40_189_296 + 1;


  switch_1430:
    ;
    switch (tmpval_1424) {

      case 0:
        {
            GibCursor jump_893 = xs_40_189_296 + 1;

            return (GibCursorGibIntProd) {jump_893, 0};
            break;
        }

      case 1:
        {
            GibInt tmpval_1426 = *(GibInt *) tmpcur_1425;
            GibCursor tmpcur_1427 = tmpcur_1425 + sizeof(GibInt);
            GibCursor jump_894 = tmpcur_1425 + 8;
            GibCursorGibIntProd tmp_struct_22 =
                                 sum_list(end_r_619, tmpcur_1427);
            GibCursor pvrtmp_1428 = tmp_struct_22.field0;
            GibInt pvrtmp_1429 = tmp_struct_22.field1;
            GibInt tailprim_896 = tmpval_1426 + pvrtmp_1429;

            return (GibCursorGibIntProd) {pvrtmp_1428, tailprim_896};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_1634 = *(uintptr_t *) tmpcur_1425;
            GibCursor tmpcur_1634 = GIB_UNTAG(tagged_tmpcur_1634);
            GibCursor tmpaftercur_1635 = tmpcur_1425 + 8;
            GibBoxedTag tagtmp_1636 = *(GibBoxedTag *) tmpcur_1634;
            GibCursor tailtmp_1637 = tmpcur_1634 + 1;

            tmpval_1424 = tagtmp_1636;
            tmpcur_1425 = tailtmp_1637;
            goto switch_1430;
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            GibCursor tmpcur_1634 = *(GibCursor *) tmpcur_1425;
            GibCursor tmpaftercur_1635 = tmpcur_1425 + 8;
            GibBoxedTag tagtmp_1636 = *(GibBoxedTag *) tmpcur_1634;
            GibCursor tailtmp_1637 = tmpcur_1634 + 1;

            tmpval_1424 = tagtmp_1636;
            tmpcur_1425 = tailtmp_1637;
            goto switch_1430;
            break;
        }

      default:
        {
            printf("Unknown tag in: tmpval_1424, %d\n", tmpval_1424);
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorProd build_list(GibCursor end_r_621,
                                           GibCursor loc_620,
                                           GibInt n_43_192_300,
                                           GibInt n_new)
{
    if (loc_620 + 32 > end_r_621) {
        gib_grow_region(&loc_620, &end_r_621);
    }

    GibCursor loc_740 = loc_620 + 1;
    GibCursor loc_741 = loc_740 + 8;
    GibBool fltIf_260_301 = n_43_192_300 == 0;

    if (fltIf_260_301) {
        *(GibBoxedTag *) loc_620 = 0;

        GibCursor writetag_1021 = loc_620 + 1;

        return (GibCursorGibCursorGibCursorProd) {end_r_621, loc_620,
                                                  writetag_1021};
    } else {
        GibInt fltAppE_262_302 = n_43_192_300 - 1;
        GibCursorGibCursorGibCursorProd tmp_struct_23 =
            build_list(end_r_621, loc_741, fltAppE_262_302, n_new);
        GibCursor pvrtmp_1435 = tmp_struct_23.field0;
        GibCursor pvrtmp_1436 = tmp_struct_23.field1;
        GibCursor pvrtmp_1437 = tmp_struct_23.field2;

        *(GibBoxedTag *) loc_620 = 1;

        GibCursor writetag_1024 = loc_620 + 1;

        *(GibInt *) writetag_1024 = n_new - n_43_192_300;

        GibCursor writecur_1025 = writetag_1024 + sizeof(GibInt);

        return (GibCursorGibCursorGibCursorProd) {pvrtmp_1435, loc_620,
                                                  pvrtmp_1437};
    }
}
GibInt do_tree(GibInt n_22_186_293)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    GibChunk region_1403 =
                  gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_731 = region_1403.start;
    GibCursor end_r_731 = region_1403.end;

    GibCursorGibCursorGibCursorProd tmp_struct_19 =
                                     buildtree(end_r_731, r_731, n_22_186_293);

    GibCursor pvrtmp_1407 = tmp_struct_19.field0;
    GibCursor pvrtmp_1408 = tmp_struct_19.field1;
    GibCursor pvrtmp_1409 = tmp_struct_19.field2;

    // GibCursorGibIntProd tmp_struct_21 =  sumtree(pvrtmp_1407, pvrtmp_1408);

    // _print_Tree(NULL, pvrtmp_1408);
    // printf("\n");

    gib_shadowstack_push(rstack, pvrtmp_1408, pvrtmp_1407, Tree_T);

    GibChunk region_1405 =
                  gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_730 = region_1405.start;
    GibCursor end_r_730 = region_1405.end;

    frame = gib_shadowstack_pop(rstack);
    pvrtmp_1408 = frame->ptr;
    pvrtmp_1407 = frame->endptr;

    // _print_Tree(NULL, pvrtmp_1408);
    // printf("\n");

    GibCursorGibCursorGibCursorGibCursorProd tmp_struct_20 =
                                              add1(pvrtmp_1407, end_r_730, r_730, pvrtmp_1408);
    GibCursor pvrtmp_1414 = tmp_struct_20.field0;
    GibCursor pvrtmp_1415 = tmp_struct_20.field1;
    GibCursor pvrtmp_1416 = tmp_struct_20.field2;
    GibCursor pvrtmp_1417 = tmp_struct_20.field3;

    // _print_Tree(NULL, pvrtmp_1416);
    // printf("\n");

    GibCursorGibIntProd tmp_struct_21 =  sumtree(pvrtmp_1414, pvrtmp_1416);

    GibCursor pvrtmp_1422 = tmp_struct_21.field0;
    GibInt pvrtmp_1423 = tmp_struct_21.field1;

    return pvrtmp_1423;


}
GibCursorGibCursorGibCursorGibCursorProd add1(GibCursor end_r_606,  // input region
                                              GibCursor end_r_607, // output region
                                              GibCursor loc_605,  // output location
                                              GibCursor tr_25_168_265 // input location
                                             )
{
    if (loc_605 + 32 > end_r_607) {
        gib_grow_region(&loc_605, &end_r_607);
    }

    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    GibBoxedTag tmpval_1293 = *(GibBoxedTag *) tr_25_168_265;
    GibCursor tmpcur_1294 = tr_25_168_265 + 1;


  switch_1321:
    ;
    switch (tmpval_1293) {

      case 0:
        {
            GibInt tmpval_1295 = *(GibInt *) tmpcur_1294;
            GibCursor tmpcur_1296 = tmpcur_1294 + sizeof(GibInt);
            GibCursor jump_871 = tmpcur_1294 + 8;
            // GibInt fltPkd_249_267 = tmpval_1295 + 1;
            GibInt fltPkd_249_267 = tmpval_1295;

            *(GibBoxedTag *) loc_605 = 0;

            GibCursor writetag_971 = loc_605 + 1;

            *(GibInt *) writetag_971 = fltPkd_249_267;

            GibCursor writecur_972 = writetag_971 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_607,
                                                               jump_871,
                                                               loc_605,
                                                               writecur_972};
            break;
        }

      case 1:
        {
            *(GibBoxedTag *) loc_605 = 1;
            GibCursor loc_668 = loc_605 + 1;

            gib_shadowstack_push(rstack, loc_605, end_r_607, Tree_T);
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_0 =
                                                      add1(end_r_606, end_r_607, loc_668, tmpcur_1294);
            frame = gib_shadowstack_pop(rstack);
            loc_605 = frame->ptr;
            end_r_607 = frame->endptr;

            GibCursor pvrtmp_1301 = tmp_struct_0.field0;
            GibCursor pvrtmp_1302 = tmp_struct_0.field1;
            GibCursor pvrtmp_1303 = tmp_struct_0.field2;
            GibCursor pvrtmp_1304 = tmp_struct_0.field3;

            gib_shadowstack_push(rstack, loc_605, end_r_607, Tree_T);
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_1 =
                                                      add1(end_r_606, pvrtmp_1301, pvrtmp_1304, pvrtmp_1302);
            frame = gib_shadowstack_pop(rstack);
            loc_605 = frame->ptr;
            end_r_607 = frame->endptr;

            GibCursor pvrtmp_1309 = tmp_struct_1.field0;
            GibCursor pvrtmp_1310 = tmp_struct_1.field1;
            GibCursor pvrtmp_1311 = tmp_struct_1.field2;
            GibCursor pvrtmp_1312 = tmp_struct_1.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_1309,
                                                               pvrtmp_1310,
                                                               loc_605,
                                                               pvrtmp_1312};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_1622 = *(uintptr_t *) tmpcur_1294;
            GibCursor tmpcur_1622 = GIB_UNTAG(tagged_tmpcur_1622);
            GibCursor tmpaftercur_1623 = tmpcur_1294 + 8;
            GibBoxedTag tagtmp_1624 = *(GibBoxedTag *) tmpcur_1622;
            GibCursor tailtmp_1625 = tmpcur_1622 + 1;

            tmpval_1293 = tagtmp_1624;
            tmpcur_1294 = tailtmp_1625;
            goto switch_1321;
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            GibCursor tmpcur_1622 = *(GibCursor *) tmpcur_1294;
            GibCursor tmpaftercur_1623 = tmpcur_1294 + 8;
            // GibBoxedTag tagtmp_1624 = *(GibBoxedTag *) tmpcur_1622;
            // GibCursor tailtmp_1625 = tmpcur_1622 + 1;

            // tmpval_1293 = tagtmp_1624;
            // tmpcur_1294 = tailtmp_1625;
            // goto switch_1321;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_1 =
                    add1(end_r_606, end_r_607, loc_605, tmpcur_1622);

            // _print_Tree(NULL, tmpcur_1622);
            // printf("\nhere1\n");
            // _print_Tree(NULL, tmpaftercur_1623);
            // printf("\nhere2\n");

            return (GibCursorGibCursorGibCursorGibCursorProd) {tmp_struct_1.field0,
                                                               tmpaftercur_1623,
                                                               loc_605,
                                                               tmp_struct_1.field3};

            break;
        }

      default:
        {
            printf("Unknown tag in: tmpval_1293, %d", tmpval_1293);
            exit(1);
        }
    }
}
GibCursorGibIntProd sumtree(GibCursor end_r_609, GibCursor tr_29_172_272)
{
    GibBoxedTag tmpval_1322 = *(GibBoxedTag *) tr_29_172_272;
    GibCursor tmpcur_1323 = tr_29_172_272 + 1;


  switch_1330:
    ;
    switch (tmpval_1322) {

      case 0:
        {
            GibInt tmpval_1324 = *(GibInt *) tmpcur_1323;
            GibCursor tmpcur_1325 = tmpcur_1323 + sizeof(GibInt);
            GibCursor jump_876 = tmpcur_1323 + 8;

            return (GibCursorGibIntProd) {jump_876, tmpval_1324};
            break;
        }

      case 1:
        {
            GibCursorGibIntProd tmp_struct_5 =  sumtree(end_r_609, tmpcur_1323);
            GibCursor pvrtmp_1326 = tmp_struct_5.field0;
            GibInt pvrtmp_1327 = tmp_struct_5.field1;
            GibCursorGibIntProd tmp_struct_6 =  sumtree(end_r_609, pvrtmp_1326);
            GibCursor pvrtmp_1328 = tmp_struct_6.field0;
            GibInt pvrtmp_1329 = tmp_struct_6.field1;
            GibInt tailprim_879 = pvrtmp_1327 + pvrtmp_1329;

            return (GibCursorGibIntProd) {pvrtmp_1328, tailprim_879};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_1626 = *(uintptr_t *) tmpcur_1323;
            GibCursor tmpcur_1626 = GIB_UNTAG(tagged_tmpcur_1626);
            GibCursor tmpaftercur_1627 = tmpcur_1323 + 8;
            GibBoxedTag tagtmp_1628 = *(GibBoxedTag *) tmpcur_1626;
            GibCursor tailtmp_1629 = tmpcur_1626 + 1;

            tmpval_1322 = tagtmp_1628;
            tmpcur_1323 = tailtmp_1629;
            goto switch_1330;
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            GibCursor tmpcur_1626 = *(GibCursor *) tmpcur_1323;
            GibCursor tmpaftercur_1627 = tmpcur_1323 + 8;
            // GibBoxedTag tagtmp_1628 = *(GibBoxedTag *) tmpcur_1626;
            // GibCursor tailtmp_1629 = tmpcur_1626 + 1;
            // tmpval_1322 = tagtmp_1628;
            // tmpcur_1323 = tailtmp_1629;
            GibCursorGibIntProd tmpstruct = sumtree(end_r_609, tmpcur_1626);
            GibInt x = tmpstruct.field1;
            return (GibCursorGibIntProd) {tmpaftercur_1627, x};

            // goto switch_1330;
            break;
        }

      default:
        {
            printf("Unknown tag in: tmpval_1322, %d", tmpval_1322);
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorProd buildtree(GibCursor end_r_652,
                                          GibCursor loc_651,
                                          GibInt n_41_188_294)
{

    if (loc_651 + 32 > end_r_652) {
        gib_grow_region(&loc_651, &end_r_652);
        // GibCursor chunk_start_10 = new_chunk_9.start;
        // GibCursor chunk_end_11 = new_chunk_9.end;
        // end_r_652 = chunk_end_11;
        // *(GibBoxedTag *) loc_651 = GIB_REDIRECTION_TAG;
        // GibCursor redir = loc_651 + 1;
        // *(GibCursor *) redir = chunk_start_10;
        // loc_651 = chunk_start_10;
    }

    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    GibBool fltIf_266_295 = n_41_188_294 == 0;

    if (fltIf_266_295) {

        // push to shadow stack.
        gib_shadowstack_push(wstack, loc_651, end_r_652, Tree_T);
        // pushed.

        GibChunk region_1413 = gib_alloc_region(gib_get_inf_init_chunk_size());

        // restore from shadow stack.
        frame = gib_shadowstack_pop(wstack);
        loc_651 = frame->ptr;
        end_r_652 = frame->endptr;
        // restored.

        GibCursor r_740 = region_1413.start;
        GibCursor end_r_740 = region_1413.end;
        GibCursor loc_727 = r_740 + 1;

        *(GibBoxedTag *) loc_727 = 0;
        GibCursor writetag_1047 = loc_727 + 1;
        *(GibInt *) writetag_1047 = 100;
        GibCursor writecur_1048 = writetag_1047 + sizeof(GibInt);
        *(GibBoxedTag *) writecur_1048 = 0;
        GibCursor writetag_1050 = writecur_1048 + 1;
        *(GibInt *) writetag_1050 = 200;
        GibCursor writecur_1051 = writetag_1050 + sizeof(GibInt);
        *(GibBoxedTag *) r_740 = 1;
        GibCursor writetag_1053 = r_740 + 1;
        GibBoxedTag tmpval_1420 = *(GibBoxedTag *) r_740;
        GibCursor tmpcur_1421 = r_740 + 1;

      switch_1432:
        ;
        switch (tmpval_1420) {

          case 0:
            {
                GibInt tmpval_1422 = *(GibInt *) tmpcur_1421;
                GibCursor tmpcur_1423 = tmpcur_1421 + sizeof(GibInt);
                GibCursor jump_940 = tmpcur_1421 + 8;
                *(GibBoxedTag *) loc_651 = 0;
                GibCursor writetag_1059 = loc_651 + 1;
                *(GibInt *) writetag_1059 = tmpval_1422;
                GibCursor writecur_1060 = writetag_1059 + sizeof(GibInt);
                return (GibCursorGibCursorGibCursorProd) {end_r_652, loc_651,
                                                          writecur_1060};
                break;
            }

          case 1:
            {
                // gib_bump_refcount(end_r_652, end_r_740);
                gib_indirection_barrier(loc_651, end_r_652, tmpcur_1421, end_r_740, Tree_T);
                *(GibBoxedTag *) loc_651 = GIB_INDIRECTION_TAG;
                GibCursor writetag_1063 = loc_651 + 1;
                *(GibCursor *) writetag_1063 = tmpcur_1421;
                GibCursor writecur_1064 = writetag_1063 + 8;
                return (GibCursorGibCursorGibCursorProd) {end_r_652, loc_651,
                                                          writecur_1064};
                break;
            }

          case GIB_REDIRECTION_TAG:
            {
                uintptr_t tagged_tmpcur_1722 = *(uintptr_t *) tmpcur_1421;
                GibCursor tmpcur_1722 = GIB_UNTAG(tagged_tmpcur_1722);
                GibCursor tmpaftercur_1723 = tmpcur_1421 + 8;
                GibBoxedTag tagtmp_1724 = *(GibBoxedTag *) tmpcur_1722;
                GibCursor tailtmp_1725 = tmpcur_1722 + 1;

                tmpval_1420 = tagtmp_1724;
                tmpcur_1421 = tailtmp_1725;
                goto switch_1432;
                break;
            }

          case GIB_INDIRECTION_TAG:
            {
                GibCursor tmpcur_1722 = *(GibCursor *) tmpcur_1421;
                GibCursor tmpaftercur_1723 = tmpcur_1421 + 8;
                GibBoxedTag tagtmp_1724 = *(GibBoxedTag *) tmpcur_1722;
                GibCursor tailtmp_1725 = tmpcur_1722 + 1;

                tmpval_1420 = tagtmp_1724;
                tmpcur_1421 = tailtmp_1725;
                goto switch_1432;
                break;
            }

          default:
            {
                printf("Unknown tag in: tmpval_1420: %d", tmpval_1420);
                exit(1);
            }
        }
    } else {

        *(GibBoxedTag *) loc_651 = 1;
        GibInt fltAppE_270_302 = n_41_188_294 - 1;
        GibCursor loc_743 = loc_651 + 1;

        // push to shadow stack.
        gib_shadowstack_push(rstack, loc_651, end_r_652, Tree_T);
        // pushed.

        GibCursorGibCursorGibCursorProd tmp_struct_7 =
                                         buildtree(end_r_652, loc_743, fltAppE_270_302);

        GibCursor pvrtmp_1433 = tmp_struct_7.field0;
        GibCursor pvrtmp_1434 = tmp_struct_7.field1;
        GibCursor pvrtmp_1435 = tmp_struct_7.field2;
        GibInt fltAppE_272_304 = n_41_188_294 - 1;


        GibCursorGibCursorGibCursorProd tmp_struct_8 =
                                         buildtree(pvrtmp_1433, pvrtmp_1435, fltAppE_272_304);

        // restore from shadow stack.
        frame = gib_shadowstack_pop(rstack);
        loc_651 = frame->ptr;
        end_r_652 = frame->endptr;
        // restored.

        GibCursor pvrtmp_1440 = tmp_struct_8.field0;
        GibCursor pvrtmp_1441 = tmp_struct_8.field1;
        GibCursor pvrtmp_1442 = tmp_struct_8.field2;


        return (GibCursorGibCursorGibCursorProd) {pvrtmp_1440, loc_651,
                                                  pvrtmp_1442};
    }
}
GibCursorGibCursorGibCursorGibCursorProd _copy_Tree(GibCursor end_r_624,
                                                    GibCursor end_r_625,
                                                    GibCursor loc_623,
                                                    GibCursor arg_112_193_304)
{
    if (loc_623 + 32 > end_r_625) {
        gib_grow_region(&loc_623, &end_r_625);
    }

    GibBoxedTag tmpval_1446 = *(GibBoxedTag *) arg_112_193_304;
    GibCursor tmpcur_1447 = arg_112_193_304 + 1;


  switch_1474:
    ;
    switch (tmpval_1446) {

      case 0:
        {
            GibInt tmpval_1448 = *(GibInt *) tmpcur_1447;
            GibCursor tmpcur_1449 = tmpcur_1447 + sizeof(GibInt);
            GibCursor jump_899 = tmpcur_1447 + 8;

            *(GibBoxedTag *) loc_623 = 0;

            GibCursor writetag_1030 = loc_623 + 1;

            *(GibInt *) writetag_1030 = tmpval_1448;

            GibCursor writecur_1031 = writetag_1030 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_625,
                                                               jump_899,
                                                               loc_623,
                                                               writecur_1031};
            break;
        }

      case 1:
        {
            GibCursor loc_759 = loc_623 + 1;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_27 =
                                                      _copy_Tree(end_r_624, end_r_625, loc_759, tmpcur_1447);
            GibCursor pvrtmp_1454 = tmp_struct_27.field0;
            GibCursor pvrtmp_1455 = tmp_struct_27.field1;
            GibCursor pvrtmp_1456 = tmp_struct_27.field2;
            GibCursor pvrtmp_1457 = tmp_struct_27.field3;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_28 =
                                                      _copy_Tree(end_r_624, pvrtmp_1454, pvrtmp_1457, pvrtmp_1455);
            GibCursor pvrtmp_1462 = tmp_struct_28.field0;
            GibCursor pvrtmp_1463 = tmp_struct_28.field1;
            GibCursor pvrtmp_1464 = tmp_struct_28.field2;
            GibCursor pvrtmp_1465 = tmp_struct_28.field3;

            *(GibBoxedTag *) loc_623 = 1;

            GibCursor writetag_1036 = loc_623 + 1;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_1462,
                                                               pvrtmp_1463,
                                                               loc_623,
                                                               pvrtmp_1465};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_1638 = *(uintptr_t *) tmpcur_1447;
            GibCursor tmpcur_1638 = GIB_UNTAG(tagged_tmpcur_1638);
            GibCursor tmpaftercur_1639 = tmpcur_1447 + 8;
            GibBoxedTag tagtmp_1640 = *(GibBoxedTag *) tmpcur_1638;
            GibCursor tailtmp_1641 = tmpcur_1638 + 1;

            tmpval_1446 = tagtmp_1640;
            tmpcur_1447 = tailtmp_1641;
            goto switch_1474;
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            GibCursor tmpcur_1638 = *(GibCursor *) tmpcur_1447;
            GibCursor tmpaftercur_1639 = tmpcur_1447 + 8;
            GibBoxedTag tagtmp_1640 = *(GibBoxedTag *) tmpcur_1638;
            GibCursor tailtmp_1641 = tmpcur_1638 + 1;

            tmpval_1446 = tagtmp_1640;
            tmpcur_1447 = tailtmp_1641;
            goto switch_1474;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1446");
            exit(1);
        }
    }
}
GibCursorProd _traverse_Tree(GibCursor end_r_631, GibCursor arg_126_207_318)
{
    GibBoxedTag tmpval_1504 = *(GibBoxedTag *) arg_126_207_318;
    GibCursor tmpcur_1505 = arg_126_207_318 + 1;


  switch_1510:
    ;
    switch (tmpval_1504) {

      case 0:
        {
            GibInt tmpval_1506 = *(GibInt *) tmpcur_1505;
            GibCursor tmpcur_1507 = tmpcur_1505 + sizeof(GibInt);
            GibCursor jump_909 = tmpcur_1505 + 8;

            return (GibCursorProd) {jump_909};
            break;
        }

      case 1:
        {
            GibCursorProd tmp_struct_34 =
                           _traverse_Tree(end_r_631, tmpcur_1505);
            GibCursor pvrtmp_1508 = tmp_struct_34.field0;
            GibCursorProd tmp_struct_35 =
                           _traverse_Tree(end_r_631, pvrtmp_1508);
            GibCursor pvrtmp_1509 = tmp_struct_35.field0;

            return (GibCursorProd) {pvrtmp_1509};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_1646 = *(uintptr_t *) tmpcur_1505;
            GibCursor tmpcur_1646 = GIB_UNTAG(tagged_tmpcur_1646);
            GibCursor tmpaftercur_1647 = tmpcur_1505 + 8;
            GibBoxedTag tagtmp_1648 = *(GibBoxedTag *) tmpcur_1646;
            GibCursor tailtmp_1649 = tmpcur_1646 + 1;

            tmpval_1504 = tagtmp_1648;
            tmpcur_1505 = tailtmp_1649;
            goto switch_1510;
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            GibCursor tmpcur_1646 = *(GibCursor *) tmpcur_1505;
            GibCursor tmpaftercur_1647 = tmpcur_1505 + 8;
            GibBoxedTag tagtmp_1648 = *(GibBoxedTag *) tmpcur_1646;
            GibCursor tailtmp_1649 = tmpcur_1646 + 1;

            tmpval_1504 = tagtmp_1648;
            tmpcur_1505 = tailtmp_1649;
            goto switch_1510;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1504");
            exit(1);
        }
    }
}
GibCursorProd _print_Tree(GibCursor end_r_633, GibCursor arg_133_213_324)
{
    GibBoxedTag tmpval_1511 = *(GibBoxedTag *) arg_133_213_324;
    GibCursor tmpcur_1512 = arg_133_213_324 + 1;


  switch_1517:
    ;
    switch (tmpval_1511) {

      case 0:
        {
            GibInt tmpval_1513 = *(GibInt *) tmpcur_1512;
            GibCursor tmpcur_1514 = tmpcur_1512 + sizeof(GibInt);
            GibCursor jump_914 = tmpcur_1512 + 8;
            unsigned char wildcard_136_215_326 = gib_print_symbol(1289);
            unsigned char y_135_216_327 = printf("%ld", tmpval_1513);
            unsigned char wildcard_137_217_328 = gib_print_symbol(1286);

            return (GibCursorProd) {jump_914};
            break;
        }

      case 1:
        {
            unsigned char wildcard_142_220_331 = gib_print_symbol(1287);
            GibCursorProd tmp_struct_36 =  _print_Tree(end_r_633, tmpcur_1512);
            GibCursor pvrtmp_1515 = tmp_struct_36.field0;
            GibCursorProd tmp_struct_37 =  _print_Tree(end_r_633, pvrtmp_1515);
            GibCursor pvrtmp_1516 = tmp_struct_37.field0;
            unsigned char wildcard_143_223_334 = gib_print_symbol(1286);

            return (GibCursorProd) {pvrtmp_1516};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            printf(" ->r ");

            uintptr_t tagged_tmpcur_1650 = *(uintptr_t *) tmpcur_1512;
            GibCursor tmpcur_1650 = GIB_UNTAG(tagged_tmpcur_1650);
            GibCursor tmpaftercur_1651 = tmpcur_1512 + 8;
            GibBoxedTag tagtmp_1652 = *(GibBoxedTag *) tmpcur_1650;
            GibCursor tailtmp_1653 = tmpcur_1650 + 1;

            tmpval_1511 = tagtmp_1652;
            tmpcur_1512 = tailtmp_1653;
            goto switch_1517;
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            printf(" ->i ");

            GibCursor tmpcur_1650 = *(GibCursor *) tmpcur_1512;
            GibCursor tmpaftercur_1651 = tmpcur_1512 + 8;
            GibBoxedTag tagtmp_1652 = *(GibBoxedTag *) tmpcur_1650;
            GibCursor tailtmp_1653 = tmpcur_1650 + 1;

            tmpval_1511 = tagtmp_1652;
            tmpcur_1512 = tailtmp_1653;
            // goto switch_1517;
            _print_Tree(NULL, tmpcur_1650);
            return (GibCursorProd) {tmpaftercur_1651};
            break;
        }

/*
      case COPIED_TAG:
        {
            printf(" COPIED \n");
            fflush(stdout);
            break;
        }

      case COPIED_TO_TAG:
        {
            printf(" COPIED_TO \n");
            fflush(stdout);
            break;
        }

      case CAUTERIZED_TAG:
        {
            printf(" CAUTERIZED \n");
            fflush(stdout);
            break;
        }
*/
      default:
        {
            printf("Unknown tag in: tmpval_1511: %d", tmpval_1511);
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd _copy_List(GibCursor end_r_636,
                                                    GibCursor end_r_637,
                                                    GibCursor loc_635,
                                                    GibCursor arg_144_224_335)
{
    if (loc_635 + 32 > end_r_637) {
        gib_grow_region(&loc_635, &end_r_637);
    }

    GibCursor loc_807 = loc_635 + 1;
    GibCursor loc_808 = loc_807 + 8;
    GibBoxedTag tmpval_1518 = *(GibBoxedTag *) arg_144_224_335;
    GibCursor tmpcur_1519 = arg_144_224_335 + 1;


  switch_1538:
    ;
    switch (tmpval_1518) {

      case 0:
        {
            GibCursor jump_919 = arg_144_224_335 + 1;

            *(GibBoxedTag *) loc_635 = 0;

            GibCursor writetag_1063 = loc_635 + 1;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_637,
                                                               jump_919,
                                                               loc_635,
                                                               writetag_1063};
            break;
        }

      case 1:
        {
            GibInt tmpval_1524 = *(GibInt *) tmpcur_1519;
            GibCursor tmpcur_1525 = tmpcur_1519 + sizeof(GibInt);
            GibCursor jump_921 = tmpcur_1519 + 8;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_38 =
                                                      _copy_List(end_r_636, end_r_637, loc_808, tmpcur_1525);
            GibCursor pvrtmp_1526 = tmp_struct_38.field0;
            GibCursor pvrtmp_1527 = tmp_struct_38.field1;
            GibCursor pvrtmp_1528 = tmp_struct_38.field2;
            GibCursor pvrtmp_1529 = tmp_struct_38.field3;

            *(GibBoxedTag *) loc_635 = 1;

            GibCursor writetag_1068 = loc_635 + 1;

            *(GibInt *) writetag_1068 = tmpval_1524;

            GibCursor writecur_1069 = writetag_1068 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_1526,
                                                               pvrtmp_1527,
                                                               loc_635,
                                                               pvrtmp_1529};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_1654 = *(uintptr_t *) tmpcur_1519;
            GibCursor tmpcur_1654 = GIB_UNTAG(tagged_tmpcur_1654);
            GibCursor tmpaftercur_1655 = tmpcur_1519 + 8;
            GibBoxedTag tagtmp_1656 = *(GibBoxedTag *) tmpcur_1654;
            GibCursor tailtmp_1657 = tmpcur_1654 + 1;

            tmpval_1518 = tagtmp_1656;
            tmpcur_1519 = tailtmp_1657;
            goto switch_1538;
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            GibCursor tmpcur_1654 = *(GibCursor *) tmpcur_1519;
            GibCursor tmpaftercur_1655 = tmpcur_1519 + 8;
            GibBoxedTag tagtmp_1656 = *(GibBoxedTag *) tmpcur_1654;
            GibCursor tailtmp_1657 = tmpcur_1654 + 1;

            tmpval_1518 = tagtmp_1656;
            tmpcur_1519 = tailtmp_1657;
            goto switch_1538;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1518");
            exit(1);
        }
    }
}
GibCursorProd _traverse_List(GibCursor end_r_643, GibCursor arg_154_234_345)
{
    GibBoxedTag tmpval_1560 = *(GibBoxedTag *) arg_154_234_345;
    GibCursor tmpcur_1561 = arg_154_234_345 + 1;


  switch_1565:
    ;
    switch (tmpval_1560) {

      case 0:
        {
            GibCursor jump_929 = arg_154_234_345 + 1;

            return (GibCursorProd) {jump_929};
            break;
        }

      case 1:
        {
            GibInt tmpval_1562 = *(GibInt *) tmpcur_1561;
            GibCursor tmpcur_1563 = tmpcur_1561 + sizeof(GibInt);
            GibCursor jump_931 = tmpcur_1561 + 8;
            GibCursorProd tmp_struct_43 =
                           _traverse_List(end_r_643, tmpcur_1563);
            GibCursor pvrtmp_1564 = tmp_struct_43.field0;

            return (GibCursorProd) {pvrtmp_1564};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_1662 = *(uintptr_t *) tmpcur_1561;
            GibCursor tmpcur_1662 = GIB_UNTAG(tagged_tmpcur_1662);
            GibCursor tmpaftercur_1663 = tmpcur_1561 + 8;
            GibBoxedTag tagtmp_1664 = *(GibBoxedTag *) tmpcur_1662;
            GibCursor tailtmp_1665 = tmpcur_1662 + 1;

            tmpval_1560 = tagtmp_1664;
            tmpcur_1561 = tailtmp_1665;
            goto switch_1565;
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            GibCursor tmpcur_1662 = *(GibCursor *) tmpcur_1561;
            GibCursor tmpaftercur_1663 = tmpcur_1561 + 8;
            GibBoxedTag tagtmp_1664 = *(GibBoxedTag *) tmpcur_1662;
            GibCursor tailtmp_1665 = tmpcur_1662 + 1;

            tmpval_1560 = tagtmp_1664;
            tmpcur_1561 = tailtmp_1665;
            goto switch_1565;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1560");
            exit(1);
        }
    }
}
GibCursorProd _print_List(GibCursor end_r_645, GibCursor arg_159_238_349)
{
    GibBoxedTag tmpval_1566 = *(GibBoxedTag *) arg_159_238_349;
    GibCursor tmpcur_1567 = arg_159_238_349 + 1;


  switch_1571:
    ;
    switch (tmpval_1566) {

      case 0:
        {
            GibCursor jump_934 = arg_159_238_349 + 1;
            unsigned char wildcard_160_239_350 = gib_print_symbol(1288);
            unsigned char wildcard_161_240_351 = gib_print_symbol(1286);
            fflush(stdout);

            return (GibCursorProd) {jump_934};
            break;
        }

      case 1:
        {
            GibInt tmpval_1568 = *(GibInt *) tmpcur_1567;
            GibCursor tmpcur_1569 = tmpcur_1567 + sizeof(GibInt);
            GibCursor jump_936 = tmpcur_1567 + 8;
            unsigned char wildcard_166_243_354 = gib_print_symbol(1290);
            unsigned char y_164_244_355 = printf("%ld", tmpval_1568);
            GibCursorProd tmp_struct_44 =  _print_List(end_r_645, tmpcur_1569);
            GibCursor pvrtmp_1570 = tmp_struct_44.field0;
            unsigned char wildcard_167_246_357 = gib_print_symbol(1286);
            fflush(stdout);

            return (GibCursorProd) {pvrtmp_1570};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            printf(" ->r ");

            uintptr_t tagged_tmpcur_1666 = *(uintptr_t *) tmpcur_1567;
            GibCursor tmpcur_1666 = GIB_UNTAG(tagged_tmpcur_1666);
            GibCursor tmpaftercur_1667 = tmpcur_1567 + 8;
            GibBoxedTag tagtmp_1668 = *(GibBoxedTag *) tmpcur_1666;
            GibCursor tailtmp_1669 = tmpcur_1666 + 1;

            tmpval_1566 = tagtmp_1668;
            tmpcur_1567 = tailtmp_1669;
            goto switch_1571;
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            printf(" ->i ");

            GibCursor tmpcur_1666 = *(GibCursor *) tmpcur_1567;
            GibCursor tmpaftercur_1667 = tmpcur_1567 + 8;
            GibBoxedTag tagtmp_1668 = *(GibBoxedTag *) tmpcur_1666;
            GibCursor tailtmp_1669 = tmpcur_1666 + 1;

            tmpval_1566 = tagtmp_1668;
            tmpcur_1567 = tailtmp_1669;
            goto switch_1571;
            break;
        }

      default:
        {
            printf("Unknown tag in: tmpval_1566 %d", tmpval_1566);
            exit(1);
        }
    }
}

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Hand-written code starts here
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */


/*
 *

 * The nursery is set to 4KiB and every alloc_region requests space
 * just under 2*KiB. Therefore the third allocation on every thread should
 * be malloc'd, indicated on the stdout by MALLOC!!!.


 * Compile:
 * ~~~~~~~~~~


1) Compile the Rust RTS:

cd $GIBBONDIR/gibbon-rts && cargo build --release


2) Compile the C RTS:

gcc -std=gnu11 -m64 -fcilkplus -D_GIBBON_DEBUG -D_GIBBON_PARALLEL \
-Wno-unused-variable -Wno-unused-label -Wall -Wextra -Wpedantic  \
-O3  -flto \
-I $GIBBONDIR/gibbon-compiler/cbits  -L$GIBBONDIR/gibbon-rts/target/debug \
-Wl,-rpath=$GIBBONDIR/gibbon-rts/target/debug \
-c $GIBBONDIR/gibbon-compiler/cbits/gibbon_rts.c \
-o $GIBBONDIR/gibbon-compiler/cbits/gibbon_rts.o -lm -lgibbon_rts


3) Compile this program:

gcc -std=gnu11 -m64 -fcilkplus -D_GIBBON_DEBUG -D_GIBBON_PARALLEL  \
-Wno-unused-variable -Wno-unused-label -Wall -Wextra -Wpedantic \
-O0 -g  -flto \
$GIBBONDIR/gibbon-compiler/cbits/gibbon_rts.o -I$GIBBONDIR/gibbon-compiler/cbits \
-L$GIBBONDIR/gibbon-rts/target/debug  \
-Wl,-rpath=$GIBBONDIR/gibbon-rts/target/debug \
$GIBBONDIR/gibbon-compiler/examples/test_new_rts.c \
-o $GIBBONDIR/gibbon-compiler/examples/test_new_rts.exe -lm -lgibbon_rts


 * Run:
 * ~~~~~~~~~~

$GIBBONDIR/gibbon-compiler/examples/test_new_rts.exe


 */

// https://stackoverflow.com/a/27627015
void print_binary(uint64_t number, int *i)
{
    if (number >> 1) {
        print_binary(number >> 1, i);
    }
    (*i)++;
    putc((number & 1) ? '1' : '0', stdout);
}

// https://stackoverflow.com/a/18426582.
void test_ptr_tagging()
{
    printf("\nTest pointer tagging:\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n");
    int i = 0;

    // The mask to use.
    const uintptr_t MASK = ~(1ULL << 48);
    printf("The mask to use: %ld\n", MASK);
    print_binary((uintptr_t) MASK, &i);
    printf("\ni=%d\n\n", i);
    i = 0;

    // Original pointer.
    char *addr = malloc(1024);
    printf("Original pointer: %p\n", addr);
    print_binary((uintptr_t) addr, &i);
    printf("\ni=%d\n\n", i);
    i = 0;

    // Data to be stored.
    uint16_t data = 65535;
    printf("Data to be stored: %d\n", data);
    print_binary(data, &i);
    printf("\ni=%d\n\n", i);
    i = 0;

    uint64_t data2 = data;
    data2 = data2 << 48;
    printf("Left shifted data: %ld\n", data2);
    print_binary(data2, &i);
    printf("\ni=%d\n\n", i);
    i = 0;

    // Store data into the pointer.
    // Note: To be on the safe side and future-proof (because future implementations
    //     can increase the number of significant bits in the pointer), we should
    //     store values from the most significant bits down to the lower ones
    char *tagged = (char *) (((uintptr_t)addr & MASK) | data2);
    printf("Tagged pointer: %p\n", tagged);
    print_binary((uintptr_t) tagged, &i);
    printf("\ni=%d\n\n", i);
    i = 0;

    // Recovered data.
    uint16_t data3 = (uintptr_t) tagged >> 48;
    printf("Recovered data: %d\n", data3);
    print_binary((uintptr_t) data3, &i);
    printf("\ni=%d\n\n", i);
    i = 0;

    // Deference the pointer.
    // Sign extend first to make the pointer canonical
    // Note: Technically this is implementation defined. You may want a more
    //     standard-compliant way to sign-extend the value
    // uintptr_t ptr2 = (((uintptr_t) tagged << 16) >> 16);
    // uintptr_t ptr2 = (((uintptr_t)tagged & ((1ull << 48) - 1)) |
    //                   ~(((uintptr_t)tagged & (1ull << 47)) - 1));
    char *ptr2 = (char *) (((uintptr_t) tagged << 16) >> 16);
    printf("Deferenced pointer: %p\n", ptr2);
    print_binary((uintptr_t) ptr2, &i);
    printf("\ni=%d\n\n", i);
    i = 0;

    char *addr2 = (char *) ptr2;
    printf("addr2: %p\n", addr2);
    print_binary((uintptr_t) addr2, &i);
    printf("\ni=%d\n\n", i);
    i = 0;


    // Check if tagging and untagging cancels out.
    printf("Checking original data == recovered data.\n");
    assert(data3 == data);
    printf("Checking original pointer == recovered pointer.\n");
    assert(addr2 == addr);
    printf("Checks passed.");

}

int gib_main_expr(void)
{
    info_table_initialize();
    symbol_table_initialize();

    GibInt fltPrd_235_251 =  do_reverse(gib_get_size_param());
    printf("reverse: %" PRIu64 "\n", fltPrd_235_251);
    // GibInt fltPrd_236_252 =  do_tree(gib_get_size_param());
    // printf("sum tree: %" PRIu64 "\n", fltPrd_236_252);

    // test_ptr_tagging();

    return 0;
}
