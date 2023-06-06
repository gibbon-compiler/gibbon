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
GibInt addints(GibInt x_41_169_271, GibInt y_42_170_272);
GibCursorGibCursorGibIntProd sumTree(GibCursor end_r_541,
                                     GibCursor tr_53_181_273);
GibCursorGibCursorGibCursorProd mkSharedTree(GibCursor end_r_543,
                                             GibCursor loc_542,
                                             GibInt n_57_185_279);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_Tree(GibCursor end_r_546, GibCursor end_r_547, GibCursor loc_545,
           GibCursor arg_98_187_283);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_Tree(GibCursor end_r_550, GibCursor end_r_551,
                        GibCursor loc_549, GibCursor arg_105_194_290);
GibCursorGibCursorProd _traverse_Tree(GibCursor end_r_553,
                                      GibCursor arg_112_201_297);
GibCursorGibCursorProd _print_Tree(GibCursor end_r_555,
                                   GibCursor arg_119_207_303);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_PList(GibCursor end_r_558, GibCursor end_r_559, GibCursor loc_557,
            GibCursor arg_136_227_323);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_PList(GibCursor end_r_562, GibCursor end_r_563,
                         GibCursor loc_561, GibCursor arg_141_232_328);
GibCursorGibCursorProd _traverse_PList(GibCursor end_r_565,
                                       GibCursor arg_146_237_333);
GibCursorGibCursorProd _print_PList(GibCursor end_r_567,
                                    GibCursor arg_151_241_337);
GibCursorGibCursorGibCursorGibCursorProd caseFn_164(GibCursor end_r_570,
                                                    GibCursor end_r_571,
                                                    GibCursor loc_569,
                                                    GibCursor tr_58_165_256_352);
typedef enum {
            GibInt_T,
            GibFloat_T,
            GibSym_T,
            GibBool_T,
            GibVector_T,
            GibList_T,
            GibCursor_T,
            PList_T,
            Tree_T,
        } GibDatatype;
void info_table_initialize(void)
{
    int error = gib_info_table_initialize(9);

    if (error < 0) {
        fprintf(stderr, "Couldn't initialize info table, errorno=%d", error);
        exit(1);
    }

    GibDatatype field_tys[2];

    field_tys[0] = PList_T;
    error = gib_info_table_insert_packed_dcon(PList_T, 0, 8, 0, 1, 1, field_tys,
                                              1);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, PList_T, 0);
        exit(1);
    }
    error = gib_info_table_insert_packed_dcon(PList_T, 1, 0, 0, 0, 0, field_tys,
                                              0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, PList_T, 1);
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
    error = gib_info_table_insert_packed_dcon(Tree_T, 1, 0, 0, 0, 2, field_tys,
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
    gib_add_symbol(1416, ")");
    gib_add_symbol(1417, "(Node");
    gib_add_symbol(1418, "(Nil");
    gib_add_symbol(1419, "(Leaf");
    gib_add_symbol(1420, "(Cons");
    gib_add_symbol(1421, " ->r ");
    gib_add_symbol(1422, " ->i ");
    gib_add_symbol(1423, " ");
}
GibInt addints(GibInt x_41_169_271, GibInt y_42_170_272)
{
    GibInt tailprim_726 = x_41_169_271 + y_42_170_272;

    return tailprim_726;
}
GibCursorGibCursorGibIntProd sumTree(GibCursor end_r_541,
                                     GibCursor tr_53_181_273)
{
    GibPackedTag tmpval_1435 = *(GibPackedTag *) tr_53_181_273;
    GibCursor tmpcur_1436 = tr_53_181_273 + 1;


  switch_1457:
    ;
    switch (tmpval_1435) {

      case 0:
        {
            GibInt tmpval_1437 = *(GibInt *) tmpcur_1436;
            GibCursor tmpcur_1438 = tmpcur_1436 + sizeof(GibInt);
            GibCursor jump_727 = tmpcur_1436 + 8;

            return (GibCursorGibCursorGibIntProd) {end_r_541, jump_727,
                                                   tmpval_1437};
            break;
        }

      case 1:
        {
            GibCursorGibCursorGibIntProd tmp_struct_0 =
                                          sumTree(end_r_541, tmpcur_1436);
            GibCursor pvrtmp_1439 = tmp_struct_0.field0;
            GibCursor pvrtmp_1440 = tmp_struct_0.field1;
            GibInt pvrtmp_1441 = tmp_struct_0.field2;
            GibCursorGibCursorGibIntProd tmp_struct_1 =
                                          sumTree(pvrtmp_1439, pvrtmp_1440);
            GibCursor pvrtmp_1442 = tmp_struct_1.field0;
            GibCursor pvrtmp_1443 = tmp_struct_1.field1;
            GibInt pvrtmp_1444 = tmp_struct_1.field2;
            GibInt tailprim_730 = pvrtmp_1441 + pvrtmp_1444;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_1442, pvrtmp_1443,
                                                   tailprim_730};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_3 = *(uintptr_t *) tmpcur_1436;
            GibCursor tmpcur_1445 = GIB_UNTAG(tagged_tmpcur_3);
            GibCursor tmpaftercur_1446 = tmpcur_1436 + 8;
            uint16_t tmptag_1447 = GIB_GET_TAG(tagged_tmpcur_3);
            GibCursor end_from_tagged_indr_781 = tmpcur_1445 + tmptag_1447;
            GibCursor jump_783 = tmpcur_1436 + 8;
            GibCursorGibCursorGibIntProd tmp_struct_2 =
                                          sumTree(end_from_tagged_indr_781, tmpcur_1445);
            GibCursor pvrtmp_1448 = tmp_struct_2.field0;
            GibCursor pvrtmp_1449 = tmp_struct_2.field1;
            GibInt pvrtmp_1450 = tmp_struct_2.field2;

            return (GibCursorGibCursorGibIntProd) {end_r_541, jump_783,
                                                   pvrtmp_1450};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_5 = *(uintptr_t *) tmpcur_1436;
            GibCursor tmpcur_1451 = GIB_UNTAG(tagged_tmpcur_5);
            GibCursor tmpaftercur_1452 = tmpcur_1436 + 8;
            uint16_t tmptag_1453 = GIB_GET_TAG(tagged_tmpcur_5);
            GibCursor end_from_tagged_indr_781 = tmpcur_1451 + tmptag_1453;
            GibCursorGibCursorGibIntProd tmp_struct_4 =
                                          sumTree(end_from_tagged_indr_781, tmpcur_1451);
            GibCursor pvrtmp_1454 = tmp_struct_4.field0;
            GibCursor pvrtmp_1455 = tmp_struct_4.field1;
            GibInt pvrtmp_1456 = tmp_struct_4.field2;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_1454, pvrtmp_1455,
                                                   pvrtmp_1456};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1435");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorProd mkSharedTree(GibCursor end_r_543,
                                             GibCursor loc_542,
                                             GibInt n_57_185_279)
{
    if (loc_542 + 18 > end_r_543) {
        gib_grow_region(&loc_542, &end_r_543);
    }

    GibBool fltIf_262_280 = n_57_185_279 == 0;

    if (fltIf_262_280) {
        *(GibPackedTag *) loc_542 = 0;

        GibCursor writetag_979 = loc_542 + 1;
        GibCursor after_tag_980 = loc_542 + 1;

        *(GibInt *) after_tag_980 = 1;

        GibCursor writecur_984 = after_tag_980 + sizeof(GibInt);

        return (GibCursorGibCursorGibCursorProd) {end_r_543, loc_542,
                                                  writecur_984};
    } else {
        GibInt fltAppE_263_281 = n_57_185_279 - 1;
        GibChunk region_1462 =
                 gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
        GibCursor r_594 = region_1462.start;
        GibCursor end_r_594 = region_1462.end;
        GibCursorGibCursorGibCursorProd tmp_struct_6 =
                                         mkSharedTree(end_r_594, r_594, fltAppE_263_281);
        GibCursor pvrtmp_1463 = tmp_struct_6.field0;
        GibCursor pvrtmp_1464 = tmp_struct_6.field1;
        GibCursor pvrtmp_1465 = tmp_struct_6.field2;
        // _print_Tree(NULL, r_594);
        GibCursorGibCursorGibCursorGibCursorProd tmp_struct_7 =
                                                  caseFn_164(pvrtmp_1463, end_r_543, loc_542, pvrtmp_1464);
        GibCursor pvrtmp_1470 = tmp_struct_7.field0;
        GibCursor pvrtmp_1471 = tmp_struct_7.field1;
        GibCursor pvrtmp_1472 = tmp_struct_7.field2;
        GibCursor pvrtmp_1473 = tmp_struct_7.field3;

        // _print_Tree(NULL, pvrtmp_1472);
        // gib_free_region(end_r_594);
        return (GibCursorGibCursorGibCursorProd) {pvrtmp_1471, pvrtmp_1472,
                                                  pvrtmp_1473};
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_Tree(GibCursor end_r_546,
                                                             GibCursor end_r_547,
                                                             GibCursor loc_545,
                                                             GibCursor arg_98_187_283)
{
    if (loc_545 + 18 > end_r_547) {
        gib_grow_region(&loc_545, &end_r_547);
    }

    GibPackedTag tmpval_1480 = *(GibPackedTag *) arg_98_187_283;
    GibCursor tmpcur_1481 = arg_98_187_283 + 1;


  switch_1538:
    ;
    switch (tmpval_1480) {

      case 0:
        {
            GibInt tmpval_1482 = *(GibInt *) tmpcur_1481;
            GibCursor tmpcur_1483 = tmpcur_1481 + sizeof(GibInt);
            GibCursor jump_733 = tmpcur_1481 + 8;

            *(GibPackedTag *) loc_545 = 0;

            GibCursor writetag_994 = loc_545 + 1;
            GibCursor after_tag_995 = loc_545 + 1;

            *(GibInt *) after_tag_995 = tmpval_1482;

            GibCursor writecur_999 = after_tag_995 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_546,
                                                                        end_r_547,
                                                                        jump_733,
                                                                        loc_545,
                                                                        writecur_999};
            break;
        }

      case 1:
        {
            GibCursor loc_609 = loc_545 + 1;

            *(GibPackedTag *) loc_545 = 1;

            GibCursor writetag_1009 = loc_545 + 1;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_11 =
                                                               _copy_Tree(end_r_546, end_r_547, loc_609, tmpcur_1481);
            GibCursor pvrtmp_1488 = tmp_struct_11.field0;
            GibCursor pvrtmp_1489 = tmp_struct_11.field1;
            GibCursor pvrtmp_1490 = tmp_struct_11.field2;
            GibCursor pvrtmp_1491 = tmp_struct_11.field3;
            GibCursor pvrtmp_1492 = tmp_struct_11.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_12 =
                                                               _copy_Tree(pvrtmp_1488, pvrtmp_1489, pvrtmp_1492, pvrtmp_1490);
            GibCursor pvrtmp_1497 = tmp_struct_12.field0;
            GibCursor pvrtmp_1498 = tmp_struct_12.field1;
            GibCursor pvrtmp_1499 = tmp_struct_12.field2;
            GibCursor pvrtmp_1500 = tmp_struct_12.field3;
            GibCursor pvrtmp_1501 = tmp_struct_12.field4;
            GibCursor after_tag_1010 = loc_545 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_1497,
                                                                        pvrtmp_1498,
                                                                        pvrtmp_1499,
                                                                        loc_545,
                                                                        pvrtmp_1501};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_14 = *(uintptr_t *) tmpcur_1481;
            GibCursor tmpcur_1510 = GIB_UNTAG(tagged_tmpcur_14);
            GibCursor tmpaftercur_1511 = tmpcur_1481 + 8;
            uint16_t tmptag_1512 = GIB_GET_TAG(tagged_tmpcur_14);
            GibCursor end_from_tagged_indr_787 = tmpcur_1510 + tmptag_1512;
            GibCursor jump_789 = tmpcur_1481 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_13 =
                                                               _copy_Tree(end_from_tagged_indr_787, end_r_547, loc_545, tmpcur_1510);
            GibCursor pvrtmp_1513 = tmp_struct_13.field0;
            GibCursor pvrtmp_1514 = tmp_struct_13.field1;
            GibCursor pvrtmp_1515 = tmp_struct_13.field2;
            GibCursor pvrtmp_1516 = tmp_struct_13.field3;
            GibCursor pvrtmp_1517 = tmp_struct_13.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_546,
                                                                        pvrtmp_1514,
                                                                        jump_789,
                                                                        pvrtmp_1516,
                                                                        pvrtmp_1517};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_16 = *(uintptr_t *) tmpcur_1481;
            GibCursor tmpcur_1524 = GIB_UNTAG(tagged_tmpcur_16);
            GibCursor tmpaftercur_1525 = tmpcur_1481 + 8;
            uint16_t tmptag_1526 = GIB_GET_TAG(tagged_tmpcur_16);
            GibCursor end_from_tagged_indr_787 = tmpcur_1524 + tmptag_1526;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_15 =
                                                               _copy_Tree(end_from_tagged_indr_787, end_r_547, loc_545, tmpcur_1524);
            GibCursor pvrtmp_1527 = tmp_struct_15.field0;
            GibCursor pvrtmp_1528 = tmp_struct_15.field1;
            GibCursor pvrtmp_1529 = tmp_struct_15.field2;
            GibCursor pvrtmp_1530 = tmp_struct_15.field3;
            GibCursor pvrtmp_1531 = tmp_struct_15.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_1527,
                                                                        pvrtmp_1528,
                                                                        pvrtmp_1529,
                                                                        pvrtmp_1530,
                                                                        pvrtmp_1531};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1480");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_Tree(GibCursor end_r_550,
                                                                          GibCursor end_r_551,
                                                                          GibCursor loc_549,
                                                                          GibCursor arg_105_194_290)
{
    GibPackedTag tmpval_1539 = *(GibPackedTag *) arg_105_194_290;
    GibCursor tmpcur_1540 = arg_105_194_290 + 1;


  switch_1597:
    ;
    switch (tmpval_1539) {

      case 0:
        {
            GibInt tmpval_1541 = *(GibInt *) tmpcur_1540;
            GibCursor tmpcur_1542 = tmpcur_1540 + sizeof(GibInt);
            GibCursor jump_738 = tmpcur_1540 + 8;

            *(GibPackedTag *) loc_549 = 0;

            GibCursor writetag_1031 = loc_549 + 1;
            GibCursor after_tag_1032 = loc_549 + 1;

            *(GibInt *) after_tag_1032 = tmpval_1541;

            GibCursor writecur_1036 = after_tag_1032 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_550,
                                                                        end_r_551,
                                                                        jump_738,
                                                                        loc_549,
                                                                        writecur_1036};
            break;
        }

      case 1:
        {
            GibCursor loc_627 = loc_549 + 1;

            *(GibPackedTag *) loc_549 = 1;

            GibCursor writetag_1046 = loc_549 + 1;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_20 =
                                                               _copy_without_ptrs_Tree(end_r_550, end_r_551, loc_627, tmpcur_1540);
            GibCursor pvrtmp_1547 = tmp_struct_20.field0;
            GibCursor pvrtmp_1548 = tmp_struct_20.field1;
            GibCursor pvrtmp_1549 = tmp_struct_20.field2;
            GibCursor pvrtmp_1550 = tmp_struct_20.field3;
            GibCursor pvrtmp_1551 = tmp_struct_20.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_21 =
                                                               _copy_without_ptrs_Tree(pvrtmp_1547, pvrtmp_1548, pvrtmp_1551, pvrtmp_1549);
            GibCursor pvrtmp_1556 = tmp_struct_21.field0;
            GibCursor pvrtmp_1557 = tmp_struct_21.field1;
            GibCursor pvrtmp_1558 = tmp_struct_21.field2;
            GibCursor pvrtmp_1559 = tmp_struct_21.field3;
            GibCursor pvrtmp_1560 = tmp_struct_21.field4;
            GibCursor after_tag_1047 = loc_549 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_1556,
                                                                        pvrtmp_1557,
                                                                        pvrtmp_1558,
                                                                        loc_549,
                                                                        pvrtmp_1560};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_23 = *(uintptr_t *) tmpcur_1540;
            GibCursor tmpcur_1569 = GIB_UNTAG(tagged_tmpcur_23);
            GibCursor tmpaftercur_1570 = tmpcur_1540 + 8;
            uint16_t tmptag_1571 = GIB_GET_TAG(tagged_tmpcur_23);
            GibCursor end_from_tagged_indr_793 = tmpcur_1569 + tmptag_1571;
            GibCursor jump_795 = tmpcur_1540 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_22 =
                                                               _copy_without_ptrs_Tree(end_from_tagged_indr_793, end_r_551, loc_549, tmpcur_1569);
            GibCursor pvrtmp_1572 = tmp_struct_22.field0;
            GibCursor pvrtmp_1573 = tmp_struct_22.field1;
            GibCursor pvrtmp_1574 = tmp_struct_22.field2;
            GibCursor pvrtmp_1575 = tmp_struct_22.field3;
            GibCursor pvrtmp_1576 = tmp_struct_22.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_550,
                                                                        pvrtmp_1573,
                                                                        jump_795,
                                                                        pvrtmp_1575,
                                                                        pvrtmp_1576};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_25 = *(uintptr_t *) tmpcur_1540;
            GibCursor tmpcur_1583 = GIB_UNTAG(tagged_tmpcur_25);
            GibCursor tmpaftercur_1584 = tmpcur_1540 + 8;
            uint16_t tmptag_1585 = GIB_GET_TAG(tagged_tmpcur_25);
            GibCursor end_from_tagged_indr_793 = tmpcur_1583 + tmptag_1585;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_24 =
                                                               _copy_without_ptrs_Tree(end_from_tagged_indr_793, end_r_551, loc_549, tmpcur_1583);
            GibCursor pvrtmp_1586 = tmp_struct_24.field0;
            GibCursor pvrtmp_1587 = tmp_struct_24.field1;
            GibCursor pvrtmp_1588 = tmp_struct_24.field2;
            GibCursor pvrtmp_1589 = tmp_struct_24.field3;
            GibCursor pvrtmp_1590 = tmp_struct_24.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_1586,
                                                                        pvrtmp_1587,
                                                                        pvrtmp_1588,
                                                                        pvrtmp_1589,
                                                                        pvrtmp_1590};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1539");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_Tree(GibCursor end_r_553,
                                      GibCursor arg_112_201_297)
{
    GibPackedTag tmpval_1598 = *(GibPackedTag *) arg_112_201_297;
    GibCursor tmpcur_1599 = arg_112_201_297 + 1;


  switch_1616:
    ;
    switch (tmpval_1598) {

      case 0:
        {
            GibInt tmpval_1600 = *(GibInt *) tmpcur_1599;
            GibCursor tmpcur_1601 = tmpcur_1599 + sizeof(GibInt);
            GibCursor jump_743 = tmpcur_1599 + 8;

            return (GibCursorGibCursorProd) {end_r_553, jump_743};
            break;
        }

      case 1:
        {
            GibCursorGibCursorProd tmp_struct_26 =
                                    _traverse_Tree(end_r_553, tmpcur_1599);
            GibCursor pvrtmp_1602 = tmp_struct_26.field0;
            GibCursor pvrtmp_1603 = tmp_struct_26.field1;
            GibCursorGibCursorProd tmp_struct_27 =
                                    _traverse_Tree(pvrtmp_1602, pvrtmp_1603);
            GibCursor pvrtmp_1604 = tmp_struct_27.field0;
            GibCursor pvrtmp_1605 = tmp_struct_27.field1;

            return (GibCursorGibCursorProd) {pvrtmp_1604, pvrtmp_1605};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_29 = *(uintptr_t *) tmpcur_1599;
            GibCursor tmpcur_1606 = GIB_UNTAG(tagged_tmpcur_29);
            GibCursor tmpaftercur_1607 = tmpcur_1599 + 8;
            uint16_t tmptag_1608 = GIB_GET_TAG(tagged_tmpcur_29);
            GibCursor end_from_tagged_indr_799 = tmpcur_1606 + tmptag_1608;
            GibCursor jump_801 = tmpcur_1599 + 8;
            GibCursorGibCursorProd tmp_struct_28 =
                                    _traverse_Tree(end_from_tagged_indr_799, tmpcur_1606);
            GibCursor pvrtmp_1609 = tmp_struct_28.field0;
            GibCursor pvrtmp_1610 = tmp_struct_28.field1;

            return (GibCursorGibCursorProd) {end_r_553, jump_801};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_31 = *(uintptr_t *) tmpcur_1599;
            GibCursor tmpcur_1611 = GIB_UNTAG(tagged_tmpcur_31);
            GibCursor tmpaftercur_1612 = tmpcur_1599 + 8;
            uint16_t tmptag_1613 = GIB_GET_TAG(tagged_tmpcur_31);
            GibCursor end_from_tagged_indr_799 = tmpcur_1611 + tmptag_1613;
            GibCursorGibCursorProd tmp_struct_30 =
                                    _traverse_Tree(end_from_tagged_indr_799, tmpcur_1611);
            GibCursor pvrtmp_1614 = tmp_struct_30.field0;
            GibCursor pvrtmp_1615 = tmp_struct_30.field1;

            return (GibCursorGibCursorProd) {pvrtmp_1614, pvrtmp_1615};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1598");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_Tree(GibCursor end_r_555,
                                   GibCursor arg_119_207_303)
{
    GibPackedTag tmpval_1617 = *(GibPackedTag *) arg_119_207_303;
    GibCursor tmpcur_1618 = arg_119_207_303 + 1;


  switch_1635:
    ;
    switch (tmpval_1617) {

      case 0:
        {
            GibInt tmpval_1619 = *(GibInt *) tmpcur_1618;
            GibCursor tmpcur_1620 = tmpcur_1618 + sizeof(GibInt);
            GibCursor jump_748 = tmpcur_1618 + 8;
            unsigned char wildcard_122_209_305 = gib_print_symbol(1419);
            unsigned char wildcard_125_210_306 = gib_print_symbol(1423);
            unsigned char y_121_211_307 = printf("%ld", tmpval_1619);
            unsigned char wildcard_124_212_308 = gib_print_symbol(1423);
            unsigned char y_121_213_309 = gib_print_symbol(1423);
            unsigned char wildcard_123_214_310 = gib_print_symbol(1416);

            return (GibCursorGibCursorProd) {end_r_555, jump_748};
            break;
        }

      case 1:
        {
            unsigned char wildcard_130_217_313 = gib_print_symbol(1417);
            unsigned char wildcard_135_218_314 = gib_print_symbol(1423);
            GibCursorGibCursorProd tmp_struct_32 =
                                    _print_Tree(end_r_555, tmpcur_1618);
            GibCursor pvrtmp_1621 = tmp_struct_32.field0;
            GibCursor pvrtmp_1622 = tmp_struct_32.field1;
            unsigned char wildcard_134_220_316 = gib_print_symbol(1423);
            unsigned char y_128_221_317 = gib_print_symbol(1423);
            unsigned char wildcard_133_222_318 = gib_print_symbol(1423);
            GibCursorGibCursorProd tmp_struct_33 =
                                    _print_Tree(pvrtmp_1621, pvrtmp_1622);
            GibCursor pvrtmp_1623 = tmp_struct_33.field0;
            GibCursor pvrtmp_1624 = tmp_struct_33.field1;
            unsigned char wildcard_132_224_320 = gib_print_symbol(1423);
            unsigned char y_129_225_321 = gib_print_symbol(1423);
            unsigned char wildcard_131_226_322 = gib_print_symbol(1416);

            return (GibCursorGibCursorProd) {pvrtmp_1623, pvrtmp_1624};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_35 = *(uintptr_t *) tmpcur_1618;
            GibCursor tmpcur_1625 = GIB_UNTAG(tagged_tmpcur_35);
            GibCursor tmpaftercur_1626 = tmpcur_1618 + 8;
            uint16_t tmptag_1627 = GIB_GET_TAG(tagged_tmpcur_35);
            GibCursor end_from_tagged_indr_805 = tmpcur_1625 + tmptag_1627;
            GibCursor jump_807 = tmpcur_1618 + 8;
            unsigned char wildcard_810 = gib_print_symbol(1422);
            GibCursorGibCursorProd tmp_struct_34 =
                                    _print_Tree(end_from_tagged_indr_805, tmpcur_1625);
            GibCursor pvrtmp_1628 = tmp_struct_34.field0;
            GibCursor pvrtmp_1629 = tmp_struct_34.field1;

            return (GibCursorGibCursorProd) {end_r_555, jump_807};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_37 = *(uintptr_t *) tmpcur_1618;
            GibCursor tmpcur_1630 = GIB_UNTAG(tagged_tmpcur_37);
            GibCursor tmpaftercur_1631 = tmpcur_1618 + 8;
            uint16_t tmptag_1632 = GIB_GET_TAG(tagged_tmpcur_37);
            GibCursor end_from_tagged_indr_805 = tmpcur_1630 + tmptag_1632;
            unsigned char wildcard_810 = gib_print_symbol(1421);
            GibCursorGibCursorProd tmp_struct_36 =
                                    _print_Tree(end_from_tagged_indr_805, tmpcur_1630);
            GibCursor pvrtmp_1633 = tmp_struct_36.field0;
            GibCursor pvrtmp_1634 = tmp_struct_36.field1;

            return (GibCursorGibCursorProd) {pvrtmp_1633, pvrtmp_1634};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1617");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_PList(GibCursor end_r_558,
                                                              GibCursor end_r_559,
                                                              GibCursor loc_557,
                                                              GibCursor arg_136_227_323)
{
    if (loc_557 + 18 > end_r_559) {
        gib_grow_region(&loc_557, &end_r_559);
    }

    GibPackedTag tmpval_1636 = *(GibPackedTag *) arg_136_227_323;
    GibCursor tmpcur_1637 = arg_136_227_323 + 1;


  switch_1685:
    ;
    switch (tmpval_1636) {

      case 0:
        {
            GibInt tmpval_1638 = *(GibInt *) tmpcur_1637;
            GibCursor tmpcur_1639 = tmpcur_1637 + sizeof(GibInt);
            GibCursor loc_657 = loc_557 + 9;

            *(GibPackedTag *) loc_557 = 0;

            GibCursor writetag_1101 = loc_557 + 1;
            GibCursor after_tag_1102 = loc_557 + 1;

            *(GibInt *) after_tag_1102 = tmpval_1638;

            GibCursor writecur_1106 = after_tag_1102 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_38 =
                                                               _copy_PList(end_r_558, end_r_559, loc_657, tmpcur_1639);
            GibCursor pvrtmp_1640 = tmp_struct_38.field0;
            GibCursor pvrtmp_1641 = tmp_struct_38.field1;
            GibCursor pvrtmp_1642 = tmp_struct_38.field2;
            GibCursor pvrtmp_1643 = tmp_struct_38.field3;
            GibCursor pvrtmp_1644 = tmp_struct_38.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_1640,
                                                                        pvrtmp_1641,
                                                                        pvrtmp_1642,
                                                                        loc_557,
                                                                        pvrtmp_1644};
            break;
        }

      case 1:
        {
            GibCursor jump_756 = arg_136_227_323 + 1;

            *(GibPackedTag *) loc_557 = 1;

            GibCursor writetag_1111 = loc_557 + 1;
            GibCursor after_tag_1112 = loc_557 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_558,
                                                                        end_r_559,
                                                                        jump_756,
                                                                        loc_557,
                                                                        after_tag_1112};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_40 = *(uintptr_t *) tmpcur_1637;
            GibCursor tmpcur_1657 = GIB_UNTAG(tagged_tmpcur_40);
            GibCursor tmpaftercur_1658 = tmpcur_1637 + 8;
            uint16_t tmptag_1659 = GIB_GET_TAG(tagged_tmpcur_40);
            GibCursor end_from_tagged_indr_811 = tmpcur_1657 + tmptag_1659;
            GibCursor jump_813 = tmpcur_1637 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_39 =
                                                               _copy_PList(end_from_tagged_indr_811, end_r_559, loc_557, tmpcur_1657);
            GibCursor pvrtmp_1660 = tmp_struct_39.field0;
            GibCursor pvrtmp_1661 = tmp_struct_39.field1;
            GibCursor pvrtmp_1662 = tmp_struct_39.field2;
            GibCursor pvrtmp_1663 = tmp_struct_39.field3;
            GibCursor pvrtmp_1664 = tmp_struct_39.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_558,
                                                                        pvrtmp_1661,
                                                                        jump_813,
                                                                        pvrtmp_1663,
                                                                        pvrtmp_1664};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_42 = *(uintptr_t *) tmpcur_1637;
            GibCursor tmpcur_1671 = GIB_UNTAG(tagged_tmpcur_42);
            GibCursor tmpaftercur_1672 = tmpcur_1637 + 8;
            uint16_t tmptag_1673 = GIB_GET_TAG(tagged_tmpcur_42);
            GibCursor end_from_tagged_indr_811 = tmpcur_1671 + tmptag_1673;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_41 =
                                                               _copy_PList(end_from_tagged_indr_811, end_r_559, loc_557, tmpcur_1671);
            GibCursor pvrtmp_1674 = tmp_struct_41.field0;
            GibCursor pvrtmp_1675 = tmp_struct_41.field1;
            GibCursor pvrtmp_1676 = tmp_struct_41.field2;
            GibCursor pvrtmp_1677 = tmp_struct_41.field3;
            GibCursor pvrtmp_1678 = tmp_struct_41.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_1674,
                                                                        pvrtmp_1675,
                                                                        pvrtmp_1676,
                                                                        pvrtmp_1677,
                                                                        pvrtmp_1678};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1636");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_PList(GibCursor end_r_562,
                                                                           GibCursor end_r_563,
                                                                           GibCursor loc_561,
                                                                           GibCursor arg_141_232_328)
{
    GibPackedTag tmpval_1686 = *(GibPackedTag *) arg_141_232_328;
    GibCursor tmpcur_1687 = arg_141_232_328 + 1;


  switch_1735:
    ;
    switch (tmpval_1686) {

      case 0:
        {
            GibInt tmpval_1688 = *(GibInt *) tmpcur_1687;
            GibCursor tmpcur_1689 = tmpcur_1687 + sizeof(GibInt);
            GibCursor loc_670 = loc_561 + 9;

            *(GibPackedTag *) loc_561 = 0;

            GibCursor writetag_1133 = loc_561 + 1;
            GibCursor after_tag_1134 = loc_561 + 1;

            *(GibInt *) after_tag_1134 = tmpval_1688;

            GibCursor writecur_1138 = after_tag_1134 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_46 =
                                                               _copy_without_ptrs_PList(end_r_562, end_r_563, loc_670, tmpcur_1689);
            GibCursor pvrtmp_1690 = tmp_struct_46.field0;
            GibCursor pvrtmp_1691 = tmp_struct_46.field1;
            GibCursor pvrtmp_1692 = tmp_struct_46.field2;
            GibCursor pvrtmp_1693 = tmp_struct_46.field3;
            GibCursor pvrtmp_1694 = tmp_struct_46.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_1690,
                                                                        pvrtmp_1691,
                                                                        pvrtmp_1692,
                                                                        loc_561,
                                                                        pvrtmp_1694};
            break;
        }

      case 1:
        {
            GibCursor jump_761 = arg_141_232_328 + 1;

            *(GibPackedTag *) loc_561 = 1;

            GibCursor writetag_1143 = loc_561 + 1;
            GibCursor after_tag_1144 = loc_561 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_562,
                                                                        end_r_563,
                                                                        jump_761,
                                                                        loc_561,
                                                                        after_tag_1144};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_48 = *(uintptr_t *) tmpcur_1687;
            GibCursor tmpcur_1707 = GIB_UNTAG(tagged_tmpcur_48);
            GibCursor tmpaftercur_1708 = tmpcur_1687 + 8;
            uint16_t tmptag_1709 = GIB_GET_TAG(tagged_tmpcur_48);
            GibCursor end_from_tagged_indr_817 = tmpcur_1707 + tmptag_1709;
            GibCursor jump_819 = tmpcur_1687 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_47 =
                                                               _copy_without_ptrs_PList(end_from_tagged_indr_817, end_r_563, loc_561, tmpcur_1707);
            GibCursor pvrtmp_1710 = tmp_struct_47.field0;
            GibCursor pvrtmp_1711 = tmp_struct_47.field1;
            GibCursor pvrtmp_1712 = tmp_struct_47.field2;
            GibCursor pvrtmp_1713 = tmp_struct_47.field3;
            GibCursor pvrtmp_1714 = tmp_struct_47.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_562,
                                                                        pvrtmp_1711,
                                                                        jump_819,
                                                                        pvrtmp_1713,
                                                                        pvrtmp_1714};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_50 = *(uintptr_t *) tmpcur_1687;
            GibCursor tmpcur_1721 = GIB_UNTAG(tagged_tmpcur_50);
            GibCursor tmpaftercur_1722 = tmpcur_1687 + 8;
            uint16_t tmptag_1723 = GIB_GET_TAG(tagged_tmpcur_50);
            GibCursor end_from_tagged_indr_817 = tmpcur_1721 + tmptag_1723;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_49 =
                                                               _copy_without_ptrs_PList(end_from_tagged_indr_817, end_r_563, loc_561, tmpcur_1721);
            GibCursor pvrtmp_1724 = tmp_struct_49.field0;
            GibCursor pvrtmp_1725 = tmp_struct_49.field1;
            GibCursor pvrtmp_1726 = tmp_struct_49.field2;
            GibCursor pvrtmp_1727 = tmp_struct_49.field3;
            GibCursor pvrtmp_1728 = tmp_struct_49.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_1724,
                                                                        pvrtmp_1725,
                                                                        pvrtmp_1726,
                                                                        pvrtmp_1727,
                                                                        pvrtmp_1728};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1686");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_PList(GibCursor end_r_565,
                                       GibCursor arg_146_237_333)
{
    GibPackedTag tmpval_1736 = *(GibPackedTag *) arg_146_237_333;
    GibCursor tmpcur_1737 = arg_146_237_333 + 1;


  switch_1752:
    ;
    switch (tmpval_1736) {

      case 0:
        {
            GibInt tmpval_1738 = *(GibInt *) tmpcur_1737;
            GibCursor tmpcur_1739 = tmpcur_1737 + sizeof(GibInt);
            GibCursorGibCursorProd tmp_struct_51 =
                                    _traverse_PList(end_r_565, tmpcur_1739);
            GibCursor pvrtmp_1740 = tmp_struct_51.field0;
            GibCursor pvrtmp_1741 = tmp_struct_51.field1;

            return (GibCursorGibCursorProd) {pvrtmp_1740, pvrtmp_1741};
            break;
        }

      case 1:
        {
            GibCursor jump_766 = arg_146_237_333 + 1;

            return (GibCursorGibCursorProd) {end_r_565, jump_766};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_53 = *(uintptr_t *) tmpcur_1737;
            GibCursor tmpcur_1742 = GIB_UNTAG(tagged_tmpcur_53);
            GibCursor tmpaftercur_1743 = tmpcur_1737 + 8;
            uint16_t tmptag_1744 = GIB_GET_TAG(tagged_tmpcur_53);
            GibCursor end_from_tagged_indr_823 = tmpcur_1742 + tmptag_1744;
            GibCursor jump_825 = tmpcur_1737 + 8;
            GibCursorGibCursorProd tmp_struct_52 =
                                    _traverse_PList(end_from_tagged_indr_823, tmpcur_1742);
            GibCursor pvrtmp_1745 = tmp_struct_52.field0;
            GibCursor pvrtmp_1746 = tmp_struct_52.field1;

            return (GibCursorGibCursorProd) {end_r_565, jump_825};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_55 = *(uintptr_t *) tmpcur_1737;
            GibCursor tmpcur_1747 = GIB_UNTAG(tagged_tmpcur_55);
            GibCursor tmpaftercur_1748 = tmpcur_1737 + 8;
            uint16_t tmptag_1749 = GIB_GET_TAG(tagged_tmpcur_55);
            GibCursor end_from_tagged_indr_823 = tmpcur_1747 + tmptag_1749;
            GibCursorGibCursorProd tmp_struct_54 =
                                    _traverse_PList(end_from_tagged_indr_823, tmpcur_1747);
            GibCursor pvrtmp_1750 = tmp_struct_54.field0;
            GibCursor pvrtmp_1751 = tmp_struct_54.field1;

            return (GibCursorGibCursorProd) {pvrtmp_1750, pvrtmp_1751};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1736");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_PList(GibCursor end_r_567,
                                    GibCursor arg_151_241_337)
{
    GibPackedTag tmpval_1753 = *(GibPackedTag *) arg_151_241_337;
    GibCursor tmpcur_1754 = arg_151_241_337 + 1;


  switch_1769:
    ;
    switch (tmpval_1753) {

      case 0:
        {
            GibInt tmpval_1755 = *(GibInt *) tmpcur_1754;
            GibCursor tmpcur_1756 = tmpcur_1754 + sizeof(GibInt);
            unsigned char wildcard_156_244_340 = gib_print_symbol(1420);
            unsigned char wildcard_161_245_341 = gib_print_symbol(1423);
            unsigned char y_154_246_342 = printf("%ld", tmpval_1755);
            unsigned char wildcard_160_247_343 = gib_print_symbol(1423);
            unsigned char y_154_248_344 = gib_print_symbol(1423);
            unsigned char wildcard_159_249_345 = gib_print_symbol(1423);
            GibCursorGibCursorProd tmp_struct_56 =
                                    _print_PList(end_r_567, tmpcur_1756);
            GibCursor pvrtmp_1757 = tmp_struct_56.field0;
            GibCursor pvrtmp_1758 = tmp_struct_56.field1;
            unsigned char wildcard_158_251_347 = gib_print_symbol(1423);
            unsigned char y_155_252_348 = gib_print_symbol(1423);
            unsigned char wildcard_157_253_349 = gib_print_symbol(1416);

            return (GibCursorGibCursorProd) {pvrtmp_1757, pvrtmp_1758};
            break;
        }

      case 1:
        {
            GibCursor jump_771 = arg_151_241_337 + 1;
            unsigned char wildcard_162_254_350 = gib_print_symbol(1418);
            unsigned char wildcard_163_255_351 = gib_print_symbol(1416);

            return (GibCursorGibCursorProd) {end_r_567, jump_771};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_58 = *(uintptr_t *) tmpcur_1754;
            GibCursor tmpcur_1759 = GIB_UNTAG(tagged_tmpcur_58);
            GibCursor tmpaftercur_1760 = tmpcur_1754 + 8;
            uint16_t tmptag_1761 = GIB_GET_TAG(tagged_tmpcur_58);
            GibCursor end_from_tagged_indr_829 = tmpcur_1759 + tmptag_1761;
            GibCursor jump_831 = tmpcur_1754 + 8;
            unsigned char wildcard_834 = gib_print_symbol(1422);
            GibCursorGibCursorProd tmp_struct_57 =
                                    _print_PList(end_from_tagged_indr_829, tmpcur_1759);
            GibCursor pvrtmp_1762 = tmp_struct_57.field0;
            GibCursor pvrtmp_1763 = tmp_struct_57.field1;

            return (GibCursorGibCursorProd) {end_r_567, jump_831};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_60 = *(uintptr_t *) tmpcur_1754;
            GibCursor tmpcur_1764 = GIB_UNTAG(tagged_tmpcur_60);
            GibCursor tmpaftercur_1765 = tmpcur_1754 + 8;
            uint16_t tmptag_1766 = GIB_GET_TAG(tagged_tmpcur_60);
            GibCursor end_from_tagged_indr_829 = tmpcur_1764 + tmptag_1766;
            unsigned char wildcard_834 = gib_print_symbol(1421);
            GibCursorGibCursorProd tmp_struct_59 =
                                    _print_PList(end_from_tagged_indr_829, tmpcur_1764);
            GibCursor pvrtmp_1767 = tmp_struct_59.field0;
            GibCursor pvrtmp_1768 = tmp_struct_59.field1;

            return (GibCursorGibCursorProd) {pvrtmp_1767, pvrtmp_1768};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1753");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd caseFn_164(GibCursor end_r_570,
                                                    GibCursor end_r_571,
                                                    GibCursor loc_569,
                                                    GibCursor tr_58_165_256_352)
{
    if (loc_569 + 18 > end_r_571) {
        gib_grow_region(&loc_569, &end_r_571);
    }

    GibPackedTag tmpval_1770 = *(GibPackedTag *) tr_58_165_256_352;
    GibCursor tmpcur_1771 = tr_58_165_256_352 + 1;


  switch_1816:
    ;
    switch (tmpval_1770) {

      case 0:
        {
            GibInt tmpval_1772 = *(GibInt *) tmpcur_1771;
            GibCursor tmpcur_1773 = tmpcur_1771 + sizeof(GibInt);
            GibCursor loc_696 = loc_569 + 1;

            *(GibPackedTag *) loc_569 = 1;

            GibCursor writetag_1194 = loc_569 + 1;

            if (loc_696 + 18 > end_r_571) {
                gib_grow_region(&loc_696, &end_r_571);
            }
            gib_indirection_barrier(loc_696, end_r_571, tr_58_165_256_352,
                                    end_r_570, Tree_T);

            GibCursor end_1189 = loc_696 + 9;

            if (end_1189 + 18 > end_r_571) {
                gib_grow_region(&end_1189, &end_r_571);
            }
            gib_indirection_barrier(end_1189, end_r_571, tr_58_165_256_352,
                                    end_r_570, Tree_T);

            GibCursor end_1192 = end_1189 + 9;
            GibCursor after_tag_1195 = loc_569 + 1;

            // _print_Tree(NULL, loc_569);

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_570,
                                                               end_r_571,
                                                               loc_569,
                                                               end_1192};
            break;
        }

      case 1:
        {
            GibCursor loc_708 = loc_569 + 1;

            *(GibPackedTag *) loc_569 = 1;

            GibCursor writetag_1211 = loc_569 + 1;

            if (loc_708 + 18 > end_r_571) {
                gib_grow_region(&loc_708, &end_r_571);
            }
            gib_indirection_barrier(loc_708, end_r_571, tr_58_165_256_352,
                                    end_r_570, Tree_T);

            GibCursor end_1206 = loc_708 + 9;

            if (end_1206 + 18 > end_r_571) {
                gib_grow_region(&end_1206, &end_r_571);
            }
            gib_indirection_barrier(end_1206, end_r_571, tr_58_165_256_352,
                                    end_r_570, Tree_T);

            GibCursor end_1209 = end_1206 + 9;
            GibCursor after_tag_1212 = loc_569 + 1;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_570,
                                                               end_r_571,
                                                               loc_569,
                                                               end_1209};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_74 = *(uintptr_t *) tmpcur_1771;
            GibCursor tmpcur_1790 = GIB_UNTAG(tagged_tmpcur_74);
            GibCursor tmpaftercur_1791 = tmpcur_1771 + 8;
            uint16_t tmptag_1792 = GIB_GET_TAG(tagged_tmpcur_74);
            GibCursor end_from_tagged_indr_835 = tmpcur_1790 + tmptag_1792;
            GibCursor jump_837 = tmpcur_1771 + 8;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_73 =
                                                      caseFn_164(end_from_tagged_indr_835, end_r_571, loc_569, tmpcur_1790);
            GibCursor pvrtmp_1793 = tmp_struct_73.field0;
            GibCursor pvrtmp_1794 = tmp_struct_73.field1;
            GibCursor pvrtmp_1795 = tmp_struct_73.field2;
            GibCursor pvrtmp_1796 = tmp_struct_73.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_570,
                                                               pvrtmp_1794,
                                                               pvrtmp_1795,
                                                               pvrtmp_1796};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_76 = *(uintptr_t *) tmpcur_1771;
            GibCursor tmpcur_1803 = GIB_UNTAG(tagged_tmpcur_76);
            GibCursor tmpaftercur_1804 = tmpcur_1771 + 8;
            uint16_t tmptag_1805 = GIB_GET_TAG(tagged_tmpcur_76);
            GibCursor end_from_tagged_indr_835 = tmpcur_1803 + tmptag_1805;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_75 =
                                                      caseFn_164(end_from_tagged_indr_835, end_r_571, loc_569, tmpcur_1803);
            GibCursor pvrtmp_1806 = tmp_struct_75.field0;
            GibCursor pvrtmp_1807 = tmp_struct_75.field1;
            GibCursor pvrtmp_1808 = tmp_struct_75.field2;
            GibCursor pvrtmp_1809 = tmp_struct_75.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_1806,
                                                               pvrtmp_1807,
                                                               pvrtmp_1808,
                                                               pvrtmp_1809};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1770");
            exit(1);
        }
    }
}
int main(int argc, char **argv)
{
    int init_87 = gib_init(argc, argv);

    info_table_initialize();
    symbol_table_initialize();

    GibInt n_38_166_268 = gib_get_size_param();
    GibChunk region_1424 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_577 = region_1424.start;
    GibCursor end_r_577 = region_1424.end;
    GibCursorGibCursorGibCursorProd tmp_struct_80 =
                                     mkSharedTree(end_r_577, r_577, n_38_166_268);
    GibCursor pvrtmp_1425 = tmp_struct_80.field0;
    GibCursor pvrtmp_1426 = tmp_struct_80.field1;
    GibCursor pvrtmp_1427 = tmp_struct_80.field2;

    // _print_Tree(pvrtmp_1425, pvrtmp_1426);
    // printf("\n");
    // fflush(stdout);
    // fflush(stderr);

    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    gib_shadowstack_push(rstack, pvrtmp_1426, pvrtmp_1425, Stk, Tree_T);
    GibInt timed_1295;
    GibVector *times_84 = gib_vector_alloc(gib_get_iters_param(),
                                           sizeof(double));
    struct timespec begin_timed_1295;
    struct timespec end_timed_1295;

    GibGcStateSnapshot *snapshot = gib_gc_init_state(1);
    for (long long iters_timed_1295 = 0; iters_timed_1295 <
         gib_get_iters_param(); iters_timed_1295++) {
        if (iters_timed_1295 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_save_state();
            gib_ptr_bumpalloc_save_state();
            gib_gc_save_state(snapshot, 1, region_1424.end);
        }
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed_1295);

        GibInt tailapp_776 =  addints(10, 20);
        gib_perform_GC(true);

        timed_1295 = tailapp_776;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed_1295);
        if (iters_timed_1295 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_restore_state();
            gib_ptr_bumpalloc_restore_state();
            gib_gc_restore_state(snapshot);
        }

        double itertime_81 = gib_difftimespecs(&begin_timed_1295,
                                               &end_timed_1295);

        // printf("itertime: %lf\n", itertime_81);
        gib_vector_inplace_update(times_84, iters_timed_1295, &itertime_81);
    }
    gib_vector_inplace_sort(times_84, gib_compare_doubles);

    frame = gib_shadowstack_pop(rstack);
    pvrtmp_1426 = frame->ptr;
    pvrtmp_1425 = frame->endptr;

    // _print_Tree(pvrtmp_1425, pvrtmp_1426);
    // printf("\n");
    // fflush(stdout);
    // fflush(stderr);

    double *tmp_85 = (double *) gib_vector_nth(times_84, gib_get_iters_param() / 2);
    double selftimed_83 = *tmp_85;
    double batchtime_82 = gib_sum_timing_array(times_84);

    // gib_print_timing_array(times_84);
    gib_vector_free(times_84);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_82);
    printf("SELFTIMED: %e\n", selftimed_83);

    GibCursorGibCursorGibIntProd tmp_struct_86 =
                                  sumTree(pvrtmp_1425, pvrtmp_1426);
    GibCursor pvrtmp_1432 = tmp_struct_86.field0;
    GibCursor pvrtmp_1433 = tmp_struct_86.field1;
    GibInt pvrtmp_1434 = tmp_struct_86.field2;

    printf("%ld", pvrtmp_1434);
    printf("\n");
    gib_free_region(end_r_577);
    // return 0;

    int exit_88 = gib_exit();

    return exit_88;
}
