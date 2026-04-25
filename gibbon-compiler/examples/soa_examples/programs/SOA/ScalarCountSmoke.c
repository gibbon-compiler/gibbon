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

#ifdef _GIBBON_ENABLE_PAPI
#include <papi.h>
#endif

#ifdef _GIBBON_ENABLE_PAPI_NATIVE
static int gibbon_native_papi_eventset = PAPI_NULL;
static int gibbon_native_papi_inited = 0;
#define GIBBON_NATIVE_PAPI_EVENT_COUNT 7
#define GIBBON_NATIVE_PAPI_MAX_ALTS 4
static const char *gibbon_native_papi_metric_labels[GIBBON_NATIVE_PAPI_EVENT_COUNT] = {
    "CPU_CYCLES",
    "INSTRUCTIONS",
    "L1D_LOAD_MISSES",
    "L1I_LOAD_MISSES",
    "L2D_MISSES",
    "L2I_MISSES",
    "LLC_LOAD_MISSES",
};
static const char *gibbon_native_papi_event_candidates[GIBBON_NATIVE_PAPI_EVENT_COUNT][GIBBON_NATIVE_PAPI_MAX_ALTS] = {
    {"perf::PERF_COUNT_HW_CPU_CYCLES", "perf::CPU-CYCLES", "perf::CYCLES", "ix86arch::UNHALTED_CORE_CYCLES"},
    {"perf::PERF_COUNT_HW_INSTRUCTIONS", "perf::INSTRUCTIONS", "ix86arch::INSTRUCTION_RETIRED", NULL},
    {"perf::L1-DCACHE-LOAD-MISSES", "perf::PERF_COUNT_HW_CACHE_L1D", NULL, NULL},
    {"perf::L1-ICACHE-LOAD-MISSES", "perf::PERF_COUNT_HW_CACHE_L1I", NULL, NULL},
    {"L2_RQSTS:DEMAND_DATA_RD_MISS", "L2_RQSTS:MISS", "L2_REQUEST:DEMAND_DATA_RD_MISS", "L2_REQUEST:MISS"},
    {"L2_RQSTS:CODE_RD_MISS", "L2_REQUEST:CODE_RD_MISS", NULL, NULL},
    {"perf::LLC-LOAD-MISSES", "ix86arch::LLC_MISSES", "LONGEST_LAT_CACHE:MISS", "adl_grt::LONGEST_LAT_CACHE:MISS"},
};
static const char *gibbon_native_papi_selected_events[GIBBON_NATIVE_PAPI_EVENT_COUNT] = {NULL};
static void papi_init_or_die(void) {
    if (gibbon_native_papi_inited) return;
    int rv = PAPI_library_init(PAPI_VER_CURRENT);
    if (rv != PAPI_VER_CURRENT) {
        fprintf(stderr, "PAPI_library_init failed: %d\n", rv);
        exit(1);
    }
    rv = PAPI_create_eventset(&gibbon_native_papi_eventset);
    if (rv != PAPI_OK) {
        fprintf(stderr, "PAPI_create_eventset failed: %s\n", PAPI_strerror(rv));
        exit(1);
    }
    for (int i = 0; i < GIBBON_NATIVE_PAPI_EVENT_COUNT; i++) {
        int added = 0;
        for (int j = 0; j < GIBBON_NATIVE_PAPI_MAX_ALTS; j++) {
            const char *ev_name = gibbon_native_papi_event_candidates[i][j];
            int code;
            if (ev_name == NULL) {
                continue;
            }
            rv = PAPI_event_name_to_code((char*)ev_name, &code);
            if (rv != PAPI_OK) {
                continue;
            }
            rv = PAPI_add_event(gibbon_native_papi_eventset, code);
            if (rv == PAPI_OK) {
                gibbon_native_papi_selected_events[i] = ev_name;
                added = 1;
                break;
            }
        }
        if (!added) {
            fprintf(stderr, "No usable native PAPI event found for metric %s\n", gibbon_native_papi_metric_labels[i]);
            exit(1);
        }
    }
    gibbon_native_papi_inited = 1;
}
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
typedef struct GibCursorPtr3Prod_struct {
            GibCursor field0[3];
        } GibCursorPtr3Prod;
typedef struct GibMutCursorProd_struct {
            GibCursor *field0;
        } GibMutCursorProd;
unsigned char _print_List(GibCursor cursor_ptr_810[3],
                          GibCursor arg_67_83_126[3]);
unsigned char _traverse_List(GibCursor cursor_ptr_900[3],
                             GibCursor arg_60_97_140[3]);
unsigned char mkList(GibCursor cursor_ptr_989[3], GibCursor cursor_ptr_990[3],
                     GibInt len_19_102_145);
unsigned char add1List(GibCursor cursor_ptr_1047[3],
                       GibCursor cursor_ptr_1046[3],
                       GibCursor cursor_ptr_1048[3],
                       GibCursor xs_21_104_149[3]);
unsigned char _copy_List(GibCursor cursor_ptr_1219[3],
                         GibCursor cursor_ptr_1218[3],
                         GibCursor cursor_ptr_1220[3],
                         GibCursor arg_53_108_155[3]);
GibInt sumList(GibCursor cursor_ptr_1390[3], GibCursor xs_25_115_162[3]);
typedef enum {
            GibInt_T,
            GibFloat_T,
            GibSym_T,
            GibBool_T,
            GibVector_T,
            GibList_T,
            GibCursor_T,
            List_T,
        } GibDatatype;
void info_table_initialize(void)
{
    int error = gib_info_table_initialize(8);
    
    if (error < 0) {
        fprintf(stderr, "Couldn't initialize info table, errorno=%d", error);
        exit(1);
    }
    
    GibDatatype field_tys[3];
    
    field_tys[0] = List_T;
    error = gib_info_table_insert_packed_dcon(List_T, 0, 12, 0, 2, 1, field_tys,
                                              1);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, List_T, 0);
        exit(1);
    }
    error = gib_info_table_insert_packed_dcon(List_T, 1, 0, 0, 0, 0, field_tys,
                                              0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, List_T, 1);
        exit(1);
    }
    gib_info_table_finalize();
}
void symbol_table_initialize(void)
{
    gib_add_symbol(1539, ")");
    gib_add_symbol(1540, "(Nil");
    gib_add_symbol(1541, "(Cons");
    gib_add_symbol(1542, " ->r ");
    gib_add_symbol(1543, " ->i ");
    gib_add_symbol(1544, " ");
}
unsigned char _print_List(GibCursor cursor_ptr_810[3],
                          GibCursor arg_67_83_126[3])
{
    GibCursor *end_r_372 = &cursor_ptr_810[0];
    GibCursor *end_r_373 = &cursor_ptr_810[1];
    GibCursor *end_r_374 = &cursor_ptr_810[2];
    GibCursor *restrict loc_369 = &arg_67_83_126[0];
    GibCursor deref_dcon_var_814 = *loc_369;
    GibPackedTag tmpval_1551 = *(GibPackedTag *) deref_dcon_var_814;
    GibCursor tmpcur_1552 = deref_dcon_var_814 + 1;
    
    
  switch_1566:
    ;
    switch (tmpval_1551) {
        
      case 0:
        {
            GibCursor *restrict soa_field_0_816 = &arg_67_83_126[1];
            GibCursor deref_817 = *soa_field_0_816;
            GibCursor *restrict soa_field_1_818 = &arg_67_83_126[2];
            GibCursor deref_819 = *soa_field_1_818;
            GibInt tmpval_1553 = *(GibInt *) deref_817;
            GibCursor tmpcur_1554 = deref_817 + sizeof(GibInt);
            
            *soa_field_0_816 += 8;
            
            GibFloat tmpval_1555 = *(GibFloat *) deref_819;
            GibCursor tmpcur_1556 = deref_819 + sizeof(GibFloat);
            
            *soa_field_1_818 += 4;
            
            GibCursor cursor_ptr_812[3] = {tmpcur_1552, tmpcur_1554,
                                           tmpcur_1556};
            
            *loc_369 += 1;
            
            GibCursor jumpf_floc_loc_572 = deref_817 + 8;
            GibCursor jumpf_floc_loc_573 = deref_819 + 4;
            GibCursor loc_453 = tmpcur_1552 + 0;
            
            *loc_369 += 0;
            
            GibCursor loc_452 = jumpf_floc_loc_573 + 0;
            GibCursor loc_451 = jumpf_floc_loc_572 + 0;
            GibCursor cursor_ptr_828[3] = {tmpcur_1552, jumpf_floc_loc_572,
                                           jumpf_floc_loc_573};
            unsigned char wildcard_74_87_130 = gib_print_symbol(1541);
            unsigned char wildcard_78_88_131 = gib_print_symbol(1544);
            unsigned char y_71_89_132 = printf("%ld", tmpval_1553);
            unsigned char wildcard_77_90_133 = gib_print_symbol(1544);
            unsigned char y_72_91_134 = printf("%.2f", tmpval_1555);
            unsigned char wildcard_76_92_135 = gib_print_symbol(1544);
            unsigned char y_73_93_136 =
                           _print_List(cursor_ptr_810, arg_67_83_126);
            GibCursor loc_cursor_ptr_829[3];
            
            memcpy(loc_cursor_ptr_829, arg_67_83_126, sizeof(GibCursor [3]));
            
            unsigned char wildcard_75_94_137 = gib_print_symbol(1539);
            
            return 0;
            break;
        }
        
      case 1:
        {
            GibCursor *restrict soa_field_0_844 = &arg_67_83_126[1];
            GibCursor deref_845 = *soa_field_0_844;
            GibCursor *restrict soa_field_1_846 = &arg_67_83_126[2];
            GibCursor deref_847 = *soa_field_1_846;
            
            *loc_369 += 1;
            
            GibCursor jump_floc_loc_579 = deref_845 + 0;
            GibCursor jump_floc_loc_580 = deref_847 + 0;
            GibCursor cursor_ptr_850[3] = {tmpcur_1552, jump_floc_loc_579,
                                           jump_floc_loc_580};
            unsigned char wildcard_79_95_138 = gib_print_symbol(1540);
            unsigned char wildcard_80_96_139 = gib_print_symbol(1539);
            
            return 0;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            GibCursor *restrict soa_field_0_852 = &arg_67_83_126[1];
            GibCursor deref_853 = *soa_field_0_852;
            GibCursor *restrict soa_field_1_854 = &arg_67_83_126[2];
            GibCursor deref_855 = *soa_field_1_854;
            
            memcpy(arg_67_83_126, tmpcur_1552, sizeof(GibCursor [3]));
            
            GibCursor jump_dloc_640 = deref_dcon_var_814 + 25;
            
            *loc_369 += 25;
            
            GibCursor deref_861 = *soa_field_0_852;
            GibCursor deref_862 = *soa_field_1_854;
            GibCursor cursor_ptr_860[3] = {jump_dloc_640, deref_861, deref_862};
            unsigned char wildcard_647 = gib_print_symbol(1543);
            unsigned char call_643 =  _print_List(arg_67_83_126, arg_67_83_126);
            GibCursor loc_cursor_ptr_863[3];
            
            memcpy(loc_cursor_ptr_863, arg_67_83_126, sizeof(GibCursor [3]));
            return call_643;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            GibCursor *restrict soa_field_0_878 = &arg_67_83_126[1];
            GibCursor deref_879 = *soa_field_0_878;
            GibCursor *restrict soa_field_1_880 = &arg_67_83_126[2];
            GibCursor deref_881 = *soa_field_1_880;
            uintptr_t tagged_tmpcur_2 = *(uintptr_t *) tmpcur_1552;
            GibCursor tmpcur_1557 = GIB_UNTAG(tagged_tmpcur_2);
            GibCursor tmpaftercur_1558 = tmpcur_1552 + 8;
            uint16_t tmptag_1559 = GIB_GET_TAG(tagged_tmpcur_2);
            
            *(GibCursor *) loc_369 = tmpcur_1557;
            
            GibCursor end_from_tagged_dcon_redir_889 = tmpcur_1557 +
                      tmptag_1559;
            GibCursor field_nxt_887 = deref_879 + 1;
            uintptr_t tagged_tmpcur_1 = *(uintptr_t *) field_nxt_887;
            GibCursor tmpcur_1560 = GIB_UNTAG(tagged_tmpcur_1);
            GibCursor tmpaftercur_1561 = field_nxt_887 + 8;
            uint16_t tmptag_1562 = GIB_GET_TAG(tagged_tmpcur_1);
            
            *(GibCursor *) soa_field_0_878 = tmpcur_1560;
            
            GibCursor end_from_tagged_fld_redir_890 = tmpcur_1560 + tmptag_1562;
            GibCursor field_nxt_888 = deref_881 + 1;
            uintptr_t tagged_tmpcur_0 = *(uintptr_t *) field_nxt_888;
            GibCursor tmpcur_1563 = GIB_UNTAG(tagged_tmpcur_0);
            GibCursor tmpaftercur_1564 = field_nxt_888 + 8;
            uint16_t tmptag_1565 = GIB_GET_TAG(tagged_tmpcur_0);
            
            *(GibCursor *) soa_field_1_880 = tmpcur_1563;
            
            GibCursor end_from_tagged_fld_redir_891 = tmpcur_1563 + tmptag_1565;
            GibCursor indr_636[3] = {tmpcur_1557, tmpcur_1560, tmpcur_1563};
            unsigned char wildcard_647 = gib_print_symbol(1542);
            unsigned char call_643 =  _print_List(arg_67_83_126, arg_67_83_126);
            GibCursor loc_cursor_ptr_892[3];
            
            memcpy(loc_cursor_ptr_892, arg_67_83_126, sizeof(GibCursor [3]));
            return call_643;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1551");
            exit(1);
        }
    }
}
unsigned char _traverse_List(GibCursor cursor_ptr_900[3],
                             GibCursor arg_60_97_140[3])
{
    GibCursor *end_r_378 = &cursor_ptr_900[0];
    GibCursor *end_r_379 = &cursor_ptr_900[1];
    GibCursor *end_r_380 = &cursor_ptr_900[2];
    GibCursor *restrict loc_375 = &arg_60_97_140[0];
    GibCursor deref_dcon_var_904 = *loc_375;
    GibPackedTag tmpval_1567 = *(GibPackedTag *) deref_dcon_var_904;
    GibCursor tmpcur_1568 = deref_dcon_var_904 + 1;
    
    
  switch_1582:
    ;
    switch (tmpval_1567) {
        
      case 0:
        {
            GibCursor *restrict soa_field_0_906 = &arg_60_97_140[1];
            GibCursor deref_907 = *soa_field_0_906;
            GibCursor *restrict soa_field_1_908 = &arg_60_97_140[2];
            GibCursor deref_909 = *soa_field_1_908;
            GibInt tmpval_1569 = *(GibInt *) deref_907;
            GibCursor tmpcur_1570 = deref_907 + sizeof(GibInt);
            
            *soa_field_0_906 += 8;
            
            GibFloat tmpval_1571 = *(GibFloat *) deref_909;
            GibCursor tmpcur_1572 = deref_909 + sizeof(GibFloat);
            
            *soa_field_1_908 += 4;
            
            GibCursor cursor_ptr_902[3] = {tmpcur_1568, tmpcur_1570,
                                           tmpcur_1572};
            
            *loc_375 += 1;
            
            GibCursor jumpf_floc_loc_583 = deref_907 + 8;
            GibCursor jumpf_floc_loc_584 = deref_909 + 4;
            GibCursor loc_466 = tmpcur_1568 + 0;
            
            *loc_375 += 0;
            
            GibCursor loc_465 = jumpf_floc_loc_584 + 0;
            GibCursor loc_464 = jumpf_floc_loc_583 + 0;
            GibCursor cursor_ptr_918[3] = {tmpcur_1568, jumpf_floc_loc_583,
                                           jumpf_floc_loc_584};
            unsigned char y_66_101_144 =
                           _traverse_List(cursor_ptr_900, arg_60_97_140);
            GibCursor loc_cursor_ptr_919[3];
            
            memcpy(loc_cursor_ptr_919, arg_60_97_140, sizeof(GibCursor [3]));
            return 0;
            break;
        }
        
      case 1:
        {
            GibCursor *restrict soa_field_0_934 = &arg_60_97_140[1];
            GibCursor deref_935 = *soa_field_0_934;
            GibCursor *restrict soa_field_1_936 = &arg_60_97_140[2];
            GibCursor deref_937 = *soa_field_1_936;
            
            *loc_375 += 1;
            
            GibCursor jump_floc_loc_590 = deref_935 + 0;
            GibCursor jump_floc_loc_591 = deref_937 + 0;
            GibCursor cursor_ptr_940[3] = {tmpcur_1568, jump_floc_loc_590,
                                           jump_floc_loc_591};
            
            return 0;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            GibCursor *restrict soa_field_0_942 = &arg_60_97_140[1];
            GibCursor deref_943 = *soa_field_0_942;
            GibCursor *restrict soa_field_1_944 = &arg_60_97_140[2];
            GibCursor deref_945 = *soa_field_1_944;
            
            memcpy(arg_60_97_140, tmpcur_1568, sizeof(GibCursor [3]));
            
            GibCursor jump_dloc_652 = deref_dcon_var_904 + 25;
            
            *loc_375 += 25;
            
            GibCursor deref_951 = *soa_field_0_942;
            GibCursor deref_952 = *soa_field_1_944;
            GibCursor cursor_ptr_950[3] = {jump_dloc_652, deref_951, deref_952};
            unsigned char call_655 =
                           _traverse_List(arg_60_97_140, arg_60_97_140);
            GibCursor loc_cursor_ptr_953[3];
            
            memcpy(loc_cursor_ptr_953, arg_60_97_140, sizeof(GibCursor [3]));
            return call_655;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            GibCursor *restrict soa_field_0_968 = &arg_60_97_140[1];
            GibCursor deref_969 = *soa_field_0_968;
            GibCursor *restrict soa_field_1_970 = &arg_60_97_140[2];
            GibCursor deref_971 = *soa_field_1_970;
            uintptr_t tagged_tmpcur_5 = *(uintptr_t *) tmpcur_1568;
            GibCursor tmpcur_1573 = GIB_UNTAG(tagged_tmpcur_5);
            GibCursor tmpaftercur_1574 = tmpcur_1568 + 8;
            uint16_t tmptag_1575 = GIB_GET_TAG(tagged_tmpcur_5);
            
            *(GibCursor *) loc_375 = tmpcur_1573;
            
            GibCursor end_from_tagged_dcon_redir_979 = tmpcur_1573 +
                      tmptag_1575;
            GibCursor field_nxt_977 = deref_969 + 1;
            uintptr_t tagged_tmpcur_4 = *(uintptr_t *) field_nxt_977;
            GibCursor tmpcur_1576 = GIB_UNTAG(tagged_tmpcur_4);
            GibCursor tmpaftercur_1577 = field_nxt_977 + 8;
            uint16_t tmptag_1578 = GIB_GET_TAG(tagged_tmpcur_4);
            
            *(GibCursor *) soa_field_0_968 = tmpcur_1576;
            
            GibCursor end_from_tagged_fld_redir_980 = tmpcur_1576 + tmptag_1578;
            GibCursor field_nxt_978 = deref_971 + 1;
            uintptr_t tagged_tmpcur_3 = *(uintptr_t *) field_nxt_978;
            GibCursor tmpcur_1579 = GIB_UNTAG(tagged_tmpcur_3);
            GibCursor tmpaftercur_1580 = field_nxt_978 + 8;
            uint16_t tmptag_1581 = GIB_GET_TAG(tagged_tmpcur_3);
            
            *(GibCursor *) soa_field_1_970 = tmpcur_1579;
            
            GibCursor end_from_tagged_fld_redir_981 = tmpcur_1579 + tmptag_1581;
            GibCursor indr_648[3] = {tmpcur_1573, tmpcur_1576, tmpcur_1579};
            unsigned char call_655 =
                           _traverse_List(arg_60_97_140, arg_60_97_140);
            GibCursor loc_cursor_ptr_982[3];
            
            memcpy(loc_cursor_ptr_982, arg_60_97_140, sizeof(GibCursor [3]));
            return call_655;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1567");
            exit(1);
        }
    }
}
unsigned char mkList(GibCursor cursor_ptr_989[3], GibCursor cursor_ptr_990[3],
                     GibInt len_19_102_145)
{
    gib_scalar_count_footer_begin();
    
    GibCursor *end_r_386 = &cursor_ptr_989[2];
    GibCursor *end_r_385 = &cursor_ptr_989[1];
    GibCursor *end_r_384 = &cursor_ptr_989[0];
    GibCursor *restrict loc_IntTy_382 = &cursor_ptr_990[1];
    GibCursor deref_992 = *loc_IntTy_382;
    GibCursor cpy_993[3];
    
    memcpy(cpy_993, cursor_ptr_990, sizeof(GibCursor [3]));
    
    GibCursor *restrict loc_FloatTy_383 = &cursor_ptr_990[2];
    GibCursor deref_994 = *loc_FloatTy_383;
    GibCursor *restrict loc_381 = &cursor_ptr_990[0];
    GibCursor deref_995 = *end_r_386;
    GibCursor deref_996 = *loc_FloatTy_383;
    GibCursor deref_997 = *end_r_385;
    GibCursor deref_998 = *loc_IntTy_382;
    GibCursor deref_999 = *end_r_384;
    GibCursor deref_1000 = *loc_381;
    
    if (deref_996 + 13 > deref_995 || (deref_998 + 17 > deref_997 ||
                                       deref_1000 + 34 > deref_999)) {
        gib_grow_region(loc_FloatTy_383, end_r_386);
        gib_grow_region(loc_IntTy_382, end_r_385);
        gib_grow_region(loc_381, end_r_384);
        deref_996 = *loc_FloatTy_383;
        deref_998 = *loc_IntTy_382;
        deref_1000 = *loc_381;
    }
    
    GibBool fltIf_119_146 = len_19_102_145 <= 0;
    
    if (fltIf_119_146) {
        *(GibPackedTag *) deref_1000 = 1;
        
        GibCursor writetag_1004 = deref_1000 + 1;
        GibCursor after_tag_1005 = deref_1000 + 1;
        
        *loc_381 += 1;
        
        GibCursor aft_soa_loc_1010[3] = {after_tag_1005, deref_998, deref_996};
        GibCursor end_taildc_593[3];
        
        memcpy(end_taildc_593, cursor_ptr_990, sizeof(GibCursor [3]));
        gib_scalar_count_footer_end("mkList");
        return 0;
    } else {
        GibInt fltAppE_120_147 = len_19_102_145 - 1;
        GibCursor new_dloc_481 = deref_1000 + 1;
        
        *loc_381 += 1;
        
        GibCursor new_floc_loc_483 = deref_996 + 4;
        
        *loc_FloatTy_383 += 4;
        
        GibCursor new_floc_loc_482 = deref_998 + 8;
        
        *loc_IntTy_382 += 8;
        
        GibCursor cursor_ptr_1017[3] = {new_dloc_481, new_floc_loc_482,
                                        new_floc_loc_483};
        
        *(GibPackedTag *) deref_1000 = 0;
        
        GibCursor writetag_1031 = deref_1000 + 1;
        GibCursor after_tag_1032 = deref_1000 + 1;
        
        gib_scalar_count_footer_bump(deref_997);
        gib_scalar_count_footer_bump(deref_995);
        *(GibInt *) deref_998 = len_19_102_145;
        
        GibCursor writecur_1037 = deref_998 + sizeof(GibInt);
        
        *(GibFloat *) deref_996 = 1.0;
        
        GibCursor writecur_1039 = deref_996 + sizeof(GibFloat);
        unsigned char tup_packed_1029 =
                       mkList(cursor_ptr_989, cursor_ptr_990, fltAppE_120_147);
        GibCursor end_rst_20_103_148[3];
        
        memcpy(end_rst_20_103_148, cursor_ptr_990, sizeof(GibCursor [3]));
        
        GibCursor end_taildc_594[3];
        
        memcpy(end_taildc_594, cursor_ptr_990, sizeof(GibCursor [3]));
        gib_scalar_count_footer_end("mkList");
        return 0;
    }
}
unsigned char add1List(GibCursor cursor_ptr_1047[3],
                       GibCursor cursor_ptr_1046[3],
                       GibCursor cursor_ptr_1048[3], GibCursor xs_21_104_149[3])
{
    GibCursor *end_r_398 = &cursor_ptr_1046[2];
    GibCursor *end_r_397 = &cursor_ptr_1046[1];
    GibCursor *end_r_396 = &cursor_ptr_1046[0];
    GibCursor *restrict loc_IntTy_391 = &cursor_ptr_1048[1];
    GibCursor deref_1050 = *loc_IntTy_391;
    GibCursor cpy_1051[3];
    
    memcpy(cpy_1051, cursor_ptr_1048, sizeof(GibCursor [3]));
    
    GibCursor *restrict loc_390 = &cursor_ptr_1048[0];
    GibCursor *restrict loc_FloatTy_392 = &cursor_ptr_1048[2];
    GibCursor deref_1052 = *loc_FloatTy_392;
    GibCursor deref_1053 = *end_r_398;
    GibCursor deref_1054 = *loc_FloatTy_392;
    GibCursor deref_1055 = *end_r_397;
    GibCursor deref_1056 = *loc_IntTy_391;
    GibCursor deref_1057 = *end_r_396;
    GibCursor deref_1058 = *loc_390;
    
    if (deref_1054 + 13 > deref_1053 || (deref_1056 + 17 > deref_1055 ||
                                         deref_1058 + 34 > deref_1057)) {
        gib_grow_region(loc_FloatTy_392, end_r_398);
        gib_grow_region(loc_IntTy_391, end_r_397);
        gib_grow_region(loc_390, end_r_396);
        deref_1054 = *loc_FloatTy_392;
        deref_1056 = *loc_IntTy_391;
        deref_1058 = *loc_390;
    }
    
    GibCursor *end_r_393 = &cursor_ptr_1047[0];
    GibCursor *end_r_394 = &cursor_ptr_1047[1];
    GibCursor *end_r_395 = &cursor_ptr_1047[2];
    GibCursor *restrict loc_387 = &xs_21_104_149[0];
    GibCursor deref_dcon_var_1062 = *loc_387;
    GibPackedTag tmpval_1583 = *(GibPackedTag *) deref_dcon_var_1062;
    GibCursor tmpcur_1584 = deref_dcon_var_1062 + 1;
    
    
  switch_1598:
    ;
    switch (tmpval_1583) {
        
      case 1:
        {
            GibCursor *restrict soa_field_0_1064 = &xs_21_104_149[1];
            GibCursor deref_1065 = *soa_field_0_1064;
            GibCursor *restrict soa_field_1_1066 = &xs_21_104_149[2];
            GibCursor deref_1067 = *soa_field_1_1066;
            
            *loc_387 += 1;
            
            GibCursor jump_floc_loc_596 = deref_1065 + 0;
            GibCursor jump_floc_loc_597 = deref_1067 + 0;
            GibCursor cursor_ptr_1070[3] = {tmpcur_1584, jump_floc_loc_596,
                                            jump_floc_loc_597};
            
            *(GibPackedTag *) deref_1058 = 1;
            
            GibCursor writetag_1074 = deref_1058 + 1;
            GibCursor after_tag_1075 = deref_1058 + 1;
            
            *loc_390 += 1;
            
            GibCursor aft_soa_loc_1080[3] = {after_tag_1075, deref_1056,
                                             deref_1054};
            GibCursor end_taildc_598[3];
            
            memcpy(end_taildc_598, cursor_ptr_1048, sizeof(GibCursor [3]));
            return 0;
            break;
        }
        
      case 0:
        {
            GibCursor *restrict soa_field_0_1085 = &xs_21_104_149[1];
            GibCursor deref_1086 = *soa_field_0_1085;
            GibCursor *restrict soa_field_1_1087 = &xs_21_104_149[2];
            GibCursor deref_1088 = *soa_field_1_1087;
            GibInt tmpval_1585 = *(GibInt *) deref_1086;
            GibCursor tmpcur_1586 = deref_1086 + sizeof(GibInt);
            
            *soa_field_0_1085 += 8;
            
            GibFloat tmpval_1587 = *(GibFloat *) deref_1088;
            GibCursor tmpcur_1588 = deref_1088 + sizeof(GibFloat);
            
            *soa_field_1_1087 += 4;
            
            GibCursor cursor_ptr_1060[3] = {tmpcur_1584, tmpcur_1586,
                                            tmpcur_1588};
            
            *loc_387 += 1;
            
            GibCursor jumpf_floc_loc_600 = deref_1086 + 8;
            GibCursor jumpf_floc_loc_601 = deref_1088 + 4;
            GibInt fltPkd_121_153 = tmpval_1585 + 1;
            GibCursor new_dloc_510 = deref_1058 + 1;
            
            *loc_390 += 1;
            
            GibCursor new_floc_loc_512 = deref_1054 + 4;
            
            *loc_FloatTy_392 += 4;
            
            GibCursor new_floc_loc_511 = deref_1056 + 8;
            
            *loc_IntTy_391 += 8;
            
            GibCursor cursor_ptr_1101[3] = {new_dloc_510, new_floc_loc_511,
                                            new_floc_loc_512};
            
            *(GibPackedTag *) deref_1058 = 0;
            
            GibCursor writetag_1128 = deref_1058 + 1;
            GibCursor after_tag_1129 = deref_1058 + 1;
            
            *(GibInt *) deref_1056 = fltPkd_121_153;
            
            GibCursor writecur_1133 = deref_1056 + sizeof(GibInt);
            
            *(GibFloat *) deref_1054 = tmpval_1587;
            
            GibCursor writecur_1135 = deref_1054 + sizeof(GibFloat);
            unsigned char tup_packed_1126 =
                           add1List(cursor_ptr_1047, cursor_ptr_1046, cursor_ptr_1048, xs_21_104_149);
            GibCursor end_fltPkd_122_154[3];
            
            memcpy(end_fltPkd_122_154, cursor_ptr_1048, sizeof(GibCursor [3]));
            
            GibCursor loc_cursor_ptr_1102[3];
            
            memcpy(loc_cursor_ptr_1102, xs_21_104_149, sizeof(GibCursor [3]));
            
            GibCursor end_taildc_605[3];
            
            memcpy(end_taildc_605, cursor_ptr_1048, sizeof(GibCursor [3]));
            return 0;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            GibCursor *restrict soa_field_0_1142 = &xs_21_104_149[1];
            GibCursor deref_1143 = *soa_field_0_1142;
            GibCursor *restrict soa_field_1_1144 = &xs_21_104_149[2];
            GibCursor deref_1145 = *soa_field_1_1144;
            
            memcpy(xs_21_104_149, tmpcur_1584, sizeof(GibCursor [3]));
            
            GibCursor jump_dloc_664 = deref_dcon_var_1062 + 25;
            
            *loc_387 += 25;
            
            GibCursor deref_1151 = *soa_field_0_1142;
            GibCursor deref_1152 = *soa_field_1_1144;
            GibCursor cursor_ptr_1150[3] = {jump_dloc_664, deref_1151,
                                            deref_1152};
            unsigned char tup_packed_1177 =
                           add1List(xs_21_104_149, cursor_ptr_1046, cursor_ptr_1048, xs_21_104_149);
            GibCursor end_call_667[3];
            
            memcpy(end_call_667, cursor_ptr_1048, sizeof(GibCursor [3]));
            
            GibCursor loc_cursor_ptr_1153[3];
            
            memcpy(loc_cursor_ptr_1153, xs_21_104_149, sizeof(GibCursor [3]));
            return 0;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            GibCursor *restrict soa_field_0_1180 = &xs_21_104_149[1];
            GibCursor deref_1181 = *soa_field_0_1180;
            GibCursor *restrict soa_field_1_1182 = &xs_21_104_149[2];
            GibCursor deref_1183 = *soa_field_1_1182;
            uintptr_t tagged_tmpcur_8 = *(uintptr_t *) tmpcur_1584;
            GibCursor tmpcur_1589 = GIB_UNTAG(tagged_tmpcur_8);
            GibCursor tmpaftercur_1590 = tmpcur_1584 + 8;
            uint16_t tmptag_1591 = GIB_GET_TAG(tagged_tmpcur_8);
            
            *(GibCursor *) loc_387 = tmpcur_1589;
            
            GibCursor end_from_tagged_dcon_redir_1191 = tmpcur_1589 +
                      tmptag_1591;
            GibCursor field_nxt_1189 = deref_1181 + 1;
            uintptr_t tagged_tmpcur_7 = *(uintptr_t *) field_nxt_1189;
            GibCursor tmpcur_1592 = GIB_UNTAG(tagged_tmpcur_7);
            GibCursor tmpaftercur_1593 = field_nxt_1189 + 8;
            uint16_t tmptag_1594 = GIB_GET_TAG(tagged_tmpcur_7);
            
            *(GibCursor *) soa_field_0_1180 = tmpcur_1592;
            
            GibCursor end_from_tagged_fld_redir_1192 = tmpcur_1592 +
                      tmptag_1594;
            GibCursor field_nxt_1190 = deref_1183 + 1;
            uintptr_t tagged_tmpcur_6 = *(uintptr_t *) field_nxt_1190;
            GibCursor tmpcur_1595 = GIB_UNTAG(tagged_tmpcur_6);
            GibCursor tmpaftercur_1596 = field_nxt_1190 + 8;
            uint16_t tmptag_1597 = GIB_GET_TAG(tagged_tmpcur_6);
            
            *(GibCursor *) soa_field_1_1182 = tmpcur_1595;
            
            GibCursor end_from_tagged_fld_redir_1193 = tmpcur_1595 +
                      tmptag_1597;
            GibCursor indr_660[3] = {tmpcur_1589, tmpcur_1592, tmpcur_1595};
            GibCursor copy_dloc_672 = deref_1058 + 0;
            
            *loc_390 += 0;
            
            GibCursor copy_floc_loc_674 = deref_1054 + 0;
            
            *loc_FloatTy_392 += 0;
            
            GibCursor copy_floc_loc_673 = deref_1056 + 0;
            
            *loc_IntTy_391 += 0;
            
            GibCursor cursor_ptr_1197[3] = {copy_dloc_672, copy_floc_loc_673,
                                            copy_floc_loc_674};
            unsigned char tup_packed_1215 =
                           add1List(xs_21_104_149, cursor_ptr_1046, cursor_ptr_1048, xs_21_104_149);
            GibCursor end_call_667[3];
            
            memcpy(end_call_667, cursor_ptr_1048, sizeof(GibCursor [3]));
            
            GibCursor loc_cursor_ptr_1198[3];
            
            memcpy(loc_cursor_ptr_1198, xs_21_104_149, sizeof(GibCursor [3]));
            return 0;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1583");
            exit(1);
        }
    }
}
unsigned char _copy_List(GibCursor cursor_ptr_1219[3],
                         GibCursor cursor_ptr_1218[3],
                         GibCursor cursor_ptr_1220[3],
                         GibCursor arg_53_108_155[3])
{
    GibCursor *end_r_410 = &cursor_ptr_1218[2];
    GibCursor *end_r_408 = &cursor_ptr_1218[0];
    GibCursor *end_r_409 = &cursor_ptr_1218[1];
    GibCursor *restrict loc_FloatTy_404 = &cursor_ptr_1220[2];
    GibCursor deref_1222 = *loc_FloatTy_404;
    GibCursor cpy_1223[3];
    
    memcpy(cpy_1223, cursor_ptr_1220, sizeof(GibCursor [3]));
    
    GibCursor *restrict loc_402 = &cursor_ptr_1220[0];
    GibCursor *restrict loc_IntTy_403 = &cursor_ptr_1220[1];
    GibCursor deref_1224 = *loc_IntTy_403;
    GibCursor deref_1225 = *end_r_410;
    GibCursor deref_1226 = *loc_FloatTy_404;
    GibCursor deref_1227 = *end_r_409;
    GibCursor deref_1228 = *loc_IntTy_403;
    GibCursor deref_1229 = *end_r_408;
    GibCursor deref_1230 = *loc_402;
    
    if (deref_1226 + 13 > deref_1225 || (deref_1228 + 17 > deref_1227 ||
                                         deref_1230 + 34 > deref_1229)) {
        gib_grow_region(loc_FloatTy_404, end_r_410);
        gib_grow_region(loc_IntTy_403, end_r_409);
        gib_grow_region(loc_402, end_r_408);
        deref_1226 = *loc_FloatTy_404;
        deref_1228 = *loc_IntTy_403;
        deref_1230 = *loc_402;
    }
    
    GibCursor *end_r_405 = &cursor_ptr_1219[0];
    GibCursor *end_r_406 = &cursor_ptr_1219[1];
    GibCursor *end_r_407 = &cursor_ptr_1219[2];
    GibCursor *restrict loc_399 = &arg_53_108_155[0];
    GibCursor deref_dcon_var_1234 = *loc_399;
    GibPackedTag tmpval_1599 = *(GibPackedTag *) deref_dcon_var_1234;
    GibCursor tmpcur_1600 = deref_dcon_var_1234 + 1;
    
    
  switch_1614:
    ;
    switch (tmpval_1599) {
        
      case 0:
        {
            GibCursor *restrict soa_field_0_1236 = &arg_53_108_155[1];
            GibCursor deref_1237 = *soa_field_0_1236;
            GibCursor *restrict soa_field_1_1238 = &arg_53_108_155[2];
            GibCursor deref_1239 = *soa_field_1_1238;
            GibInt tmpval_1601 = *(GibInt *) deref_1237;
            GibCursor tmpcur_1602 = deref_1237 + sizeof(GibInt);
            
            *soa_field_0_1236 += 8;
            
            GibFloat tmpval_1603 = *(GibFloat *) deref_1239;
            GibCursor tmpcur_1604 = deref_1239 + sizeof(GibFloat);
            
            *soa_field_1_1238 += 4;
            
            GibCursor cursor_ptr_1232[3] = {tmpcur_1600, tmpcur_1602,
                                            tmpcur_1604};
            
            *loc_399 += 1;
            
            GibCursor jumpf_floc_loc_607 = deref_1237 + 8;
            GibCursor jumpf_floc_loc_608 = deref_1239 + 4;
            GibCursor new_dloc_538 = deref_1230 + 1;
            
            *loc_402 += 1;
            
            GibCursor new_floc_loc_540 = deref_1226 + 4;
            
            *loc_FloatTy_404 += 4;
            
            GibCursor new_floc_loc_539 = deref_1228 + 8;
            
            *loc_IntTy_403 += 8;
            
            GibCursor cursor_ptr_1252[3] = {new_dloc_538, new_floc_loc_539,
                                            new_floc_loc_540};
            
            *(GibPackedTag *) deref_1230 = 0;
            
            GibCursor writetag_1279 = deref_1230 + 1;
            GibCursor after_tag_1280 = deref_1230 + 1;
            
            *(GibInt *) deref_1228 = tmpval_1601;
            
            GibCursor writecur_1284 = deref_1228 + sizeof(GibInt);
            
            *(GibFloat *) deref_1226 = tmpval_1603;
            
            GibCursor writecur_1286 = deref_1226 + sizeof(GibFloat);
            unsigned char tup_packed_1277 =
                           _copy_List(cursor_ptr_1219, cursor_ptr_1218, cursor_ptr_1220, arg_53_108_155);
            GibCursor end_y_59_114_161[3];
            
            memcpy(end_y_59_114_161, cursor_ptr_1220, sizeof(GibCursor [3]));
            
            GibCursor loc_cursor_ptr_1253[3];
            
            memcpy(loc_cursor_ptr_1253, arg_53_108_155, sizeof(GibCursor [3]));
            
            GibCursor end_taildc_612[3];
            
            memcpy(end_taildc_612, cursor_ptr_1220, sizeof(GibCursor [3]));
            return 0;
            break;
        }
        
      case 1:
        {
            GibCursor *restrict soa_field_0_1293 = &arg_53_108_155[1];
            GibCursor deref_1294 = *soa_field_0_1293;
            GibCursor *restrict soa_field_1_1295 = &arg_53_108_155[2];
            GibCursor deref_1296 = *soa_field_1_1295;
            
            *loc_399 += 1;
            
            GibCursor jump_floc_loc_614 = deref_1294 + 0;
            GibCursor jump_floc_loc_615 = deref_1296 + 0;
            GibCursor cursor_ptr_1299[3] = {tmpcur_1600, jump_floc_loc_614,
                                            jump_floc_loc_615};
            
            *(GibPackedTag *) deref_1230 = 1;
            
            GibCursor writetag_1303 = deref_1230 + 1;
            GibCursor after_tag_1304 = deref_1230 + 1;
            
            *loc_402 += 1;
            
            GibCursor aft_soa_loc_1309[3] = {after_tag_1304, deref_1228,
                                             deref_1226};
            GibCursor end_taildc_616[3];
            
            memcpy(end_taildc_616, cursor_ptr_1220, sizeof(GibCursor [3]));
            return 0;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            GibCursor *restrict soa_field_0_1314 = &arg_53_108_155[1];
            GibCursor deref_1315 = *soa_field_0_1314;
            GibCursor *restrict soa_field_1_1316 = &arg_53_108_155[2];
            GibCursor deref_1317 = *soa_field_1_1316;
            
            memcpy(arg_53_108_155, tmpcur_1600, sizeof(GibCursor [3]));
            
            GibCursor jump_dloc_679 = deref_dcon_var_1234 + 25;
            
            *loc_399 += 25;
            
            GibCursor deref_1323 = *soa_field_0_1314;
            GibCursor deref_1324 = *soa_field_1_1316;
            GibCursor cursor_ptr_1322[3] = {jump_dloc_679, deref_1323,
                                            deref_1324};
            unsigned char tup_packed_1349 =
                           _copy_List(arg_53_108_155, cursor_ptr_1218, cursor_ptr_1220, arg_53_108_155);
            GibCursor end_call_682[3];
            
            memcpy(end_call_682, cursor_ptr_1220, sizeof(GibCursor [3]));
            
            GibCursor loc_cursor_ptr_1325[3];
            
            memcpy(loc_cursor_ptr_1325, arg_53_108_155, sizeof(GibCursor [3]));
            return 0;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            GibCursor *restrict soa_field_0_1352 = &arg_53_108_155[1];
            GibCursor deref_1353 = *soa_field_0_1352;
            GibCursor *restrict soa_field_1_1354 = &arg_53_108_155[2];
            GibCursor deref_1355 = *soa_field_1_1354;
            uintptr_t tagged_tmpcur_11 = *(uintptr_t *) tmpcur_1600;
            GibCursor tmpcur_1605 = GIB_UNTAG(tagged_tmpcur_11);
            GibCursor tmpaftercur_1606 = tmpcur_1600 + 8;
            uint16_t tmptag_1607 = GIB_GET_TAG(tagged_tmpcur_11);
            
            *(GibCursor *) loc_399 = tmpcur_1605;
            
            GibCursor end_from_tagged_dcon_redir_1363 = tmpcur_1605 +
                      tmptag_1607;
            GibCursor field_nxt_1361 = deref_1353 + 1;
            uintptr_t tagged_tmpcur_10 = *(uintptr_t *) field_nxt_1361;
            GibCursor tmpcur_1608 = GIB_UNTAG(tagged_tmpcur_10);
            GibCursor tmpaftercur_1609 = field_nxt_1361 + 8;
            uint16_t tmptag_1610 = GIB_GET_TAG(tagged_tmpcur_10);
            
            *(GibCursor *) soa_field_0_1352 = tmpcur_1608;
            
            GibCursor end_from_tagged_fld_redir_1364 = tmpcur_1608 +
                      tmptag_1610;
            GibCursor field_nxt_1362 = deref_1355 + 1;
            uintptr_t tagged_tmpcur_9 = *(uintptr_t *) field_nxt_1362;
            GibCursor tmpcur_1611 = GIB_UNTAG(tagged_tmpcur_9);
            GibCursor tmpaftercur_1612 = field_nxt_1362 + 8;
            uint16_t tmptag_1613 = GIB_GET_TAG(tagged_tmpcur_9);
            
            *(GibCursor *) soa_field_1_1354 = tmpcur_1611;
            
            GibCursor end_from_tagged_fld_redir_1365 = tmpcur_1611 +
                      tmptag_1613;
            GibCursor indr_675[3] = {tmpcur_1605, tmpcur_1608, tmpcur_1611};
            GibCursor copy_dloc_687 = deref_1230 + 0;
            
            *loc_402 += 0;
            
            GibCursor copy_floc_loc_689 = deref_1226 + 0;
            
            *loc_FloatTy_404 += 0;
            
            GibCursor copy_floc_loc_688 = deref_1228 + 0;
            
            *loc_IntTy_403 += 0;
            
            GibCursor cursor_ptr_1369[3] = {copy_dloc_687, copy_floc_loc_688,
                                            copy_floc_loc_689};
            unsigned char tup_packed_1387 =
                           _copy_List(arg_53_108_155, cursor_ptr_1218, cursor_ptr_1220, arg_53_108_155);
            GibCursor end_call_682[3];
            
            memcpy(end_call_682, cursor_ptr_1220, sizeof(GibCursor [3]));
            
            GibCursor loc_cursor_ptr_1370[3];
            
            memcpy(loc_cursor_ptr_1370, arg_53_108_155, sizeof(GibCursor [3]));
            return 0;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1599");
            exit(1);
        }
    }
}
GibInt sumList(GibCursor cursor_ptr_1390[3], GibCursor xs_25_115_162[3])
{
    GibCursor *end_r_414 = &cursor_ptr_1390[0];
    GibCursor *end_r_415 = &cursor_ptr_1390[1];
    GibCursor *end_r_416 = &cursor_ptr_1390[2];
    GibCursor *restrict loc_411 = &xs_25_115_162[0];
    GibCursor deref_dcon_var_1394 = *loc_411;
    GibPackedTag tmpval_1615 = *(GibPackedTag *) deref_dcon_var_1394;
    GibCursor tmpcur_1616 = deref_dcon_var_1394 + 1;
    
    
  switch_1630:
    ;
    switch (tmpval_1615) {
        
      case 1:
        {
            GibCursor *restrict soa_field_0_1396 = &xs_25_115_162[1];
            GibCursor deref_1397 = *soa_field_0_1396;
            GibCursor *restrict soa_field_1_1398 = &xs_25_115_162[2];
            GibCursor deref_1399 = *soa_field_1_1398;
            
            *loc_411 += 1;
            
            GibCursor jump_floc_loc_619 = deref_1397 + 0;
            GibCursor jump_floc_loc_620 = deref_1399 + 0;
            GibCursor cursor_ptr_1402[3] = {tmpcur_1616, jump_floc_loc_619,
                                            jump_floc_loc_620};
            
            return 0;
            break;
        }
        
      case 0:
        {
            GibCursor *restrict soa_field_0_1404 = &xs_25_115_162[1];
            GibCursor deref_1405 = *soa_field_0_1404;
            GibCursor *restrict soa_field_1_1406 = &xs_25_115_162[2];
            GibCursor deref_1407 = *soa_field_1_1406;
            GibInt tmpval_1617 = *(GibInt *) deref_1405;
            GibCursor tmpcur_1618 = deref_1405 + sizeof(GibInt);
            
            *soa_field_0_1404 += 8;
            
            GibFloat tmpval_1619 = *(GibFloat *) deref_1407;
            GibCursor tmpcur_1620 = deref_1407 + sizeof(GibFloat);
            GibCursor cursor_ptr_1392[3] = {tmpcur_1616, tmpcur_1618,
                                            tmpcur_1620};
            
            *loc_411 += 1;
            
            GibCursor jumpf_floc_loc_622 = deref_1405 + 8;
            GibCursor jumpf_floc_loc_623 = deref_1407 + 4;
            GibCursor loc_557 = tmpcur_1616 + 0;
            
            *loc_411 += 0;
            
            GibCursor loc_556 = jumpf_floc_loc_623 + 0;
            GibCursor loc_555 = jumpf_floc_loc_622 + 0;
            GibCursor cursor_ptr_1415[3] = {tmpcur_1616, jumpf_floc_loc_622,
                                            jumpf_floc_loc_623};
            GibInt fltPrm_123_166 =  sumList(cursor_ptr_1390, xs_25_115_162);
            GibCursor loc_cursor_ptr_1416[3];
            
            memcpy(loc_cursor_ptr_1416, xs_25_115_162, sizeof(GibCursor [3]));
            
            GibInt tailprim_627 = tmpval_1617 + fltPrm_123_166;
            
            return tailprim_627;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            GibCursor *restrict soa_field_0_1431 = &xs_25_115_162[1];
            GibCursor deref_1432 = *soa_field_0_1431;
            GibCursor *restrict soa_field_1_1433 = &xs_25_115_162[2];
            GibCursor deref_1434 = *soa_field_1_1433;
            
            memcpy(xs_25_115_162, tmpcur_1616, sizeof(GibCursor [3]));
            
            GibCursor jump_dloc_694 = deref_dcon_var_1394 + 25;
            
            *loc_411 += 25;
            
            GibCursor deref_1440 = *soa_field_0_1431;
            GibCursor deref_1441 = *soa_field_1_1433;
            GibCursor cursor_ptr_1439[3] = {jump_dloc_694, deref_1440,
                                            deref_1441};
            GibInt call_697 =  sumList(xs_25_115_162, xs_25_115_162);
            GibCursor loc_cursor_ptr_1442[3];
            
            memcpy(loc_cursor_ptr_1442, xs_25_115_162, sizeof(GibCursor [3]));
            return call_697;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            GibCursor *restrict soa_field_0_1457 = &xs_25_115_162[1];
            GibCursor deref_1458 = *soa_field_0_1457;
            GibCursor *restrict soa_field_1_1459 = &xs_25_115_162[2];
            GibCursor deref_1460 = *soa_field_1_1459;
            uintptr_t tagged_tmpcur_14 = *(uintptr_t *) tmpcur_1616;
            GibCursor tmpcur_1621 = GIB_UNTAG(tagged_tmpcur_14);
            GibCursor tmpaftercur_1622 = tmpcur_1616 + 8;
            uint16_t tmptag_1623 = GIB_GET_TAG(tagged_tmpcur_14);
            
            *(GibCursor *) loc_411 = tmpcur_1621;
            
            GibCursor end_from_tagged_dcon_redir_1468 = tmpcur_1621 +
                      tmptag_1623;
            GibCursor field_nxt_1466 = deref_1458 + 1;
            uintptr_t tagged_tmpcur_13 = *(uintptr_t *) field_nxt_1466;
            GibCursor tmpcur_1624 = GIB_UNTAG(tagged_tmpcur_13);
            GibCursor tmpaftercur_1625 = field_nxt_1466 + 8;
            uint16_t tmptag_1626 = GIB_GET_TAG(tagged_tmpcur_13);
            
            *(GibCursor *) soa_field_0_1457 = tmpcur_1624;
            
            GibCursor end_from_tagged_fld_redir_1469 = tmpcur_1624 +
                      tmptag_1626;
            GibCursor field_nxt_1467 = deref_1460 + 1;
            uintptr_t tagged_tmpcur_12 = *(uintptr_t *) field_nxt_1467;
            GibCursor tmpcur_1627 = GIB_UNTAG(tagged_tmpcur_12);
            GibCursor tmpaftercur_1628 = field_nxt_1467 + 8;
            uint16_t tmptag_1629 = GIB_GET_TAG(tagged_tmpcur_12);
            GibCursor end_from_tagged_fld_redir_1470 = tmpcur_1627 +
                      tmptag_1629;
            GibCursor indr_690[3] = {tmpcur_1621, tmpcur_1624, tmpcur_1627};
            GibInt call_697 =  sumList(xs_25_115_162, xs_25_115_162);
            GibCursor loc_cursor_ptr_1471[3];
            
            memcpy(loc_cursor_ptr_1471, xs_25_115_162, sizeof(GibCursor [3]));
            return call_697;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1615");
            exit(1);
        }
    }
}
int main(int argc, char **argv)
{
    int init_15 = gib_init(argc, argv);
    
    info_table_initialize();
    symbol_table_initialize();
    
    GibChunk region_1545 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_444 = region_1545.start;
    GibCursor end_r_444 = region_1545.end;
    GibChunk region_1546 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_445 = region_1546.start;
    GibCursor end_r_445 = region_1546.end;
    GibChunk region_1547 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_446 = region_1547.start;
    GibCursor end_r_446 = region_1547.end;
    GibCursor reg_ptr_1478[3] = {r_444, r_445, r_446};
    GibCursor reg_cursor_ptr_1479[3] = {end_r_444, end_r_445, end_r_446};
    GibCursor cursor_ptr_1480[3];
    
    memcpy(cursor_ptr_1480, reg_ptr_1478, sizeof(GibCursor [3]));
    
    unsigned char tup_packed_1492 =
                   mkList(reg_cursor_ptr_1479, cursor_ptr_1480, 10000);
    GibCursor end_xs_17_81_124[3];
    
    memcpy(end_xs_17_81_124, cursor_ptr_1480, sizeof(GibCursor [3]));
    
    GibChunk region_1548 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_441 = region_1548.start;
    GibCursor end_r_441 = region_1548.end;
    GibChunk region_1549 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_442 = region_1549.start;
    GibCursor end_r_442 = region_1549.end;
    GibChunk region_1550 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_443 = region_1550.start;
    GibCursor end_r_443 = region_1550.end;
    GibCursor reg_ptr_1494[3] = {r_441, r_442, r_443};
    GibCursor reg_cursor_ptr_1495[3] = {end_r_441, end_r_442, end_r_443};
    GibCursor cursor_ptr_1496[3];
    
    memcpy(cursor_ptr_1496, reg_ptr_1494, sizeof(GibCursor [3]));
    
    GibCursor copy_address_1502[3];
    
    memcpy(copy_address_1502, reg_ptr_1478, sizeof(GibCursor [3]));
    
    unsigned char tup_packed_1521 =
                   add1List(reg_cursor_ptr_1479, reg_cursor_ptr_1495, cursor_ptr_1496, copy_address_1502);
    GibCursor end_xs__18_82_125[3];
    
    memcpy(end_xs__18_82_125, cursor_ptr_1496, sizeof(GibCursor [3]));
    
    GibCursor copy_address_1526[3];
    
    memcpy(copy_address_1526, reg_ptr_1494, sizeof(GibCursor [3]));
    
    GibInt tailapp_631 =  sumList(reg_cursor_ptr_1495, copy_address_1526);
    
    printf("%ld", tailapp_631);
    printf("\n");
    
    int exit_16 = gib_exit();
    
    return exit_16;
}