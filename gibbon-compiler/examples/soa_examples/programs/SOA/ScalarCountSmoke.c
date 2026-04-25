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
unsigned char _print_List(GibCursor cursor_ptr_820[3],
                          GibCursor arg_67_83_126[3]);
unsigned char _traverse_List(GibCursor cursor_ptr_912[3],
                             GibCursor arg_60_97_140[3]);
unsigned char mkList(GibCursor cursor_ptr_1003[3], GibCursor cursor_ptr_1004[3],
                     GibInt len_19_102_145);
unsigned char add1List(GibCursor cursor_ptr_1061[3],
                       GibCursor cursor_ptr_1060[3],
                       GibCursor cursor_ptr_1062[3],
                       GibCursor xs_21_104_149[3]);
unsigned char _copy_List(GibCursor cursor_ptr_1235[3],
                         GibCursor cursor_ptr_1234[3],
                         GibCursor cursor_ptr_1236[3],
                         GibCursor arg_53_108_155[3]);
GibInt sumList(GibCursor cursor_ptr_1408[3], GibCursor xs_25_115_162[3]);
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
    gib_add_symbol(1560, ")");
    gib_add_symbol(1561, "(Nil");
    gib_add_symbol(1562, "(Cons");
    gib_add_symbol(1563, " ->r ");
    gib_add_symbol(1564, " ->i ");
    gib_add_symbol(1565, " ");
}
unsigned char _print_List(GibCursor cursor_ptr_820[3],
                          GibCursor arg_67_83_126[3])
{
    GibCursor *end_r_372 = &cursor_ptr_820[0];
    GibCursor *end_r_373 = &cursor_ptr_820[1];
    GibCursor *end_r_374 = &cursor_ptr_820[2];
    GibCursor *restrict loc_369 = &arg_67_83_126[0];
    GibCursor deref_dcon_var_824 = *loc_369;
    GibPackedTag tmpval_1572 = *(GibPackedTag *) deref_dcon_var_824;
    GibCursor tmpcur_1573 = deref_dcon_var_824 + 1;
    
    
  switch_1596:
    ;
    switch (tmpval_1572) {
        
      case 0:
        {
            GibCursor *restrict soa_field_0_826 = &arg_67_83_126[1];
            GibCursor deref_827 = *soa_field_0_826;
            GibCursor *restrict soa_field_1_828 = &arg_67_83_126[2];
            GibCursor deref_829 = *soa_field_1_828;
            GibInt tmpval_1574 = *(GibInt *) deref_827;
            GibCursor tmpcur_1575 = deref_827 + sizeof(GibInt);
            
            *soa_field_0_826 += 8;
            
            GibFloat tmpval_1576 = *(GibFloat *) deref_829;
            GibCursor tmpcur_1577 = deref_829 + sizeof(GibFloat);
            
            *soa_field_1_828 += 4;
            
            GibCursor cursor_ptr_822[3] = {tmpcur_1573, tmpcur_1575,
                                           tmpcur_1577};
            
            *loc_369 += 1;
            
            GibCursor jumpf_floc_loc_572 = deref_827 + 8;
            GibCursor jumpf_floc_loc_573 = deref_829 + 4;
            GibCursor loc_453 = tmpcur_1573 + 0;
            
            *loc_369 += 0;
            
            GibCursor loc_452 = jumpf_floc_loc_573 + 0;
            GibCursor loc_451 = jumpf_floc_loc_572 + 0;
            GibCursor cursor_ptr_838[3] = {tmpcur_1573, jumpf_floc_loc_572,
                                           jumpf_floc_loc_573};
            unsigned char wildcard_74_87_130 = gib_print_symbol(1562);
            unsigned char wildcard_78_88_131 = gib_print_symbol(1565);
            unsigned char y_71_89_132 = printf("%ld", tmpval_1574);
            unsigned char wildcard_77_90_133 = gib_print_symbol(1565);
            unsigned char y_72_91_134 = printf("%.2f", tmpval_1576);
            unsigned char wildcard_76_92_135 = gib_print_symbol(1565);
            unsigned char y_73_93_136 =
                           _print_List(cursor_ptr_820, arg_67_83_126);
            GibCursor loc_cursor_ptr_839[3];
            
            memcpy(loc_cursor_ptr_839, arg_67_83_126, sizeof(GibCursor [3]));
            
            unsigned char wildcard_75_94_137 = gib_print_symbol(1560);
            
            return 0;
            break;
        }
        
      case 1:
        {
            GibCursor *restrict soa_field_0_854 = &arg_67_83_126[1];
            GibCursor deref_855 = *soa_field_0_854;
            GibCursor *restrict soa_field_1_856 = &arg_67_83_126[2];
            GibCursor deref_857 = *soa_field_1_856;
            
            *loc_369 += 1;
            
            GibCursor jump_floc_loc_579 = deref_855 + 0;
            GibCursor jump_floc_loc_580 = deref_857 + 0;
            GibCursor cursor_ptr_860[3] = {tmpcur_1573, jump_floc_loc_579,
                                           jump_floc_loc_580};
            unsigned char wildcard_79_95_138 = gib_print_symbol(1561);
            unsigned char wildcard_80_96_139 = gib_print_symbol(1560);
            
            return 0;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            GibCursor *restrict soa_field_0_862 = &arg_67_83_126[1];
            GibCursor deref_863 = *soa_field_0_862;
            GibCursor *restrict soa_field_1_864 = &arg_67_83_126[2];
            GibCursor deref_865 = *soa_field_1_864;
            uintptr_t tagged_tmpcur_2 = *(uintptr_t *) tmpcur_1573;
            GibCursor tmpcur_1578 = GIB_UNTAG(tagged_tmpcur_2);
            GibCursor tmpaftercur_1579 = tmpcur_1573 + 8;
            uint16_t tmptag_1580 = GIB_GET_TAG(tagged_tmpcur_2);
            
            *(GibCursor *) loc_369 = tmpcur_1578;
            
            GibCursor end_from_tagged_dcon_redir_878 = tmpcur_1578 +
                      tmptag_1580;
            GibCursor field_nxt_875 = deref_863 + 1;
            uintptr_t tagged_tmpcur_1 = *(uintptr_t *) field_nxt_875;
            GibCursor tmpcur_1581 = GIB_UNTAG(tagged_tmpcur_1);
            GibCursor tmpaftercur_1582 = field_nxt_875 + 8;
            uint16_t tmptag_1583 = GIB_GET_TAG(tagged_tmpcur_1);
            
            *(GibCursor *) soa_field_0_862 = tmpcur_1581;
            
            GibCursor end_from_tagged_fld_redir_879 = tmpcur_1581 + tmptag_1583;
            GibCursor field_nxt_876 = deref_865 + 1;
            uintptr_t tagged_tmpcur_0 = *(uintptr_t *) field_nxt_876;
            GibCursor tmpcur_1584 = GIB_UNTAG(tagged_tmpcur_0);
            GibCursor tmpaftercur_1585 = field_nxt_876 + 8;
            uint16_t tmptag_1586 = GIB_GET_TAG(tagged_tmpcur_0);
            
            *(GibCursor *) soa_field_1_864 = tmpcur_1584;
            
            GibCursor end_from_tagged_fld_redir_880 = tmpcur_1584 + tmptag_1586;
            GibCursor indr_636[3] = {tmpcur_1578, tmpcur_1581, tmpcur_1584};
            GibCursor jump_dloc_640 = deref_dcon_var_824 + 9;
            GibCursor aft_indir_loc_648 = deref_863 + 9;
            GibCursor aft_indir_loc_649 = deref_865 + 9;
            GibCursor cursor_ptr_881[3] = {jump_dloc_640, aft_indir_loc_648,
                                           aft_indir_loc_649};
            unsigned char wildcard_647 = gib_print_symbol(1564);
            unsigned char call_643 =  _print_List(arg_67_83_126, arg_67_83_126);
            GibCursor loc_cursor_ptr_882[3];
            
            memcpy(loc_cursor_ptr_882, arg_67_83_126, sizeof(GibCursor [3]));
            return call_643;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            GibCursor *restrict soa_field_0_890 = &arg_67_83_126[1];
            GibCursor deref_891 = *soa_field_0_890;
            GibCursor *restrict soa_field_1_892 = &arg_67_83_126[2];
            GibCursor deref_893 = *soa_field_1_892;
            uintptr_t tagged_tmpcur_5 = *(uintptr_t *) tmpcur_1573;
            GibCursor tmpcur_1587 = GIB_UNTAG(tagged_tmpcur_5);
            GibCursor tmpaftercur_1588 = tmpcur_1573 + 8;
            uint16_t tmptag_1589 = GIB_GET_TAG(tagged_tmpcur_5);
            
            *(GibCursor *) loc_369 = tmpcur_1587;
            
            GibCursor end_from_tagged_dcon_redir_901 = tmpcur_1587 +
                      tmptag_1589;
            GibCursor field_nxt_899 = deref_891 + 1;
            uintptr_t tagged_tmpcur_4 = *(uintptr_t *) field_nxt_899;
            GibCursor tmpcur_1590 = GIB_UNTAG(tagged_tmpcur_4);
            GibCursor tmpaftercur_1591 = field_nxt_899 + 8;
            uint16_t tmptag_1592 = GIB_GET_TAG(tagged_tmpcur_4);
            
            *(GibCursor *) soa_field_0_890 = tmpcur_1590;
            
            GibCursor end_from_tagged_fld_redir_902 = tmpcur_1590 + tmptag_1592;
            GibCursor field_nxt_900 = deref_893 + 1;
            uintptr_t tagged_tmpcur_3 = *(uintptr_t *) field_nxt_900;
            GibCursor tmpcur_1593 = GIB_UNTAG(tagged_tmpcur_3);
            GibCursor tmpaftercur_1594 = field_nxt_900 + 8;
            uint16_t tmptag_1595 = GIB_GET_TAG(tagged_tmpcur_3);
            
            *(GibCursor *) soa_field_1_892 = tmpcur_1593;
            
            GibCursor end_from_tagged_fld_redir_903 = tmpcur_1593 + tmptag_1595;
            GibCursor indr_636[3] = {tmpcur_1587, tmpcur_1590, tmpcur_1593};
            unsigned char wildcard_647 = gib_print_symbol(1563);
            unsigned char call_643 =  _print_List(arg_67_83_126, arg_67_83_126);
            GibCursor loc_cursor_ptr_904[3];
            
            memcpy(loc_cursor_ptr_904, arg_67_83_126, sizeof(GibCursor [3]));
            return call_643;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1572");
            exit(1);
        }
    }
}
unsigned char _traverse_List(GibCursor cursor_ptr_912[3],
                             GibCursor arg_60_97_140[3])
{
    GibCursor *end_r_378 = &cursor_ptr_912[0];
    GibCursor *end_r_379 = &cursor_ptr_912[1];
    GibCursor *end_r_380 = &cursor_ptr_912[2];
    GibCursor *restrict loc_375 = &arg_60_97_140[0];
    GibCursor deref_dcon_var_916 = *loc_375;
    GibPackedTag tmpval_1597 = *(GibPackedTag *) deref_dcon_var_916;
    GibCursor tmpcur_1598 = deref_dcon_var_916 + 1;
    
    
  switch_1621:
    ;
    switch (tmpval_1597) {
        
      case 0:
        {
            GibCursor *restrict soa_field_0_918 = &arg_60_97_140[1];
            GibCursor deref_919 = *soa_field_0_918;
            GibCursor *restrict soa_field_1_920 = &arg_60_97_140[2];
            GibCursor deref_921 = *soa_field_1_920;
            GibInt tmpval_1599 = *(GibInt *) deref_919;
            GibCursor tmpcur_1600 = deref_919 + sizeof(GibInt);
            
            *soa_field_0_918 += 8;
            
            GibFloat tmpval_1601 = *(GibFloat *) deref_921;
            GibCursor tmpcur_1602 = deref_921 + sizeof(GibFloat);
            
            *soa_field_1_920 += 4;
            
            GibCursor cursor_ptr_914[3] = {tmpcur_1598, tmpcur_1600,
                                           tmpcur_1602};
            
            *loc_375 += 1;
            
            GibCursor jumpf_floc_loc_583 = deref_919 + 8;
            GibCursor jumpf_floc_loc_584 = deref_921 + 4;
            GibCursor loc_466 = tmpcur_1598 + 0;
            
            *loc_375 += 0;
            
            GibCursor loc_465 = jumpf_floc_loc_584 + 0;
            GibCursor loc_464 = jumpf_floc_loc_583 + 0;
            GibCursor cursor_ptr_930[3] = {tmpcur_1598, jumpf_floc_loc_583,
                                           jumpf_floc_loc_584};
            unsigned char y_66_101_144 =
                           _traverse_List(cursor_ptr_912, arg_60_97_140);
            GibCursor loc_cursor_ptr_931[3];
            
            memcpy(loc_cursor_ptr_931, arg_60_97_140, sizeof(GibCursor [3]));
            return 0;
            break;
        }
        
      case 1:
        {
            GibCursor *restrict soa_field_0_946 = &arg_60_97_140[1];
            GibCursor deref_947 = *soa_field_0_946;
            GibCursor *restrict soa_field_1_948 = &arg_60_97_140[2];
            GibCursor deref_949 = *soa_field_1_948;
            
            *loc_375 += 1;
            
            GibCursor jump_floc_loc_590 = deref_947 + 0;
            GibCursor jump_floc_loc_591 = deref_949 + 0;
            GibCursor cursor_ptr_952[3] = {tmpcur_1598, jump_floc_loc_590,
                                           jump_floc_loc_591};
            
            return 0;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            GibCursor *restrict soa_field_0_954 = &arg_60_97_140[1];
            GibCursor deref_955 = *soa_field_0_954;
            GibCursor *restrict soa_field_1_956 = &arg_60_97_140[2];
            GibCursor deref_957 = *soa_field_1_956;
            uintptr_t tagged_tmpcur_8 = *(uintptr_t *) tmpcur_1598;
            GibCursor tmpcur_1603 = GIB_UNTAG(tagged_tmpcur_8);
            GibCursor tmpaftercur_1604 = tmpcur_1598 + 8;
            uint16_t tmptag_1605 = GIB_GET_TAG(tagged_tmpcur_8);
            
            *(GibCursor *) loc_375 = tmpcur_1603;
            
            GibCursor end_from_tagged_dcon_redir_970 = tmpcur_1603 +
                      tmptag_1605;
            GibCursor field_nxt_967 = deref_955 + 1;
            uintptr_t tagged_tmpcur_7 = *(uintptr_t *) field_nxt_967;
            GibCursor tmpcur_1606 = GIB_UNTAG(tagged_tmpcur_7);
            GibCursor tmpaftercur_1607 = field_nxt_967 + 8;
            uint16_t tmptag_1608 = GIB_GET_TAG(tagged_tmpcur_7);
            
            *(GibCursor *) soa_field_0_954 = tmpcur_1606;
            
            GibCursor end_from_tagged_fld_redir_971 = tmpcur_1606 + tmptag_1608;
            GibCursor field_nxt_968 = deref_957 + 1;
            uintptr_t tagged_tmpcur_6 = *(uintptr_t *) field_nxt_968;
            GibCursor tmpcur_1609 = GIB_UNTAG(tagged_tmpcur_6);
            GibCursor tmpaftercur_1610 = field_nxt_968 + 8;
            uint16_t tmptag_1611 = GIB_GET_TAG(tagged_tmpcur_6);
            
            *(GibCursor *) soa_field_1_956 = tmpcur_1609;
            
            GibCursor end_from_tagged_fld_redir_972 = tmpcur_1609 + tmptag_1611;
            GibCursor indr_650[3] = {tmpcur_1603, tmpcur_1606, tmpcur_1609};
            GibCursor jump_dloc_654 = deref_dcon_var_916 + 9;
            GibCursor aft_indir_loc_662 = deref_955 + 9;
            GibCursor aft_indir_loc_663 = deref_957 + 9;
            GibCursor cursor_ptr_973[3] = {jump_dloc_654, aft_indir_loc_662,
                                           aft_indir_loc_663};
            unsigned char call_657 =
                           _traverse_List(arg_60_97_140, arg_60_97_140);
            GibCursor loc_cursor_ptr_974[3];
            
            memcpy(loc_cursor_ptr_974, arg_60_97_140, sizeof(GibCursor [3]));
            return call_657;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            GibCursor *restrict soa_field_0_982 = &arg_60_97_140[1];
            GibCursor deref_983 = *soa_field_0_982;
            GibCursor *restrict soa_field_1_984 = &arg_60_97_140[2];
            GibCursor deref_985 = *soa_field_1_984;
            uintptr_t tagged_tmpcur_11 = *(uintptr_t *) tmpcur_1598;
            GibCursor tmpcur_1612 = GIB_UNTAG(tagged_tmpcur_11);
            GibCursor tmpaftercur_1613 = tmpcur_1598 + 8;
            uint16_t tmptag_1614 = GIB_GET_TAG(tagged_tmpcur_11);
            
            *(GibCursor *) loc_375 = tmpcur_1612;
            
            GibCursor end_from_tagged_dcon_redir_993 = tmpcur_1612 +
                      tmptag_1614;
            GibCursor field_nxt_991 = deref_983 + 1;
            uintptr_t tagged_tmpcur_10 = *(uintptr_t *) field_nxt_991;
            GibCursor tmpcur_1615 = GIB_UNTAG(tagged_tmpcur_10);
            GibCursor tmpaftercur_1616 = field_nxt_991 + 8;
            uint16_t tmptag_1617 = GIB_GET_TAG(tagged_tmpcur_10);
            
            *(GibCursor *) soa_field_0_982 = tmpcur_1615;
            
            GibCursor end_from_tagged_fld_redir_994 = tmpcur_1615 + tmptag_1617;
            GibCursor field_nxt_992 = deref_985 + 1;
            uintptr_t tagged_tmpcur_9 = *(uintptr_t *) field_nxt_992;
            GibCursor tmpcur_1618 = GIB_UNTAG(tagged_tmpcur_9);
            GibCursor tmpaftercur_1619 = field_nxt_992 + 8;
            uint16_t tmptag_1620 = GIB_GET_TAG(tagged_tmpcur_9);
            
            *(GibCursor *) soa_field_1_984 = tmpcur_1618;
            
            GibCursor end_from_tagged_fld_redir_995 = tmpcur_1618 + tmptag_1620;
            GibCursor indr_650[3] = {tmpcur_1612, tmpcur_1615, tmpcur_1618};
            unsigned char call_657 =
                           _traverse_List(arg_60_97_140, arg_60_97_140);
            GibCursor loc_cursor_ptr_996[3];
            
            memcpy(loc_cursor_ptr_996, arg_60_97_140, sizeof(GibCursor [3]));
            return call_657;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1597");
            exit(1);
        }
    }
}
unsigned char mkList(GibCursor cursor_ptr_1003[3], GibCursor cursor_ptr_1004[3],
                     GibInt len_19_102_145)
{
    gib_scalar_count_footer_begin();
    
    GibCursor *end_r_386 = &cursor_ptr_1003[2];
    GibCursor *end_r_384 = &cursor_ptr_1003[0];
    GibCursor *end_r_385 = &cursor_ptr_1003[1];
    GibCursor *restrict loc_IntTy_382 = &cursor_ptr_1004[1];
    GibCursor deref_1006 = *loc_IntTy_382;
    GibCursor cpy_1007[3];
    
    memcpy(cpy_1007, cursor_ptr_1004, sizeof(GibCursor [3]));
    
    GibCursor *restrict loc_FloatTy_383 = &cursor_ptr_1004[2];
    GibCursor deref_1008 = *loc_FloatTy_383;
    GibCursor *restrict loc_381 = &cursor_ptr_1004[0];
    GibCursor deref_1009 = *end_r_386;
    GibCursor deref_1010 = *loc_FloatTy_383;
    GibCursor deref_1011 = *end_r_385;
    GibCursor deref_1012 = *loc_IntTy_382;
    GibCursor deref_1013 = *end_r_384;
    GibCursor deref_1014 = *loc_381;
    
    if (deref_1010 + 13 > deref_1009 || (deref_1012 + 17 > deref_1011 ||
                                         deref_1014 + 34 > deref_1013)) {
        gib_grow_region(loc_FloatTy_383, end_r_386);
        gib_grow_region(loc_IntTy_382, end_r_385);
        gib_grow_region(loc_381, end_r_384);
        deref_1010 = *loc_FloatTy_383;
        deref_1012 = *loc_IntTy_382;
        deref_1014 = *loc_381;
    }
    
    GibBool fltIf_119_146 = len_19_102_145 <= 0;
    
    if (fltIf_119_146) {
        *(GibPackedTag *) deref_1014 = 1;
        
        GibCursor writetag_1018 = deref_1014 + 1;
        GibCursor after_tag_1019 = deref_1014 + 1;
        
        *loc_381 += 1;
        
        GibCursor aft_soa_loc_1024[3] = {after_tag_1019, deref_1012,
                                         deref_1010};
        GibCursor end_taildc_593[3];
        
        memcpy(end_taildc_593, cursor_ptr_1004, sizeof(GibCursor [3]));
        gib_scalar_count_footer_end("mkList");
        return 0;
    } else {
        GibInt fltAppE_120_147 = len_19_102_145 - 1;
        GibCursor new_dloc_481 = deref_1014 + 1;
        
        *loc_381 += 1;
        
        GibCursor new_floc_loc_483 = deref_1010 + 4;
        
        *loc_FloatTy_383 += 4;
        
        GibCursor new_floc_loc_482 = deref_1012 + 8;
        
        *loc_IntTy_382 += 8;
        
        GibCursor cursor_ptr_1031[3] = {new_dloc_481, new_floc_loc_482,
                                        new_floc_loc_483};
        
        *(GibPackedTag *) deref_1014 = 0;
        
        GibCursor writetag_1045 = deref_1014 + 1;
        GibCursor after_tag_1046 = deref_1014 + 1;
        
        gib_scalar_count_footer_bump(deref_1011);
        gib_scalar_count_footer_bump(deref_1009);
        *(GibInt *) deref_1012 = len_19_102_145;
        
        GibCursor writecur_1051 = deref_1012 + sizeof(GibInt);
        
        *(GibFloat *) deref_1010 = 1.0;
        
        GibCursor writecur_1053 = deref_1010 + sizeof(GibFloat);
        unsigned char tup_packed_1043 =
                       mkList(cursor_ptr_1003, cursor_ptr_1004, fltAppE_120_147);
        GibCursor end_rst_20_103_148[3];
        
        memcpy(end_rst_20_103_148, cursor_ptr_1004, sizeof(GibCursor [3]));
        
        GibCursor end_taildc_594[3];
        
        memcpy(end_taildc_594, cursor_ptr_1004, sizeof(GibCursor [3]));
        gib_scalar_count_footer_end("mkList");
        return 0;
    }
}
unsigned char add1List(GibCursor cursor_ptr_1061[3],
                       GibCursor cursor_ptr_1060[3],
                       GibCursor cursor_ptr_1062[3], GibCursor xs_21_104_149[3])
{
    GibCursor loop_mut_input_end_scalar0 = cursor_ptr_1061[1];
    GibCursor loop_mut_first_footer =
              gib_scalar_count_first_footer(loop_mut_input_end_scalar0);
    GibCursor tmp_copy_22 = loop_mut_input_end_scalar0;
    GibCursor *loop_mut_count_footer_loc = &tmp_copy_22;
    GibCursor tmp_copy_21 = loop_mut_first_footer;
    GibCursor *loop_mut_next_footer_loc = &tmp_copy_21;
    GibInt loop_mut_first_chunk_count =
           gib_scalar_count_footer_get(loop_mut_input_end_scalar0);
    GibCursor *restrict loop_mut_in_dcon_loc = &xs_21_104_149[0];
    GibCursor *restrict loop_mut_out_dcon_loc = &cursor_ptr_1062[0];
    GibCursor *restrict loop_mut_out_dcon_end_loc = &cursor_ptr_1060[0];
    GibCursor loop_mut_out_dcon_cur = *loop_mut_out_dcon_loc;
    GibCursor loop_mut_out_dcon_end = cursor_ptr_1060[0];
    GibInt loop_mut_dcon_bytes = loop_mut_first_chunk_count + 9;
    GibCursor loop_mut_dcon_req = loop_mut_out_dcon_cur + loop_mut_dcon_bytes;
    GibBool loop_mut_dcon_fits = loop_mut_dcon_req <= loop_mut_out_dcon_end;
    GibCursor *restrict loop_mut_in_loc_0 = &xs_21_104_149[1];
    GibCursor *restrict loop_mut_out_loc_0 = &cursor_ptr_1062[1];
    GibCursor *restrict loop_mut_out_end_loc_0 = &cursor_ptr_1060[1];
    GibCursor loop_mut_out_cur_pre_0 = *loop_mut_out_loc_0;
    GibCursor loop_mut_out_end_0 = cursor_ptr_1060[1];
    GibInt loop_mut_req_bytes_0 = loop_mut_first_chunk_count * 8;
    GibCursor loop_mut_req_end_0 = loop_mut_out_cur_pre_0 +
              loop_mut_req_bytes_0;
    GibBool loop_mut_fits_0 = loop_mut_req_end_0 <= loop_mut_out_end_0;
    GibCursor *restrict loop_mut_in_loc_1 = &xs_21_104_149[2];
    GibCursor *restrict loop_mut_out_loc_1 = &cursor_ptr_1062[2];
    GibCursor *restrict loop_mut_out_end_loc_1 = &cursor_ptr_1060[2];
    GibCursor loop_mut_out_cur_pre_1 = *loop_mut_out_loc_1;
    GibCursor loop_mut_out_end_1 = cursor_ptr_1060[2];
    GibInt loop_mut_req_bytes_1 = loop_mut_first_chunk_count * 4;
    GibCursor loop_mut_req_end_1 = loop_mut_out_cur_pre_1 +
              loop_mut_req_bytes_1;
    GibBool loop_mut_fits_1 = loop_mut_req_end_1 <= loop_mut_out_end_1;
    GibBool fltPrm_1559 = loop_mut_fits_0 && loop_mut_fits_1;
    GibBool loop_mut_fast_ok = loop_mut_dcon_fits && fltPrm_1559;
    
    if (loop_mut_fast_ok) {
        while (*loop_mut_count_footer_loc != NULL) {
            GibCursor loop_mut_current_count_footer =
                      *loop_mut_count_footer_loc;
            GibInt loop_mut_chunk_count =
                   gib_scalar_count_footer_get(loop_mut_current_count_footer);
            GibCursor loop_mut_current_next_footer = *loop_mut_next_footer_loc;
            GibBool loop_mut_is_null_next_footer =
                    loop_mut_current_next_footer == 0;
            GibBool loop_mut_is_end_next_footer =
                    loop_mut_current_next_footer == loop_mut_input_end_scalar0;
            GibBool loop_mut_is_last_chunk = loop_mut_is_null_next_footer ||
                    loop_mut_is_end_next_footer;
            
            for (GibInt loop_mut_dcon_i = 0; loop_mut_dcon_i <
                 loop_mut_chunk_count; loop_mut_dcon_i++) {
                GibCursor loop_mut_dcon_read_cur = *loop_mut_in_dcon_loc;
                GibPackedTag tmptag_1622 =
                             *(GibPackedTag *) loop_mut_dcon_read_cur;
                GibCursor tmpcur_1623 = loop_mut_dcon_read_cur + 1;
                GibCursor loop_mut_dcon_write_cur = *loop_mut_out_dcon_loc;
                
                *(GibPackedTag *) loop_mut_dcon_write_cur = tmptag_1622;
                
                GibCursor loop_mut_dcon_write = loop_mut_dcon_write_cur + 1;
                
                *loop_mut_out_dcon_loc += 1;
                *loop_mut_in_dcon_loc += 1;
            }
            for (GibInt loop_mut_field_i_0 = 0; loop_mut_field_i_0 <
                 loop_mut_chunk_count; loop_mut_field_i_0++) {
                GibCursor loop_mut_in_cur_0 = *loop_mut_in_loc_0;
                GibInt tmpval_1624 = *(GibInt *) loop_mut_in_cur_0;
                GibCursor tmpcur_1625 = loop_mut_in_cur_0 + sizeof(GibInt);
                GibInt loop_mut_field_val_0 = tmpval_1624 + 1;
                GibCursor loop_mut_out_cur_0 = *loop_mut_out_loc_0;
                
                *(GibInt *) loop_mut_out_cur_0 = loop_mut_field_val_0;
                
                GibCursor loop_mut_write_cur_0 = loop_mut_out_cur_0 +
                          sizeof(GibInt);
                
                *loop_mut_in_loc_0 += 8;
                *loop_mut_out_loc_0 += 8;
            }
            for (GibInt loop_mut_field_i_1 = 0; loop_mut_field_i_1 <
                 loop_mut_chunk_count; loop_mut_field_i_1++) {
                GibCursor loop_mut_in_cur_1 = *loop_mut_in_loc_1;
                GibFloat tmpval_1626 = *(GibFloat *) loop_mut_in_cur_1;
                GibCursor tmpcur_1627 = loop_mut_in_cur_1 + sizeof(GibFloat);
                GibCursor loop_mut_out_cur_1 = *loop_mut_out_loc_1;
                
                *(GibFloat *) loop_mut_out_cur_1 = tmpval_1626;
                
                GibCursor loop_mut_write_cur_1 = loop_mut_out_cur_1 +
                          sizeof(GibFloat);
                
                *loop_mut_in_loc_1 += 4;
                *loop_mut_out_loc_1 += 4;
            }
            
            GibCursor loop_mut_boundary_read_cur = *loop_mut_in_dcon_loc;
            GibPackedTag tmptag_1628 =
                         *(GibPackedTag *) loop_mut_boundary_read_cur;
            GibCursor tmpcur_1629 = loop_mut_boundary_read_cur + 1;
            
            if (loop_mut_is_last_chunk) {
                GibCursor loop_mut_dcon_base_cur = *loop_mut_out_dcon_loc;
                
                *(GibPackedTag *) loop_mut_dcon_base_cur = tmptag_1628;
                
                GibCursor loop_mut_dcon_base_write = loop_mut_dcon_base_cur + 1;
                
                *loop_mut_out_dcon_loc += 1;
                *(GibCursor *) loop_mut_in_dcon_loc = tmpcur_1629;
                *(GibCursor *) loop_mut_count_footer_loc = 0;
            } else {
                uintptr_t tagged_tmpcur_14 = *(uintptr_t *) tmpcur_1629;
                GibCursor tmpcur_1630 = GIB_UNTAG(tagged_tmpcur_14);
                GibCursor tmpaftercur_1631 = tmpcur_1629 + 8;
                uint16_t tmptag_1632 = GIB_GET_TAG(tagged_tmpcur_14);
                
                gib_grow_region(loop_mut_out_dcon_loc,
                                loop_mut_out_dcon_end_loc);
                *(GibCursor *) loop_mut_in_dcon_loc = tmpcur_1630;
                
                GibCursor loop_mut_boundary_cur_0 = *loop_mut_in_loc_0;
                GibPackedTag tmptag_1633 =
                             *(GibPackedTag *) loop_mut_boundary_cur_0;
                GibCursor tmpcur_1634 = loop_mut_boundary_cur_0 + 1;
                uintptr_t tagged_tmpcur_13 = *(uintptr_t *) tmpcur_1634;
                GibCursor tmpcur_1635 = GIB_UNTAG(tagged_tmpcur_13);
                GibCursor tmpaftercur_1636 = tmpcur_1634 + 8;
                uint16_t tmptag_1637 = GIB_GET_TAG(tagged_tmpcur_13);
                
                gib_grow_region(loop_mut_out_loc_0, loop_mut_out_end_loc_0);
                *(GibCursor *) loop_mut_in_loc_0 = tmpcur_1635;
                
                GibCursor loop_mut_boundary_cur_1 = *loop_mut_in_loc_1;
                GibPackedTag tmptag_1638 =
                             *(GibPackedTag *) loop_mut_boundary_cur_1;
                GibCursor tmpcur_1639 = loop_mut_boundary_cur_1 + 1;
                uintptr_t tagged_tmpcur_12 = *(uintptr_t *) tmpcur_1639;
                GibCursor tmpcur_1640 = GIB_UNTAG(tagged_tmpcur_12);
                GibCursor tmpaftercur_1641 = tmpcur_1639 + 8;
                uint16_t tmptag_1642 = GIB_GET_TAG(tagged_tmpcur_12);
                
                gib_grow_region(loop_mut_out_loc_1, loop_mut_out_end_loc_1);
                *(GibCursor *) loop_mut_in_loc_1 = tmpcur_1640;
                
                GibCursor loop_mut_next_next_footer =
                          gib_scalar_count_footer_next(loop_mut_current_next_footer);
                
                *(GibCursor *) loop_mut_count_footer_loc =
                    loop_mut_current_next_footer;
                *(GibCursor *) loop_mut_next_footer_loc =
                    loop_mut_next_next_footer;
            }
        }
        return 0;
    } else {
        GibCursor *end_r_398 = &cursor_ptr_1060[2];
        GibCursor *end_r_397 = &cursor_ptr_1060[1];
        GibCursor *end_r_396 = &cursor_ptr_1060[0];
        GibCursor *restrict loc_IntTy_391 = &cursor_ptr_1062[1];
        GibCursor deref_1064 = *loc_IntTy_391;
        GibCursor cpy_1065[3];
        
        memcpy(cpy_1065, cursor_ptr_1062, sizeof(GibCursor [3]));
        
        GibCursor *restrict loc_390 = &cursor_ptr_1062[0];
        GibCursor *restrict loc_FloatTy_392 = &cursor_ptr_1062[2];
        GibCursor deref_1066 = *loc_FloatTy_392;
        GibCursor deref_1067 = *end_r_398;
        GibCursor deref_1068 = *loc_FloatTy_392;
        GibCursor deref_1069 = *end_r_397;
        GibCursor deref_1070 = *loc_IntTy_391;
        GibCursor deref_1071 = *end_r_396;
        GibCursor deref_1072 = *loc_390;
        
        if (deref_1068 + 13 > deref_1067 || (deref_1070 + 17 > deref_1069 ||
                                             deref_1072 + 34 > deref_1071)) {
            gib_grow_region(loc_FloatTy_392, end_r_398);
            gib_grow_region(loc_IntTy_391, end_r_397);
            gib_grow_region(loc_390, end_r_396);
            deref_1068 = *loc_FloatTy_392;
            deref_1070 = *loc_IntTy_391;
            deref_1072 = *loc_390;
        }
        
        GibCursor *end_r_393 = &cursor_ptr_1061[0];
        GibCursor *end_r_394 = &cursor_ptr_1061[1];
        GibCursor *end_r_395 = &cursor_ptr_1061[2];
        GibCursor *restrict loc_387 = &xs_21_104_149[0];
        GibCursor deref_dcon_var_1076 = *loc_387;
        GibPackedTag tmpval_1643 = *(GibPackedTag *) deref_dcon_var_1076;
        GibCursor tmpcur_1644 = deref_dcon_var_1076 + 1;
        
        
      switch_1667:
        ;
        switch (tmpval_1643) {
            
          case 1:
            {
                GibCursor *restrict soa_field_0_1078 = &xs_21_104_149[1];
                GibCursor deref_1079 = *soa_field_0_1078;
                GibCursor *restrict soa_field_1_1080 = &xs_21_104_149[2];
                GibCursor deref_1081 = *soa_field_1_1080;
                
                *loc_387 += 1;
                
                GibCursor jump_floc_loc_596 = deref_1079 + 0;
                GibCursor jump_floc_loc_597 = deref_1081 + 0;
                GibCursor cursor_ptr_1084[3] = {tmpcur_1644, jump_floc_loc_596,
                                                jump_floc_loc_597};
                
                *(GibPackedTag *) deref_1072 = 1;
                
                GibCursor writetag_1088 = deref_1072 + 1;
                GibCursor after_tag_1089 = deref_1072 + 1;
                
                *loc_390 += 1;
                
                GibCursor aft_soa_loc_1094[3] = {after_tag_1089, deref_1070,
                                                 deref_1068};
                GibCursor end_taildc_598[3];
                
                memcpy(end_taildc_598, cursor_ptr_1062, sizeof(GibCursor [3]));
                return 0;
                break;
            }
            
          case 0:
            {
                GibCursor *restrict soa_field_0_1099 = &xs_21_104_149[1];
                GibCursor deref_1100 = *soa_field_0_1099;
                GibCursor *restrict soa_field_1_1101 = &xs_21_104_149[2];
                GibCursor deref_1102 = *soa_field_1_1101;
                GibInt tmpval_1645 = *(GibInt *) deref_1100;
                GibCursor tmpcur_1646 = deref_1100 + sizeof(GibInt);
                
                *soa_field_0_1099 += 8;
                
                GibFloat tmpval_1647 = *(GibFloat *) deref_1102;
                GibCursor tmpcur_1648 = deref_1102 + sizeof(GibFloat);
                
                *soa_field_1_1101 += 4;
                
                GibCursor cursor_ptr_1074[3] = {tmpcur_1644, tmpcur_1646,
                                                tmpcur_1648};
                
                *loc_387 += 1;
                
                GibCursor jumpf_floc_loc_600 = deref_1100 + 8;
                GibCursor jumpf_floc_loc_601 = deref_1102 + 4;
                GibInt fltPkd_121_153 = tmpval_1645 + 1;
                GibCursor new_dloc_510 = deref_1072 + 1;
                
                *loc_390 += 1;
                
                GibCursor new_floc_loc_512 = deref_1068 + 4;
                
                *loc_FloatTy_392 += 4;
                
                GibCursor new_floc_loc_511 = deref_1070 + 8;
                
                *loc_IntTy_391 += 8;
                
                GibCursor cursor_ptr_1115[3] = {new_dloc_510, new_floc_loc_511,
                                                new_floc_loc_512};
                
                *(GibPackedTag *) deref_1072 = 0;
                
                GibCursor writetag_1142 = deref_1072 + 1;
                GibCursor after_tag_1143 = deref_1072 + 1;
                
                *(GibInt *) deref_1070 = fltPkd_121_153;
                
                GibCursor writecur_1147 = deref_1070 + sizeof(GibInt);
                
                *(GibFloat *) deref_1068 = tmpval_1647;
                
                GibCursor writecur_1149 = deref_1068 + sizeof(GibFloat);
                unsigned char tup_packed_1140 =
                               add1List(cursor_ptr_1061, cursor_ptr_1060, cursor_ptr_1062, xs_21_104_149);
                GibCursor end_fltPkd_122_154[3];
                
                memcpy(end_fltPkd_122_154, cursor_ptr_1062,
                       sizeof(GibCursor [3]));
                
                GibCursor loc_cursor_ptr_1116[3];
                
                memcpy(loc_cursor_ptr_1116, xs_21_104_149,
                       sizeof(GibCursor [3]));
                
                GibCursor end_taildc_605[3];
                
                memcpy(end_taildc_605, cursor_ptr_1062, sizeof(GibCursor [3]));
                return 0;
                break;
            }
            
          case GIB_INDIRECTION_TAG:
            {
                GibCursor *restrict soa_field_0_1156 = &xs_21_104_149[1];
                GibCursor deref_1157 = *soa_field_0_1156;
                GibCursor *restrict soa_field_1_1158 = &xs_21_104_149[2];
                GibCursor deref_1159 = *soa_field_1_1158;
                uintptr_t tagged_tmpcur_17 = *(uintptr_t *) tmpcur_1644;
                GibCursor tmpcur_1649 = GIB_UNTAG(tagged_tmpcur_17);
                GibCursor tmpaftercur_1650 = tmpcur_1644 + 8;
                uint16_t tmptag_1651 = GIB_GET_TAG(tagged_tmpcur_17);
                
                *(GibCursor *) loc_387 = tmpcur_1649;
                
                GibCursor end_from_tagged_dcon_redir_1172 = tmpcur_1649 +
                          tmptag_1651;
                GibCursor field_nxt_1169 = deref_1157 + 1;
                uintptr_t tagged_tmpcur_16 = *(uintptr_t *) field_nxt_1169;
                GibCursor tmpcur_1652 = GIB_UNTAG(tagged_tmpcur_16);
                GibCursor tmpaftercur_1653 = field_nxt_1169 + 8;
                uint16_t tmptag_1654 = GIB_GET_TAG(tagged_tmpcur_16);
                
                *(GibCursor *) soa_field_0_1156 = tmpcur_1652;
                
                GibCursor end_from_tagged_fld_redir_1173 = tmpcur_1652 +
                          tmptag_1654;
                GibCursor field_nxt_1170 = deref_1159 + 1;
                uintptr_t tagged_tmpcur_15 = *(uintptr_t *) field_nxt_1170;
                GibCursor tmpcur_1655 = GIB_UNTAG(tagged_tmpcur_15);
                GibCursor tmpaftercur_1656 = field_nxt_1170 + 8;
                uint16_t tmptag_1657 = GIB_GET_TAG(tagged_tmpcur_15);
                
                *(GibCursor *) soa_field_1_1158 = tmpcur_1655;
                
                GibCursor end_from_tagged_fld_redir_1174 = tmpcur_1655 +
                          tmptag_1657;
                GibCursor indr_664[3] = {tmpcur_1649, tmpcur_1652, tmpcur_1655};
                GibCursor jump_dloc_668 = deref_dcon_var_1076 + 9;
                GibCursor aft_indir_loc_676 = deref_1157 + 9;
                GibCursor aft_indir_loc_677 = deref_1159 + 9;
                GibCursor cursor_ptr_1175[3] = {jump_dloc_668,
                                                aft_indir_loc_676,
                                                aft_indir_loc_677};
                unsigned char tup_packed_1193 =
                               add1List(xs_21_104_149, cursor_ptr_1060, cursor_ptr_1062, xs_21_104_149);
                GibCursor end_call_671[3];
                
                memcpy(end_call_671, cursor_ptr_1062, sizeof(GibCursor [3]));
                
                GibCursor loc_cursor_ptr_1176[3];
                
                memcpy(loc_cursor_ptr_1176, xs_21_104_149,
                       sizeof(GibCursor [3]));
                return 0;
                break;
            }
            
          case GIB_REDIRECTION_TAG:
            {
                GibCursor *restrict soa_field_0_1196 = &xs_21_104_149[1];
                GibCursor deref_1197 = *soa_field_0_1196;
                GibCursor *restrict soa_field_1_1198 = &xs_21_104_149[2];
                GibCursor deref_1199 = *soa_field_1_1198;
                uintptr_t tagged_tmpcur_20 = *(uintptr_t *) tmpcur_1644;
                GibCursor tmpcur_1658 = GIB_UNTAG(tagged_tmpcur_20);
                GibCursor tmpaftercur_1659 = tmpcur_1644 + 8;
                uint16_t tmptag_1660 = GIB_GET_TAG(tagged_tmpcur_20);
                
                *(GibCursor *) loc_387 = tmpcur_1658;
                
                GibCursor end_from_tagged_dcon_redir_1207 = tmpcur_1658 +
                          tmptag_1660;
                GibCursor field_nxt_1205 = deref_1197 + 1;
                uintptr_t tagged_tmpcur_19 = *(uintptr_t *) field_nxt_1205;
                GibCursor tmpcur_1661 = GIB_UNTAG(tagged_tmpcur_19);
                GibCursor tmpaftercur_1662 = field_nxt_1205 + 8;
                uint16_t tmptag_1663 = GIB_GET_TAG(tagged_tmpcur_19);
                
                *(GibCursor *) soa_field_0_1196 = tmpcur_1661;
                
                GibCursor end_from_tagged_fld_redir_1208 = tmpcur_1661 +
                          tmptag_1663;
                GibCursor field_nxt_1206 = deref_1199 + 1;
                uintptr_t tagged_tmpcur_18 = *(uintptr_t *) field_nxt_1206;
                GibCursor tmpcur_1664 = GIB_UNTAG(tagged_tmpcur_18);
                GibCursor tmpaftercur_1665 = field_nxt_1206 + 8;
                uint16_t tmptag_1666 = GIB_GET_TAG(tagged_tmpcur_18);
                
                *(GibCursor *) soa_field_1_1198 = tmpcur_1664;
                
                GibCursor end_from_tagged_fld_redir_1209 = tmpcur_1664 +
                          tmptag_1666;
                GibCursor indr_664[3] = {tmpcur_1658, tmpcur_1661, tmpcur_1664};
                GibCursor copy_dloc_678 = deref_1072 + 0;
                
                *loc_390 += 0;
                
                GibCursor copy_floc_loc_680 = deref_1068 + 0;
                
                *loc_FloatTy_392 += 0;
                
                GibCursor copy_floc_loc_679 = deref_1070 + 0;
                
                *loc_IntTy_391 += 0;
                
                GibCursor cursor_ptr_1213[3] = {copy_dloc_678,
                                                copy_floc_loc_679,
                                                copy_floc_loc_680};
                unsigned char tup_packed_1231 =
                               add1List(xs_21_104_149, cursor_ptr_1060, cursor_ptr_1062, xs_21_104_149);
                GibCursor end_call_671[3];
                
                memcpy(end_call_671, cursor_ptr_1062, sizeof(GibCursor [3]));
                
                GibCursor loc_cursor_ptr_1214[3];
                
                memcpy(loc_cursor_ptr_1214, xs_21_104_149,
                       sizeof(GibCursor [3]));
                return 0;
                break;
            }
            
          default:
            {
                printf("%s\n", "Unknown tag in: tmpval_1643");
                exit(1);
            }
        }
    }
}
unsigned char _copy_List(GibCursor cursor_ptr_1235[3],
                         GibCursor cursor_ptr_1234[3],
                         GibCursor cursor_ptr_1236[3],
                         GibCursor arg_53_108_155[3])
{
    GibCursor *end_r_410 = &cursor_ptr_1234[2];
    GibCursor *end_r_408 = &cursor_ptr_1234[0];
    GibCursor *end_r_409 = &cursor_ptr_1234[1];
    GibCursor *restrict loc_FloatTy_404 = &cursor_ptr_1236[2];
    GibCursor deref_1238 = *loc_FloatTy_404;
    GibCursor cpy_1239[3];
    
    memcpy(cpy_1239, cursor_ptr_1236, sizeof(GibCursor [3]));
    
    GibCursor *restrict loc_402 = &cursor_ptr_1236[0];
    GibCursor *restrict loc_IntTy_403 = &cursor_ptr_1236[1];
    GibCursor deref_1240 = *loc_IntTy_403;
    GibCursor deref_1241 = *end_r_410;
    GibCursor deref_1242 = *loc_FloatTy_404;
    GibCursor deref_1243 = *end_r_409;
    GibCursor deref_1244 = *loc_IntTy_403;
    GibCursor deref_1245 = *end_r_408;
    GibCursor deref_1246 = *loc_402;
    
    if (deref_1242 + 13 > deref_1241 || (deref_1244 + 17 > deref_1243 ||
                                         deref_1246 + 34 > deref_1245)) {
        gib_grow_region(loc_FloatTy_404, end_r_410);
        gib_grow_region(loc_IntTy_403, end_r_409);
        gib_grow_region(loc_402, end_r_408);
        deref_1242 = *loc_FloatTy_404;
        deref_1244 = *loc_IntTy_403;
        deref_1246 = *loc_402;
    }
    
    GibCursor *end_r_405 = &cursor_ptr_1235[0];
    GibCursor *end_r_406 = &cursor_ptr_1235[1];
    GibCursor *end_r_407 = &cursor_ptr_1235[2];
    GibCursor *restrict loc_399 = &arg_53_108_155[0];
    GibCursor deref_dcon_var_1250 = *loc_399;
    GibPackedTag tmpval_1668 = *(GibPackedTag *) deref_dcon_var_1250;
    GibCursor tmpcur_1669 = deref_dcon_var_1250 + 1;
    
    
  switch_1692:
    ;
    switch (tmpval_1668) {
        
      case 0:
        {
            GibCursor *restrict soa_field_0_1252 = &arg_53_108_155[1];
            GibCursor deref_1253 = *soa_field_0_1252;
            GibCursor *restrict soa_field_1_1254 = &arg_53_108_155[2];
            GibCursor deref_1255 = *soa_field_1_1254;
            GibInt tmpval_1670 = *(GibInt *) deref_1253;
            GibCursor tmpcur_1671 = deref_1253 + sizeof(GibInt);
            
            *soa_field_0_1252 += 8;
            
            GibFloat tmpval_1672 = *(GibFloat *) deref_1255;
            GibCursor tmpcur_1673 = deref_1255 + sizeof(GibFloat);
            
            *soa_field_1_1254 += 4;
            
            GibCursor cursor_ptr_1248[3] = {tmpcur_1669, tmpcur_1671,
                                            tmpcur_1673};
            
            *loc_399 += 1;
            
            GibCursor jumpf_floc_loc_607 = deref_1253 + 8;
            GibCursor jumpf_floc_loc_608 = deref_1255 + 4;
            GibCursor new_dloc_538 = deref_1246 + 1;
            
            *loc_402 += 1;
            
            GibCursor new_floc_loc_540 = deref_1242 + 4;
            
            *loc_FloatTy_404 += 4;
            
            GibCursor new_floc_loc_539 = deref_1244 + 8;
            
            *loc_IntTy_403 += 8;
            
            GibCursor cursor_ptr_1268[3] = {new_dloc_538, new_floc_loc_539,
                                            new_floc_loc_540};
            
            *(GibPackedTag *) deref_1246 = 0;
            
            GibCursor writetag_1295 = deref_1246 + 1;
            GibCursor after_tag_1296 = deref_1246 + 1;
            
            *(GibInt *) deref_1244 = tmpval_1670;
            
            GibCursor writecur_1300 = deref_1244 + sizeof(GibInt);
            
            *(GibFloat *) deref_1242 = tmpval_1672;
            
            GibCursor writecur_1302 = deref_1242 + sizeof(GibFloat);
            unsigned char tup_packed_1293 =
                           _copy_List(cursor_ptr_1235, cursor_ptr_1234, cursor_ptr_1236, arg_53_108_155);
            GibCursor end_y_59_114_161[3];
            
            memcpy(end_y_59_114_161, cursor_ptr_1236, sizeof(GibCursor [3]));
            
            GibCursor loc_cursor_ptr_1269[3];
            
            memcpy(loc_cursor_ptr_1269, arg_53_108_155, sizeof(GibCursor [3]));
            
            GibCursor end_taildc_612[3];
            
            memcpy(end_taildc_612, cursor_ptr_1236, sizeof(GibCursor [3]));
            return 0;
            break;
        }
        
      case 1:
        {
            GibCursor *restrict soa_field_0_1309 = &arg_53_108_155[1];
            GibCursor deref_1310 = *soa_field_0_1309;
            GibCursor *restrict soa_field_1_1311 = &arg_53_108_155[2];
            GibCursor deref_1312 = *soa_field_1_1311;
            
            *loc_399 += 1;
            
            GibCursor jump_floc_loc_614 = deref_1310 + 0;
            GibCursor jump_floc_loc_615 = deref_1312 + 0;
            GibCursor cursor_ptr_1315[3] = {tmpcur_1669, jump_floc_loc_614,
                                            jump_floc_loc_615};
            
            *(GibPackedTag *) deref_1246 = 1;
            
            GibCursor writetag_1319 = deref_1246 + 1;
            GibCursor after_tag_1320 = deref_1246 + 1;
            
            *loc_402 += 1;
            
            GibCursor aft_soa_loc_1325[3] = {after_tag_1320, deref_1244,
                                             deref_1242};
            GibCursor end_taildc_616[3];
            
            memcpy(end_taildc_616, cursor_ptr_1236, sizeof(GibCursor [3]));
            return 0;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            GibCursor *restrict soa_field_0_1330 = &arg_53_108_155[1];
            GibCursor deref_1331 = *soa_field_0_1330;
            GibCursor *restrict soa_field_1_1332 = &arg_53_108_155[2];
            GibCursor deref_1333 = *soa_field_1_1332;
            uintptr_t tagged_tmpcur_25 = *(uintptr_t *) tmpcur_1669;
            GibCursor tmpcur_1674 = GIB_UNTAG(tagged_tmpcur_25);
            GibCursor tmpaftercur_1675 = tmpcur_1669 + 8;
            uint16_t tmptag_1676 = GIB_GET_TAG(tagged_tmpcur_25);
            
            *(GibCursor *) loc_399 = tmpcur_1674;
            
            GibCursor end_from_tagged_dcon_redir_1346 = tmpcur_1674 +
                      tmptag_1676;
            GibCursor field_nxt_1343 = deref_1331 + 1;
            uintptr_t tagged_tmpcur_24 = *(uintptr_t *) field_nxt_1343;
            GibCursor tmpcur_1677 = GIB_UNTAG(tagged_tmpcur_24);
            GibCursor tmpaftercur_1678 = field_nxt_1343 + 8;
            uint16_t tmptag_1679 = GIB_GET_TAG(tagged_tmpcur_24);
            
            *(GibCursor *) soa_field_0_1330 = tmpcur_1677;
            
            GibCursor end_from_tagged_fld_redir_1347 = tmpcur_1677 +
                      tmptag_1679;
            GibCursor field_nxt_1344 = deref_1333 + 1;
            uintptr_t tagged_tmpcur_23 = *(uintptr_t *) field_nxt_1344;
            GibCursor tmpcur_1680 = GIB_UNTAG(tagged_tmpcur_23);
            GibCursor tmpaftercur_1681 = field_nxt_1344 + 8;
            uint16_t tmptag_1682 = GIB_GET_TAG(tagged_tmpcur_23);
            
            *(GibCursor *) soa_field_1_1332 = tmpcur_1680;
            
            GibCursor end_from_tagged_fld_redir_1348 = tmpcur_1680 +
                      tmptag_1682;
            GibCursor indr_681[3] = {tmpcur_1674, tmpcur_1677, tmpcur_1680};
            GibCursor jump_dloc_685 = deref_dcon_var_1250 + 9;
            GibCursor aft_indir_loc_693 = deref_1331 + 9;
            GibCursor aft_indir_loc_694 = deref_1333 + 9;
            GibCursor cursor_ptr_1349[3] = {jump_dloc_685, aft_indir_loc_693,
                                            aft_indir_loc_694};
            unsigned char tup_packed_1367 =
                           _copy_List(arg_53_108_155, cursor_ptr_1234, cursor_ptr_1236, arg_53_108_155);
            GibCursor end_call_688[3];
            
            memcpy(end_call_688, cursor_ptr_1236, sizeof(GibCursor [3]));
            
            GibCursor loc_cursor_ptr_1350[3];
            
            memcpy(loc_cursor_ptr_1350, arg_53_108_155, sizeof(GibCursor [3]));
            return 0;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            GibCursor *restrict soa_field_0_1370 = &arg_53_108_155[1];
            GibCursor deref_1371 = *soa_field_0_1370;
            GibCursor *restrict soa_field_1_1372 = &arg_53_108_155[2];
            GibCursor deref_1373 = *soa_field_1_1372;
            uintptr_t tagged_tmpcur_28 = *(uintptr_t *) tmpcur_1669;
            GibCursor tmpcur_1683 = GIB_UNTAG(tagged_tmpcur_28);
            GibCursor tmpaftercur_1684 = tmpcur_1669 + 8;
            uint16_t tmptag_1685 = GIB_GET_TAG(tagged_tmpcur_28);
            
            *(GibCursor *) loc_399 = tmpcur_1683;
            
            GibCursor end_from_tagged_dcon_redir_1381 = tmpcur_1683 +
                      tmptag_1685;
            GibCursor field_nxt_1379 = deref_1371 + 1;
            uintptr_t tagged_tmpcur_27 = *(uintptr_t *) field_nxt_1379;
            GibCursor tmpcur_1686 = GIB_UNTAG(tagged_tmpcur_27);
            GibCursor tmpaftercur_1687 = field_nxt_1379 + 8;
            uint16_t tmptag_1688 = GIB_GET_TAG(tagged_tmpcur_27);
            
            *(GibCursor *) soa_field_0_1370 = tmpcur_1686;
            
            GibCursor end_from_tagged_fld_redir_1382 = tmpcur_1686 +
                      tmptag_1688;
            GibCursor field_nxt_1380 = deref_1373 + 1;
            uintptr_t tagged_tmpcur_26 = *(uintptr_t *) field_nxt_1380;
            GibCursor tmpcur_1689 = GIB_UNTAG(tagged_tmpcur_26);
            GibCursor tmpaftercur_1690 = field_nxt_1380 + 8;
            uint16_t tmptag_1691 = GIB_GET_TAG(tagged_tmpcur_26);
            
            *(GibCursor *) soa_field_1_1372 = tmpcur_1689;
            
            GibCursor end_from_tagged_fld_redir_1383 = tmpcur_1689 +
                      tmptag_1691;
            GibCursor indr_681[3] = {tmpcur_1683, tmpcur_1686, tmpcur_1689};
            GibCursor copy_dloc_695 = deref_1246 + 0;
            
            *loc_402 += 0;
            
            GibCursor copy_floc_loc_697 = deref_1242 + 0;
            
            *loc_FloatTy_404 += 0;
            
            GibCursor copy_floc_loc_696 = deref_1244 + 0;
            
            *loc_IntTy_403 += 0;
            
            GibCursor cursor_ptr_1387[3] = {copy_dloc_695, copy_floc_loc_696,
                                            copy_floc_loc_697};
            unsigned char tup_packed_1405 =
                           _copy_List(arg_53_108_155, cursor_ptr_1234, cursor_ptr_1236, arg_53_108_155);
            GibCursor end_call_688[3];
            
            memcpy(end_call_688, cursor_ptr_1236, sizeof(GibCursor [3]));
            
            GibCursor loc_cursor_ptr_1388[3];
            
            memcpy(loc_cursor_ptr_1388, arg_53_108_155, sizeof(GibCursor [3]));
            return 0;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1668");
            exit(1);
        }
    }
}
GibInt sumList(GibCursor cursor_ptr_1408[3], GibCursor xs_25_115_162[3])
{
    GibCursor *end_r_414 = &cursor_ptr_1408[0];
    GibCursor *end_r_415 = &cursor_ptr_1408[1];
    GibCursor *end_r_416 = &cursor_ptr_1408[2];
    GibCursor *restrict loc_411 = &xs_25_115_162[0];
    GibCursor deref_dcon_var_1412 = *loc_411;
    GibPackedTag tmpval_1693 = *(GibPackedTag *) deref_dcon_var_1412;
    GibCursor tmpcur_1694 = deref_dcon_var_1412 + 1;
    
    
  switch_1717:
    ;
    switch (tmpval_1693) {
        
      case 1:
        {
            GibCursor *restrict soa_field_0_1414 = &xs_25_115_162[1];
            GibCursor deref_1415 = *soa_field_0_1414;
            GibCursor *restrict soa_field_1_1416 = &xs_25_115_162[2];
            GibCursor deref_1417 = *soa_field_1_1416;
            
            *loc_411 += 1;
            
            GibCursor jump_floc_loc_619 = deref_1415 + 0;
            GibCursor jump_floc_loc_620 = deref_1417 + 0;
            GibCursor cursor_ptr_1420[3] = {tmpcur_1694, jump_floc_loc_619,
                                            jump_floc_loc_620};
            
            return 0;
            break;
        }
        
      case 0:
        {
            GibCursor *restrict soa_field_0_1422 = &xs_25_115_162[1];
            GibCursor deref_1423 = *soa_field_0_1422;
            GibCursor *restrict soa_field_1_1424 = &xs_25_115_162[2];
            GibCursor deref_1425 = *soa_field_1_1424;
            GibInt tmpval_1695 = *(GibInt *) deref_1423;
            GibCursor tmpcur_1696 = deref_1423 + sizeof(GibInt);
            
            *soa_field_0_1422 += 8;
            
            GibFloat tmpval_1697 = *(GibFloat *) deref_1425;
            GibCursor tmpcur_1698 = deref_1425 + sizeof(GibFloat);
            GibCursor cursor_ptr_1410[3] = {tmpcur_1694, tmpcur_1696,
                                            tmpcur_1698};
            
            *loc_411 += 1;
            
            GibCursor jumpf_floc_loc_622 = deref_1423 + 8;
            GibCursor jumpf_floc_loc_623 = deref_1425 + 4;
            GibCursor loc_557 = tmpcur_1694 + 0;
            
            *loc_411 += 0;
            
            GibCursor loc_556 = jumpf_floc_loc_623 + 0;
            GibCursor loc_555 = jumpf_floc_loc_622 + 0;
            GibCursor cursor_ptr_1433[3] = {tmpcur_1694, jumpf_floc_loc_622,
                                            jumpf_floc_loc_623};
            GibInt fltPrm_123_166 =  sumList(cursor_ptr_1408, xs_25_115_162);
            GibCursor loc_cursor_ptr_1434[3];
            
            memcpy(loc_cursor_ptr_1434, xs_25_115_162, sizeof(GibCursor [3]));
            
            GibInt tailprim_627 = tmpval_1695 + fltPrm_123_166;
            
            return tailprim_627;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            GibCursor *restrict soa_field_0_1449 = &xs_25_115_162[1];
            GibCursor deref_1450 = *soa_field_0_1449;
            GibCursor *restrict soa_field_1_1451 = &xs_25_115_162[2];
            GibCursor deref_1452 = *soa_field_1_1451;
            uintptr_t tagged_tmpcur_31 = *(uintptr_t *) tmpcur_1694;
            GibCursor tmpcur_1699 = GIB_UNTAG(tagged_tmpcur_31);
            GibCursor tmpaftercur_1700 = tmpcur_1694 + 8;
            uint16_t tmptag_1701 = GIB_GET_TAG(tagged_tmpcur_31);
            
            *(GibCursor *) loc_411 = tmpcur_1699;
            
            GibCursor end_from_tagged_dcon_redir_1465 = tmpcur_1699 +
                      tmptag_1701;
            GibCursor field_nxt_1462 = deref_1450 + 1;
            uintptr_t tagged_tmpcur_30 = *(uintptr_t *) field_nxt_1462;
            GibCursor tmpcur_1702 = GIB_UNTAG(tagged_tmpcur_30);
            GibCursor tmpaftercur_1703 = field_nxt_1462 + 8;
            uint16_t tmptag_1704 = GIB_GET_TAG(tagged_tmpcur_30);
            
            *(GibCursor *) soa_field_0_1449 = tmpcur_1702;
            
            GibCursor end_from_tagged_fld_redir_1466 = tmpcur_1702 +
                      tmptag_1704;
            GibCursor field_nxt_1463 = deref_1452 + 1;
            uintptr_t tagged_tmpcur_29 = *(uintptr_t *) field_nxt_1463;
            GibCursor tmpcur_1705 = GIB_UNTAG(tagged_tmpcur_29);
            GibCursor tmpaftercur_1706 = field_nxt_1463 + 8;
            uint16_t tmptag_1707 = GIB_GET_TAG(tagged_tmpcur_29);
            GibCursor end_from_tagged_fld_redir_1467 = tmpcur_1705 +
                      tmptag_1707;
            GibCursor indr_698[3] = {tmpcur_1699, tmpcur_1702, tmpcur_1705};
            GibCursor jump_dloc_702 = deref_dcon_var_1412 + 9;
            GibCursor aft_indir_loc_710 = deref_1450 + 9;
            GibCursor aft_indir_loc_711 = deref_1452 + 9;
            GibCursor cursor_ptr_1468[3] = {jump_dloc_702, aft_indir_loc_710,
                                            aft_indir_loc_711};
            GibInt call_705 =  sumList(xs_25_115_162, xs_25_115_162);
            GibCursor loc_cursor_ptr_1469[3];
            
            memcpy(loc_cursor_ptr_1469, xs_25_115_162, sizeof(GibCursor [3]));
            return call_705;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            GibCursor *restrict soa_field_0_1477 = &xs_25_115_162[1];
            GibCursor deref_1478 = *soa_field_0_1477;
            GibCursor *restrict soa_field_1_1479 = &xs_25_115_162[2];
            GibCursor deref_1480 = *soa_field_1_1479;
            uintptr_t tagged_tmpcur_34 = *(uintptr_t *) tmpcur_1694;
            GibCursor tmpcur_1708 = GIB_UNTAG(tagged_tmpcur_34);
            GibCursor tmpaftercur_1709 = tmpcur_1694 + 8;
            uint16_t tmptag_1710 = GIB_GET_TAG(tagged_tmpcur_34);
            
            *(GibCursor *) loc_411 = tmpcur_1708;
            
            GibCursor end_from_tagged_dcon_redir_1488 = tmpcur_1708 +
                      tmptag_1710;
            GibCursor field_nxt_1486 = deref_1478 + 1;
            uintptr_t tagged_tmpcur_33 = *(uintptr_t *) field_nxt_1486;
            GibCursor tmpcur_1711 = GIB_UNTAG(tagged_tmpcur_33);
            GibCursor tmpaftercur_1712 = field_nxt_1486 + 8;
            uint16_t tmptag_1713 = GIB_GET_TAG(tagged_tmpcur_33);
            
            *(GibCursor *) soa_field_0_1477 = tmpcur_1711;
            
            GibCursor end_from_tagged_fld_redir_1489 = tmpcur_1711 +
                      tmptag_1713;
            GibCursor field_nxt_1487 = deref_1480 + 1;
            uintptr_t tagged_tmpcur_32 = *(uintptr_t *) field_nxt_1487;
            GibCursor tmpcur_1714 = GIB_UNTAG(tagged_tmpcur_32);
            GibCursor tmpaftercur_1715 = field_nxt_1487 + 8;
            uint16_t tmptag_1716 = GIB_GET_TAG(tagged_tmpcur_32);
            GibCursor end_from_tagged_fld_redir_1490 = tmpcur_1714 +
                      tmptag_1716;
            GibCursor indr_698[3] = {tmpcur_1708, tmpcur_1711, tmpcur_1714};
            GibInt call_705 =  sumList(xs_25_115_162, xs_25_115_162);
            GibCursor loc_cursor_ptr_1491[3];
            
            memcpy(loc_cursor_ptr_1491, xs_25_115_162, sizeof(GibCursor [3]));
            return call_705;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1693");
            exit(1);
        }
    }
}
int main(int argc, char **argv)
{
    int init_35 = gib_init(argc, argv);
    
    info_table_initialize();
    symbol_table_initialize();
    
    GibChunk region_1566 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_444 = region_1566.start;
    GibCursor end_r_444 = region_1566.end;
    GibChunk region_1567 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_445 = region_1567.start;
    GibCursor end_r_445 = region_1567.end;
    GibChunk region_1568 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_446 = region_1568.start;
    GibCursor end_r_446 = region_1568.end;
    GibCursor reg_ptr_1498[3] = {r_444, r_445, r_446};
    GibCursor reg_cursor_ptr_1499[3] = {end_r_444, end_r_445, end_r_446};
    GibCursor cursor_ptr_1500[3];
    
    memcpy(cursor_ptr_1500, reg_ptr_1498, sizeof(GibCursor [3]));
    
    unsigned char tup_packed_1512 =
                   mkList(reg_cursor_ptr_1499, cursor_ptr_1500, 10000);
    GibCursor end_xs_17_81_124[3];
    
    memcpy(end_xs_17_81_124, cursor_ptr_1500, sizeof(GibCursor [3]));
    
    GibChunk region_1569 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_441 = region_1569.start;
    GibCursor end_r_441 = region_1569.end;
    GibChunk region_1570 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_442 = region_1570.start;
    GibCursor end_r_442 = region_1570.end;
    GibChunk region_1571 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_443 = region_1571.start;
    GibCursor end_r_443 = region_1571.end;
    GibCursor reg_ptr_1514[3] = {r_441, r_442, r_443};
    GibCursor reg_cursor_ptr_1515[3] = {end_r_441, end_r_442, end_r_443};
    GibCursor cursor_ptr_1516[3];
    
    memcpy(cursor_ptr_1516, reg_ptr_1514, sizeof(GibCursor [3]));
    
    GibCursor copy_address_1522[3];
    
    memcpy(copy_address_1522, reg_ptr_1498, sizeof(GibCursor [3]));
    
    unsigned char tup_packed_1541 =
                   add1List(reg_cursor_ptr_1499, reg_cursor_ptr_1515, cursor_ptr_1516, copy_address_1522);
    GibCursor end_xs__18_82_125[3];
    
    memcpy(end_xs__18_82_125, cursor_ptr_1516, sizeof(GibCursor [3]));
    
    GibCursor copy_address_1546[3];
    
    memcpy(copy_address_1546, reg_ptr_1514, sizeof(GibCursor [3]));
    
    GibInt tailapp_631 =  sumList(reg_cursor_ptr_1515, copy_address_1546);
    
    printf("%ld", tailapp_631);
    printf("\n");
    
    int exit_36 = gib_exit();
    
    return exit_36;
}