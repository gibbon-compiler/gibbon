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
#include <immintrin.h>

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
unsigned char add1List_vectorized(GibCursor cursor_ptr_1062[3],
                                  GibCursor cursor_ptr_1061[3],
                                  GibCursor cursor_ptr_1063[3],
                                  GibCursor xs_21_104_149[3]);
unsigned char add1List_loop_scalar(GibCursor cursor_ptr_1062[3],
                                   GibCursor cursor_ptr_1061[3],
                                   GibCursor cursor_ptr_1063[3],
                                   GibCursor xs_21_104_149[3]);
unsigned char add1List_vectorized_indirections(GibCursor cursor_ptr_1062[3],
                                               GibCursor cursor_ptr_1061[3],
                                               GibCursor cursor_ptr_1063[3],
                                               GibCursor xs_21_104_149[3]);
unsigned char add1List_auto_vectorized_indirections(GibCursor cursor_ptr_1062[3],
                                                    GibCursor cursor_ptr_1061[3],
                                                    GibCursor cursor_ptr_1063[3],
                                                    GibCursor xs_21_104_149[3]);
unsigned char add1List_loop_scalar_indirections(GibCursor cursor_ptr_1062[3],
                                                GibCursor cursor_ptr_1061[3],
                                                GibCursor cursor_ptr_1063[3],
                                                GibCursor xs_21_104_149[3]);
unsigned char add1List_scalar(GibCursor cursor_ptr_1062[3],
                              GibCursor cursor_ptr_1061[3],
                              GibCursor cursor_ptr_1063[3],
                              GibCursor xs_21_104_149[3]);
unsigned char add1List(GibCursor cursor_ptr_1062[3],
                       GibCursor cursor_ptr_1061[3],
                       GibCursor cursor_ptr_1063[3],
                       GibCursor xs_21_104_149[3]);
unsigned char _copy_List(GibCursor cursor_ptr_1236[3],
                         GibCursor cursor_ptr_1235[3],
                         GibCursor cursor_ptr_1237[3],
                         GibCursor arg_53_108_155[3]);
GibInt sumList(GibCursor cursor_ptr_1409[3], GibCursor xs_25_115_162[3]);
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
            GibCursor chk_loc_849 = cursor_ptr_822[0];
            GibCursor chk_end_850 = cursor_ptr_820[0];
            GibBool chk_851 = chk_loc_849 < chk_end_850;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_846 = cursor_ptr_822[1];
            GibCursor chk_end_847 = cursor_ptr_820[1];
            GibBool chk_848 = chk_loc_846 < chk_end_847;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_843 = cursor_ptr_822[2];
            GibCursor chk_end_844 = cursor_ptr_820[2];
            GibBool chk_845 = chk_loc_843 < chk_end_844;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
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
            GibCursor chk_end_886 = cursor_ptr_820[0];
            GibBool chk_887 = deref_dcon_var_824 < chk_end_886;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
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
            GibCursor chk_end_908 = cursor_ptr_820[0];
            GibBool chk_909 = deref_dcon_var_824 < chk_end_908;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
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
            GibCursor chk_loc_941 = cursor_ptr_914[0];
            GibCursor chk_end_942 = cursor_ptr_912[0];
            GibBool chk_943 = chk_loc_941 < chk_end_942;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_938 = cursor_ptr_914[1];
            GibCursor chk_end_939 = cursor_ptr_912[1];
            GibBool chk_940 = chk_loc_938 < chk_end_939;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_935 = cursor_ptr_914[2];
            GibCursor chk_end_936 = cursor_ptr_912[2];
            GibBool chk_937 = chk_loc_935 < chk_end_936;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
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
            GibCursor chk_end_978 = cursor_ptr_912[0];
            GibBool chk_979 = deref_dcon_var_916 < chk_end_978;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
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
            GibCursor chk_end_1000 = cursor_ptr_912[0];
            GibBool chk_1001 = deref_dcon_var_916 < chk_end_1000;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
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
    GibCursor *end_r_385 = &cursor_ptr_1003[1];
    GibCursor *end_r_384 = &cursor_ptr_1003[0];
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
        
        *(GibInt *) deref_1012 = len_19_102_145;
        
        GibCursor writecur_1050 = deref_1012 + sizeof(GibInt);
        
        gib_scalar_count_footer_bump(deref_1011, 0, 0);
        *(GibFloat *) deref_1010 = 1.0;
        
        GibCursor writecur_1052 = deref_1010 + sizeof(GibFloat);
        
        gib_scalar_count_footer_bump(deref_1009, 0, 1);
        
        GibCursor chk_loc_1040 = cursor_ptr_1031[0];
        GibCursor chk_end_1041 = cursor_ptr_1003[0];
        GibBool chk_1042 = chk_loc_1040 < chk_end_1041;
        
        #ifdef _GIBBON_DEBUG
        #endif
        
        GibCursor chk_loc_1037 = cursor_ptr_1031[1];
        GibCursor chk_end_1038 = cursor_ptr_1003[1];
        GibBool chk_1039 = chk_loc_1037 < chk_end_1038;
        
        #ifdef _GIBBON_DEBUG
        #endif
        
        GibCursor chk_loc_1034 = cursor_ptr_1031[2];
        GibCursor chk_end_1035 = cursor_ptr_1003[2];
        GibBool chk_1036 = chk_loc_1034 < chk_end_1035;
        
        #ifdef _GIBBON_DEBUG
        #endif
        
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

static inline void manual_vec_add1_ensure_space(GibCursor *cursor,
                                                GibCursor *end,
                                                size_t bytes_needed)
{
    while (*cursor + bytes_needed > *end) {
        gib_grow_region(cursor, end);
    }
}

static inline GibCursor manual_vec_add1_follow_redirection(GibCursor redir,
                                                          GibCursor *footer)
{
    GibPackedTag tag = *(GibPackedTag *) redir;

    if (tag != GIB_REDIRECTION_TAG) {
        fprintf(stderr, "manual add1List expected redirection tag, found %u\n",
                (unsigned) tag);
        exit(1);
    }

    uintptr_t tagged_ptr = GIB_LOAD_TAGGEDPTR(redir + 1);
    GibCursor next = GIB_UNTAG(tagged_ptr);
    *footer = next + GIB_GET_TAG(tagged_ptr);
    return next;
}

static inline void manual_write_indirection_tag(GibCursor from,
                                                GibCursor to,
                                                GibCursor to_footer)
{
    uint64_t footer_offset_64 = (uint64_t) (to_footer - to);

    if (footer_offset_64 > UINT16_MAX) {
        fprintf(stderr,
                "manual add1List indirection footer offset too large: %" PRIu64 "\n",
                footer_offset_64);
        exit(1);
    }

    *(GibPackedTag *) from = GIB_INDIRECTION_TAG;
    GIB_STORE_TAGGEDPTR(from + sizeof(GibPackedTag),
                        GIB_STORE_TAG(to, (uint16_t) footer_offset_64));
}

static void __attribute__((noinline))
manual_vec_add1_int_chunk_sse2(GibCursor in, GibCursor out, uint64_t count)
{
    uint64_t i = 0;
    __m128i ones = _mm_set1_epi64x(1);

    for (; i + 3 < count; i += 4) {
        __m128i vals0 =
            _mm_loadu_si128((const __m128i *) (const void *)
                            (in + (i * sizeof(GibInt))));
        __m128i vals1 =
            _mm_loadu_si128((const __m128i *) (const void *)
                            (in + ((i + 2) * sizeof(GibInt))));
        __m128i bumped0 = _mm_add_epi64(vals0, ones);
        __m128i bumped1 = _mm_add_epi64(vals1, ones);

        _mm_storeu_si128((__m128i *) (void *) (out + (i * sizeof(GibInt))),
                         bumped0);
        _mm_storeu_si128((__m128i *) (void *)
                         (out + ((i + 2) * sizeof(GibInt))), bumped1);
    }

    for (; i + 1 < count; i += 2) {
        __m128i vals =
            _mm_loadu_si128((const __m128i *) (const void *)
                            (in + (i * sizeof(GibInt))));
        __m128i bumped = _mm_add_epi64(vals, ones);

        _mm_storeu_si128((__m128i *) (void *) (out + (i * sizeof(GibInt))),
                         bumped);
    }

    for (; i < count; i++) {
        *(GibInt *) (out + (i * sizeof(GibInt))) =
            (*(GibInt *) (in + (i * sizeof(GibInt)))) + 1;
    }
}

static void __attribute__((noinline,target("avx2")))
manual_vec_add1_int_chunk_avx2(GibCursor in, GibCursor out, uint64_t count)
{
    uint64_t i = 0;
    __m256i ones = _mm256_set1_epi64x(1);

    for (; i + 7 < count; i += 8) {
        __m256i vals0 =
            _mm256_loadu_si256((const __m256i *) (const void *)
                               (in + (i * sizeof(GibInt))));
        __m256i vals1 =
            _mm256_loadu_si256((const __m256i *) (const void *)
                               (in + ((i + 4) * sizeof(GibInt))));
        __m256i bumped0 = _mm256_add_epi64(vals0, ones);
        __m256i bumped1 = _mm256_add_epi64(vals1, ones);

        _mm256_storeu_si256((__m256i *) (void *)
                            (out + (i * sizeof(GibInt))), bumped0);
        _mm256_storeu_si256((__m256i *) (void *)
                            (out + ((i + 4) * sizeof(GibInt))), bumped1);
    }

    for (; i + 3 < count; i += 4) {
        __m256i vals =
            _mm256_loadu_si256((const __m256i *) (const void *)
                               (in + (i * sizeof(GibInt))));
        __m256i bumped = _mm256_add_epi64(vals, ones);

        _mm256_storeu_si256((__m256i *) (void *)
                            (out + (i * sizeof(GibInt))), bumped);
    }

    _mm256_zeroupper();

    if (i < count) {
        manual_vec_add1_int_chunk_sse2(in + (i * sizeof(GibInt)),
                                       out + (i * sizeof(GibInt)),
                                       count - i);
    }
}

static void __attribute__((noinline))
manual_vec_add1_int_chunk(GibCursor in, GibCursor out, uint64_t count)
{
#if !defined(MANUAL_DISABLE_AVX2) && defined(__GNUC__) && \
    (defined(__x86_64__) || defined(__i386__))
    if (__builtin_cpu_supports("avx2")) {
        manual_vec_add1_int_chunk_avx2(in, out, count);
        return;
    }
#endif
    manual_vec_add1_int_chunk_sse2(in, out, count);
}

static void __attribute__((noinline,optimize("no-tree-vectorize")))
manual_scalar_add1_int_chunk(GibCursor in, GibCursor out, uint64_t count)
{
    for (uint64_t i = 0; i < count; i++) {
        *(GibInt *) (out + (i * sizeof(GibInt))) =
            (*(GibInt *) (in + (i * sizeof(GibInt)))) + 1;
    }
}

static void __attribute__((noinline))
manual_auto_add1_int_chunk(GibCursor in, GibCursor out, uint64_t count)
{
    const GibInt *restrict src = (const GibInt *restrict) in;
    GibInt *restrict dst = (GibInt *restrict) out;

    for (uint64_t i = 0; i < count; i++) {
        dst[i] = src[i] + 1;
    }
}

static inline double manual_now_seconds(void)
{
    struct timespec ts;

    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double) ts.tv_sec + ((double) ts.tv_nsec / 1000000000.0);
}

static unsigned char add1List_count_loop(GibCursor cursor_ptr_1062[3],
                                         GibCursor cursor_ptr_1061[3],
                                         GibCursor cursor_ptr_1063[3],
                                         GibCursor xs_21_104_149[3],
                                         bool use_vector_instructions)
{
    GibCursor in_dcon = xs_21_104_149[0];
    GibCursor in_int = xs_21_104_149[1];
    GibCursor in_float = xs_21_104_149[2];
    GibCursor out_dcon = cursor_ptr_1063[0];
    GibCursor out_int = cursor_ptr_1063[1];
    GibCursor out_float = cursor_ptr_1063[2];
    GibCursor out_dcon_end = cursor_ptr_1061[0];
    GibCursor out_int_end = cursor_ptr_1061[1];
    GibCursor out_float_end = cursor_ptr_1061[2];
    GibOldgenChunkFooter *final_int_footer =
        (GibOldgenChunkFooter *) cursor_ptr_1062[1];
    GibOldgenChunkFooter *final_float_footer =
        (GibOldgenChunkFooter *) cursor_ptr_1062[2];
    GibOldgenChunkFooter *next_int_count_footer = NULL;
    GibOldgenChunkFooter *next_float_count_footer = NULL;
    bool first_chunk = true;

    if (final_int_footer == NULL || final_int_footer->reg_info == NULL ||
        final_int_footer->reg_info->first_chunk_footer == NULL) {
        fprintf(stderr, "manual add1List could not find int scalar-count footer\n");
        exit(1);
    }

    if (final_float_footer == NULL || final_float_footer->reg_info == NULL ||
        final_float_footer->reg_info->first_chunk_footer == NULL) {
        fprintf(stderr, "manual add1List could not find float scalar-count footer\n");
        exit(1);
    }

    next_int_count_footer =
        (GibOldgenChunkFooter *) final_int_footer->reg_info->first_chunk_footer;
    next_float_count_footer =
        (GibOldgenChunkFooter *) final_float_footer->reg_info->first_chunk_footer;

    while (true) {
        GibOldgenChunkFooter *int_count_footer =
            first_chunk ? final_int_footer : next_int_count_footer;
        GibOldgenChunkFooter *float_count_footer =
            first_chunk ? final_float_footer : next_float_count_footer;

        if (int_count_footer == NULL || float_count_footer == NULL) {
            fprintf(stderr, "manual add1List reached a null count footer\n");
            exit(1);
        }

        uint64_t count =
            gib_scalar_count_footer_get((char *) int_count_footer, 0, 0);
        uint64_t float_count =
            gib_scalar_count_footer_get((char *) float_count_footer, 0, 1);
        size_t dcon_bytes = (size_t) count + 9;
        size_t int_bytes = (size_t) (count * sizeof(GibInt));
        size_t float_bytes = (size_t) (count * sizeof(GibFloat));

        if (float_count != count) {
            fprintf(stderr,
                    "manual add1List field-count mismatch: int=%" PRIu64
                    " float=%" PRIu64 "\n",
                    count, float_count);
            exit(1);
        }

        manual_vec_add1_ensure_space(&out_dcon, &out_dcon_end, dcon_bytes);
        manual_vec_add1_ensure_space(&out_int, &out_int_end, int_bytes + 9);
        manual_vec_add1_ensure_space(&out_float, &out_float_end, float_bytes + 9);

        memset(out_dcon, 0, (size_t) count);
        out_dcon += count;
        in_dcon += count;

        if (use_vector_instructions) {
            manual_vec_add1_int_chunk(in_int, out_int, count);
        } else {
            manual_scalar_add1_int_chunk(in_int, out_int, count);
        }
        in_int += int_bytes;
        out_int += int_bytes;

        memcpy(out_float, in_float, float_bytes);
        in_float += float_bytes;
        out_float += float_bytes;

        GibPackedTag next_tag = *(GibPackedTag *) in_dcon;

        if (next_tag == 1) {
            *(GibPackedTag *) out_dcon = 1;
            out_dcon += 1;
            in_dcon += 1;
            break;
        } else if (next_tag == GIB_REDIRECTION_TAG) {
            GibCursor ignored_footer = NULL;

            gib_grow_region(&out_dcon, &out_dcon_end);
            gib_grow_region(&out_int, &out_int_end);
            gib_grow_region(&out_float, &out_float_end);

            in_dcon = manual_vec_add1_follow_redirection(in_dcon,
                                                         &ignored_footer);
            in_int = manual_vec_add1_follow_redirection(in_int,
                                                        &ignored_footer);
            in_float = manual_vec_add1_follow_redirection(in_float,
                                                          &ignored_footer);

            if (first_chunk) {
                first_chunk = false;
            } else {
                next_int_count_footer = next_int_count_footer->next;
                next_float_count_footer = next_float_count_footer->next;
            }
        } else {
            fprintf(stderr,
                    "manual add1List expected Nil or redirection, found %u\n",
                    (unsigned) next_tag);
            exit(1);
        }
    }

    xs_21_104_149[0] = in_dcon;
    xs_21_104_149[1] = in_int;
    xs_21_104_149[2] = in_float;
    cursor_ptr_1063[0] = out_dcon;
    cursor_ptr_1063[1] = out_int;
    cursor_ptr_1063[2] = out_float;
    cursor_ptr_1061[0] = out_dcon_end;
    cursor_ptr_1061[1] = out_int_end;
    cursor_ptr_1061[2] = out_float_end;
    return 0;
}

unsigned char add1List_vectorized(GibCursor cursor_ptr_1062[3],
                                  GibCursor cursor_ptr_1061[3],
                                  GibCursor cursor_ptr_1063[3],
                                  GibCursor xs_21_104_149[3])
{
    return add1List_count_loop(cursor_ptr_1062, cursor_ptr_1061,
                               cursor_ptr_1063, xs_21_104_149, true);
}

unsigned char add1List_loop_scalar(GibCursor cursor_ptr_1062[3],
                                   GibCursor cursor_ptr_1061[3],
                                   GibCursor cursor_ptr_1063[3],
                                   GibCursor xs_21_104_149[3])
{
    return add1List_count_loop(cursor_ptr_1062, cursor_ptr_1061,
                               cursor_ptr_1063, xs_21_104_149, false);
}

static unsigned char add1List_count_loop_indirections(GibCursor cursor_ptr_1062[3],
                                                      GibCursor cursor_ptr_1061[3],
                                                      GibCursor cursor_ptr_1063[3],
                                                      GibCursor xs_21_104_149[3],
                                                      int add_mode)
{
    GibCursor input_dcon_start = xs_21_104_149[0];
    GibCursor input_int_start = xs_21_104_149[1];
    GibCursor input_float_start = xs_21_104_149[2];
    GibCursor in_dcon = input_dcon_start;
    GibCursor in_int = input_int_start;
    GibCursor out_dcon_indir = cursor_ptr_1063[0];
    GibCursor out_int_indir = cursor_ptr_1063[1];
    GibCursor out_float_indir = cursor_ptr_1063[2];
    GibCursor out_int = out_int_indir + 9;
    GibCursor out_int_end = cursor_ptr_1061[1];
    GibCursor out_int_target = NULL;
    GibCursor out_int_target_footer = NULL;
    GibOldgenChunkFooter *final_dcon_footer =
        (GibOldgenChunkFooter *) cursor_ptr_1062[0];
    GibOldgenChunkFooter *final_int_footer =
        (GibOldgenChunkFooter *) cursor_ptr_1062[1];
    GibOldgenChunkFooter *final_float_footer =
        (GibOldgenChunkFooter *) cursor_ptr_1062[2];
    GibOldgenChunkFooter *next_int_count_footer = NULL;
    bool first_chunk = true;

    if (final_dcon_footer == NULL || final_dcon_footer->reg_info == NULL ||
        final_dcon_footer->reg_info->first_chunk_footer == NULL ||
        final_int_footer == NULL || final_int_footer->reg_info == NULL ||
        final_int_footer->reg_info->first_chunk_footer == NULL ||
        final_float_footer == NULL || final_float_footer->reg_info == NULL ||
        final_float_footer->reg_info->first_chunk_footer == NULL) {
        fprintf(stderr, "manual add1List could not find an input footer\n");
        exit(1);
    }

    manual_vec_add1_ensure_space(&out_dcon_indir, &cursor_ptr_1061[0], 9);
    manual_vec_add1_ensure_space(&out_int, &out_int_end, 0);
    manual_vec_add1_ensure_space(&out_float_indir, &cursor_ptr_1061[2], 9);

    next_int_count_footer =
        (GibOldgenChunkFooter *) final_int_footer->reg_info->first_chunk_footer;

    while (true) {
        GibOldgenChunkFooter *int_count_footer =
            first_chunk ? final_int_footer : next_int_count_footer;

        if (int_count_footer == NULL) {
            fprintf(stderr, "manual add1List reached a null int count footer\n");
            exit(1);
        }

        uint64_t count =
            gib_scalar_count_footer_get((char *) int_count_footer, 0, 0);
        size_t int_bytes = (size_t) (count * sizeof(GibInt));

        manual_vec_add1_ensure_space(&out_int, &out_int_end, int_bytes + 9);

        if (out_int_target == NULL) {
            out_int_target = out_int;
            out_int_target_footer = out_int_end;
        }

        in_dcon += count;

        if (add_mode == 1) {
            manual_vec_add1_int_chunk(in_int, out_int, count);
        } else if (add_mode == 2) {
            manual_auto_add1_int_chunk(in_int, out_int, count);
        } else {
            manual_scalar_add1_int_chunk(in_int, out_int, count);
        }

        in_int += int_bytes;
        out_int += int_bytes;

        GibPackedTag next_tag = *(GibPackedTag *) in_dcon;

        if (next_tag == 1) {
            in_dcon += 1;
            break;
        } else if (next_tag == GIB_REDIRECTION_TAG) {
            GibCursor ignored_footer = NULL;

            gib_grow_region(&out_int, &out_int_end);
            in_dcon = manual_vec_add1_follow_redirection(in_dcon,
                                                         &ignored_footer);
            in_int = manual_vec_add1_follow_redirection(in_int,
                                                        &ignored_footer);

            if (first_chunk) {
                first_chunk = false;
            } else {
                next_int_count_footer = next_int_count_footer->next;
            }
        } else {
            fprintf(stderr,
                    "manual add1List expected Nil or redirection, found %u\n",
                    (unsigned) next_tag);
            exit(1);
        }
    }

    manual_write_indirection_tag(out_dcon_indir, input_dcon_start,
        (GibCursor)
        ((GibOldgenChunkFooter *) final_dcon_footer->reg_info->first_chunk_footer));
    manual_write_indirection_tag(out_int_indir, out_int_target,
                                 out_int_target_footer);
    manual_write_indirection_tag(out_float_indir, input_float_start,
        (GibCursor)
        ((GibOldgenChunkFooter *) final_float_footer->reg_info->first_chunk_footer));

    xs_21_104_149[0] = in_dcon;
    xs_21_104_149[1] = in_int;
    xs_21_104_149[2] = input_float_start;
    cursor_ptr_1063[0] = out_dcon_indir + 9;
    cursor_ptr_1063[1] = out_int;
    cursor_ptr_1063[2] = out_float_indir + 9;
    cursor_ptr_1061[1] = out_int_end;
    return 0;
}

unsigned char add1List_vectorized_indirections(GibCursor cursor_ptr_1062[3],
                                               GibCursor cursor_ptr_1061[3],
                                               GibCursor cursor_ptr_1063[3],
                                               GibCursor xs_21_104_149[3])
{
    return add1List_count_loop_indirections(cursor_ptr_1062, cursor_ptr_1061,
                                            cursor_ptr_1063, xs_21_104_149,
                                            1);
}

unsigned char add1List_auto_vectorized_indirections(GibCursor cursor_ptr_1062[3],
                                                    GibCursor cursor_ptr_1061[3],
                                                    GibCursor cursor_ptr_1063[3],
                                                    GibCursor xs_21_104_149[3])
{
    return add1List_count_loop_indirections(cursor_ptr_1062, cursor_ptr_1061,
                                            cursor_ptr_1063, xs_21_104_149,
                                            2);
}

unsigned char add1List_loop_scalar_indirections(GibCursor cursor_ptr_1062[3],
                                                GibCursor cursor_ptr_1061[3],
                                                GibCursor cursor_ptr_1063[3],
                                                GibCursor xs_21_104_149[3])
{
    return add1List_count_loop_indirections(cursor_ptr_1062, cursor_ptr_1061,
                                            cursor_ptr_1063, xs_21_104_149,
                                            0);
}

unsigned char add1List_scalar(GibCursor cursor_ptr_1062[3],
                              GibCursor cursor_ptr_1061[3],
                              GibCursor cursor_ptr_1063[3],
                              GibCursor xs_21_104_149[3])
{
    GibCursor *end_r_398 = &cursor_ptr_1061[2];
    GibCursor *end_r_397 = &cursor_ptr_1061[1];
    GibCursor *end_r_396 = &cursor_ptr_1061[0];
    GibCursor *restrict loc_IntTy_391 = &cursor_ptr_1063[1];
    GibCursor deref_1065 = *loc_IntTy_391;
    GibCursor cpy_1066[3];
    
    memcpy(cpy_1066, cursor_ptr_1063, sizeof(GibCursor [3]));
    
    GibCursor *restrict loc_390 = &cursor_ptr_1063[0];
    GibCursor *restrict loc_FloatTy_392 = &cursor_ptr_1063[2];
    GibCursor deref_1067 = *loc_FloatTy_392;
    GibCursor deref_1068 = *end_r_398;
    GibCursor deref_1069 = *loc_FloatTy_392;
    GibCursor deref_1070 = *end_r_397;
    GibCursor deref_1071 = *loc_IntTy_391;
    GibCursor deref_1072 = *end_r_396;
    GibCursor deref_1073 = *loc_390;
    
    if (deref_1069 + 13 > deref_1068 || (deref_1071 + 17 > deref_1070 ||
                                         deref_1073 + 34 > deref_1072)) {
        gib_grow_region(loc_FloatTy_392, end_r_398);
        gib_grow_region(loc_IntTy_391, end_r_397);
        gib_grow_region(loc_390, end_r_396);
        deref_1069 = *loc_FloatTy_392;
        deref_1071 = *loc_IntTy_391;
        deref_1073 = *loc_390;
    }
    
    GibCursor *end_r_393 = &cursor_ptr_1062[0];
    GibCursor *end_r_394 = &cursor_ptr_1062[1];
    GibCursor *end_r_395 = &cursor_ptr_1062[2];
    GibCursor *restrict loc_387 = &xs_21_104_149[0];
    GibCursor deref_dcon_var_1077 = *loc_387;
    GibPackedTag tmpval_1622 = *(GibPackedTag *) deref_dcon_var_1077;
    GibCursor tmpcur_1623 = deref_dcon_var_1077 + 1;
    
    
  switch_1646:
    ;
    switch (tmpval_1622) {
        
      case 1:
        {
            GibCursor *restrict soa_field_0_1079 = &xs_21_104_149[1];
            GibCursor deref_1080 = *soa_field_0_1079;
            GibCursor *restrict soa_field_1_1081 = &xs_21_104_149[2];
            GibCursor deref_1082 = *soa_field_1_1081;
            
            *loc_387 += 1;
            
            GibCursor jump_floc_loc_596 = deref_1080 + 0;
            GibCursor jump_floc_loc_597 = deref_1082 + 0;
            GibCursor cursor_ptr_1085[3] = {tmpcur_1623, jump_floc_loc_596,
                                            jump_floc_loc_597};
            
            *(GibPackedTag *) deref_1073 = 1;
            
            GibCursor writetag_1089 = deref_1073 + 1;
            GibCursor after_tag_1090 = deref_1073 + 1;
            
            *loc_390 += 1;
            
            GibCursor aft_soa_loc_1095[3] = {after_tag_1090, deref_1071,
                                             deref_1069};
            GibCursor end_taildc_598[3];
            
            memcpy(end_taildc_598, cursor_ptr_1063, sizeof(GibCursor [3]));
            return 0;
            break;
        }
        
      case 0:
        {
            GibCursor *restrict soa_field_0_1100 = &xs_21_104_149[1];
            GibCursor deref_1101 = *soa_field_0_1100;
            GibCursor *restrict soa_field_1_1102 = &xs_21_104_149[2];
            GibCursor deref_1103 = *soa_field_1_1102;
            GibInt tmpval_1624 = *(GibInt *) deref_1101;
            GibCursor tmpcur_1625 = deref_1101 + sizeof(GibInt);
            
            *soa_field_0_1100 += 8;
            
            GibFloat tmpval_1626 = *(GibFloat *) deref_1103;
            GibCursor tmpcur_1627 = deref_1103 + sizeof(GibFloat);
            
            *soa_field_1_1102 += 4;
            
            GibCursor cursor_ptr_1075[3] = {tmpcur_1623, tmpcur_1625,
                                            tmpcur_1627};
            
            *loc_387 += 1;
            
            GibCursor jumpf_floc_loc_600 = deref_1101 + 8;
            GibCursor jumpf_floc_loc_601 = deref_1103 + 4;
            GibInt fltPkd_121_153 = tmpval_1624 + 1;
            GibCursor new_dloc_510 = deref_1073 + 1;
            
            *loc_390 += 1;
            
            GibCursor new_floc_loc_512 = deref_1069 + 4;
            
            *loc_FloatTy_392 += 4;
            
            GibCursor new_floc_loc_511 = deref_1071 + 8;
            
            *loc_IntTy_391 += 8;
            
            GibCursor cursor_ptr_1116[3] = {new_dloc_510, new_floc_loc_511,
                                            new_floc_loc_512};
            
            *(GibPackedTag *) deref_1073 = 0;
            
            GibCursor writetag_1143 = deref_1073 + 1;
            GibCursor after_tag_1144 = deref_1073 + 1;
            
            *(GibInt *) deref_1071 = fltPkd_121_153;
            
            GibCursor writecur_1148 = deref_1071 + sizeof(GibInt);
            
            *(GibFloat *) deref_1069 = tmpval_1626;
            
            GibCursor writecur_1150 = deref_1069 + sizeof(GibFloat);
            GibCursor chk_loc_1138 = cursor_ptr_1075[0];
            GibCursor chk_end_1139 = cursor_ptr_1062[0];
            GibBool chk_1140 = chk_loc_1138 < chk_end_1139;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1135 = cursor_ptr_1075[1];
            GibCursor chk_end_1136 = cursor_ptr_1062[1];
            GibBool chk_1137 = chk_loc_1135 < chk_end_1136;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1132 = cursor_ptr_1075[2];
            GibCursor chk_end_1133 = cursor_ptr_1062[2];
            GibBool chk_1134 = chk_loc_1132 < chk_end_1133;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1129 = cursor_ptr_1116[0];
            GibCursor chk_end_1130 = cursor_ptr_1061[0];
            GibBool chk_1131 = chk_loc_1129 < chk_end_1130;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1126 = cursor_ptr_1116[1];
            GibCursor chk_end_1127 = cursor_ptr_1061[1];
            GibBool chk_1128 = chk_loc_1126 < chk_end_1127;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1123 = cursor_ptr_1116[2];
            GibCursor chk_end_1124 = cursor_ptr_1061[2];
            GibBool chk_1125 = chk_loc_1123 < chk_end_1124;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            unsigned char tup_packed_1141 =
                           add1List_scalar(cursor_ptr_1062, cursor_ptr_1061, cursor_ptr_1063, xs_21_104_149);
            GibCursor end_fltPkd_122_154[3];
            
            memcpy(end_fltPkd_122_154, cursor_ptr_1063, sizeof(GibCursor [3]));
            
            GibCursor loc_cursor_ptr_1117[3];
            
            memcpy(loc_cursor_ptr_1117, xs_21_104_149, sizeof(GibCursor [3]));
            
            GibCursor end_taildc_605[3];
            
            memcpy(end_taildc_605, cursor_ptr_1063, sizeof(GibCursor [3]));
            return 0;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            GibCursor *restrict soa_field_0_1157 = &xs_21_104_149[1];
            GibCursor deref_1158 = *soa_field_0_1157;
            GibCursor *restrict soa_field_1_1159 = &xs_21_104_149[2];
            GibCursor deref_1160 = *soa_field_1_1159;
            uintptr_t tagged_tmpcur_14 = *(uintptr_t *) tmpcur_1623;
            GibCursor tmpcur_1628 = GIB_UNTAG(tagged_tmpcur_14);
            GibCursor tmpaftercur_1629 = tmpcur_1623 + 8;
            uint16_t tmptag_1630 = GIB_GET_TAG(tagged_tmpcur_14);
            
            *(GibCursor *) loc_387 = tmpcur_1628;
            
            GibCursor end_from_tagged_dcon_redir_1173 = tmpcur_1628 +
                      tmptag_1630;
            GibCursor field_nxt_1170 = deref_1158 + 1;
            uintptr_t tagged_tmpcur_13 = *(uintptr_t *) field_nxt_1170;
            GibCursor tmpcur_1631 = GIB_UNTAG(tagged_tmpcur_13);
            GibCursor tmpaftercur_1632 = field_nxt_1170 + 8;
            uint16_t tmptag_1633 = GIB_GET_TAG(tagged_tmpcur_13);
            
            *(GibCursor *) soa_field_0_1157 = tmpcur_1631;
            
            GibCursor end_from_tagged_fld_redir_1174 = tmpcur_1631 +
                      tmptag_1633;
            GibCursor field_nxt_1171 = deref_1160 + 1;
            uintptr_t tagged_tmpcur_12 = *(uintptr_t *) field_nxt_1171;
            GibCursor tmpcur_1634 = GIB_UNTAG(tagged_tmpcur_12);
            GibCursor tmpaftercur_1635 = field_nxt_1171 + 8;
            uint16_t tmptag_1636 = GIB_GET_TAG(tagged_tmpcur_12);
            
            *(GibCursor *) soa_field_1_1159 = tmpcur_1634;
            
            GibCursor end_from_tagged_fld_redir_1175 = tmpcur_1634 +
                      tmptag_1636;
            GibCursor indr_664[3] = {tmpcur_1628, tmpcur_1631, tmpcur_1634};
            GibCursor jump_dloc_668 = deref_dcon_var_1077 + 9;
            GibCursor aft_indir_loc_676 = deref_1158 + 9;
            GibCursor aft_indir_loc_677 = deref_1160 + 9;
            GibCursor cursor_ptr_1176[3] = {jump_dloc_668, aft_indir_loc_676,
                                            aft_indir_loc_677};
            GibCursor chk_end_1192 = cursor_ptr_1062[0];
            GibBool chk_1193 = deref_dcon_var_1077 < chk_end_1192;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1189 = cursor_ptr_1063[0];
            GibCursor chk_end_1190 = cursor_ptr_1061[0];
            GibBool chk_1191 = chk_loc_1189 < chk_end_1190;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1186 = cursor_ptr_1063[1];
            GibCursor chk_end_1187 = cursor_ptr_1061[1];
            GibBool chk_1188 = chk_loc_1186 < chk_end_1187;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1183 = cursor_ptr_1063[2];
            GibCursor chk_end_1184 = cursor_ptr_1061[2];
            GibBool chk_1185 = chk_loc_1183 < chk_end_1184;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            unsigned char tup_packed_1194 =
                           add1List_scalar(xs_21_104_149, cursor_ptr_1061, cursor_ptr_1063, xs_21_104_149);
            GibCursor end_call_671[3];
            
            memcpy(end_call_671, cursor_ptr_1063, sizeof(GibCursor [3]));
            
            GibCursor loc_cursor_ptr_1177[3];
            
            memcpy(loc_cursor_ptr_1177, xs_21_104_149, sizeof(GibCursor [3]));
            return 0;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            GibCursor *restrict soa_field_0_1197 = &xs_21_104_149[1];
            GibCursor deref_1198 = *soa_field_0_1197;
            GibCursor *restrict soa_field_1_1199 = &xs_21_104_149[2];
            GibCursor deref_1200 = *soa_field_1_1199;
            uintptr_t tagged_tmpcur_17 = *(uintptr_t *) tmpcur_1623;
            GibCursor tmpcur_1637 = GIB_UNTAG(tagged_tmpcur_17);
            GibCursor tmpaftercur_1638 = tmpcur_1623 + 8;
            uint16_t tmptag_1639 = GIB_GET_TAG(tagged_tmpcur_17);
            
            *(GibCursor *) loc_387 = tmpcur_1637;
            
            GibCursor end_from_tagged_dcon_redir_1208 = tmpcur_1637 +
                      tmptag_1639;
            GibCursor field_nxt_1206 = deref_1198 + 1;
            uintptr_t tagged_tmpcur_16 = *(uintptr_t *) field_nxt_1206;
            GibCursor tmpcur_1640 = GIB_UNTAG(tagged_tmpcur_16);
            GibCursor tmpaftercur_1641 = field_nxt_1206 + 8;
            uint16_t tmptag_1642 = GIB_GET_TAG(tagged_tmpcur_16);
            
            *(GibCursor *) soa_field_0_1197 = tmpcur_1640;
            
            GibCursor end_from_tagged_fld_redir_1209 = tmpcur_1640 +
                      tmptag_1642;
            GibCursor field_nxt_1207 = deref_1200 + 1;
            uintptr_t tagged_tmpcur_15 = *(uintptr_t *) field_nxt_1207;
            GibCursor tmpcur_1643 = GIB_UNTAG(tagged_tmpcur_15);
            GibCursor tmpaftercur_1644 = field_nxt_1207 + 8;
            uint16_t tmptag_1645 = GIB_GET_TAG(tagged_tmpcur_15);
            
            *(GibCursor *) soa_field_1_1199 = tmpcur_1643;
            
            GibCursor end_from_tagged_fld_redir_1210 = tmpcur_1643 +
                      tmptag_1645;
            GibCursor indr_664[3] = {tmpcur_1637, tmpcur_1640, tmpcur_1643};
            GibCursor copy_dloc_678 = deref_1073 + 0;
            
            *loc_390 += 0;
            
            GibCursor copy_floc_loc_680 = deref_1069 + 0;
            
            *loc_FloatTy_392 += 0;
            
            GibCursor copy_floc_loc_679 = deref_1071 + 0;
            
            *loc_IntTy_391 += 0;
            
            GibCursor cursor_ptr_1214[3] = {copy_dloc_678, copy_floc_loc_679,
                                            copy_floc_loc_680};
            GibCursor chk_end_1230 = cursor_ptr_1062[0];
            GibBool chk_1231 = deref_dcon_var_1077 < chk_end_1230;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1227 = cursor_ptr_1214[0];
            GibCursor chk_end_1228 = cursor_ptr_1061[0];
            GibBool chk_1229 = chk_loc_1227 < chk_end_1228;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1224 = cursor_ptr_1214[1];
            GibCursor chk_end_1225 = cursor_ptr_1061[1];
            GibBool chk_1226 = chk_loc_1224 < chk_end_1225;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1221 = cursor_ptr_1214[2];
            GibCursor chk_end_1222 = cursor_ptr_1061[2];
            GibBool chk_1223 = chk_loc_1221 < chk_end_1222;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            unsigned char tup_packed_1232 =
                           add1List_scalar(xs_21_104_149, cursor_ptr_1061, cursor_ptr_1063, xs_21_104_149);
            GibCursor end_call_671[3];
            
            memcpy(end_call_671, cursor_ptr_1063, sizeof(GibCursor [3]));
            
            GibCursor loc_cursor_ptr_1215[3];
            
            memcpy(loc_cursor_ptr_1215, xs_21_104_149, sizeof(GibCursor [3]));
            return 0;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1622");
            exit(1);
        }
    }
}
unsigned char add1List(GibCursor cursor_ptr_1062[3],
                       GibCursor cursor_ptr_1061[3],
                       GibCursor cursor_ptr_1063[3], GibCursor xs_21_104_149[3])
{
    return add1List_vectorized(cursor_ptr_1062, cursor_ptr_1061,
                               cursor_ptr_1063, xs_21_104_149);
}
unsigned char _copy_List(GibCursor cursor_ptr_1236[3],
                         GibCursor cursor_ptr_1235[3],
                         GibCursor cursor_ptr_1237[3],
                         GibCursor arg_53_108_155[3])
{
    GibCursor *end_r_410 = &cursor_ptr_1235[2];
    GibCursor *end_r_408 = &cursor_ptr_1235[0];
    GibCursor *end_r_409 = &cursor_ptr_1235[1];
    GibCursor *restrict loc_FloatTy_404 = &cursor_ptr_1237[2];
    GibCursor deref_1239 = *loc_FloatTy_404;
    GibCursor cpy_1240[3];
    
    memcpy(cpy_1240, cursor_ptr_1237, sizeof(GibCursor [3]));
    
    GibCursor *restrict loc_402 = &cursor_ptr_1237[0];
    GibCursor *restrict loc_IntTy_403 = &cursor_ptr_1237[1];
    GibCursor deref_1241 = *loc_IntTy_403;
    GibCursor deref_1242 = *end_r_410;
    GibCursor deref_1243 = *loc_FloatTy_404;
    GibCursor deref_1244 = *end_r_409;
    GibCursor deref_1245 = *loc_IntTy_403;
    GibCursor deref_1246 = *end_r_408;
    GibCursor deref_1247 = *loc_402;
    
    if (deref_1243 + 13 > deref_1242 || (deref_1245 + 17 > deref_1244 ||
                                         deref_1247 + 34 > deref_1246)) {
        gib_grow_region(loc_FloatTy_404, end_r_410);
        gib_grow_region(loc_IntTy_403, end_r_409);
        gib_grow_region(loc_402, end_r_408);
        deref_1243 = *loc_FloatTy_404;
        deref_1245 = *loc_IntTy_403;
        deref_1247 = *loc_402;
    }
    
    GibCursor *end_r_405 = &cursor_ptr_1236[0];
    GibCursor *end_r_406 = &cursor_ptr_1236[1];
    GibCursor *end_r_407 = &cursor_ptr_1236[2];
    GibCursor *restrict loc_399 = &arg_53_108_155[0];
    GibCursor deref_dcon_var_1251 = *loc_399;
    GibPackedTag tmpval_1647 = *(GibPackedTag *) deref_dcon_var_1251;
    GibCursor tmpcur_1648 = deref_dcon_var_1251 + 1;
    
    
  switch_1671:
    ;
    switch (tmpval_1647) {
        
      case 0:
        {
            GibCursor *restrict soa_field_0_1253 = &arg_53_108_155[1];
            GibCursor deref_1254 = *soa_field_0_1253;
            GibCursor *restrict soa_field_1_1255 = &arg_53_108_155[2];
            GibCursor deref_1256 = *soa_field_1_1255;
            GibInt tmpval_1649 = *(GibInt *) deref_1254;
            GibCursor tmpcur_1650 = deref_1254 + sizeof(GibInt);
            
            *soa_field_0_1253 += 8;
            
            GibFloat tmpval_1651 = *(GibFloat *) deref_1256;
            GibCursor tmpcur_1652 = deref_1256 + sizeof(GibFloat);
            
            *soa_field_1_1255 += 4;
            
            GibCursor cursor_ptr_1249[3] = {tmpcur_1648, tmpcur_1650,
                                            tmpcur_1652};
            
            *loc_399 += 1;
            
            GibCursor jumpf_floc_loc_607 = deref_1254 + 8;
            GibCursor jumpf_floc_loc_608 = deref_1256 + 4;
            GibCursor new_dloc_538 = deref_1247 + 1;
            
            *loc_402 += 1;
            
            GibCursor new_floc_loc_540 = deref_1243 + 4;
            
            *loc_FloatTy_404 += 4;
            
            GibCursor new_floc_loc_539 = deref_1245 + 8;
            
            *loc_IntTy_403 += 8;
            
            GibCursor cursor_ptr_1269[3] = {new_dloc_538, new_floc_loc_539,
                                            new_floc_loc_540};
            
            *(GibPackedTag *) deref_1247 = 0;
            
            GibCursor writetag_1296 = deref_1247 + 1;
            GibCursor after_tag_1297 = deref_1247 + 1;
            
            *(GibInt *) deref_1245 = tmpval_1649;
            
            GibCursor writecur_1301 = deref_1245 + sizeof(GibInt);
            
            *(GibFloat *) deref_1243 = tmpval_1651;
            
            GibCursor writecur_1303 = deref_1243 + sizeof(GibFloat);
            GibCursor chk_loc_1291 = cursor_ptr_1249[0];
            GibCursor chk_end_1292 = cursor_ptr_1236[0];
            GibBool chk_1293 = chk_loc_1291 < chk_end_1292;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1288 = cursor_ptr_1249[1];
            GibCursor chk_end_1289 = cursor_ptr_1236[1];
            GibBool chk_1290 = chk_loc_1288 < chk_end_1289;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1285 = cursor_ptr_1249[2];
            GibCursor chk_end_1286 = cursor_ptr_1236[2];
            GibBool chk_1287 = chk_loc_1285 < chk_end_1286;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1282 = cursor_ptr_1269[0];
            GibCursor chk_end_1283 = cursor_ptr_1235[0];
            GibBool chk_1284 = chk_loc_1282 < chk_end_1283;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1279 = cursor_ptr_1269[1];
            GibCursor chk_end_1280 = cursor_ptr_1235[1];
            GibBool chk_1281 = chk_loc_1279 < chk_end_1280;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1276 = cursor_ptr_1269[2];
            GibCursor chk_end_1277 = cursor_ptr_1235[2];
            GibBool chk_1278 = chk_loc_1276 < chk_end_1277;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            unsigned char tup_packed_1294 =
                           _copy_List(cursor_ptr_1236, cursor_ptr_1235, cursor_ptr_1237, arg_53_108_155);
            GibCursor end_y_59_114_161[3];
            
            memcpy(end_y_59_114_161, cursor_ptr_1237, sizeof(GibCursor [3]));
            
            GibCursor loc_cursor_ptr_1270[3];
            
            memcpy(loc_cursor_ptr_1270, arg_53_108_155, sizeof(GibCursor [3]));
            
            GibCursor end_taildc_612[3];
            
            memcpy(end_taildc_612, cursor_ptr_1237, sizeof(GibCursor [3]));
            return 0;
            break;
        }
        
      case 1:
        {
            GibCursor *restrict soa_field_0_1310 = &arg_53_108_155[1];
            GibCursor deref_1311 = *soa_field_0_1310;
            GibCursor *restrict soa_field_1_1312 = &arg_53_108_155[2];
            GibCursor deref_1313 = *soa_field_1_1312;
            
            *loc_399 += 1;
            
            GibCursor jump_floc_loc_614 = deref_1311 + 0;
            GibCursor jump_floc_loc_615 = deref_1313 + 0;
            GibCursor cursor_ptr_1316[3] = {tmpcur_1648, jump_floc_loc_614,
                                            jump_floc_loc_615};
            
            *(GibPackedTag *) deref_1247 = 1;
            
            GibCursor writetag_1320 = deref_1247 + 1;
            GibCursor after_tag_1321 = deref_1247 + 1;
            
            *loc_402 += 1;
            
            GibCursor aft_soa_loc_1326[3] = {after_tag_1321, deref_1245,
                                             deref_1243};
            GibCursor end_taildc_616[3];
            
            memcpy(end_taildc_616, cursor_ptr_1237, sizeof(GibCursor [3]));
            return 0;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            GibCursor *restrict soa_field_0_1331 = &arg_53_108_155[1];
            GibCursor deref_1332 = *soa_field_0_1331;
            GibCursor *restrict soa_field_1_1333 = &arg_53_108_155[2];
            GibCursor deref_1334 = *soa_field_1_1333;
            uintptr_t tagged_tmpcur_20 = *(uintptr_t *) tmpcur_1648;
            GibCursor tmpcur_1653 = GIB_UNTAG(tagged_tmpcur_20);
            GibCursor tmpaftercur_1654 = tmpcur_1648 + 8;
            uint16_t tmptag_1655 = GIB_GET_TAG(tagged_tmpcur_20);
            
            *(GibCursor *) loc_399 = tmpcur_1653;
            
            GibCursor end_from_tagged_dcon_redir_1347 = tmpcur_1653 +
                      tmptag_1655;
            GibCursor field_nxt_1344 = deref_1332 + 1;
            uintptr_t tagged_tmpcur_19 = *(uintptr_t *) field_nxt_1344;
            GibCursor tmpcur_1656 = GIB_UNTAG(tagged_tmpcur_19);
            GibCursor tmpaftercur_1657 = field_nxt_1344 + 8;
            uint16_t tmptag_1658 = GIB_GET_TAG(tagged_tmpcur_19);
            
            *(GibCursor *) soa_field_0_1331 = tmpcur_1656;
            
            GibCursor end_from_tagged_fld_redir_1348 = tmpcur_1656 +
                      tmptag_1658;
            GibCursor field_nxt_1345 = deref_1334 + 1;
            uintptr_t tagged_tmpcur_18 = *(uintptr_t *) field_nxt_1345;
            GibCursor tmpcur_1659 = GIB_UNTAG(tagged_tmpcur_18);
            GibCursor tmpaftercur_1660 = field_nxt_1345 + 8;
            uint16_t tmptag_1661 = GIB_GET_TAG(tagged_tmpcur_18);
            
            *(GibCursor *) soa_field_1_1333 = tmpcur_1659;
            
            GibCursor end_from_tagged_fld_redir_1349 = tmpcur_1659 +
                      tmptag_1661;
            GibCursor indr_681[3] = {tmpcur_1653, tmpcur_1656, tmpcur_1659};
            GibCursor jump_dloc_685 = deref_dcon_var_1251 + 9;
            GibCursor aft_indir_loc_693 = deref_1332 + 9;
            GibCursor aft_indir_loc_694 = deref_1334 + 9;
            GibCursor cursor_ptr_1350[3] = {jump_dloc_685, aft_indir_loc_693,
                                            aft_indir_loc_694};
            GibCursor chk_end_1366 = cursor_ptr_1236[0];
            GibBool chk_1367 = deref_dcon_var_1251 < chk_end_1366;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1363 = cursor_ptr_1237[0];
            GibCursor chk_end_1364 = cursor_ptr_1235[0];
            GibBool chk_1365 = chk_loc_1363 < chk_end_1364;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1360 = cursor_ptr_1237[1];
            GibCursor chk_end_1361 = cursor_ptr_1235[1];
            GibBool chk_1362 = chk_loc_1360 < chk_end_1361;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1357 = cursor_ptr_1237[2];
            GibCursor chk_end_1358 = cursor_ptr_1235[2];
            GibBool chk_1359 = chk_loc_1357 < chk_end_1358;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            unsigned char tup_packed_1368 =
                           _copy_List(arg_53_108_155, cursor_ptr_1235, cursor_ptr_1237, arg_53_108_155);
            GibCursor end_call_688[3];
            
            memcpy(end_call_688, cursor_ptr_1237, sizeof(GibCursor [3]));
            
            GibCursor loc_cursor_ptr_1351[3];
            
            memcpy(loc_cursor_ptr_1351, arg_53_108_155, sizeof(GibCursor [3]));
            return 0;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            GibCursor *restrict soa_field_0_1371 = &arg_53_108_155[1];
            GibCursor deref_1372 = *soa_field_0_1371;
            GibCursor *restrict soa_field_1_1373 = &arg_53_108_155[2];
            GibCursor deref_1374 = *soa_field_1_1373;
            uintptr_t tagged_tmpcur_23 = *(uintptr_t *) tmpcur_1648;
            GibCursor tmpcur_1662 = GIB_UNTAG(tagged_tmpcur_23);
            GibCursor tmpaftercur_1663 = tmpcur_1648 + 8;
            uint16_t tmptag_1664 = GIB_GET_TAG(tagged_tmpcur_23);
            
            *(GibCursor *) loc_399 = tmpcur_1662;
            
            GibCursor end_from_tagged_dcon_redir_1382 = tmpcur_1662 +
                      tmptag_1664;
            GibCursor field_nxt_1380 = deref_1372 + 1;
            uintptr_t tagged_tmpcur_22 = *(uintptr_t *) field_nxt_1380;
            GibCursor tmpcur_1665 = GIB_UNTAG(tagged_tmpcur_22);
            GibCursor tmpaftercur_1666 = field_nxt_1380 + 8;
            uint16_t tmptag_1667 = GIB_GET_TAG(tagged_tmpcur_22);
            
            *(GibCursor *) soa_field_0_1371 = tmpcur_1665;
            
            GibCursor end_from_tagged_fld_redir_1383 = tmpcur_1665 +
                      tmptag_1667;
            GibCursor field_nxt_1381 = deref_1374 + 1;
            uintptr_t tagged_tmpcur_21 = *(uintptr_t *) field_nxt_1381;
            GibCursor tmpcur_1668 = GIB_UNTAG(tagged_tmpcur_21);
            GibCursor tmpaftercur_1669 = field_nxt_1381 + 8;
            uint16_t tmptag_1670 = GIB_GET_TAG(tagged_tmpcur_21);
            
            *(GibCursor *) soa_field_1_1373 = tmpcur_1668;
            
            GibCursor end_from_tagged_fld_redir_1384 = tmpcur_1668 +
                      tmptag_1670;
            GibCursor indr_681[3] = {tmpcur_1662, tmpcur_1665, tmpcur_1668};
            GibCursor copy_dloc_695 = deref_1247 + 0;
            
            *loc_402 += 0;
            
            GibCursor copy_floc_loc_697 = deref_1243 + 0;
            
            *loc_FloatTy_404 += 0;
            
            GibCursor copy_floc_loc_696 = deref_1245 + 0;
            
            *loc_IntTy_403 += 0;
            
            GibCursor cursor_ptr_1388[3] = {copy_dloc_695, copy_floc_loc_696,
                                            copy_floc_loc_697};
            GibCursor chk_end_1404 = cursor_ptr_1236[0];
            GibBool chk_1405 = deref_dcon_var_1251 < chk_end_1404;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1401 = cursor_ptr_1388[0];
            GibCursor chk_end_1402 = cursor_ptr_1235[0];
            GibBool chk_1403 = chk_loc_1401 < chk_end_1402;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1398 = cursor_ptr_1388[1];
            GibCursor chk_end_1399 = cursor_ptr_1235[1];
            GibBool chk_1400 = chk_loc_1398 < chk_end_1399;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1395 = cursor_ptr_1388[2];
            GibCursor chk_end_1396 = cursor_ptr_1235[2];
            GibBool chk_1397 = chk_loc_1395 < chk_end_1396;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            unsigned char tup_packed_1406 =
                           _copy_List(arg_53_108_155, cursor_ptr_1235, cursor_ptr_1237, arg_53_108_155);
            GibCursor end_call_688[3];
            
            memcpy(end_call_688, cursor_ptr_1237, sizeof(GibCursor [3]));
            
            GibCursor loc_cursor_ptr_1389[3];
            
            memcpy(loc_cursor_ptr_1389, arg_53_108_155, sizeof(GibCursor [3]));
            return 0;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1647");
            exit(1);
        }
    }
}
GibInt sumList(GibCursor cursor_ptr_1409[3], GibCursor xs_25_115_162[3])
{
    GibCursor *end_r_414 = &cursor_ptr_1409[0];
    GibCursor *end_r_415 = &cursor_ptr_1409[1];
    GibCursor *end_r_416 = &cursor_ptr_1409[2];
    GibCursor *restrict loc_411 = &xs_25_115_162[0];
    GibCursor deref_dcon_var_1413 = *loc_411;
    GibPackedTag tmpval_1672 = *(GibPackedTag *) deref_dcon_var_1413;
    GibCursor tmpcur_1673 = deref_dcon_var_1413 + 1;
    
    
  switch_1696:
    ;
    switch (tmpval_1672) {
        
      case 1:
        {
            GibCursor *restrict soa_field_0_1415 = &xs_25_115_162[1];
            GibCursor deref_1416 = *soa_field_0_1415;
            GibCursor *restrict soa_field_1_1417 = &xs_25_115_162[2];
            GibCursor deref_1418 = *soa_field_1_1417;
            
            *loc_411 += 1;
            
            GibCursor jump_floc_loc_619 = deref_1416 + 0;
            GibCursor jump_floc_loc_620 = deref_1418 + 0;
            GibCursor cursor_ptr_1421[3] = {tmpcur_1673, jump_floc_loc_619,
                                            jump_floc_loc_620};
            
            return 0;
            break;
        }
        
      case 0:
        {
            GibCursor *restrict soa_field_0_1423 = &xs_25_115_162[1];
            GibCursor deref_1424 = *soa_field_0_1423;
            GibCursor *restrict soa_field_1_1425 = &xs_25_115_162[2];
            GibCursor deref_1426 = *soa_field_1_1425;
            GibInt tmpval_1674 = *(GibInt *) deref_1424;
            GibCursor tmpcur_1675 = deref_1424 + sizeof(GibInt);
            
            *soa_field_0_1423 += 8;
            
            GibFloat tmpval_1676 = *(GibFloat *) deref_1426;
            GibCursor tmpcur_1677 = deref_1426 + sizeof(GibFloat);
            GibCursor cursor_ptr_1411[3] = {tmpcur_1673, tmpcur_1675,
                                            tmpcur_1677};
            
            *loc_411 += 1;
            
            GibCursor jumpf_floc_loc_622 = deref_1424 + 8;
            GibCursor jumpf_floc_loc_623 = deref_1426 + 4;
            GibCursor loc_557 = tmpcur_1673 + 0;
            
            *loc_411 += 0;
            
            GibCursor loc_556 = jumpf_floc_loc_623 + 0;
            GibCursor loc_555 = jumpf_floc_loc_622 + 0;
            GibCursor cursor_ptr_1434[3] = {tmpcur_1673, jumpf_floc_loc_622,
                                            jumpf_floc_loc_623};
            GibCursor chk_loc_1445 = cursor_ptr_1411[0];
            GibCursor chk_end_1446 = cursor_ptr_1409[0];
            GibBool chk_1447 = chk_loc_1445 < chk_end_1446;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1442 = cursor_ptr_1411[1];
            GibCursor chk_end_1443 = cursor_ptr_1409[1];
            GibBool chk_1444 = chk_loc_1442 < chk_end_1443;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1439 = cursor_ptr_1411[2];
            GibCursor chk_end_1440 = cursor_ptr_1409[2];
            GibBool chk_1441 = chk_loc_1439 < chk_end_1440;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibInt fltPrm_123_166 =  sumList(cursor_ptr_1409, xs_25_115_162);
            GibCursor loc_cursor_ptr_1435[3];
            
            memcpy(loc_cursor_ptr_1435, xs_25_115_162, sizeof(GibCursor [3]));
            
            GibInt tailprim_627 = tmpval_1674 + fltPrm_123_166;
            
            return tailprim_627;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            GibCursor *restrict soa_field_0_1450 = &xs_25_115_162[1];
            GibCursor deref_1451 = *soa_field_0_1450;
            GibCursor *restrict soa_field_1_1452 = &xs_25_115_162[2];
            GibCursor deref_1453 = *soa_field_1_1452;
            uintptr_t tagged_tmpcur_26 = *(uintptr_t *) tmpcur_1673;
            GibCursor tmpcur_1678 = GIB_UNTAG(tagged_tmpcur_26);
            GibCursor tmpaftercur_1679 = tmpcur_1673 + 8;
            uint16_t tmptag_1680 = GIB_GET_TAG(tagged_tmpcur_26);
            
            *(GibCursor *) loc_411 = tmpcur_1678;
            
            GibCursor end_from_tagged_dcon_redir_1466 = tmpcur_1678 +
                      tmptag_1680;
            GibCursor field_nxt_1463 = deref_1451 + 1;
            uintptr_t tagged_tmpcur_25 = *(uintptr_t *) field_nxt_1463;
            GibCursor tmpcur_1681 = GIB_UNTAG(tagged_tmpcur_25);
            GibCursor tmpaftercur_1682 = field_nxt_1463 + 8;
            uint16_t tmptag_1683 = GIB_GET_TAG(tagged_tmpcur_25);
            
            *(GibCursor *) soa_field_0_1450 = tmpcur_1681;
            
            GibCursor end_from_tagged_fld_redir_1467 = tmpcur_1681 +
                      tmptag_1683;
            GibCursor field_nxt_1464 = deref_1453 + 1;
            uintptr_t tagged_tmpcur_24 = *(uintptr_t *) field_nxt_1464;
            GibCursor tmpcur_1684 = GIB_UNTAG(tagged_tmpcur_24);
            GibCursor tmpaftercur_1685 = field_nxt_1464 + 8;
            uint16_t tmptag_1686 = GIB_GET_TAG(tagged_tmpcur_24);
            GibCursor end_from_tagged_fld_redir_1468 = tmpcur_1684 +
                      tmptag_1686;
            GibCursor indr_698[3] = {tmpcur_1678, tmpcur_1681, tmpcur_1684};
            GibCursor jump_dloc_702 = deref_dcon_var_1413 + 9;
            GibCursor aft_indir_loc_710 = deref_1451 + 9;
            GibCursor aft_indir_loc_711 = deref_1453 + 9;
            GibCursor cursor_ptr_1469[3] = {jump_dloc_702, aft_indir_loc_710,
                                            aft_indir_loc_711};
            GibCursor chk_end_1474 = cursor_ptr_1409[0];
            GibBool chk_1475 = deref_dcon_var_1413 < chk_end_1474;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibInt call_705 =  sumList(xs_25_115_162, xs_25_115_162);
            GibCursor loc_cursor_ptr_1470[3];
            
            memcpy(loc_cursor_ptr_1470, xs_25_115_162, sizeof(GibCursor [3]));
            return call_705;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            GibCursor *restrict soa_field_0_1478 = &xs_25_115_162[1];
            GibCursor deref_1479 = *soa_field_0_1478;
            GibCursor *restrict soa_field_1_1480 = &xs_25_115_162[2];
            GibCursor deref_1481 = *soa_field_1_1480;
            uintptr_t tagged_tmpcur_29 = *(uintptr_t *) tmpcur_1673;
            GibCursor tmpcur_1687 = GIB_UNTAG(tagged_tmpcur_29);
            GibCursor tmpaftercur_1688 = tmpcur_1673 + 8;
            uint16_t tmptag_1689 = GIB_GET_TAG(tagged_tmpcur_29);
            
            *(GibCursor *) loc_411 = tmpcur_1687;
            
            GibCursor end_from_tagged_dcon_redir_1489 = tmpcur_1687 +
                      tmptag_1689;
            GibCursor field_nxt_1487 = deref_1479 + 1;
            uintptr_t tagged_tmpcur_28 = *(uintptr_t *) field_nxt_1487;
            GibCursor tmpcur_1690 = GIB_UNTAG(tagged_tmpcur_28);
            GibCursor tmpaftercur_1691 = field_nxt_1487 + 8;
            uint16_t tmptag_1692 = GIB_GET_TAG(tagged_tmpcur_28);
            
            *(GibCursor *) soa_field_0_1478 = tmpcur_1690;
            
            GibCursor end_from_tagged_fld_redir_1490 = tmpcur_1690 +
                      tmptag_1692;
            GibCursor field_nxt_1488 = deref_1481 + 1;
            uintptr_t tagged_tmpcur_27 = *(uintptr_t *) field_nxt_1488;
            GibCursor tmpcur_1693 = GIB_UNTAG(tagged_tmpcur_27);
            GibCursor tmpaftercur_1694 = field_nxt_1488 + 8;
            uint16_t tmptag_1695 = GIB_GET_TAG(tagged_tmpcur_27);
            GibCursor end_from_tagged_fld_redir_1491 = tmpcur_1693 +
                      tmptag_1695;
            GibCursor indr_698[3] = {tmpcur_1687, tmpcur_1690, tmpcur_1693};
            GibCursor chk_end_1496 = cursor_ptr_1409[0];
            GibBool chk_1497 = deref_dcon_var_1413 < chk_end_1496;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibInt call_705 =  sumList(xs_25_115_162, xs_25_115_162);
            GibCursor loc_cursor_ptr_1492[3];
            
            memcpy(loc_cursor_ptr_1492, xs_25_115_162, sizeof(GibCursor [3]));
            return call_705;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1672");
            exit(1);
        }
    }
}
int main(int argc, char **argv)
{
    int init_30 = gib_init(argc, argv);
    
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
    GibCursor reg_ptr_1499[3] = {r_444, r_445, r_446};
    GibCursor reg_cursor_ptr_1500[3] = {end_r_444, end_r_445, end_r_446};
    GibCursor cursor_ptr_1501[3];
    
    memcpy(cursor_ptr_1501, reg_ptr_1499, sizeof(GibCursor [3]));
    
    GibCursor chk_loc_1510 = cursor_ptr_1501[0];
    GibCursor chk_end_1511 = reg_cursor_ptr_1500[0];
    GibBool chk_1512 = chk_loc_1510 < chk_end_1511;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    GibCursor chk_loc_1507 = cursor_ptr_1501[1];
    GibCursor chk_end_1508 = reg_cursor_ptr_1500[1];
    GibBool chk_1509 = chk_loc_1507 < chk_end_1508;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    GibCursor chk_loc_1504 = cursor_ptr_1501[2];
    GibCursor chk_end_1505 = reg_cursor_ptr_1500[2];
    GibBool chk_1506 = chk_loc_1504 < chk_end_1505;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    unsigned char tup_packed_1513 =
                   mkList(reg_cursor_ptr_1500, cursor_ptr_1501, 10000);
    GibCursor end_xs_17_81_124[3];
    
    memcpy(end_xs_17_81_124, cursor_ptr_1501, sizeof(GibCursor [3]));
    
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
    GibCursor reg_ptr_1515[3] = {r_441, r_442, r_443};
    GibCursor reg_cursor_ptr_1516[3] = {end_r_441, end_r_442, end_r_443};
    GibCursor cursor_ptr_1517[3];
    
    memcpy(cursor_ptr_1517, reg_ptr_1515, sizeof(GibCursor [3]));
    
    GibCursor chk_loc_1539 = cursor_ptr_1501[0];
    GibCursor chk_end_1540 = reg_cursor_ptr_1500[0];
    GibBool chk_1541 = chk_loc_1539 < chk_end_1540;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    GibCursor chk_loc_1536 = cursor_ptr_1501[1];
    GibCursor chk_end_1537 = reg_cursor_ptr_1500[1];
    GibBool chk_1538 = chk_loc_1536 < chk_end_1537;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    GibCursor chk_loc_1533 = cursor_ptr_1501[2];
    GibCursor chk_end_1534 = reg_cursor_ptr_1500[2];
    GibBool chk_1535 = chk_loc_1533 < chk_end_1534;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    GibCursor chk_loc_1530 = cursor_ptr_1517[0];
    GibCursor chk_end_1531 = reg_cursor_ptr_1516[0];
    GibBool chk_1532 = chk_loc_1530 < chk_end_1531;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    GibCursor chk_loc_1527 = cursor_ptr_1517[1];
    GibCursor chk_end_1528 = reg_cursor_ptr_1516[1];
    GibBool chk_1529 = chk_loc_1527 < chk_end_1528;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    GibCursor chk_loc_1524 = cursor_ptr_1517[2];
    GibCursor chk_end_1525 = reg_cursor_ptr_1516[2];
    GibBool chk_1526 = chk_loc_1524 < chk_end_1525;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    GibCursor copy_address_1523[3];
    
    memcpy(copy_address_1523, reg_ptr_1499, sizeof(GibCursor [3]));
    
    double vectorized_add1_start = manual_now_seconds();
    unsigned char tup_packed_1542 =
                   add1List_vectorized(reg_cursor_ptr_1500, reg_cursor_ptr_1516, cursor_ptr_1517, copy_address_1523);
    double vectorized_add1_seconds =
        manual_now_seconds() - vectorized_add1_start;
    GibCursor end_xs__18_82_125[3];
    
    memcpy(end_xs__18_82_125, cursor_ptr_1517, sizeof(GibCursor [3]));
    
    GibCursor chk_loc_1554 = cursor_ptr_1517[0];
    GibCursor chk_end_1555 = reg_cursor_ptr_1516[0];
    GibBool chk_1556 = chk_loc_1554 < chk_end_1555;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    GibCursor chk_loc_1551 = cursor_ptr_1517[1];
    GibCursor chk_end_1552 = reg_cursor_ptr_1516[1];
    GibBool chk_1553 = chk_loc_1551 < chk_end_1552;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    GibCursor chk_loc_1548 = cursor_ptr_1517[2];
    GibCursor chk_end_1549 = reg_cursor_ptr_1516[2];
    GibBool chk_1550 = chk_loc_1548 < chk_end_1549;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    GibCursor copy_address_1547[3];
    
    memcpy(copy_address_1547, reg_ptr_1515, sizeof(GibCursor [3]));
    
    GibInt vectorized_sum =  sumList(reg_cursor_ptr_1516, copy_address_1547);
    
    GibChunk loop_scalar_region_0 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor loop_scalar_r_0 = loop_scalar_region_0.start;
    GibCursor loop_scalar_end_r_0 = loop_scalar_region_0.end;
    GibChunk loop_scalar_region_1 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor loop_scalar_r_1 = loop_scalar_region_1.start;
    GibCursor loop_scalar_end_r_1 = loop_scalar_region_1.end;
    GibChunk loop_scalar_region_2 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor loop_scalar_r_2 = loop_scalar_region_2.start;
    GibCursor loop_scalar_end_r_2 = loop_scalar_region_2.end;
    GibCursor loop_scalar_reg_ptr[3] =
        {loop_scalar_r_0, loop_scalar_r_1, loop_scalar_r_2};
    GibCursor loop_scalar_reg_cursor_ptr[3] =
        {loop_scalar_end_r_0, loop_scalar_end_r_1, loop_scalar_end_r_2};
    GibCursor loop_scalar_cursor_ptr[3];
    
    memcpy(loop_scalar_cursor_ptr, loop_scalar_reg_ptr, sizeof(GibCursor [3]));
    
    GibCursor loop_scalar_copy_address[3];
    
    memcpy(loop_scalar_copy_address, reg_ptr_1499, sizeof(GibCursor [3]));
    
    double loop_scalar_add1_start = manual_now_seconds();
    unsigned char loop_scalar_tup_packed =
                   add1List_loop_scalar(reg_cursor_ptr_1500, loop_scalar_reg_cursor_ptr, loop_scalar_cursor_ptr, loop_scalar_copy_address);
    double loop_scalar_add1_seconds =
        manual_now_seconds() - loop_scalar_add1_start;
    
    GibCursor loop_scalar_sum_address[3];
    
    memcpy(loop_scalar_sum_address, loop_scalar_reg_ptr, sizeof(GibCursor [3]));
    
    GibInt loop_scalar_sum =
        sumList(loop_scalar_reg_cursor_ptr, loop_scalar_sum_address);
    
    GibChunk indir_loop_scalar_region_0 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor indir_loop_scalar_r_0 = indir_loop_scalar_region_0.start;
    GibCursor indir_loop_scalar_end_r_0 = indir_loop_scalar_region_0.end;
    GibChunk indir_loop_scalar_region_1 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor indir_loop_scalar_r_1 = indir_loop_scalar_region_1.start;
    GibCursor indir_loop_scalar_end_r_1 = indir_loop_scalar_region_1.end;
    GibChunk indir_loop_scalar_region_2 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor indir_loop_scalar_r_2 = indir_loop_scalar_region_2.start;
    GibCursor indir_loop_scalar_end_r_2 = indir_loop_scalar_region_2.end;
    GibCursor indir_loop_scalar_reg_ptr[3] =
        {indir_loop_scalar_r_0, indir_loop_scalar_r_1, indir_loop_scalar_r_2};
    GibCursor indir_loop_scalar_reg_cursor_ptr[3] =
        {indir_loop_scalar_end_r_0, indir_loop_scalar_end_r_1,
         indir_loop_scalar_end_r_2};
    GibCursor indir_loop_scalar_cursor_ptr[3];
    
    memcpy(indir_loop_scalar_cursor_ptr, indir_loop_scalar_reg_ptr,
           sizeof(GibCursor [3]));
    
    GibCursor indir_loop_scalar_copy_address[3];
    
    memcpy(indir_loop_scalar_copy_address, reg_ptr_1499, sizeof(GibCursor [3]));
    
    double indir_loop_scalar_add1_start = manual_now_seconds();
    unsigned char indir_loop_scalar_tup_packed =
                   add1List_loop_scalar_indirections(reg_cursor_ptr_1500, indir_loop_scalar_reg_cursor_ptr, indir_loop_scalar_cursor_ptr, indir_loop_scalar_copy_address);
    double indir_loop_scalar_add1_seconds =
        manual_now_seconds() - indir_loop_scalar_add1_start;
    
    GibCursor indir_loop_scalar_sum_address[3];
    
    memcpy(indir_loop_scalar_sum_address, indir_loop_scalar_reg_ptr,
           sizeof(GibCursor [3]));
    
    GibInt indir_loop_scalar_sum =
        sumList(indir_loop_scalar_reg_cursor_ptr, indir_loop_scalar_sum_address);
    
    GibChunk indir_auto_region_0 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor indir_auto_r_0 = indir_auto_region_0.start;
    GibCursor indir_auto_end_r_0 = indir_auto_region_0.end;
    GibChunk indir_auto_region_1 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor indir_auto_r_1 = indir_auto_region_1.start;
    GibCursor indir_auto_end_r_1 = indir_auto_region_1.end;
    GibChunk indir_auto_region_2 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor indir_auto_r_2 = indir_auto_region_2.start;
    GibCursor indir_auto_end_r_2 = indir_auto_region_2.end;
    GibCursor indir_auto_reg_ptr[3] =
        {indir_auto_r_0, indir_auto_r_1, indir_auto_r_2};
    GibCursor indir_auto_reg_cursor_ptr[3] =
        {indir_auto_end_r_0, indir_auto_end_r_1, indir_auto_end_r_2};
    GibCursor indir_auto_cursor_ptr[3];
    
    memcpy(indir_auto_cursor_ptr, indir_auto_reg_ptr, sizeof(GibCursor [3]));
    
    GibCursor indir_auto_copy_address[3];
    
    memcpy(indir_auto_copy_address, reg_ptr_1499, sizeof(GibCursor [3]));
    
    double indir_auto_add1_start = manual_now_seconds();
    unsigned char indir_auto_tup_packed =
                   add1List_auto_vectorized_indirections(reg_cursor_ptr_1500, indir_auto_reg_cursor_ptr, indir_auto_cursor_ptr, indir_auto_copy_address);
    double indir_auto_add1_seconds =
        manual_now_seconds() - indir_auto_add1_start;
    
    GibCursor indir_auto_sum_address[3];
    
    memcpy(indir_auto_sum_address, indir_auto_reg_ptr, sizeof(GibCursor [3]));
    
    GibInt indir_auto_sum =
        sumList(indir_auto_reg_cursor_ptr, indir_auto_sum_address);
    
    GibChunk indir_vector_region_0 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor indir_vector_r_0 = indir_vector_region_0.start;
    GibCursor indir_vector_end_r_0 = indir_vector_region_0.end;
    GibChunk indir_vector_region_1 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor indir_vector_r_1 = indir_vector_region_1.start;
    GibCursor indir_vector_end_r_1 = indir_vector_region_1.end;
    GibChunk indir_vector_region_2 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor indir_vector_r_2 = indir_vector_region_2.start;
    GibCursor indir_vector_end_r_2 = indir_vector_region_2.end;
    GibCursor indir_vector_reg_ptr[3] =
        {indir_vector_r_0, indir_vector_r_1, indir_vector_r_2};
    GibCursor indir_vector_reg_cursor_ptr[3] =
        {indir_vector_end_r_0, indir_vector_end_r_1, indir_vector_end_r_2};
    GibCursor indir_vector_cursor_ptr[3];
    
    memcpy(indir_vector_cursor_ptr, indir_vector_reg_ptr, sizeof(GibCursor [3]));
    
    GibCursor indir_vector_copy_address[3];
    
    memcpy(indir_vector_copy_address, reg_ptr_1499, sizeof(GibCursor [3]));
    
    double indir_vector_add1_start = manual_now_seconds();
    unsigned char indir_vector_tup_packed =
                   add1List_vectorized_indirections(reg_cursor_ptr_1500, indir_vector_reg_cursor_ptr, indir_vector_cursor_ptr, indir_vector_copy_address);
    double indir_vector_add1_seconds =
        manual_now_seconds() - indir_vector_add1_start;
    
    GibCursor indir_vector_sum_address[3];
    
    memcpy(indir_vector_sum_address, indir_vector_reg_ptr, sizeof(GibCursor [3]));
    
    GibInt indir_vector_sum =
        sumList(indir_vector_reg_cursor_ptr, indir_vector_sum_address);
    
    GibChunk scalar_region_0 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor scalar_r_0 = scalar_region_0.start;
    GibCursor scalar_end_r_0 = scalar_region_0.end;
    GibChunk scalar_region_1 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor scalar_r_1 = scalar_region_1.start;
    GibCursor scalar_end_r_1 = scalar_region_1.end;
    GibChunk scalar_region_2 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor scalar_r_2 = scalar_region_2.start;
    GibCursor scalar_end_r_2 = scalar_region_2.end;
    GibCursor scalar_reg_ptr[3] = {scalar_r_0, scalar_r_1, scalar_r_2};
    GibCursor scalar_reg_cursor_ptr[3] =
        {scalar_end_r_0, scalar_end_r_1, scalar_end_r_2};
    GibCursor scalar_cursor_ptr[3];
    
    memcpy(scalar_cursor_ptr, scalar_reg_ptr, sizeof(GibCursor [3]));
    
    GibCursor scalar_copy_address[3];
    
    memcpy(scalar_copy_address, reg_ptr_1499, sizeof(GibCursor [3]));
    
    double scalar_add1_start = manual_now_seconds();
    unsigned char scalar_tup_packed =
                   add1List_scalar(reg_cursor_ptr_1500, scalar_reg_cursor_ptr, scalar_cursor_ptr, scalar_copy_address);
    double scalar_add1_seconds = manual_now_seconds() - scalar_add1_start;
    
    GibCursor scalar_sum_address[3];
    
    memcpy(scalar_sum_address, scalar_reg_ptr, sizeof(GibCursor [3]));
    
    GibInt scalar_sum =  sumList(scalar_reg_cursor_ptr, scalar_sum_address);
    double loop_scalar_over_recursive =
        loop_scalar_add1_seconds > 0.0
            ? scalar_add1_seconds / loop_scalar_add1_seconds
            : 0.0;
    double vectorized_over_recursive =
        vectorized_add1_seconds > 0.0
            ? scalar_add1_seconds / vectorized_add1_seconds
            : 0.0;
    double vectorized_over_loop_scalar =
        vectorized_add1_seconds > 0.0
            ? loop_scalar_add1_seconds / vectorized_add1_seconds
            : 0.0;
    double indir_loop_scalar_over_recursive =
        indir_loop_scalar_add1_seconds > 0.0
            ? scalar_add1_seconds / indir_loop_scalar_add1_seconds
            : 0.0;
    double indir_auto_over_recursive =
        indir_auto_add1_seconds > 0.0
            ? scalar_add1_seconds / indir_auto_add1_seconds
            : 0.0;
    double indir_auto_over_indir_loop_scalar =
        indir_auto_add1_seconds > 0.0
            ? indir_loop_scalar_add1_seconds / indir_auto_add1_seconds
            : 0.0;
    double indir_vectorized_over_recursive =
        indir_vector_add1_seconds > 0.0
            ? scalar_add1_seconds / indir_vector_add1_seconds
            : 0.0;
    double indir_vectorized_over_indir_loop_scalar =
        indir_vector_add1_seconds > 0.0
            ? indir_loop_scalar_add1_seconds / indir_vector_add1_seconds
            : 0.0;
    
    printf("recursive_sum=%ld\n", scalar_sum);
    printf("loop_scalar_sum=%ld\n", loop_scalar_sum);
    printf("loop_vectorized_sum=%ld\n", vectorized_sum);
    printf("indir_loop_scalar_sum=%ld\n", indir_loop_scalar_sum);
    printf("indir_loop_auto_sum=%ld\n", indir_auto_sum);
    printf("indir_loop_vectorized_sum=%ld\n", indir_vector_sum);
    printf("recursive_add1_seconds=%.9f\n", scalar_add1_seconds);
    printf("loop_scalar_add1_seconds=%.9f\n", loop_scalar_add1_seconds);
    printf("loop_vectorized_add1_seconds=%.9f\n", vectorized_add1_seconds);
    printf("indir_loop_scalar_add1_seconds=%.9f\n",
           indir_loop_scalar_add1_seconds);
    printf("indir_loop_auto_add1_seconds=%.9f\n",
           indir_auto_add1_seconds);
    printf("indir_loop_vectorized_add1_seconds=%.9f\n",
           indir_vector_add1_seconds);
    printf("speedup_loop_scalar_over_recursive=%.3fx\n",
           loop_scalar_over_recursive);
    printf("speedup_loop_vectorized_over_recursive=%.3fx\n",
           vectorized_over_recursive);
    printf("speedup_loop_vectorized_over_loop_scalar=%.3fx\n",
           vectorized_over_loop_scalar);
    printf("speedup_indir_loop_scalar_over_recursive=%.3fx\n",
           indir_loop_scalar_over_recursive);
    printf("speedup_indir_loop_auto_over_recursive=%.3fx\n",
           indir_auto_over_recursive);
    printf("speedup_indir_loop_auto_over_indir_loop_scalar=%.3fx\n",
           indir_auto_over_indir_loop_scalar);
    printf("speedup_indir_loop_vectorized_over_recursive=%.3fx\n",
           indir_vectorized_over_recursive);
    printf("speedup_indir_loop_vectorized_over_indir_loop_scalar=%.3fx\n",
           indir_vectorized_over_indir_loop_scalar);
    printf("sums_match=%s\n",
           vectorized_sum == loop_scalar_sum && vectorized_sum == scalar_sum &&
           vectorized_sum == indir_loop_scalar_sum &&
           vectorized_sum == indir_auto_sum &&
           vectorized_sum == indir_vector_sum
               ? "yes" : "no");
    
    int exit_31 = gib_exit();
    
    return exit_31;
}
