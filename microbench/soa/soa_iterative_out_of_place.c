#include "globals.c"
#include "list_soa.c"

int main(){

    #ifdef PAPI
    int retval, EventSet = PAPI_NULL;
    long long values[2];

    retval = PAPI_library_init(PAPI_VER_CURRENT);
    if (retval != PAPI_VER_CURRENT) {
        fprintf(stderr, "PAPI library init error!\n");
        exit(1);
    }

    if (PAPI_create_eventset(&EventSet) != PAPI_OK)
        fprintf(stderr, "Error creating event set\n");

    if (PAPI_add_event(EventSet, PAPI_TOT_INS) != PAPI_OK)
        fprintf(stderr, "Error adding total instructions event\n");

    if (PAPI_add_event(EventSet, PAPI_L2_DCM) != PAPI_OK)
        fprintf(stderr, "Error adding load instructions event\n");
    #endif


 //for a list of 100 elements
 // a Cons Tag takes 1 byte
 // each Int in the cons tag takes 4 bytes
 // 100 bytes for Cons tag + 1 for Nil tag
 // 400 bytes for Ints
 //int listLength = 10000000;
 SoAList *SoARegion = (SoAList*) malloc(sizeof(SoAList));
 SoARegion->tagRegion = (CursorTy) malloc(sizeof(TagTy) * (listLength + 1));
 SoARegion->IntRegion = (CursorTy) malloc(sizeof(IntTy) * listLength * sizeof(IntTy));

 SoAList copyLocation;
 copyLocation.tagRegion = SoARegion->tagRegion;
 copyLocation.IntRegion = SoARegion->IntRegion;
 SoAList *mkListOut = mkSoAList(SoARegion, listLength, &copyLocation);

 SoAList *SoARegionAdd = (SoAList*) malloc(sizeof(SoAList));
 SoARegionAdd->tagRegion = (CursorTy) malloc(sizeof(TagTy) * (listLength + 1));
 SoARegionAdd->IntRegion = (CursorTy) malloc(sizeof(IntTy) * listLength * sizeof(IntTy));

 SoAList copyLocationAdd;
 copyLocationAdd.tagRegion = SoARegionAdd->tagRegion;
 copyLocationAdd.IntRegion = SoARegionAdd->IntRegion;

 clock_t start, end;
 double cpu_time_used;

 start = clock();

  #ifdef PAPI
  if (PAPI_start(EventSet) != PAPI_OK) {
    fprintf(stderr, "PAPI start error!\n");
    exit(1);
  }
  #endif


 add1ForOutOfPlaceSoA(mkListOut, SoARegionAdd);

  #ifdef PAPI
  if (PAPI_stop(EventSet, values) != PAPI_OK) {
    fprintf(stderr, "PAPI stop error!\n");
    exit(1);
  }
  #endif

 end = clock();

 cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;

 IntTy sumList = sum(&copyLocationAdd);

 printf("The sum of the list is %d\n", sumList);
 printf("The time taken by add1 was %f seconds.\n", cpu_time_used);

  #ifdef PAPI
  printf("Total Instructions: %lld\n", values[0]);
  printf("L2 data cache misses: %lld\n", values[1]);
  #endif


 return 0;
}

