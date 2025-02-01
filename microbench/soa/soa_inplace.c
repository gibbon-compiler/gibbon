#include "globals.c"
#include "list_soa.c"

int main(){

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
 add1InPlaceSoA(mkListOut);
 end = clock();

 cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;

 IntTy sumList = sum(mkListOut);

 printf("The sum of the list is %d\n", sumList);
 printf("The time taken by add1 was %f seconds.\n", cpu_time_used);

 return 0;
}

