#include "globals.c"
#include "list_soa.c"
#include <immintrin.h>
#include <stddef.h>
#include <avxintrin.h>

void add1InPlaceSoAOptManuallyVectorized(SoAList *InRegion, int intBufferSize){

        CursorTy intCursor = InRegion->IntRegion;
	size_t i;
	int sizeofIntTy = sizeof(IntTy);
	int stride8Int = sizeofIntTy * 8;
        
        __m256i one = _mm256_set1_epi32(1);
        for (i = 0; i <= intBufferSize - 8; i += 8){
		
		__m256i data = _mm256_lddqu_si256((__m256i*)intCursor);
		data = _mm256_add_epi32(data, one);
		_mm256_storeu_si256((__m256i*)intCursor, data);
		intCursor = intCursor + stride8Int;
	}

	for (; i < intBufferSize; i++){
		*((IntTy*) intCursor) += 1;
		intCursor = intCursor + sizeofIntTy;
	}


}



int main(){
  
  //printf("Size of int: %zu bytes\n", sizeof(IntTy));	
  //printf("SSE: %d\n", __builtin_cpu_supports("sse"));
  //printf("SSE2: %d\n", __builtin_cpu_supports("sse2"));
  //printf("AVX: %d\n", __builtin_cpu_supports("avx"));
  //printf("AVX2: %d\n", __builtin_cpu_supports("avx2"));
  //printf("AVX512: %d\n", __builtin_cpu_supports("avx512f"));
 
 //for a list of 100 elements 
 // a Cons Tag takes 1 byte 
 // each Int in the cons tag takes 4 bytes 
 // 100 bytes for Cons tag + 1 for Nil tag 
 // 400 bytes for Ints 	
 //int listLength = 10000000;
 SoAList *SoARegion = (SoAList*) malloc(sizeof(SoAList));
 SoARegion->tagRegion = (CursorTy) malloc(sizeof(TagTy) * (listLength + 1)); 
 SoARegion->IntRegion = (CursorTy) malloc(sizeof(IntTy) * listLength);


 SoAList copyLocation;
 copyLocation.tagRegion = SoARegion->tagRegion;
 copyLocation.IntRegion = SoARegion->IntRegion;
 SoAList *mkListOut = mkSoAList(SoARegion, listLength, &copyLocation);

 SoAList *SoARegionAdd = (SoAList*) malloc(sizeof(SoAList));
 SoARegionAdd->tagRegion = (CursorTy) malloc(sizeof(TagTy) * (listLength + 1));
 SoARegionAdd->IntRegion = (CursorTy) malloc(sizeof(IntTy) * listLength);

 SoAList copyLocationAdd; 
 copyLocationAdd.tagRegion = SoARegionAdd->tagRegion; 
 copyLocationAdd.IntRegion = SoARegionAdd->IntRegion;

 clock_t start, end; 
 double cpu_time_used;
 
 start = clock();
 add1InPlaceSoAOptManuallyVectorized(mkListOut, listLength);
 end = clock();

 cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
 
 IntTy sumList = sum(mkListOut);

 printf("The sum of the list is %d\n", sumList);
 printf("The time taken by add1 was %f seconds.\n", cpu_time_used);

 return 0;
}
