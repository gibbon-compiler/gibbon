#include <stdio.h>
#include <stdlib.h>
#include <time.h>

typedef char* CursorTy; 
typedef int IntTy; 
typedef char TagTy;

typedef struct {
	CursorTy tagRegion; 
	CursorTy IntRegion;
} SoAList;

SoAList *mkSoAList(SoAList *InRegion, int listLength, SoAList *StartPosition){
	if (listLength <= 0){
		*((TagTy*) InRegion->tagRegion) = '1';
	        return StartPosition;	
	}
	else {
		*((TagTy*) InRegion->tagRegion) = '0';
		*((IntTy*) InRegion->IntRegion) = listLength;
		CursorTy newTagLocation = (InRegion->tagRegion) + 1;
		CursorTy newIntLocation = (InRegion->IntRegion) + sizeof(IntTy);
		InRegion->tagRegion = newTagLocation; 
		InRegion->IntRegion = newIntLocation;
		SoAList *returnedRegion = mkSoAList(InRegion, listLength - 1, StartPosition); 
		return returnedRegion;
	}
}



void printSoAList(SoAList *InRegion){

	TagTy tag = *((TagTy*) InRegion->tagRegion);
	switch (tag){
		case '0':
			printf("(Cons ");
		        IntTy val = *((IntTy*) InRegion->IntRegion); 
		        printf("%d ", val);
		        CursorTy newTagLocation = (InRegion->tagRegion) + 1;
                	CursorTy newIntLocation = (InRegion->IntRegion) + sizeof(IntTy);

			SoAList temp;
                	temp.tagRegion = newTagLocation;
                	temp.IntRegion = newIntLocation;
			printSoAList(&temp);
		        break;	
		case '1':
			printf("(Nil))\n");
			break;
		default: 
			break;
	}
}


SoAList *add1(SoAList *InRegion, SoAList *newRegion, SoAList *newRegionStart){

	TagTy tag = *((TagTy*) InRegion->tagRegion); 
	switch (tag){
		case '0':
			;
			IntTy val = *((IntTy*) InRegion->IntRegion); 
			//IntTy new_val = val + 1;
			*((TagTy*) newRegion->tagRegion) = '0';
			*((IntTy*) newRegion->IntRegion) = val + 1;
			newRegion->tagRegion += 1;
			newRegion->IntRegion += sizeof(IntTy); 
			InRegion->tagRegion += 1; 
			InRegion->IntRegion += sizeof(IntTy);
			return add1(InRegion, newRegion, newRegionStart);
			break;

		case '1':
			; 
			*((TagTy*) newRegion->tagRegion) = '1';
			return newRegionStart; 
			break;
	}
}


IntTy sum(SoAList *InRegion){

        TagTy tag = *((TagTy*) InRegion->tagRegion);
        switch (tag){
                case '0':
                        ;
                        IntTy val = *((IntTy*) InRegion->IntRegion);
                        InRegion->tagRegion = InRegion->tagRegion + 1;
                        InRegion->IntRegion = InRegion->IntRegion + sizeof(IntTy);
                        
			IntTy valNext = sum(InRegion);
			return val + valNext;
                        break;

                case '1':
                        ;
                        return 0;
                        break;
        }
}

void add1InPlaceSoA(SoAList *InRegion){

	TagTy tag = *((TagTy*) InRegion->tagRegion);
        CursorTy intCursor = InRegion->IntRegion;
        CursorTy tagCursor = InRegion->tagRegion;	

	while (tag != '1'){
	    
	    *((IntTy*) intCursor) = *((IntTy*) intCursor) + 1;
	    intCursor = intCursor + sizeof(IntTy);
	    tagCursor = tagCursor + 1;
            tag = *((TagTy*) tagCursor);
	}
}

void add1InPlaceSoAOpt(SoAList *InRegion, int intBufferSize){

        CursorTy intCursor = InRegion->IntRegion;

	for (int i=0; i < intBufferSize; i++){
		*((IntTy*) intCursor) = *((IntTy*) intCursor) + 1;
		intCursor = intCursor + sizeof(IntTy);
	}
}


/*
int main(){
 
 //for a list of 100 elements 
 // a Cons Tag takes 1 byte 
 // each Int in the cons tag takes 4 bytes 
 // 100 bytes for Cons tag + 1 for Nil tag 
 // 400 bytes for Ints 	
 int listLength = 10000000;
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

 //printSoAList(mkListOut);

 
 start = clock();
 SoAList *Add1SoAOut = add1(mkListOut, SoARegionAdd, &copyLocationAdd); 
 //add1InPlaceSoA(mkListOut);
 //add1InPlaceSoAOpt(mkListOut, listLength);
 end = clock();

 cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;

 //printSoAList(Add1SoAOut);
 
 //printSoAList(mkListOut);
 

 IntTy sumList = sum(Add1SoAOut);
 
 //IntTy sumList = sum(mkListOut);
 
 

 printf("The sum of the list is %d\n", sumList);
 printf("The time taken by add1 was %f seconds.\n", cpu_time_used);

 return 0;
}
*/
