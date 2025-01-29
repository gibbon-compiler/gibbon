#include<stdio.h>
#include<stdlib.h>

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
		CursorTy newIntLocation = (InRegion->IntRegion) + 8;
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
                	CursorTy newIntLocation = (InRegion->IntRegion) + 8;
                	InRegion->tagRegion = newTagLocation;
                	InRegion->IntRegion = newIntLocation;
			printSoAList(InRegion);
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
			IntTy newVal = val + 1; 
			*((TagTy*) newRegion->tagRegion) = '0';
			*((IntTy*) newRegion->IntRegion) = newVal;
			newRegion->tagRegion = newRegion->tagRegion + 1;
			newRegion->IntRegion = newRegion->IntRegion + 8; 
			InRegion->tagRegion = InRegion->tagRegion + 1; 
			InRegion->IntRegion = InRegion->IntRegion + 8;
			return add1(InRegion, newRegion, newRegionStart);
			break;

		case '1':
			; 
			*((TagTy*) newRegion->tagRegion) = '1';
			return newRegionStart; 
			break;
	}
}


int main(){
 
 //for a list of 100 elements 
 // a Cons Tag takes 1 byte 
 // each Int in the cons tag takes 8 bytes 
 // 100 bytes for Cons tag + 1 for Nil tag 
 // 800 bytes for Ints 	
 int listLength = 1000000;
 SoAList *SoARegion = (SoAList*) malloc(sizeof(SoAList));
 SoARegion->tagRegion = (CursorTy) malloc(sizeof(char) * (listLength + 1)); 
 SoARegion->IntRegion = (CursorTy) malloc(sizeof(char) * listLength * 8);

 SoAList copyLocation;
 copyLocation.tagRegion = SoARegion->tagRegion;
 copyLocation.IntRegion = SoARegion->IntRegion;
 SoAList *mkListOut = mkSoAList(SoARegion, listLength, &copyLocation);

 SoAList *SoARegionAdd = (SoAList*) malloc(sizeof(SoAList));
 SoARegionAdd->tagRegion = (CursorTy) malloc(sizeof(char) * (listLength + 1));
 SoARegionAdd->IntRegion = (CursorTy) malloc(sizeof(char) * listLength * 8);

 SoAList copyLocationAdd; 
 copyLocationAdd.tagRegion = SoARegionAdd->tagRegion; 
 copyLocationAdd.IntRegion = SoARegionAdd->IntRegion;
 SoAList *Add1SoAOut = add1(mkListOut, SoARegionAdd, &copyLocationAdd); 

 printSoAList(Add1SoAOut);

 return 0;
}
