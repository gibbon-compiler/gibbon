#include <stdio.h>
#include <stdlib.h>
#include <time.h>

typedef char* CursorTy; 
typedef char TagTy; 
typedef int IntTy; 


CursorTy mkList(CursorTy list, int length, CursorTy listStart){

	if (length <= 0){
		//write a Nil.
		*((TagTy*) list) = '1';
		return listStart;
                		
	}
	else {
		*((TagTy*) list) = '0'; 
		CursorTy writeInt = list + 1; 
		*((IntTy*) writeInt) = length; 
		CursorTy writeNext = list + 1 + sizeof(IntTy);
	        CursorTy listHead = mkList(writeNext, length - 1, listStart);
		return listHead;
	
	}
}

void printList(CursorTy listHead){

	TagTy tag = *((TagTy*) listHead);
	switch (tag){
		case '0' : 
		  printf("(Cons ");
		  IntTy val = *((IntTy*) (listHead + 1));
		  printf("%d ", val);
		  CursorTy listNext = listHead + 1 + sizeof(IntTy);
		  printList(listNext);
		  break;
		case '1' : 
		  printf("(Nil))\n");
		  break;
		default :
		  printf("Error: List was not formed correctly.\n");
		  break;
	}
}


CursorTy add1(CursorTy list, CursorTy newList, CursorTy listStart){

	TagTy tag = *((TagTy*) list);
	switch (tag){
		case '0' :
			;
			IntTy val = *((IntTy*) (list + 1)); 
			IntTy val_new = val + 1; 
			CursorTy listNext = list + 1 + sizeof(IntTy); 
			*((TagTy*) newList) = '0';
			*((IntTy*) (newList + 1)) = val_new;
			CursorTy newListNext = newList + 1 + sizeof(IntTy); 
			return add1(listNext, newListNext, listStart);
			break;
		case '1':
		      ;
		      *((TagTy*) newList) = '1';
		      return listStart;
		      break;
		default:
			printf("Error: List was not formed correctly.\n");
			break;
	}
}

IntTy sum(CursorTy list){

        TagTy tag = *((TagTy*) list);
        switch (tag){
                case '0' :
                        ;
                        IntTy val = *((IntTy*) (list + 1));
                        CursorTy listNext = list + 1 + sizeof(IntTy);
                        IntTy valNext = sum(listNext);
			return val + valNext;
                        break;
                case '1':
                      ;
                      return 0;
                      break;
                default:
                        printf("Error: List was not formed correctly.\n");
                        break;
        }
}

void add1ForInPlace(CursorTy list){

	CursorTy intCursor = list;
	TagTy tag = *((TagTy*) intCursor);

	while(tag != '1'){
                
	        intCursor = intCursor + 1;	
		*((IntTy*) intCursor) = *((IntTy*) intCursor) + 1;
		intCursor = intCursor + sizeof(IntTy); 
		tag = *((TagTy*) intCursor);
	
	}
}


/*
int main(){

  //1 Cons cell = Cons Int == 1 byte for tag + 4 bytes for Int = 5 bytes
  //1 Nil tag == 1 byte 
  //list length = 1000000 => 5 * 1000000 + 1 bytes for allocation. 

  int listLength = 10000000;
  int listBytes = (sizeof(IntTy) + 1) * listLength + 1;   
  CursorTy allocList = (CursorTy) malloc(sizeof(TagTy) * listBytes);
  if (allocList == NULL){
	  printf("Malloc failed to allocate array of size %d\n", listLength);
	  exit(0);
  }


  CursorTy mkListOut = mkList(allocList, listLength, allocList);
  
  CursorTy add1List = (CursorTy) malloc(sizeof(TagTy) * listBytes);
  if (add1List == NULL){
          printf("Malloc failed to allocate array of size %d\n", listLength);
          exit(0);
  }

  clock_t start, end; 
  double cpu_time_used;

  start = clock();
  CursorTy add1Out = add1(mkListOut, add1List, add1List);
  //add1ForInPlace(mkListOut);
  end = clock();

  cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
  
  //printList(add1Out);

  //printList(mkListOut);

  IntTy sumList = sum(add1Out);
  

  //IntTy sumList = sum(mkListOut);

  printf("The sum of the list is %d\n", sumList);
  printf("The time it took for add 1 was %f\n", cpu_time_used);

}
*/


















