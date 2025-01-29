#include <stdio.h>
#include <stdlib.h>

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
		CursorTy writeNext = list + 9;
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
		  CursorTy listNext = listHead + 9;
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
			CursorTy listNext = list + 9; 
			*((TagTy*) newList) = '0';
			*((IntTy*) (newList + 1)) = val_new;
			CursorTy newListNext = newList + 9; 
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



int main(){

  //1 Cons cell = Cons Int == 1 byte for tag + 8 types for Int = 9 bytes
  //1 Nil tag == 1 byte 
  //list length = 1000000 => 9 * 1000000 + 1 bytes for allocation. 

  int listLength = 1000000;
  int listBytes = 9 * listLength + 1;   
  CursorTy allocList = (CursorTy) malloc(sizeof(char) * listBytes);
  if (allocList == NULL){
	  printf("Malloc failed to allocate array of size %d\n", listLength);
	  exit(0);
  }


  CursorTy mkListOut = mkList(allocList, listLength, allocList);
  
  CursorTy add1List = (CursorTy) malloc(sizeof(char) * listBytes);
  if (add1List == NULL){
          printf("Malloc failed to allocate array of size %d\n", listLength);
          exit(0);
  }

  CursorTy add1Out = add1(mkListOut, add1List, add1List);
 
  
  printList(add1Out);

}


















