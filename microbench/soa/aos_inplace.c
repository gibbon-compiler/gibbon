#include "list_aos.c"

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
  add1ForInPlace(mkListOut);
  end = clock();

  cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;

  //printList(mkListOut);

  IntTy sumList = sum(mkListOut);

  printf("The sum of the list is %d\n", sumList);
  printf("The time taken by add1 was %f seconds.\n", cpu_time_used);

}
