#include "globals.c"
#include "list_aos.c"

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

  //1 Cons cell = Cons Int == 1 byte for tag + 4 bytes for Int = 5 bytes
  //1 Nil tag == 1 byte
  //list length = 1000000 => 5 * 1000000 + 1 bytes for allocation.

  //int listLength = 10000000;
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
  
  #ifdef PAPI
  if (PAPI_start(EventSet) != PAPI_OK) {
    fprintf(stderr, "PAPI start error!\n");
    exit(1);
  }
  #endif 


  add1ForInPlace(mkListOut);
  
  #ifdef PAPI
  if (PAPI_stop(EventSet, values) != PAPI_OK) {
    fprintf(stderr, "PAPI stop error!\n");
    exit(1);
  }
  #endif

  end = clock();

  cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;

  //printList(mkListOut);

  IntTy sumList = sum(mkListOut);

  printf("The sum of the list is %d\n", sumList);
  printf("The time taken by add1 was %f seconds.\n", cpu_time_used);
  
  #ifdef PAPI
  printf("Total Instructions: %lld\n", values[0]);
  printf("L2 data cache misses: %lld\n", values[1]);
  #endif
}
