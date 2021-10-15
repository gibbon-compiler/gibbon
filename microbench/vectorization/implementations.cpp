#include <cstdlib>
#include <emmintrin.h>
#include <smmintrin.h>
#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <string.h>
#include <utlist.h>
#include <time.h>
#include <limits.h>
#include <iostream>
#include <vector>
#include <mutex>
#include <bits/types/struct_timespec.h>
#include <cilk/cilk.h>
#include <math.h>
#include <immintrin.h>
#include <mmintrin.h>

typedef long long IntTy;
typedef char* CursorTy;
typedef char TagTyPacked;

std::mutex mylock;

#define NODE_SIZE 8
#define LANE_LEN  4
long long CONSTANT = 100;

#define BLOCK_SIZE 100;

typedef struct CursorIntProd_struct {
    CursorTy field0;
    IntTy    field1;
} CursorIntProd;

bool isA(CursorTy node);
bool isB(CursorTy node);
IntTy fib_recursive(IntTy n);
CursorTy PrintTree(CursorTy cur);
CursorTy _cilk(CursorTy packedData);
CursorTy dfs_recurse(CursorTy packedData);
IntTy doMath(IntTy number, IntTy constantVal);
CursorIntProd createBalancedTree(CursorTy out, IntTy n);
CursorIntProd createFibonacciTree(CursorTy out, IntTy n);
void bfs_parallel(std::vector<CursorTy> Blocks);
void bfs_vectorized(std::vector<CursorTy> Blocks);
double difftimespecs(struct timespec* t0, struct timespec* t1);

IntTy doMath(IntTy number, IntTy constantVal){
    
    //multiply
    number *= constantVal;
    //subtract
    number -= constantVal;
    //addition
    number += constantVal;
    //square
    number = number*number;
    //left shift 
    number = number << 3;
    //right shift
    number = number >> 1;
    //cast to double
    double inter = (double) number;
    //take square root;
    inter = sqrt(inter);
    //cast to int
    number = (int) inter;
    //bit wise and
    number = number & constantVal;
    //bitwise not and then and
    number = (~number) & constantVal;
    //bitwise OR
    number = number | constantVal;
    //bit wise XoR
    number = number ^ constantVal;

    //find max
    if(number < constantVal){
        number = constantVal;
    }

    //find min
    if(number > constantVal){
        number = constantVal;
    }

    return number;

}

double difftimespecs(struct timespec* t0, struct timespec* t1)
{
    return (double)((t1->tv_sec * 1000000000.0) - (t0->tv_sec * 1000000000.0))
      + ((double)(t1->tv_nsec - t0->tv_nsec));
}

CursorIntProd createFibonacciTree(CursorTy out, IntTy n){
    
    CursorIntProd tmp;

    //create a leaf Node
    if (n <= 0) {

        *out  ='A';             
        out += NODE_SIZE;          
        *(IntTy *) out = 100;  
        out += NODE_SIZE;             
        return (CursorIntProd) {out, 2*NODE_SIZE };
    }
    //else create a non-leaf Node
    else if (n > 0) {
        
        *out = 'B';
        CursorTy out0 = out + NODE_SIZE;  
        *(IntTy *) out0 = n;     
        out0 += NODE_SIZE;

        //write an indirection pointer to the right subtree
        *out0 = 'C';
        out0 += NODE_SIZE;
        CursorTy indirectionPointer = out0;
        out0 += NODE_SIZE;

        //rec 1
        tmp = createFibonacciTree(out0, (n - 1));
        CursorTy out1 = tmp.field0;
        IntTy size1   = tmp.field1;

        //rec 2
        tmp = createFibonacciTree(out1, (n - 2));
        CursorTy out2 = tmp.field0;
        IntTy size2   = tmp.field1;
        
        //write address to the right subtree 
        //(out 1) points to the right subtree
        *(CursorTy*) indirectionPointer = out1; 

        return (CursorIntProd) {out2, size1 + size2 + 2*NODE_SIZE };  

    }
}

CursorIntProd createBalancedTree(CursorTy out, IntTy n){

    CursorIntProd tmp;    
    
    //create a leaf node
    if (n <= 0) {

        *out  ='A';             
        out += NODE_SIZE;          
        *(IntTy *) out = 100;  
        out += NODE_SIZE;             
        return (CursorIntProd) {out, 2*NODE_SIZE };
    }
    //create a non-leaf node
    else if (n > 0) {
        
        *out = 'B';
        CursorTy out0 = out + NODE_SIZE;  
        *(IntTy *) out0 = n;     
        out0 += NODE_SIZE;

        //write an indirection pointer
        *out0 = 'C';
        out0 += NODE_SIZE;
        CursorTy indirectionPointer = out0;
        out0 += NODE_SIZE;

        //rec 1
        tmp = createBalancedTree(out0, (n - 1));
        CursorTy out1 = tmp.field0;
        IntTy size1   = tmp.field1;

        //rec 2
        tmp = createBalancedTree(out1, (n - 1));
        CursorTy out2 = tmp.field0;
        IntTy size2   = tmp.field1;
        
        //write address to the right subtree
        *(CursorTy*) indirectionPointer = out1;

        return (CursorIntProd) {out2, size1 + size2 + 2*NODE_SIZE };

    }
}

// a recursive implementation of the Fibonacci series
IntTy fib_recursive(IntTy n)
{
    if (n <= 1)
        return n;
    return fib_recursive(n-1) + fib_recursive(n-2);
}

//recurive depth first function
CursorTy dfs_recurse(CursorTy packedData){

    CursorTy tmp;
    CursorTy dataCursor = packedData + NODE_SIZE;
    
    //encountered a leaf node
    if( isA(packedData) ){

        IntTy data = *((IntTy*) dataCursor);
        IntTy modifiedData = doMath(data, CONSTANT);
        *((IntTy*) dataCursor) = modifiedData;

        CursorTy newCursor = dataCursor + NODE_SIZE;

        return newCursor;
    }
    //non leaf node
    else if ( isB(packedData) ){
        
        //child 1
        CursorTy child1 = dataCursor + 3*NODE_SIZE;
        tmp = dfs_recurse(child1);
        //child 2
        tmp = dfs_recurse(tmp);

        return tmp;
    }

}

//parallel implementation using cilk
CursorTy _cilk(CursorTy packedData){

    CursorTy tmp;
    CursorTy dataCursor = packedData + NODE_SIZE;
    
    //encountered a leaf node
    if( isA(packedData) ){
        
        IntTy data = *((IntTy*) dataCursor);
        IntTy modifiedData = doMath(data, CONSTANT);
        *((IntTy*) dataCursor) = modifiedData;

        CursorTy newCursor = dataCursor + NODE_SIZE;
        return newCursor;
    }
    //non leaf node
    else if ( isB(packedData) ){

        CursorTy child1 = dataCursor + 3*NODE_SIZE;
        CursorTy child2 =  *((CursorTy*) (dataCursor + 2*NODE_SIZE));

        tmp = cilk_spawn _cilk(child1);
        tmp = cilk_spawn _cilk(child2);
        cilk_sync;

        return tmp;
    }

}

void bfs_parallel(std::vector<CursorTy> Blocks){

    std::vector<CursorTy> newBlocks;

    //std::cout << Blocks.size() << std::endl;

    #pragma omp parallel for
    for(int i=0; i<Blocks.size(); i++){
    
        //encountered a leaf node
        if( isA(Blocks[i]) ){
            
            IntTy data = *((IntTy*) (Blocks[i] + NODE_SIZE) );
            IntTy modifiedData = doMath(data, CONSTANT);
            *((IntTy*) (Blocks[i] + NODE_SIZE) ) = modifiedData;

        }
        //non leaf node
        else if ( isB(Blocks[i]) ){
        
            //child 2 stored in the indirection pointer
            CursorTy* child2 = (CursorTy*) (Blocks[i] + 3*NODE_SIZE);        
            //child 1
            CursorTy child1 = Blocks[i] + 4*NODE_SIZE;
            
            mylock.lock();
            newBlocks.push_back(child1);
            newBlocks.push_back(*child2);
            mylock.unlock();
        }
    }

    if(!newBlocks.empty()){
        bfs_parallel(newBlocks);
    }

}

bool isA(CursorTy node){

    TagTyPacked start = *node;
    if(start == 'A'){return true;}
    else{return false;}
}

bool isB(CursorTy node){

    TagTyPacked start = *node;
    if(start == 'B'){return true;}
    else{return false;}
}

void bfs_vectorized(std::vector<CursorTy> Blocks){

    std::vector<CursorTy> newBlocks;
    std::vector<IntTy*> leafNodes;
    std::vector<CursorTy> nonLeafNodes;
    std::vector<bool> booleanFlags(Blocks.size());
    
    //#pragma omp simd
    for (int i=0; i<Blocks.size(); i++){
        booleanFlags[i] = isA(Blocks[i]);
    }

    for(int i=0; i<Blocks.size(); i++){
        if(booleanFlags[i]){leafNodes.push_back( (IntTy*)(Blocks[i] + NODE_SIZE) );}
        else{nonLeafNodes.push_back(Blocks[i]);}
    }

    int factorOfLane = leafNodes.size() - (leafNodes.size() % LANE_LEN);

    //#pragma omp parallel for
    for(int i=0; i<factorOfLane; i=i+LANE_LEN){

        int arr[LANE_LEN];
        arr[0] = *(leafNodes[i]);
        arr[1] = *(leafNodes[i+1]);
        arr[2] = *(leafNodes[i+2]);
        arr[3] = *(leafNodes[i+3]);

        __m128i leafValuesVec = _mm_load_si128((__m128i*) &arr[0]);
        __m128i constantVec   = _mm_set_epi32 (100, 100, 100, 100);

        //multiply 
        __m128i multiply = _mm_mullo_epi32 (leafValuesVec, constantVec);
        //subtract
        __m128i subtract = _mm_sub_epi32 (multiply, constantVec);
        //add
        __m128i addition = _mm_add_epi32 (subtract, constantVec);
        //square
        __m128i square = _mm_mullo_epi32 (addition, addition);
        //Shift packed 32-bit integers in a left by imm8 while shifting in zeros, and store the results in dst.
        __m128i leftShift = _mm_slli_epi32 (square, 3);
        //Shift packed 32-bit integers in a right by imm8 while shifting in sign bits, and store the results in dst.
        __m128i rightShift = _mm_srai_epi32 (leftShift, 1);
        //Cast vector of type __m128i to type __m128d. This intrinsic is only used for compilation and does not generate any instructions, thus it has zero latency.
        __m128d doubleCasted = _mm_castsi128_pd (rightShift);
        //Compute the square root of packed double-precision (64-bit) floating-point elements in a, and store the results in dst.
        __m128d squareRoot = _mm_sqrt_pd (doubleCasted);

        //cast back to int
        //Cast vector of type __m128d to type __m128i. This intrinsic is only used for compilation and does not generate any instructions, thus it has zero latency.
        __m128i castToInt = _mm_castpd_si128 (squareRoot);
        //compute bitwise AND of 128 bits in a and b
        __m128i bitwiseAND = _mm_and_si128 (castToInt, constantVec);
        //compute bitwise NOT of 128 bits in a, then AND with b.
        __m128i bitwiseNOTand = _mm_andnot_si128 (bitwiseAND, constantVec);
        //Compute the bitwise OR of 128 bits (representing integer data) in a and b, and store the result in dst. 
        __m128i bitwiseOR = _mm_or_si128 (bitwiseNOTand, constantVec);
        //Compute the bitwise XOR of 128 bits (representing integer data) in a and b, and store the result in dst.
        __m128i bitwiseXOR = _mm_xor_si128 (bitwiseOR, constantVec);
        //Compare packed signed 32-bit integers in a and b, and store packed maximum values in dst.
        __m128i findMax = _mm_max_epi32 (bitwiseXOR, constantVec);
        //Compare packed signed 32-bit integers in a and b, and store packed minimum values in dst.
        __m128i findMin = _mm_min_epi32 (findMax, constantVec);
        

        int *res = (int*) &findMin;
           
        *(leafNodes[i])     =  res[0];
        *(leafNodes[i+1])   =  res[1];
        *(leafNodes[i+2])   =  res[2];
        *(leafNodes[i+3])   =  res[3]; 

    }

    //sequential computation of the remaning part of the array that won't fit in the lane.
    //#pragma omp parallel for 
    for(int i=factorOfLane; i< leafNodes.size(); i++){

        IntTy data = *((IntTy*) (leafNodes[i] + NODE_SIZE) );
        IntTy modifiedData = doMath(data, CONSTANT);
        *((IntTy*) (leafNodes[i] + NODE_SIZE) ) = modifiedData;      

    }

    for (int i=0; i<nonLeafNodes.size(); i++){
        newBlocks.push_back( *( (CursorTy*) (nonLeafNodes[i] + 3*NODE_SIZE) ) );
        newBlocks.push_back( ( (CursorTy) (nonLeafNodes[i] + 4*NODE_SIZE) ) );
    }

    if(!newBlocks.empty()){
        bfs_vectorized(newBlocks);
    }

}

CursorTy PrintTree(CursorTy cur) {
    if (*cur == 'A') {
        printf("(A ");
        cur += NODE_SIZE;
        IntTy val = *(IntTy *) cur;
        cur += NODE_SIZE;
        printf("%lld",val);
        printf(") ");
        return cur;
    } else if (*cur  == 'B') {
        printf("(B ");
        cur += NODE_SIZE;     //int value
        IntTy val = *(IntTy *) cur;
        cur += 3*NODE_SIZE;
        printf("%lld ", val);
        cur = PrintTree(cur);
        cur = PrintTree(cur);
        printf(") ");
        return cur;
    }
}

int main (int argc, char** argv){

    if (argc < 2){
        printf("USAGE: executable SIZE\n");
        exit(1);
    }
    
    double time = 0;
    struct timespec beginTime;
    struct timespec endTime;

    IntTy tree_depth = std::atoi(argv[1]); //depth of the tree
   
    //allocate a huge data array for now
    CursorTy dataArray = (CursorTy) malloc(UINT_MAX);

    createBalancedTree(dataArray, tree_depth);

    clock_gettime(CLOCK_MONOTONIC_RAW, &beginTime);
    dfs_recurse(dataArray);
    clock_gettime(CLOCK_MONOTONIC_RAW, &endTime);
    time = difftimespecs(&beginTime, &endTime);  
    
    

    std::vector<CursorTy> startBlock;
    startBlock.push_back(dataArray);

    double time1 = 0;
    struct timespec beginTime1;
    struct timespec endTime1;

    clock_gettime(CLOCK_MONOTONIC_RAW, &beginTime1);
    bfs_parallel(startBlock);
    clock_gettime(CLOCK_MONOTONIC_RAW, &endTime1);
    time1 = difftimespecs(&beginTime1, &endTime1);  

   

    double time2 = 0;
    struct timespec beginTime2;
    struct timespec endTime2;

    clock_gettime(CLOCK_MONOTONIC_RAW, &beginTime2);
    bfs_vectorized(startBlock);
    clock_gettime(CLOCK_MONOTONIC_RAW, &endTime2);
    time2 = difftimespecs(&beginTime2, &endTime2); 

    double time3 = 0;
    struct timespec beginTime3;
    struct timespec endTime3;

    clock_gettime(CLOCK_MONOTONIC_RAW, &beginTime3);
    _cilk(dataArray);
    clock_gettime(CLOCK_MONOTONIC_RAW, &endTime3);
    time3 = difftimespecs(&beginTime3, &endTime3); 

    

    printf("Printing the original tree that was created\n");
    //PrintTree(dataArray);
    printf("\n");

    printf("\n");
    printf("========================================================================================\n");
    printf("Time taken for depth first implementation was (%lf) nanoseconds\n", time);
    printf("========================================================================================\n"); 
    printf("\n");

    printf("\n");
    printf("========================================================================================\n");
    printf("Time taken for breath first parallel implementation was (%lf) nanoseconds\n", time1);
    printf("========================================================================================\n"); 
    printf("\n");

    printf("\n");
    printf("========================================================================================\n");
    printf("Time taken for Cilk implementation was (%lf) nanoseconds\n", time3);
    printf("========================================================================================\n"); 
    printf("\n");

    printf("\n");
    printf("========================================================================================\n");
    printf("Time taken for breath first vectorized implementation was (%lf) nanoseconds\n", time2);
    printf("========================================================================================\n"); 
    printf("\n");

}




