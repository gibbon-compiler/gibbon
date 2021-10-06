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

typedef long long IntTy;
typedef char* CursorTy;
typedef char TagTyPacked;

std::mutex mylock;

#define NODE_SIZE 8

typedef struct CursorIntProd_struct {
    CursorTy field0;
    IntTy    field1;
} CursorIntProd;

IntTy fib(IntTy n);
bool isA(CursorTy node);
bool isB(CursorTy node);
CursorTy printTreeBalanced(CursorTy cur);
CursorTy Fibb_depth_recurse(CursorTy packedData);
CursorTy Fibb_Cilk(CursorTy packedData);
void Fibb_breath_parallel(std::vector<CursorTy> Blocks);
CursorIntProd createBalancedTree(CursorTy out, IntTy n);
void Fibb_breath_vectorized(std::vector<CursorTy> Blocks);
double difftimespecs(struct timespec* t0, struct timespec* t1);

double difftimespecs(struct timespec* t0, struct timespec* t1)
{
    return (double)((t1->tv_sec * 1000000000.0) - (t0->tv_sec * 1000000000.0))
      + ((double)(t1->tv_nsec - t0->tv_nsec));
}

CursorIntProd createBalancedTree(CursorTy out, IntTy n){

    CursorIntProd tmp;    
    
    if (n <= 0) {

        *out  ='A';             
        out += NODE_SIZE;          
        *(IntTy *) out = 35;  
        out += NODE_SIZE;             
        return (CursorIntProd) {out, 2*NODE_SIZE };
    }
    else if (n > 0) {
        
        *out = 'B';
        //n 
        CursorTy out0 = out + NODE_SIZE;  
        *(IntTy *) out0 = n;     
        out0 += NODE_SIZE;

        //write an indirection pointer
        *out0 = 'C';
        out0 += NODE_SIZE;

        CursorTy indirectionPointer = out0;
        
        //increment address to left and right subtrees
        out0 += NODE_SIZE;

        //rec 1
        tmp = createBalancedTree(out0, (n - 1));
        CursorTy out1 = tmp.field0;
        IntTy size1   = tmp.field1;

        //rec 2
        tmp = createBalancedTree(out1, (n - 2));
        CursorTy out2 = tmp.field0;
        IntTy size2   = tmp.field1;
        
        //write address to the right subtree
        *(CursorTy*) indirectionPointer = out1;

        return (CursorIntProd) {out2, size1 + size2 + 2*NODE_SIZE };  //16 bytes of data was written for this particular node.

    }
}

IntTy fib(IntTy n)
{
    if (n <= 1)
        return n;
    return fib(n-1) + fib(n-2);
}

CursorTy Fibb_depth_recurse(CursorTy packedData){

    CursorTy tmp;
    CursorTy dataCursor = packedData + NODE_SIZE;
    
    //encountered a leaf node
    if( isA(packedData) ){        
        fib( (*(IntTy*) dataCursor) );
        CursorTy newCursor = dataCursor + NODE_SIZE;
        return newCursor;
    }
    //non leaf node
    else if ( isB(packedData) ){

        //child 1
        CursorTy child1 = dataCursor + 3*NODE_SIZE;
        tmp = Fibb_depth_recurse(child1);

        //child 2
        tmp = Fibb_depth_recurse(tmp);

        return tmp;
    }

}

CursorTy Fibb_Cilk(CursorTy packedData){

    CursorTy tmp;
    CursorTy dataCursor = packedData + NODE_SIZE;
    
    //encountered a leaf node
    if( isA(packedData) ){        
        fib( (*(IntTy*) dataCursor) );
        CursorTy newCursor = dataCursor + NODE_SIZE;
        return newCursor;
    }
    //non leaf node
    else if ( isB(packedData) ){

        CursorTy child1 = dataCursor + 3*NODE_SIZE;
        CursorTy child2 =  *((CursorTy*) (dataCursor + 2*NODE_SIZE));

        tmp = cilk_spawn Fibb_Cilk(child1);
        tmp = cilk_spawn Fibb_Cilk(child2);
        cilk_sync;

        return tmp;
    }

}

void Fibb_breath_parallel(std::vector<CursorTy> Blocks){

    std::vector<CursorTy> newBlocks;

    //std::cout << Blocks.size() << std::endl;

    #pragma omp parallel for
    for(int i=0; i<Blocks.size(); i++){
    
        //encountered a leaf node
        if( isA(Blocks[i]) ){  
            //add1 to the leaf nodes
            fib( ( *(IntTy*) (Blocks[i] + NODE_SIZE) ) );
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
        Fibb_breath_parallel(newBlocks);
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

void Fibb_breath_vectorized(std::vector<CursorTy> Blocks){

    std::vector<CursorTy> newBlocks;
    std::vector<IntTy*> leafNodes;
    std::vector<CursorTy> nonLeafNodes;
    std::vector<bool> booleanFlags(Blocks.size());
    
    #pragma omp simd
    for (int i=0; i<Blocks.size(); i++){
        booleanFlags[i] = isA(Blocks[i]);
    }

    for(int i=0; i<Blocks.size(); i++){
        if(booleanFlags[i]){leafNodes.push_back( (IntTy*)(Blocks[i] + NODE_SIZE) );}
        else{nonLeafNodes.push_back(Blocks[i]);}
    }
    
    #pragma omp parallel for
    //#pragma omp simd
    for(int i=0; i<leafNodes.size(); i++){
        fib( *(leafNodes[i]) );
    }

    for (int i=0; i<nonLeafNodes.size(); i++){
        newBlocks.push_back( *( (CursorTy*) (nonLeafNodes[i] + 3*NODE_SIZE) ) );
        newBlocks.push_back( ( (CursorTy) (nonLeafNodes[i] + 4*NODE_SIZE) ) );
    }

    if(!newBlocks.empty()){
        Fibb_breath_vectorized(newBlocks);
    }

}

CursorTy printTreeBalanced(CursorTy cur) {
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
        cur = printTreeBalanced(cur);
        cur = printTreeBalanced(cur);
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

    IntTy tree_depth = atoll(argv[1]); //depth of the tree

    //tree structure
    CursorIntProd myTree;
   
    //allocate a huge data array for now
    CursorTy dataArray = (CursorTy) malloc(UINT_MAX);

    myTree = createBalancedTree(dataArray, tree_depth);

    clock_gettime(CLOCK_MONOTONIC_RAW, &beginTime);
    Fibb_depth_recurse(dataArray);
    clock_gettime(CLOCK_MONOTONIC_RAW, &endTime);
    time = difftimespecs(&beginTime, &endTime);  
    
    printf("\n");
    printf("========================================================================================\n");
    printf("Time taken for depth first Fibonacci implementation was (%lf) nanoseconds\n", time);
    printf("========================================================================================\n"); 
    printf("\n");

    std::vector<CursorTy> startBlock;
    startBlock.push_back(dataArray);

    double time1 = 0;
    struct timespec beginTime1;
    struct timespec endTime1;

    clock_gettime(CLOCK_MONOTONIC_RAW, &beginTime1);
    Fibb_breath_parallel(startBlock);
    clock_gettime(CLOCK_MONOTONIC_RAW, &endTime1);
    time1 = difftimespecs(&beginTime1, &endTime1);  

    printf("\n");
    printf("========================================================================================\n");
    printf("Time taken for breath first parallel Fibonacci implementation was (%lf) nanoseconds\n", time1);
    printf("========================================================================================\n"); 
    printf("\n");

    double time2 = 0;
    struct timespec beginTime2;
    struct timespec endTime2;

    clock_gettime(CLOCK_MONOTONIC_RAW, &beginTime2);
    Fibb_breath_vectorized(startBlock);
    clock_gettime(CLOCK_MONOTONIC_RAW, &endTime2);
    time2 = difftimespecs(&beginTime2, &endTime2); 

    printf("\n");
    printf("========================================================================================\n");
    printf("Time taken for breath first vectorized Fibonacci implementation was (%lf) nanoseconds\n", time2);
    printf("========================================================================================\n"); 
    printf("\n");

    double time3 = 0;
    struct timespec beginTime3;
    struct timespec endTime3;

    clock_gettime(CLOCK_MONOTONIC_RAW, &beginTime3);
    Fibb_Cilk(dataArray);
    clock_gettime(CLOCK_MONOTONIC_RAW, &endTime3);
    time3 = difftimespecs(&beginTime3, &endTime3); 

    printf("\n");
    printf("========================================================================================\n");
    printf("Time taken for Cilk Fibonacci implementation was (%lf) nanoseconds\n", time3);
    printf("========================================================================================\n"); 
    printf("\n");

    printf("Printing the original tree that was created\n");
    printTreeBalanced(dataArray);
    printf("\n");

}




