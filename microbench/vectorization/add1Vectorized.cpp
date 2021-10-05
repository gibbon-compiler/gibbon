#include <bits/types/struct_timespec.h>
#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <string.h>
#include <utlist.h>
#include <uthash.h>
#include <time.h>
#include <limits.h>
#include <iostream>
#include <vector>

typedef long long IntTy;
typedef char* CursorTy;
typedef char TagTyPacked;

#define NODE_SIZE 8

typedef struct CursorIntProd_struct {
    CursorTy field0;
    IntTy    field1;
} CursorIntProd;

class Thread {

    public:
        CursorTy address;
        IntTy sum;
        Thread(CursorIntProd node);
};

Thread::Thread(CursorIntProd node){
    address = node.field0;
    sum = node.field1;
}


CursorTy printTree(CursorTy cur);
CursorIntProd createTree(CursorTy out, IntTy n);
CursorIntProd sumTree(CursorTy buffer);
void add1_recursive(CursorTy bufferIn, CursorTy bufferOut);
void add1_vectorized(IntTy*  bufferIn, IntTy*  bufferOut, IntTy size);
double difftimespecs(struct timespec* t0, struct timespec* t1);

CursorIntProd createBalancedTree(CursorTy out, IntTy n);
CursorTy printTreeBalanced(CursorTy cur) ;

CursorIntProd sumTree_bfs(std::vector<Thread*> Threads);

// CursorIntProd sumTree_bfs(std::vector<Thread*> Threads){

//     std::vector<Thread*> nextBlock;

//     for (Thread* thread : Threads){
//         TagTyPacked start = *(thread->address);
//         CursorTy next = thread->address + 8;
//         IntTy value;
//         //CursorTy next1;
//         if(start == 0){
//             value = *(IntTy*) next;
//             CursorTy next = next+8;
//             return (CursorIntProd) {next, value};
//         }
//         else if(start == 1){
//             value = *(IntTy*) next;
//             next += 8;

//             value += *(IntTy*) next;
//             next += 8;

//             value += *(IntTy*) next;
//             next += 8;

//             nextBlock.push_back(new Thread( (CursorIntProd) {next, value} ) );

//         }
//         else if(start == 4){

//             next+= 8;

//             value = *(IntTy*) next;
//             next += 8;

//             value += *(IntTy*) next;
//             next += 8;

//             value += *(IntTy*) next;
//             next += 8;

//             value += *(IntTy*) next;
//             next += 8;

//             nextBlock.push_back(new Thread( (CursorIntProd) {next, value} ) );
//         }

//         sumTree_bfs(nextBlock);
//     }

// }




double difftimespecs(struct timespec* t0, struct timespec* t1)
{
    return (double)((t1->tv_sec * 1000000000.0) - (t0->tv_sec * 1000000000.0))
      + ((double)(t1->tv_nsec - t0->tv_nsec));
}


// CursorIntProd sumTree(CursorTy buffer){

//     TagTyPacked start = *buffer;
//     CursorTy next = buffer + NODE_SIZE; //next increment the memory by the space taken by the tag.
    
//     if (start == 0){
//         //case A
//         IntTy number = *(IntTy *) next;
//         CursorTy next1 = next + NODE_SIZE;         //increment by 8
//         return (CursorIntProd) {next1, number};
//     }
//     else if (start == 1){
//         //case B
//         IntTy number = *(IntTy *) next;
//         next += NODE_SIZE;

//         CursorIntProd tmp1 = sumTree(next);
//         CursorTy next1 = tmp1.field0;
//         IntTy number1 = tmp1.field1;

//         CursorIntProd tmp2 = sumTree(next1);
//         CursorTy next2 = tmp2.field0;
//         IntTy number2 = tmp2.field1;

//         return (CursorIntProd) {next2, number + number1 + number2};
//     }
//     else if (start == 4){
//         //C_tmp
//         next += NODE_SIZE;

//         IntTy number = *(IntTy *) next;
//         next += NODE_SIZE;

//         CursorIntProd tmp1 = sumTree(next);
//         CursorTy next1 = tmp1.field0;
//         IntTy number1 = tmp1.field1;

//         CursorIntProd tmp2 = sumTree(next1);
//         CursorTy next2 = tmp2.field0;
//         IntTy number2 = tmp2.field1;

//         CursorIntProd tmp3 = sumTree(next2);
//         CursorTy next3 = tmp3.field0;
//         IntTy number3 = tmp3.field1;

//         return (CursorIntProd) {next3, (number+number1+number2+number3)};
//     }
// }

// CursorIntProd createTree(CursorTy out, IntTy n){

//     CursorIntProd tmp;    
    
//     if (n <= 0) /*Encountered node A*/ {

//         *out  = 0;             //A node has a value of 0
//          out += NODE_SIZE;             //make the A label take memory of 8 bytes (need this since both leaves and labels need to take the same space for vectorization) 
//          *(IntTy *) out = 10;  //Assign integer value to the out node
//          out += NODE_SIZE;             //Increment the address of the Cursor by 8
//          return (CursorIntProd) {out, static_cast<IntTy>(2*NODE_SIZE) };     //return 16, since 16 bytes work of data was written
//     }
//     else if (n == 1) /*Encountered node B*/{
        
//         *out = 1;
//         //n 
//         CursorTy out0 = out + NODE_SIZE;  //increment address by 8 again since we are making label size equal to leaf size
//         *(IntTy *) out0 = n;      //write n 
//         out0 += NODE_SIZE;                //increment address by 8, since we wrote an integer 

//         //rec 1
//         tmp = createTree(out0, (n - 1));
//         CursorTy out1 = tmp.field0;
//         IntTy size1   = tmp.field1;

//         //rec 2
//         tmp = createTree(out1, (n - 2));
//         CursorTy out2 = tmp.field0;
//         IntTy size2   = tmp.field1;

//         return (CursorIntProd) {out2, static_cast<IntTy>(size1 + size2 + 2*NODE_SIZE) };  //16 bytes of data was written for this particular node.

//     }
//     else /*Encountered node C*/{

//         *out = 4;

//         //n
//         CursorTy out0 = out + NODE_SIZE;   
//         *(IntTy *) out0 = n;
//         out0 += NODE_SIZE;

//         //rec1
//         tmp = createTree(out0, (n - 1));
//         CursorTy out1 = tmp.field0;
//         IntTy size1   = tmp.field1;

//         //rec2
//         tmp = createTree(out1, (n - 2));
//         CursorTy out2 = tmp.field0;
//         IntTy size2   = tmp.field1;

//         //rec3
//         tmp = createTree(out2,  (n - 3));
//         CursorTy out3 = tmp.field0;
//         IntTy size3 = tmp.field1;

//         return (CursorIntProd) {out3, static_cast<IntTy>(size1 + size2 + size3 + 2*NODE_SIZE)};

//     }

// }

//    createBinaryTree :: Int -> Tree
//   
//    createBinaryTree depth
//        |  depth < 0  =  return root         
//        |  depth > 0  =  r = createBinaryTree(n-1) | l = createBinaryTree(n-1) 
//
//
//


CursorIntProd createBalancedTree(CursorTy out, IntTy n){

    CursorIntProd tmp;    
    
    if (n <= 0) {

        *out  ='A';             
        out += NODE_SIZE;          
        *(IntTy *) out = 10;  
        out += NODE_SIZE;             
        return (CursorIntProd) {out, 2*NODE_SIZE };
    }
    else if (n > 0) {
        
        *out = 'B';
        //n 
        CursorTy out0 = out + NODE_SIZE;  
        *(IntTy *) out0 = n;     
        out0 += NODE_SIZE;           

        //rec 1
        tmp = createBalancedTree(out0, (n - 1));
        CursorTy out1 = tmp.field0;
        IntTy size1   = tmp.field1;

        //rec 2
        tmp = createBalancedTree(out1, (n - 2));
        CursorTy out2 = tmp.field0;
        IntTy size2   = tmp.field1;

        return (CursorIntProd) {out2, size1 + size2 + 2*NODE_SIZE };  //16 bytes of data was written for this particular node.

    }
}

CursorTy add1_toA_depth_recurse(CursorTy packedData){

    CursorTy tmp;

    TagTyPacked start = *packedData;
    CursorTy dataCursor = packedData + NODE_SIZE;
    
    //encountered a leaf node
    if(start == 'A'){        
        *(IntTy*) dataCursor = (*(IntTy*) dataCursor) + 1;
        CursorTy newCursor = dataCursor + NODE_SIZE;
        return newCursor;
    }
    //non leaf node
    else if (start == 'B'){
        
        //child 1
        CursorTy child1 = dataCursor + NODE_SIZE;
        tmp = add1_toA_depth_recurse(child1);

        //child 2
        tmp = add1_toA_depth_recurse(tmp);

        return tmp;
    }

}

// void add1_toA_depth_recurse(CursorTy packedData, CursorTy* cursor){

//     TagTyPacked start = *packedData;
//     CursorTy dataCursor = packedData + NODE_SIZE;
    
//     //encountered a leaf node
//     if(start == 'A'){        
//         *(IntTy*) dataCursor = (*(IntTy*) dataCursor) + 1;
//         CursorTy newCursor = dataCursor + NODE_SIZE;
//         *cursor = newCursor;
//     }
//     //non leaf node
//     else if (start == 'B'){
        
//         //child 1
//         CursorTy child1 = dataCursor + NODE_SIZE;
//         CursorTy* return1;
//         add1_toA_depth_recurse(child1, return1);

//         //child 2
//         CursorTy *return2; 
//         add1_toA_depth_recurse(*return1, return2);
//     }

// }

// CursorTy printTree(CursorTy cur) {
//     if (*cur == 0) {
//         printf("(A ");
//         cur += NODE_SIZE;
//         IntTy val = *(IntTy *) cur;
//         cur += NODE_SIZE;
//         printf("%lld",val);
//         printf(") ");
//         return cur;
//     } else if (*cur == 1) {
//         printf("(B ");
//         cur += NODE_SIZE;
//         IntTy val = *(IntTy *) cur;
//         cur += NODE_SIZE;
//         printf("%lld ", val);
//         cur = printTree(cur);
//         cur = printTree(cur);
//         printf(") ");
//         return cur;
//     }  else if (*cur == 4) {
//         printf("(C_tmp _ ");
//         cur += NODE_SIZE;
//         IntTy val = *(IntTy *) cur;
//         cur += NODE_SIZE;
//         printf("%lld ", val);
//         cur = printTree(cur);
//         cur = printTree(cur);
//         cur = printTree(cur);
//         printf(") ");
//         return cur;        
//     }
// }

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
        cur += NODE_SIZE;
        IntTy val = *(IntTy *) cur;
        cur += NODE_SIZE;
        printf("%lld ", val);
        cur = printTreeBalanced(cur);
        cur = printTreeBalanced(cur);
        printf(") ");
        return cur;
    }
    // }  else if (*cur == 4) {
    //     printf("(C_tmp _ ");
    //     cur += NODE_SIZE;
    //     IntTy val = *(IntTy *) cur;
    //     cur += NODE_SIZE;
    //     printf("%lld ", val);
    //     cur = printTree(cur);
    //     cur = printTree(cur);
    //     cur = printTree(cur);
    //     printf(") ");
    //     return cur;        
    // }
}

// CursorIntProd add1_recursive(CursorTy bufferIn, CursorTy bufferOut){

//     TagTyPacked start = *bufferIn;
//     CursorTy next = bufferIn + 8; //next increment the memory by the space taken by the tag.
    
//     if (start == 0){
//         //case A
//         IntTy number = *(IntTy *) next;
//         CursorTy next1 = next + 8;         //increment by 8
//         return (CursorIntProd) {next1, number};
//     }
//     else if (start == 1){
//         //case B
//         IntTy number = *(IntTy *) next;
//         next += 8;

//         CursorIntProd tmp1 = sumTree(next);
//         CursorTy next1 = tmp1.field0;
//         IntTy number1 = tmp1.field1;

//         CursorIntProd tmp2 = sumTree(next1);
//         CursorTy next2 = tmp2.field0;
//         IntTy number2 = tmp2.field1;

//         return (CursorIntProd) {next2, number + number1 + number2};
//     }
//     else if (start == 4){
//         //C_tmp
//         next += 8;

//         IntTy number = *(IntTy *) next;
//         next += 8;

//         CursorIntProd tmp1 = sumTree(next);
//         CursorTy next1 = tmp1.field0;
//         IntTy number1 = tmp1.field1;

//         CursorIntProd tmp2 = sumTree(next1);
//         CursorTy next2 = tmp2.field0;
//         IntTy number2 = tmp2.field1;

//         CursorIntProd tmp3 = sumTree(next2);
//         CursorTy next3 = tmp3.field0;
//         IntTy number3 = tmp3.field1;

//         return (CursorIntProd) {next3, (number+number1+number2+number3)};
//     }
// }

// void add1_recursive(CursorTy bufferIn, CursorTy bufferOut){
    
//     TagTyPacked start = *bufferIn;
//     CursorTy nextIn = bufferIn + 8;          //next increment the memory by the space taken by the tag.
//     CursorTy nextOut = bufferOut + 8;      //cursor for out buffer follows cursor for in buffer

//     if(start == 0) /*A*/ {

//         *(IntTy *) nextOut = *(IntTy *) nextIn +  1;
        
//     }
//     else if(start == 1) /*B*/ {

//         *(IntTy *) nextOut = *(IntTy *) nextIn +  1;
//         add1_recursive(nextIn, nextOut);
//         add1_recursive(CursorTy bufferIn, CursorTy bufferOut)
//     }
//     else if (start == 4) /*C*/ {

//     }



// }

void add1_vectorized(IntTy* bufferIn, IntTy* bufferOut, IntTy size){
    
    //#pragma omp simd
    #pragma clang loop vectorize_width(4) interleave_count(4)
    for (int i=1; i<size; i += 1){
       bufferOut[i] = bufferIn[i] + 1;
        //std::cout << ((IntTy*) bufferOut)[i] << std::endl;
        //((IntTy*) bufferOut)[i + 1] = ((IntTy*) bufferIn)[i + 1] + 1;
        //((IntTy*) bufferOut)[i + 2] = ((IntTy*) bufferIn)[i + 2] + 1;
        //((IntTy*) bufferOut)[i + 3] = ((IntTy*) bufferIn)[i + 3] + 1;
        //((IntTy*) bufferOut)[i + 4] = ((IntTy*) bufferIn)[i + 4] + 1;
        //((IntTy*) bufferOut)[i + 5] = ((IntTy*) bufferIn)[i + 5] + 1;
        //((IntTy*) bufferOut)[i + 6] = ((IntTy*) bufferIn)[i + 6] + 1;
    }

}

int main (int argc, char** argv){

    if (argc < 2){
        printf("USAGE: executable SIZE\n");
        exit(1);
    }
    
    double time;
    struct timespec beginTime;
    struct timespec endTime;

    IntTy tree_depth = atoll(argv[1]); //depth of the tree

    //tree structure
    CursorIntProd myTree;
   
    //allocate a huge data array for now 
    CursorTy dataArray = (CursorTy) malloc(UINT_MAX);

    myTree = createBalancedTree(dataArray, tree_depth);
    //myTree = createTree(dataArray, tree_depth); 
    
    //add1 depth recursive
    add1_toA_depth_recurse(dataArray);   

    printf("Printing the original tree that was created\n");
    printTreeBalanced(dataArray);
    printf("\n");

    //CursorIntProd summedTree = sumTree(dataArray);

    //printf("Now printing the sum\n");
    //printf("The sum is: (%lld)\n", summedTree.field1);

    //Thread * thread_start = new Thread( ( (CursorIntProd) {dataArray, *dataArray} ) ) ;

    //std::vector<Thread*> startThread;
    //startThread.push_back(thread_start);

    //CursorIntProd summedTreebfs =  sumTree_bfs(startThread);
    
    //printf("\n");
    //printf("Now printing the sum from bfs\n");
    //printf("The sum is: (%lld)\n", summedTreebfs.field1);


    //CursorTy dataArrayOut = (CursorTy) malloc(UINT_MAX);

    //IntTy size; 
    //size = myTree.field1 / sizeof(IntTy);
    
    //clock_gettime(CLOCK_MONOTONIC_RAW, &beginTime);
    //add1_vectorized((IntTy*)dataArray, (IntTy*)dataArrayOut, size);
    //clock_gettime(CLOCK_MONOTONIC_RAW, &endTime);
    //time = difftimespecs(&beginTime, &endTime);

    //printf("Printing second element (%lld)\n", ((IntTy*) dataArrayOut)[1]);
    //printf("\n");

    //printf("Time taken for vectorized implementation was (%lf) nanoseconds\n", time);

    


}




