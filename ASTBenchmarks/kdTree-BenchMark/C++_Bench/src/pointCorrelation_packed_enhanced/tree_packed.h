#ifndef HEAD
#define HEAD
#include <cstdlib>
#include <cstdint>
#include <cfloat>
#include <cmath>
#include <iostream>
#include <fstream>
#include <stdio.h>
#include <time.h>


#define LEAF_TAG 'l'
#define INNER_TAG 'i'

#define SIZE_OF_LEAF sizeof(char ) +sizeof(Node_Leaf)

#define SIZE_OF_INNER sizeof(char ) +sizeof(Node_Inner)

//#define TEST


using namespace std;

// Tag can be a bool , 0=leaf , 1=inner
// leaf     [Tag Node_Leaf]
// non-leaf [Tag Node_Inner [LeftChild....][RightChild...]
// index of right child = index of last left decenedent + 1

//used to represent the input  data read from file and used to build the tree i
struct  Point{
    float x_val;
    float y_val;
};

enum Varient {updateTree, treeOut, intOut};



//these structs justused while building the tree - to make it simpler since its not evaluated
struct __attribute__((packed))   Node_Leaf{
    float x_val;
    float y_val;
    int   corr;
};


struct __attribute__((packed))  Node_Inner_NoIndirection{
    bool     splitAxis; // 0:'x' , 1:'y'
    float    splitLoc;
    float min_x;
    float max_x;
    float min_y;
    float max_y;
};

struct __attribute__((packed))  Node_Inner_Indirection{
    bool     splitAxis; // 0:'x' , 1:'y'
    float    splitLoc;
    float min_x;
    float max_x;
    float min_y;
    float max_y;
    char *   RightChild;
};

extern int counter;
extern int counter2;
extern int nodeCount_INNER;

void readPoint(FILE *in, Point &p);
void readInput(int argc, char **argv,Point * & data , float & rad, int & npoints, Varient & mode);

long long treeSize(long long n, bool withIndirction);
char *  buildTree(int n , Point * data ,bool withIndirction);
void    buildTreeRec_NoIndirection(int startIndx ,int endIndx ,Point * data ,char * &cur ,int depth  );

char *  printPackedTree(char * & cur);

pair<int ,bool> performPointCorr_IntOut(Point & p,char *  &cur,float rad);
bool            performPointCorr_OnTree(Point & p,char * & cur,float  rad);
void performPointCorr_treeOut_rec(Point & p,char * & cur,char * & curOut,float rad);

/*TREE_H_*/
#endif
