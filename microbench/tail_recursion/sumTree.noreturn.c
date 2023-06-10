#pragma GCC optimize("O3", "inline")

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <stdint.h>


clock_t start, end;
double cpu_time_used;

typedef struct Tree {
    int value; 
    struct Tree* right; 
    struct Tree* left; 
} Tree; 

Tree* mkTreeNode (int value){

    Tree * newNode = (Tree*) malloc(sizeof(Tree));

    newNode->value = value;
    newNode->left  = NULL; 
    newNode->right = NULL; 

    return newNode; 
}

Tree* mkTree(int depth){

    if (depth <= 0){
        return NULL;
    }

    Tree* root  = mkTreeNode(depth);
    root->left  = mkTree(depth-1);
    root->right = mkTree(depth-1);

    return root;
}

void _sumTree(Tree* root, int* sum){

   if(root == NULL){
    return;
   } 

   *sum += root->value; 
   _sumTree(root->left,  sum);
   _sumTree(root->right, sum);

}

void printTree(Tree* root){

    if(root == NULL){
        printf(" NULL ");
    }
    else if (root->left == NULL && root->right == NULL){
        printf(" LEAF %d", root->value);
    }
    else{
        printf(" (NODE %d", root->value);
        printTree(root->left);
        printTree(root->right);
        printf(")");
    }

}

int main(int argc, char** argv){

    Tree* tree = mkTree(atoi(argv[1]));
    //printTree(tree);
    //printf("\n");
    //printf("\n");
    
    int sum = 0;

    start = clock(); 
    _sumTree(tree, &sum);
    end = clock(); 

    cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;

    printf("Execution time: %lf\n", cpu_time_used);
    printf("The sum of the tree was %d\n", sum);

}