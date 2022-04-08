#include <stdio.h>
#include <stdlib.h>
#include <time.h>

typedef struct tree {
    struct tree * left; 
    struct tree * right;
    int n;
} Tree;


Tree *createTreeNode(int n);
Tree *treeInsert(Tree *root, int value);
void treeInsertHelper(Tree *root, int value);
void printTreeHelper(Tree *root);
void printTree(Tree *root);
void freeTree(Tree *root);
int sumTree(Tree *root);
int sumTreeHelper(Tree *root);
Tree *helper(int s, int e);
long int power(int base, int superscript);
