#pragma GCC optimize("O3", "inline")

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <stdint.h>
#include <stdbool.h>

#define stack_size 10000000

clock_t start, end;
double cpu_time_used;

typedef struct Tree {
    int value; 
    struct Tree* right; 
    struct Tree* left; 
} Tree; 

void display(int* top, uintptr_t* stack)
{
    if(*top>=0)
    {
        printf("\n The elements in STACK \n");
        for(int i=*top; i>=0; i--)
            printf("\n%ld\n",stack[i]);
    }
    else
    {
        printf("\n The STACK is empty");
    }
   
}

static inline void push(uintptr_t pointer, int* top, uintptr_t* stack){

    if ((void*)pointer == NULL)
        return;

    if(*top < stack_size - 1 ){
        (*top)++;
        stack[*top] = pointer;
    }
    else{
        printf("Stack Overflow!!\n");
    }
}

static inline uintptr_t pop(int* top, uintptr_t* stack){

    if(*top > -1){
        uintptr_t pointer = stack[*top];
        (*top)--; 
        return pointer;
    }
    else{
        printf("Stack Underflow\n");
        return -1; 
    }

}

static inline uintptr_t _top(int* top, uintptr_t* stack){

    if(*top > -1){
        return stack[*top];
    }
    else{
        printf("Stack Underflow\n");
        return -1; 
    }

}

static inline void _pop(int* top){

    if(*top > -1){
        (*top)--; 
        return;
    }
    else{
        printf("Stack Underflow\n");
        return;
    }

}

static inline bool isEmptyStack(int* top){

    if (*top > -1){
        return false;
    }
    
    return true;
    
}

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

void _sumTreeAutoRopes(Tree* root, int* sum, uintptr_t* stack){
    
    int top = -1;

    push((uintptr_t) root, &top, stack);

    while(!isEmptyStack(&top)){

        root = (Tree*) _top(&top, stack);
        _pop(&top);
        
        *sum += root->value;
        push((uintptr_t) (root->right), &top, stack);
        push((uintptr_t) (root->left), &top, stack);
    }
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
    
    uintptr_t* stack = (uintptr_t*) malloc(sizeof(uintptr_t*) * stack_size);

    start = clock(); 
    _sumTreeAutoRopes(tree, &sum, stack);
    end = clock(); 

    cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;

    printf("Execution time: %lf\n", cpu_time_used);
    printf("The sum of the tree was %d\n", sum);

}