#pragma GCC optimize("O3", "omit-frame-pointer","inline")

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <stdint.h>

#define stack_size 10000000
//uintptr_t stack[stack_size];
//int top=-1;

clock_t start, end;
double cpu_time_used;

typedef struct Tree {
    int value; 
    struct Tree* right; 
    struct Tree* left; 
} Tree; 

// void display()
// {
//     if(top>=0)
//     {
//         printf("\n The elements in STACK \n");
//         for(int i=top; i>=0; i--)
//             printf("\n%ld\n",stack[i]);
//     }
//     else
//     {
//         printf("\n The STACK is empty");
//     }
   
// }

static inline void push(uintptr_t pointer, int* top, uintptr_t* stack){

    if(*top < stack_size - 1){
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

int isEmptyStack(int* top){

    if (*top > -1){
        return 0;
    }
    
    return -1;
    
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

void _sumTree(Tree* root, int* sum){

   if(root == NULL){
    return;
   } 

   *sum += root->value; 
   _sumTree(root->left,  sum);
   _sumTree(root->right, sum);

}

void _sumTreeAutoRopes(Tree* root, int* sum){
    
    uintptr_t* stack = (uintptr_t*) malloc(sizeof(uintptr_t*) * stack_size);
    int top = -1;

    push((uintptr_t) root, &top, stack);

    while(isEmptyStack(&top) == 0 ){

        root = (Tree*) pop(&top, stack); 
        
        *sum += root->value;
        if(root->right != NULL)
            push((uintptr_t) (root->right), &top, stack);
        if(root->left != NULL)
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

int main(){

    Tree* tree = mkTree(29);
    //printTree(tree);
    //printf("\n");
    //printf("\n");
    
    int sum = 0;

    start = clock(); 
    _sumTreeAutoRopes(tree, &sum);
    end = clock(); 

    cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;

    printf("Execution time:%lf seconds\n", cpu_time_used);
    printf("The sum of the tree was %d\n", sum);

}