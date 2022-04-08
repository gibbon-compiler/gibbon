#include "tree_insert_litmus_test.h"

Tree *createTreeNode(int n){
    
    Tree * newNode = (Tree*) malloc(sizeof(Tree));
    newNode->n = n;
    newNode->left  = NULL;
    newNode->right = NULL;

}

void treeInsertHelper(Tree *root, int value){
    
    //leaf case
    if (root->left == NULL && root->right == NULL){
        Tree * new = createTreeNode(value);
        //insert at the left of the root
        if(value < root->n){                       
            root->left = new;
        }
        //insert at the right of the root
        else{            
            root->right = new;
        }
    }
    //non leaf case
    else {
        //insert inside the left subtree
        if (value < root->n){
            //if left is NULL then insert at left
            if (root->left == NULL){
                Tree *new = createTreeNode(value); 
                root->left = new;                
            }
            else{
                treeInsertHelper(root->left, value);
            }            
        }
        //insert inside the right subtree
        else{
            //if right side is 
            if (root->right == NULL){
                Tree *new = createTreeNode(value);
                root->right = new;
            }
            else{
                treeInsertHelper(root->right, value);
            }
        }
    }

}


Tree *treeInsert(Tree *root, int value){
    
    //case NULL
    if (root == NULL){
        Tree *new = createTreeNode(value);
        return new;
    }
    else {
        treeInsertHelper(root, value);
    }

    return root;  

}


void printTreeHelper(Tree *root){

    if (root == NULL){
        return;
    }

    printf("( %d ", root->n);
    printTreeHelper(root->left);
    printTreeHelper(root->right);
    printf(")");

}

void printTree(Tree *root){

    printf("Printing the tree in pre-order\n");
    printTreeHelper(root);
    printf("\n");    
    
}

void freeTree(Tree *root){

    if (root == NULL){
        return;
    }

    freeTree(root->left);
    freeTree(root->right);
    free(root);

}


int main (int argc, char ** argv){

    Tree * root = createTreeNode(5);
    Tree * left = createTreeNode(4);
    Tree * right = createTreeNode(6);
    
    root->left  = left;
    root->right = right;

    root = treeInsert(root, 1);
    
    printTree(root);

    //free memory
    freeTree(root);

}
