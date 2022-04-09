#include "tree_insert_non_destructive.h"

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



int sumTreeHelper(Tree *root){

    //leaf case
    if (root->left == NULL && root->right == NULL){
       return root->n;
    }
    //non leaf case
    else {
        if (root->left == NULL){
            return root->n + sumTreeHelper(root->right);                
        }
        else if (root->right == NULL){
            return root->n + sumTreeHelper(root->left);
        }
        else {
            return root->n + sumTreeHelper(root->left) + sumTreeHelper(root->right);
        }     
    }
}


int sumTree(Tree *root){

    if (root == NULL){
        return 0;
    }
    
    return sumTreeHelper(root);

}


Tree * treeCopy(Tree *root){

    if(root == NULL){
        return NULL;
    }
    else {

        Tree *copiedNode  = createTreeNode(root->n);
        copiedNode->left  = treeCopy(root->left);
        copiedNode->right = treeCopy(root->right);
        return copiedNode;
    }

}

Tree *treeInsert(Tree *root, int value){

    //copy the original tree coz we don't want to modify it
    //Non destructive insert.

    Tree *copy = treeCopy(root);
    
    //case NULL
    if (copy == NULL){
        Tree *new = createTreeNode(value);
        return new;
    }
    else {
        treeInsertHelper(copy, value);
    }

    return copy;  

}


Tree *helper(int s, int e){

    if (e < s){
        return NULL;
    }
    else if (e == s){
        return createTreeNode(s);
    }
    else{
        int m = s + ((e - s) / 2);
        Tree *newNode  = createTreeNode(m);
        newNode->left  = helper(s, m - 1);
        newNode->right = helper(m + 1, e);

        return newNode;
    }

}


void printTreeHelper(Tree *root){

    if (root == NULL){
        printf(" Null ");
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

long int power(int base, int superscript){

    long int power = 1;

    for(int i = 0; i < superscript; i++){
        power *= base;
    }

    return power;

}


int main (int argc, char ** argv){

    if (argc < 3){
        printf("Error: Usage: ./a.out treeSize random-iterations\n");
        exit(1);
    }

    srand(time(NULL));

    long int sizeParam = atol(argv[1]);

    long int iterations = atol(argv[2]);

    long int totalNodes = power(2, sizeParam + 1) - 1;

    Tree *root = helper(0, totalNodes);

    printTree(root);
    
    //assign new to the root at the beginning
    Tree * new = root;

    for(int i=0; i < iterations; i++){

        //Question :: Here the old pointer to the tree remains and is not freed

        //Question :: How do we choose to delete using rand % 2 ?? if 0 then insert if 1 then delete??

        int j = rand() % totalNodes;
        new = treeInsert(new, j);
        printTree(new);

    }

    //free memory
    freeTree(root);

}
