#include "list_reverse_destructive.h"

List *createListnode(int val){
    List *newNode = (List *) malloc(sizeof(List));
    newNode->val = val;
    newNode->next = NULL;
}


void printList(List *head){

    printf("Printing the List\n");
    
    List *tmp = head;
    while(tmp != NULL){
        printf("Cons %d -> ", tmp->val);
        tmp = tmp->next;
    }

    printf("NIL\n");
}
  
List * createList(int length){

    List * head = createListnode(length);
    List * tmp = head;
    for(int i=length-1; i > 0; i--){
        List * newNode = createListnode(i);
        tmp->next = newNode;
        tmp = tmp->next;
    }

    return head;
}


List * reverseList(List *head){

    List * tmp = head;
    List * accumulator = NULL;
    while(tmp != NULL){
        //make a new Cons node
        List *newNode = createListnode(tmp->val);
        newNode->next = accumulator;
        accumulator = newNode;
        tmp = tmp->next;
    }

    return accumulator;
}

void freeList(List * head){

    List * tmp = head;
    while(tmp != NULL){
        List * toFree = tmp;
        tmp = tmp->next;
        free(toFree);
    }

}


int main(int argc, char **argv){

    if (argc < 2){
        printf("Error: Usage: ./a.out listLength\n");
        exit(1);
    }

    int length = atoi(argv[1]);
    //create list
    List * head = createList(length);
    printList(head);

    printf("Calling reverse on List.\n");
    //reverse list
    List *reversedHead = reverseList(head);
    printList(reversedHead);

    //Question :: What happens to the input list should that be freed too? 

    //free the reversed list
    freeList(reversedHead);

}


