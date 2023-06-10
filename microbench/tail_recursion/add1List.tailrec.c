#pragma GCC optimize("O3", "inline")
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

clock_t start, end;
double cpu_time_used;

typedef struct List{
    int value; 
    struct List* next; 
} List;

void initArray(int* array, int* arraySize){

    for(int i=0; i<*arraySize; i++){
        array[i] = i;
    }

}

void printArray(int* array, int* arraySize){

    for(int i=0; i<*arraySize; i++){
        printf(" %d ", array[i]);
    }

}


void add1List(List* head){

    if (head == NULL){
        return;
    }

    head->value += 1;
    add1List(head->next);
}

List* mkNode(int value){

    List* newNode = (List*) malloc(sizeof(List));
    newNode->value = value;
    newNode->next = NULL;

    return newNode;

}

List* initList(int size){

    List* head = mkNode(0);
    List* temp = head;

    for(int i=0; i<size; i++){
        temp->next = mkNode(i);
        temp = temp->next;
    }

    return head;

}


int main(int argc, char** argv){

    int list_size = atoi(argv[1]);

    List* head = initList(list_size);
    
     
    start = clock(); 
    add1List(head);
    end = clock(); 

    cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;

    printf("Execution time: %lf\n", cpu_time_used);

}