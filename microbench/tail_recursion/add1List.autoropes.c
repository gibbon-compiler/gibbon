#pragma GCC optimize("O3", "inline")

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <stdint.h>
#include <stdbool.h>


typedef struct List{
    int value; 
    struct List* next; 
} List;


#define stack_size 10000000

clock_t start, end;
double cpu_time_used;


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
        int value = stack[*top];
        (*top)--; 
        return value;
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


void add1ListAutoropes(List* head, uintptr_t* stack){
     
    int top = -1; 
    push((uintptr_t) head, &top, stack);

    while(!isEmptyStack(&top)){

        head = (List*) _top(&top, stack);
        _pop(&top);
    
        head->value += 1;

        push((uintptr_t) head->next, &top, stack);

    }
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
    
    uintptr_t* stack = (uintptr_t*) malloc(sizeof(uintptr_t) * stack_size);
     
    start = clock(); 
    add1ListAutoropes(head, stack);
    end = clock(); 

    cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;

    printf("Execution time: %lf\n", cpu_time_used);

}