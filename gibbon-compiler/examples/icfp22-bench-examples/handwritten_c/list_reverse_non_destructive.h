#include <stdio.h>
#include <stdlib.h>

typedef struct list {
    struct list *next;
    int val;
} List;


List *createListnode(int val);
List * createList(int length);
List * reverseList(List *head);
void printList(List *head);
void freeList(List * head);