#include <stdio.h>
#include <stdlib.h>

typedef struct list {
    struct list *next;
    int val;
} List;
