#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <string.h>

#define KB (1 * 1000lu)
#define MB (KB * 1000lu)
#define GB (MB * 1000lu)

// Some typedefs we'll need
typedef long long IntTy;
typedef char* CursorTy;
typedef struct CursorCursorCursorProd_struct {
    CursorTy field0;
    CursorTy field1;
    CursorTy field2;
} CursorCursorCursorProd;

typedef struct CursorCursorProd_struct {
    CursorTy field0;
    CursorTy field1;
} CursorCursorProd;

/*

Running example:

    data Foo = A Int
             | B Foo Foo
             | C Foo Foo Foo
      deriving (Show)

    mkFoo :: Int -> Foo
    mkFoo n
      | n <= 0    = A 10
      | n == 1    = B (mkFoo (n-1)) (mkFoo (n-2))
      | otherwise = C (mkFoo (n-1)) (mkFoo (n-2)) (mkFoo (n-3))

 */

CursorTy mkFoo (CursorTy out, IntTy n) {
    if (n <= 0) {
        *out = 0;
        out++;
        *(IntTy *) out = 10;
        out += 8;
        return out;
    } else if (n == 1) {
        *out = 1;
        out++;
        out = mkFoo(out, (n-1));
        out = mkFoo(out, (n-2));
        return out;
    } else {
        *out = 2;
        out++;
        out = mkFoo(out, (n-1));
        out = mkFoo(out, (n-2));
        out = mkFoo(out, (n-3));
        return out;
    }
}

CursorTy printFoo(CursorTy cur) {
    if (*cur == 0) {
        printf("(A ");
        cur++;
        IntTy val = *(IntTy *) cur;
        cur += 8;
        printf("%lld ",val);
        printf(") ");
        return cur;
    } else if (*cur == 1) {
        printf("(B ");
        cur++;
        cur = printFoo(cur);
        cur = printFoo(cur);
        printf(") ");
        return cur;
    } else {
        printf("(C ");
        cur++;
        cur = printFoo(cur);
        cur = printFoo(cur);
        cur = printFoo(cur);
        printf(") ");
        return cur;
    }
}

int main () {
    CursorTy reg1 = malloc(1 * MB);
    CursorTy out1 = reg1;
    if (reg1 == NULL) {
        fprintf(stderr, "Malloc failed: %s\n", strerror(errno));
        exit(1);
    }

    // A place to store offset information.
    CursorTy ran_reg1 = malloc(1 * MB);
    if (ran_reg1 == NULL) {
        fprintf(stderr, "Malloc failed: %s\n", strerror(errno));
        exit(1);
    }

    mkFoo(out1, 2);
    printFoo(out1);

    return 0;
}
