typedef char TagTyPacked;
typedef char TagTyBoxed;
typedef long long IntTy;
typedef IntTy SymTy;
typedef char* PtrTy;
typedef char* CursorTy;

typedef struct Int64Prod_struct {
    IntTy field0;
} Int64Prod;
typedef struct Int64CursorProd_struct {
    IntTy field0;
    CursorTy field1;
} Int64CursorProd;
typedef struct TagInt64Prod_struct {
    TagTyPacked field0;
    IntTy field1;
} TagInt64Prod;
typedef struct TagCursorProd_struct {
    TagTyPacked field0;
    CursorTy field1;
} TagCursorProd;
typedef struct TagCursorCursorProd_struct {
    TagTyPacked field0;
    CursorTy field1;
    CursorTy field2;
} TagCursorCursorProd;
typedef struct CursorProd_struct {
    CursorTy field0;
} CursorProd;
typedef struct CursorCursorProd_struct {
    CursorTy field0;
    CursorTy field1;
} CursorCursorProd;
typedef struct PtrProd_struct {
    PtrTy field0;
} PtrProd;
typedef struct PtrCursorProd_struct {
    PtrTy field0;
    CursorTy field1;
} PtrCursorProd;

typedef struct CursorCursorCursorCursorProd_struct {
    CursorTy field0;
    CursorTy field1;
    CursorTy field2;
    CursorTy field3;
} CursorCursorCursorCursorProd;

typedef struct CursorCursorCursorCursorInt64Prod_struct {
    CursorTy field0;
    CursorTy field1;
    CursorTy field2;
    CursorTy field3;
    IntTy    field4;
} CursorCursorCursorCursorInt64Prod;

typedef struct CursorCursorCursorProd_struct {
    CursorTy field0;
    CursorTy field1;
    CursorTy field2;
} CursorCursorCursorProd;

#define KB (1 * 1000lu)
#define MB (KB * 1000lu)
#define GB (MB * 1000lu)

#define REDIRECTION_SIZE 9
#define REDIRECTION_TAG 100

/* #define INF_REG_INIT_SIZE (300 * MB) */
/* #define INF_REG_INIT_SIZE 20 */
#define INF_REG_INIT_SIZE 64
#define INF_REG_MAX_SIZE (2 * GB)

#define MAX(a,b) (((a)>(b))?(a):(b))

typedef struct RegionTy_struct {
    CursorTy start;
    /* CursorTy end; */
    IntTy size;
} RegionTy;

typedef struct RegionCursorCursorProd_struct {
    RegionTy field0;
    CursorTy field1;
    CursorTy field2;
} RegionCursorCursorProd;

typedef struct RegionCursorProd_struct {
    RegionTy field0;
    CursorTy field1;
} RegionCursorProd;

CursorTy alloc_buf_malloc(IntTy buf_size);
/* RegionTy alloc_infinite_region(RegionTy old); */
/* RegionTy alloc_first_infinite_region(); */
