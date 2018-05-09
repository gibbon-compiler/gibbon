#include <assert.h>
#include <stdio.h>
// #include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <alloca.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>
#include <stdarg.h> // For va_start etc
#include <errno.h>

// Big default.  Used for --packed and --pointer/bumpalloc
// static long long global_default_buf_size = (500lu * 1000lu * 1000lu);
static long long global_default_buf_size = (5 * 1000lu * 1000lu * 1000lu); // 9GB.

static long long global_size_param = 1;
static long long global_iters_param = 1;

static char*     global_benchfile_param = NULL;

// Sequential for now:
static const int num_workers = 1;


// Helpers and debugging:
//--------------------------------------------------------------------------------

//--------------------------------------------------------------------------------

#ifdef BUMPALLOC
// #define DEBUG
#warning "Using bump allocator."

char* heap_ptr = (char*)NULL;

char* saved_heap_ptr_stack[100];
int num_saved_heap_ptr = 0;

// Requires -std=gnu11
int dbgprintf(const char *format, ...)
{
    int code = 0;
    va_list args;
    va_start(args, format);
#ifdef DEBUG
    code = vprintf(format, args);
#endif
    va_end(args);
    return code;
}

// For simplicity just use a single large slab:
void INITALLOC() {
    if (! heap_ptr)
    {
        // Use a fixed address in debug mode for easy reading:
#ifdef DEBUG
        // heap_ptr = (char*)mmap(0x010000000000, global_default_buf_size, PROT_READ|PROT_WRITE, MAP_FIXED | MAP_ANONYMOUS, -1, 0);
        heap_ptr = (char*)mmap(0x010000000000, global_default_buf_size, PROT_READ|PROT_WRITE, MAP_ANONYMOUS | MAP_PRIVATE, -1, 0);
        if (heap_ptr == MAP_FAILED) {
            fprintf(stderr, "Error: mmap failed: %s\n", strerror(errno));
            abort();
        }
#else
        heap_ptr = (char*)malloc(global_default_buf_size);
#endif
        dbgprintf("Arena size for bump alloc: %lld\n", global_default_buf_size);
    }
    dbgprintf("BUMPALLOC/INITALLOC DONE: heap_ptr = %p\n", heap_ptr);
}

#ifdef DEBUG
char* my_abort() {
    fprintf(stderr, "Error: this thread's heap was not initalized.\n");
    abort();
    return NULL;
}
void* ALLOC(int n) {
    if (!heap_ptr) my_abort();
    char* old = heap_ptr;
    printf("ALLOC: %d bytes, returning %p\n", n, old);
    // heap_ptr += 16 * n; // Optional padding for debugging.
    heap_ptr += n;
    return old;
}
#else
// #define ALLOC(n) (do heap_ptr += n)
void* ALLOC(int n) { char* old= heap_ptr; heap_ptr += n; return old; }
#endif // DEBUG

// Snapshot the current heap pointer value across all threads.
void save_alloc_state() {
    dbgprintf("   Saving(%p): pos %d", heap_ptr, num_saved_heap_ptr);
    saved_heap_ptr_stack[num_saved_heap_ptr] = heap_ptr;
    num_saved_heap_ptr++;
    dbgprintf("\n");
}

void restore_alloc_state() {
    if(num_saved_heap_ptr <= 0) {
        fprintf(stderr, "Bad call to restore_alloc_state!  Saved stack empty!\ne");
        abort();
    }
    num_saved_heap_ptr--;
    dbgprintf("Restoring(%p): pos %d, discarding %p",
              saved_heap_ptr_stack[num_saved_heap_ptr], num_saved_heap_ptr, heap_ptr);
    heap_ptr = saved_heap_ptr_stack[num_saved_heap_ptr];
}

#else
// Regular malloc mode:
void INITALLOC() {}

void save_alloc_state() {}
void restore_alloc_state() {}

#define ALLOC(n) malloc(n)

#endif // BUMPALLOC

#define ALLOC_PACKED(n) ALLOC(n)

// --------------------------------------------------------------------------------

typedef char TagTyPacked;  // Must be consistent with codegen in Target.hs
typedef char TagTyBoxed;   // Must be consistent with codegen in Target.hs
typedef long long IntTy;
typedef IntTy SymTy;
typedef char* PtrTy;
typedef char* CursorTy;

typedef struct dict_item {
    struct dict_item * next;
    int key;
    union {
        int intval;
        void * ptrval;
    };
} dict_item_t;

dict_item_t * dict_alloc() {
    return ALLOC(sizeof(dict_item_t));
}

dict_item_t *dict_insert_int(dict_item_t *ptr, SymTy key, IntTy val) {
    dict_item_t *ret = dict_alloc();
    ret->key = key;
    ret->intval = val;
    ret->next = ptr;
    return ret;
}

IntTy dict_lookup_int(dict_item_t *ptr, SymTy key) {
    while (ptr != 0) {
        if (ptr->key == key) {
            return ptr->intval;
        } else {
            ptr = ptr->next;
        }
    }
    printf("Error, key %lld not found!\n",key);
    exit(1);
}

char* read_benchfile_param() {
    if (global_benchfile_param == NULL) {
        fprintf(stderr, "read_benchfile_param: benchmark input file was not set!\n");
        exit(1);
    } else
        return global_benchfile_param;
}

// Could try alloca() here.  Better yet, we could keep our own,
// separate stack and insert our own code to restore the pointer
// before any function that (may have) called ALLOC_SCOPED returns.

// #define ALLOC_SCOPED() alloca(1024)
#define ALLOC_SCOPED() alloca(100LU*1024LU)
// #define ALLOC_SCOPED() alloc_scoped()

// Stack allocation is either too small or blows our stack.
// We need a way to make a giant stack if we want to use alloca.
// #define ALLOC_SCOPED() ALLOC(global_default_buf_size)


// Our global pointer.  No parallelism.
// static char* stack_scoped_region;
// char* alloc_scoped() { return stack_scoped_region; }


// fun fact: __ prefix is actually reserved and this is an undefined behavior.
// These functions must be provided by the code generator.
void __main_expr();


void show_usage(char** argv)
{
    printf("\n");
    printf("This binary was generated by the Gibbon compiler.\n");
    printf("\n");
    printf("Usage: %s [OPTS] [size] [iters]\n", argv[0]);

    printf("\n");
    printf("Options:\n");
    printf(" --buffer-size <bytes>      Set the buffer size (default %lld).\n", global_default_buf_size);
    printf(" --bench-input <path>       Set the input file read for benchmarking. Applies only\n");
    printf("                            IF the program was *compiled* with --bench-fun. \n");
    return;
}

double avg(const double* arr, int n)
{
    double sum = 0.0;
    for(int i=0; i<n; i++) sum += arr[i];
    return sum / (double)n;
}

double difftimespecs(struct timespec* t0, struct timespec* t1)
{
    return (double)(t1->tv_sec - t0->tv_sec)
        + ((double)(t1->tv_nsec - t0->tv_nsec) / 1000000000.0);
}

int compare_doubles(const void *a, const void *b)
{
    const double *da = (const double *) a;
    const double *db = (const double *) b;
    return (*da > *db) - (*da < *db);
}


int main(int argc, char** argv)
{
    // parameters to parse:
    //
    //   num iterations: How many times to repeat a benchmark.
    //   tree size: An integer passes to `build_tree()`.

    struct rlimit lim;
    int code;
    if ( (code = getrlimit(RLIMIT_STACK, &lim)) ) {
        fprintf(stderr, " [gibbon rts] failed to getrlimit, code %d\n", code);
        abort();
    }

    // lim.rlim_cur = 1024LU * 1024LU * 1024LU; // 1GB stack.
    lim.rlim_cur = 512LU * 1024LU * 1024LU; // 500MB stack.
    // lim.rlim_max = lim.rlim_cur; // Normal users may only be able to decrease this.

    // WARNING: Haven't yet figured out why this doesn't work on MacOS...
#ifndef __APPLE__
    code = setrlimit(RLIMIT_STACK, &lim);
    while (code) {
        fprintf(stderr, " [gibbon rts] Failed to set stack size to %llu, code %d\n", (unsigned long long)lim.rlim_cur, code);
        lim.rlim_cur /= 2;
        // lim.rlim_max /= 2;
        if(lim.rlim_cur < 100 * 1024) {
            fprintf(stderr, " [gibbon rts] Failed setrlimit stack size to something reasonable; giving up.\n");
            break; // abort();
        }
        int code = setrlimit(RLIMIT_STACK, &lim);
    }
#endif

    // TODO: atoi() error checking

    int got_numargs = 0; // How many numeric arguments have we got.

    int i;
    for (i = 1; i < argc; ++i)
    {
        if (strcmp(argv[i], "-h") == 0 || strcmp(argv[i], "--help") == 0) {
            show_usage(argv);
            exit(0);
        }
        else if (strcmp(argv[i], "--buffer-size") == 0 && i < argc - 1)
        {
            global_default_buf_size = atoll(argv[i + 1]);
            i++;
        }
        else if ((strcmp(argv[i], "--bench-input") == 0)) {
            if (i+1 >= argc) {
                fprintf(stderr, "Not enough arguments after -file, expected <file>.\n");
                show_usage(argv);
                exit(1);
            }
            global_benchfile_param = argv[i+1];
            i++;
        }
        // If present, we expect the two arguments to be <size> <iters>
        else if (got_numargs >= 2) {
            fprintf(stderr, "Extra arguments left over: ");
            for(; i < argc; i++) fprintf(stderr, "%s ", argv[i]);
            show_usage(argv);
            exit(1);
        } else {
            if (got_numargs == 0) {
                global_size_param  = atoll(argv[i]);
                got_numargs ++;
            } else {
                global_iters_param = atoll(argv[i]);
            }
        }
    }

    INITALLOC();
#ifdef BUMPALLOC
    //    save_alloc_state();
#endif
    __main_expr();

    return 0;
}

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
CursorCursorProd buildTree(CursorTy pvrtmp2, IntTy pvrtmp3);
Int64CursorProd sumTree(CursorTy in_cur);
PtrCursorProd unpack_Tree(CursorTy p12);
PtrTy print_Tree(CursorTy p23);
CursorCursorProd buildTree(CursorTy pvrtmp2, IntTy pvrtmp3)
{
    CursorTy lout272 = (CursorTy) pvrtmp2;
    IntTy i270 = (IntTy) pvrtmp3;
    IntTy b279 = i270 == (IntTy) 0;

    switch (b279) {

    case 0:
    {
        IntTy i273 = i270 - (IntTy) 1;
        CursorTy l274 = lout272 + (IntTy) 1;
        CursorCursorProd tmp_struct0 = buildTree(l274, i273);
        CursorTy pvrtmp6 = tmp_struct0.field0;
        CursorTy pvrtmp7 = tmp_struct0.field1;
        CursorTy x275 = (CursorTy) pvrtmp6;
        CursorTy end_x275 = (CursorTy) pvrtmp7;
        IntTy sizeof_x275 = end_x275 - x275;
        CursorTy l276 = l274 + sizeof_x275;
        CursorCursorProd tmp_struct1 = buildTree(l276, i273);
        CursorTy pvrtmp8 = tmp_struct1.field0;
        CursorTy pvrtmp9 = tmp_struct1.field1;
        CursorTy y277 = (CursorTy) pvrtmp8;
        CursorTy end_y277 = (CursorTy) pvrtmp9;

        *lout272 = 1;

        CursorTy writetag8 = lout272 + 1;
        CursorTy writecur9 = (CursorTy) end_x275;
        CursorTy writecur10 = (CursorTy) end_y277;
        CursorTy pvrtmp11 = (CursorTy) writecur10;
        CursorTy pvrtmp10 = (CursorTy) lout272;
        CursorTy a278 = (CursorTy) pvrtmp10;
        CursorTy end_a278 = (CursorTy) pvrtmp11;

        return (CursorCursorProd) {a278, end_a278};
        break;
    }

    default:
    {
        *lout272 = 0;

        CursorTy writetag3 = lout272 + 1;

        *(IntTy *) writetag3 = (IntTy) 1;

        CursorTy writecur4 = writetag3 + sizeof(IntTy);
        CursorTy pvrtmp5 = (CursorTy) writecur4;
        CursorTy pvrtmp4 = (CursorTy) lout272;
        CursorTy taildc0 = (CursorTy) pvrtmp4;
        CursorTy end_taildc0 = (CursorTy) pvrtmp5;

        return (CursorCursorProd) {taildc0, end_taildc0};
    }
    }
}
Int64CursorProd sumTree (CursorTy in_cur) {
    CursorTy lin = (CursorTy) in_cur;
    CursorTy tail = lin + sizeof(TagTyPacked);

    TagTyPacked tmpval = *lin;

    switch(tmpval) {
    case 0: {
        IntTy val = *(IntTy *) tail;
        CursorTy tail2 = tail + sizeof(IntTy);
        return (Int64CursorProd) {val, tail2};
    }
    case 1: {

        Int64CursorProd tmp_struct1 = sumTree(tail);
        IntTy vleft = tmp_struct1.field0;
        CursorTy end_left = tmp_struct1.field1;

        Int64CursorProd tmp_struct2 = sumTree(end_left);
        IntTy vright = tmp_struct2.field0;
        CursorTy end_right = tmp_struct2.field1;

        IntTy final = vleft + vright;

        return (Int64CursorProd) {final, end_right};
    }
    }
}
PtrTy print_Tree(CursorTy p23)
{
    TagTyPacked tag24 = *(TagTyPacked *) p23;
    CursorTy tail25 = p23 + sizeof(IntTy);

    switch (tag24) {

    case 0:
    {
        fputs("(Leaf ", stdout);

        IntTy val26 = *(IntTy *) tail25;
        CursorTy tail27 = tail25 + sizeof(IntTy);

        printf("%lld", val26);
        fputs(")", stdout);
        return tail27;
        break;
    }

    default:
    {
        fputs("(Node ", stdout);

        IntTy val28 = *(IntTy *) tail25;
        CursorTy tail29 = tail25 + sizeof(IntTy);
        CursorTy valcur31 = (CursorTy) val28;
        PtrTy temp30 = print_Tree(valcur31);

        fputs(" ", stdout);

        IntTy val32 = *(IntTy *) tail29;
        CursorTy tail33 = tail29 + sizeof(IntTy);
        CursorTy valcur35 = (CursorTy) val32;
        PtrTy temp34 = print_Tree(valcur35);

        fputs(")", stdout);
        return tail33;
    }
    }
}
void __main_expr()
{
    //
    CursorTy r279;
    CursorTy l280;
    r279 = (CursorTy) ALLOC_PACKED(global_default_buf_size);
    l280 = (CursorTy) r279;

    CursorCursorProd tmp_struct8;
    CursorTy tailapp1;
    CursorTy end_tailapp1;
    Int64CursorProd tmp_struct9;
    IntTy val;

    // criterion-interactive
    size_t input_size = 32;
    size_t input_len;
    IntTy iters;
    char* input     = (char *) malloc(input_size * sizeof(char));
    char* iters_str = (char *) malloc(input_size * sizeof(char));
    int i;

    // Indicate that we're ready to run benchmarks
    fprintf(stdout,"READY\n");
    fflush(stdout);

    // Read criterion `START_BENCH N`
    input_len = getline(&input,&input_size,stdin);


    while (strcmp(input,"EXIT\n") != 0) {

        // Extract the N ... len(START_BENCH) = 11
        strncpy(iters_str, input+11, input_len-11);
        iters = atoll(iters_str);

        // ***BENCHMARK***
        // Run the benchmark N times
        for(i = 0; i < iters; i++) {
            tmp_struct8 = buildTree(l280, (IntTy) global_size_param);
            tailapp1 = tmp_struct8.field0;
            /* end_tailapp1 = tmp_struct8.field1; */
            tmp_struct9 = sumTree(tailapp1);
            val = tmp_struct9.field0;
            /* printf("%lld\n",val); */
        }

        // Mark the end of 1 criterion run
        /* fprintf(stdout,"%lld\n",iters); */
        fprintf(stdout, "END_BENCH\n");
        fflush(stdout);

        // Recur
        input_len = getline(&input,&input_size,stdin);
    }

    return;
}
