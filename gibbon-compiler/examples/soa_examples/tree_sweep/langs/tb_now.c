/* Monotonic nanoseconds, for the tree-sweep implementations whose language
 * has no nanosecond clock of its own (MLton, OCaml). */
#include <stdint.h>
#include <time.h>

int64_t tb_now_ns(void)
{
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC_RAW, &t);
    return (int64_t) t.tv_sec * 1000000000 + t.tv_nsec;
}

#ifdef TB_OCAML
#include <caml/mlvalues.h>
value tb_now_ns_ml(value unit)
{
    (void) unit;
    return Val_long(tb_now_ns());
}
#endif
