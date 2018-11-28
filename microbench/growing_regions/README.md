# Benchmarks for "Infinite" buffers

Instead of allocating a huge 4GB region, the compiler uses a linked list of small regions
which are allocated as required. The size of the region is doubled at every allocation
and remains constant after it reaches a certain limit.

The benchmark uses `buildTree` to construct a tree of depth `n`, and then runs `sumTree` on it.
The size of the first region was 64 KB and the upper bound was 2GB (configured via `rts.h`).
Only 1 benchmark, `buildTree(27)` hit that limit.


* `infinite.c` - Uses infinite buffers

* `infinite2.c` - Same as `infinite.c` except for minor changes. In particular, the region variables are passed
as a separate struct `RegionTy`.

* `buildtree.c` - Uses a single 4GB buffer


## Results

    $ make
    $ ./infinite.exe DEPTH bench  -- criterion-interactive mode
    $ ./infinite.exe DEPTH debug  -- just run it once


    $ ./buildtree.exe DEPTH 1     -- benchmark mode


The executable was generated without any optimization flags (i.e `-O1`).

The timing information for `buildTree` doesn't include the time required for allocating the 4 GB region.
It eventually leads to a segfault on `tank`. To be consistent, it is not measured in the "infinite" version as well.


* `infinite.c`

| Size | Infinite | BuildTree | %slowdown | Total Size    | INF_INIT_SIZE | #alloc |
|------|----------|-----------|-----------|---------------|---------------|--------|
| 5    | 2.536 μs | 2.610 μs  | -2.83     | 319           | 64 KB - 2GB   | 0      |
| 10   | 83.56 μs | 79.31 μs  | 5.35      | 10,239        | 64 KB - 2GB   | 0      |
| 15   | 2.997 ms | 2.452 ms  | 2.2       | 327,679       | 64 KB - 2GB   | 0      |
| 20   | 99.47 ms | 76.56 ms  | 29.9      | 10,485,759    | 64 KB - 2GB   | 8      |
| 25   | 2.928 s  | 2.485 s   | 17.8      | 335,544,319   | 64 KB - 2GB   | 13     |
| 26   | 5.923 s  | 4.963 s   | 19.34     | 671,088,639   | 64 KB - 2GB   | 14     |
| 27   | 12.24 s  | 9.815 s   | 24.7      | 1,342,177,279 | 64 KB - 2GB   | 15     |


* `infinite2.c`

| Size | Infinite2 | BuildTree | %slowdown | Total Size | INF_INIT_SIZE | #alloc |
|------+-----------+-----------+-----------+------------+---------------+--------|
|    5 | 2.39 μs   | 2.25 μs   |      6.23 |        319 | 64 MB         |      0 |
|   10 | 77.5 μs   | 73.9 μs   |      4.87 |      10239 | 64 MB         |      0 |
|   15 | 2.64 ms   | 2.69 ms   |     -1.85 |     327679 | 64 MB         |      0 |
|   20 | 85.3 ms   | 71.3 ms   |      19.6 |   10485759 | 64 MB         |      0 |
|   25 | 2.70 s    | 2.48 s    |       8.8 |  335544319 | 64 MB         |      3 |
|      |           |           |           |            |               |        |
