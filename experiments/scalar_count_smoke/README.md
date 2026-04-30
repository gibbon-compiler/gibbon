# Scalar Count Smoke Experiments

This directory contains scripts and saved C sources for the manual SoA
scalar-count/vectorization experiments. The preserved C files live under:

```text
experiments/scalar_count_smoke/sources/
```

Those files are copies of the generated/manual smoke tests, kept here so the
experiments do not disappear when generated C files under
`gibbon-compiler/examples/soa_examples/programs/SOA/` are regenerated or
cleaned.

The main driver is:

```text
benchmark_scalar_count_smoke.py
```

It compiles one saved C source, runs the benchmark, validates that the variants
produce the same sum, and prints timing/speedup tables for these five variants:

1. recursive `add1`,
2. loopified `add1` with copied dead buffers and vectorization disabled,
3. loopified `add1` with indirections for dead buffers and vectorization disabled,
4. loopified `add1` with indirections for dead buffers and compiler auto-vectorization,
5. loopified `add1` with indirections for dead buffers and manual SIMD.

Benchmark-mode output also includes hot-loop timing tables pulled from the
manual C harnesses. For `--program list`, this reports the isolated counted
`Int` loop timings for scalar, auto-vectorized, and the selected manual SIMD
backend (`SSE2` by default, `AVX2` with `--use-avx2`). For `--program
multi-list`, it reports both total hot-loop timing across all `Int` fields and
per-field `ns/elem` summaries.

Example:

```text
python3 experiments/scalar_count_smoke/benchmark_scalar_count_smoke.py \
  --program list \
  --iterations 100 \
  --list-len 50000
```

For the multi-int smoke:

```text
python3 experiments/scalar_count_smoke/benchmark_scalar_count_smoke.py \
  --program multi-list \
  --iterations 100 \
  --list-len 8000 \
  --inner-iterations 10
```

`--program list` benchmarks `add1List` in `ScalarCountSmoke.c`.
`--program multi-list` benchmarks `add1MultiList` in
`ScalarCountMultiIntSmoke.c`.

The benchmark now uses SSE2 for the manual SIMD path by default. `--build poc`
is kept as an alias for the default `--build sse2`. Pass `--use-avx2` to switch
the manual SIMD path and compiler vectorization target to AVX2 while keeping
the same timing keys, tables, and sweep artifact structure.

The driver only passes `--inf-buffer-size` to the generated executable when you
specify it explicitly. If omitted, the executable uses its own default.
Benchmark-mode output reports this as `Chunk size: executable default`.

To generate a speedup graph across the default input sizes:

```text
python3 experiments/scalar_count_smoke/benchmark_scalar_count_smoke.py \
  --program list \
  --mode sweep \
  --iterations 20
```

For the default SSE2 backend this writes:

```text
experiments/scalar_count_smoke/results/list_speedups_sse2.csv
experiments/scalar_count_smoke/results/list_speedups_sse2.svg
experiments/scalar_count_smoke/results/list_hot_loop_speedups_sse2.csv
experiments/scalar_count_smoke/results/list_hot_loop_speedups_sse2.svg
experiments/scalar_count_smoke/results/list_runtimes_sse2.csv
experiments/scalar_count_smoke/results/list_runtimes_sse2.svg
```

The SVG plots input size on the x axis and speedup over recursive `add1` on the
y axis. The built-in default sweep sizes are:

```text
10000,50000,100000,250000,500000,1000000
```

For the multi-int smoke, use:

```text
python3 experiments/scalar_count_smoke/benchmark_scalar_count_smoke.py \
  --program multi-list \
  --mode sweep \
  --iterations 20 \
  --inner-iterations 5
```

Use `--sweep-sizes`, `--sweep-csv`, and `--sweep-svg` to customize the sweep.
Sweep mode emits three CSV/SVG artifact pairs:

1. end-to-end speedups,
2. hot-loop speedups,
3. end-to-end runtimes.

The hot-loop graph plots the overhead-adjusted hot-loop speedup of
auto-vectorized and manual SIMD loops over the scalar hot-loop baseline as
input size increases. Use `--hot-loop-sweep-csv` and `--hot-loop-sweep-svg` to
override those paths. Use `--runtime-sweep-csv` and `--runtime-sweep-svg` for
the runtime graph outputs.

Default sweep filenames now include the selected backend, for example:

```text
experiments/scalar_count_smoke/results/list_speedups_sse2.svg
experiments/scalar_count_smoke/results/list_hot_loop_speedups_avx2.svg
experiments/scalar_count_smoke/results/list_runtimes_sse2.svg
```
For evenly spaced input sizes, use the range form instead of `--sweep-sizes`:

```text
python3 experiments/scalar_count_smoke/benchmark_scalar_count_smoke.py \
  --program list \
  --mode sweep \
  --iterations 20 \
  --sweep-start 10000 \
  --sweep-step 10000 \
  --sweep-max 100000
```

The range includes `--sweep-max`; if the step does not land on it exactly, the
driver adds the max size as the final point.

Dense sweeps use sparse log-scale x-axis ticks, angled tick labels, and sampled
point markers so small step sizes remain legible in the generated SVG. The
plotter now chooses a linear or log x-axis automatically based on the sweep
distribution, every speedup SVG includes a solid red `1.0x` baseline, and the
hot-loop graph includes a theoretical SIMD-speedup reference line (`2.0x` for
SSE2, `4.0x` for AVX2).
