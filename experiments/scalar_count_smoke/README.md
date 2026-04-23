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
5. loopified `add1` with indirections for dead buffers and manual SSE2 SIMD.

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

The benchmark now uses SSE2 for the manual SIMD path. `--build poc` is kept as
an alias for the default `--build sse2`.

The driver only passes `--inf-buffer-size` to the generated executable when you
specify it explicitly. If omitted, the executable uses its own default.
Benchmark-mode output reports this as `Chunk size: executable default`.

To generate a speedup graph across input sizes up to 1 million:

```text
python3 experiments/scalar_count_smoke/benchmark_scalar_count_smoke.py \
  --program list \
  --mode sweep \
  --iterations 20
```

This writes:

```text
experiments/scalar_count_smoke/results/list_speedups.csv
experiments/scalar_count_smoke/results/list_speedups.svg
```

The SVG plots input size on the x axis and speedup over recursive `add1` on the
y axis. The default sweep sizes are:

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
