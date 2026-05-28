# Gibbon SoA Scalar-Buffer Count Context

## Current Snapshot

## Latest Handoff: Phase 1 Test Infrastructure Expansion In Progress (2026-05-27)

The current work is Phase 1 of the broader validation plan: expand the example
test matrix for the packed-layout optimization work without chasing unrelated
GC/pointer/interpreter failures.

### Scope For This Phase

Only these configurations are in scope:

- vanilla packed 64-bit baseline (`gibbon2`);
- packed 32-bit integer mode (`int32`);
- mutable-cursor loopification (`loopify`);
- loopification plus selective buffer sharing (`selective`);
- loopification plus selective sharing plus vectorization (`vectorize`);
- the same vectorized configuration with 32-bit integers
  (`int32-vectorize`).

GC-specific failures and other unrelated backend bugs are intentionally out of
scope for this phase.

### Test Runner Changes

`gibbon-compiler/tests/TestRunner.hs` now has named modes for the optimization
matrix:

- `GibbonInt32`
- `GibbonLoopify`
- `GibbonSelective`
- `GibbonVectorize`
- `GibbonInt32Vectorize`

The mode flags are:

```text
int32:
  --run --packed --int32

loopify:
  --run --packed --use-mutable-cursors
  --store-scalar-field-counts --enable-loopification

selective:
  loopify flags + --enable-selective-buffer-sharing

vectorize:
  selective flags + --enable-vectorization

int32-vectorize:
  vectorize flags + --int32
```

The runner also gained baseline-comparison support for layout/optimization
equivalence tests:

- `compare-with-baseline: true`
- optional `baseline-mode`
- optional `baseline-dir`
- optional `baseline-name`

When enabled, the runner compiles/runs a baseline program and compares each
requested mode against that output after stripping timing lines (`BATCHTIME`,
`SELFTIMED`) and normalizing whitespace. This is used to treat vanilla packed
AoS as the ground truth for SoA optimization tests.

I also fixed the runner's mode-precedence logic: per-test `run-modes` now
correctly override global YAML/CLI modes; otherwise global modes apply; otherwise
the runner falls back to `allModes`.

### YAML Test Matrix Changes

`gibbon-compiler/tests/test-gibbon-examples.yaml` now sets the global default
mode matrix to:

```yaml
run-modes: [gibbon2, int32, loopify, selective, vectorize, int32-vectorize]
```

Expected-failure lists that already included packed Gibbon modes were extended
with the new packed optimization modes so known non-optimization failures do not
become noise in this phase.

New entries were appended for:

- small vectorization-specific examples in `examples/vectorization/{AOS,SOA}`;
- paired SoA benchmark programs in
  `examples/soa_examples/programs/SOA`, compared against matching AOS sources;
- SoA-only smoke tests in `examples/soa_examples/programs/SOA`, compared against
  the same source compiled with vanilla packed Gibbon;
- layout benchmark examples under `examples/layout_benchmarks`.

The benchmark-sized SoA programs are currently restricted to 64-bit optimization
modes (`gibbon2`, `loopify`, `selective`, `vectorize`) because several compute
large sums that intentionally do not have the same result under 32-bit integer
overflow. The small vectorization tests cover both 64-bit and 32-bit
vectorization.

Known layout-benchmark bug reproducers named `*_bug` or `*_failing_*` are not in
the optimization matrix for this phase.

### New Vectorization Smoke Tests

Added small AoS/SoA pairs:

- `gibbon-compiler/examples/vectorization/AOS/VectorListMap.hs`
- `gibbon-compiler/examples/vectorization/SOA/VectorListMap.hs`
- `gibbon-compiler/examples/vectorization/AOS/VectorTreeMap.hs`
- `gibbon-compiler/examples/vectorization/SOA/VectorTreeMap.hs`

These are intentionally small so both 64-bit and 32-bit modes should produce the
same output.

Manual smoke validation performed:

```text
VectorListMap AoS baseline:       2272
VectorListMap SoA vectorized:     2272
VectorListMap SoA int32-vector:   2272
VectorTreeMap AoS baseline:       1216
VectorTreeMap SoA vectorized:     1216
VectorTreeMap SoA int32-vector:   1216
```

Build validation performed:

```text
cabal build test-gibbon-examples
cabal run test-gibbon-examples -- --help
```

Both succeeded after the test-runner edits.

### Update: Reduced Unit-Style Testing And Answer Files

The first pass used `compile-only: true` for benchmark-sized SoA/layout entries,
but that is not enough for runtime correctness. The runner now supports
`source-replacements`: exact source rewrites applied to a temporary copy under
`examples/build_tmp/reduced_sources/...`. This keeps benchmark sources untouched
while allowing the examples suite to execute reduced unit-sized variants.

For SoA benchmark-program tests in `examples/soa_examples/programs/SOA`, the
YAML now removes `compile-only`, references stored reduced answers under
`gibbon-compiler/examples/soa_examples/reduced_answers`, and adds reductions such
as:

- `100000000`, `10000000`, `1000000`, `100000`, `10000` -> `64`
- `mkTree 23`, `mkTree 15` -> depth `6`
- `mkMultiList 1000000`, `mkVList 1000`, `mkListA 3000` -> small sizes
- large `sizeParam + ...` builders -> small depths/counts
- large DomTree/OctTree direct builder depths -> smaller depths

Baseline and optimized modes both receive the same source reductions, so
`compare-with-baseline` remains a semantic output check against vanilla packed
AoS. Timing jitter is ignored by normalizing `BATCHTIME`, `SELFTIMED`, and
`ITER TIMES` lines.

Layout-benchmark entries that currently fail even in vanilla packed mode remain
skipped or expected-failing for the relevant mutable-cursor modes; those are
Phase 3 packed-field/mutable-cursor issues, not Phase 1 runtime optimization
checks.

The reduced runtime tests now have stored golden answers:

- `gibbon-compiler/examples/vectorization/VectorListMap.ans` -> `2272`
- `gibbon-compiler/examples/vectorization/VectorTreeMap.ans` -> `1216`
- `gibbon-compiler/examples/soa_examples/reduced_answers/*.ans` for the 31
  reduced SoA benchmark/smoke programs.

`TestRunner.hs` baseline-comparison mode now checks an optional `answer-file`
against the baseline output before comparing optimized mode outputs against the
baseline. The answer check is timing-normalized, so reduced benchmark answers do
not need to store unstable `BATCHTIME`, `SELFTIMED`, or `ITER TIMES` lines. This
gives the reduced tests both an AoS ground truth and a checked golden output.

`TestRunner.hs` also gained `compile-only` support. For compile-only tests it
uses `modeCFlags`, derived from the normal executable flags but replacing
`--to-exe` with `--toC`. This remains useful for examples whose vanilla baseline
does not yet compile/run.

Representative reduced-runtime validation performed manually for `List.hs`:

```text
AOS reduced List final value:            '#(2144 2144 64)
SoA vectorized reduced List final value: '#(2144 2144 64)
```

The only differences were timing lines, now covered by `isTimingLine`.

A scoped validation run was performed before the final answer-file change:

```text
GIBBONDIR=/workdisk/git/gibbon \
  cabal run test-gibbon-examples -- \
  --skip-failing --run-modes int32 \
  --test-summary-file /tmp/gibbon-phase1-int32-summary.txt -v 1
```

It completed in 105s after compile-only reduction. Result at that point:

```text
150 expected passes
1 unexpected pass: test_printpacked.hs in GibbonInt32
31 expected failures
6 unexpected failures:
  AnonLambdas.hs, NeedsClosure.hs, Reverse.hs, SS.hs, T64_1.gib,
  test18b_tupconstraint.gib in GibbonInt32
105 skipped
```

Those remaining int32 failures are outside the SoA/vectorization-specific test
entries and should be triaged only if the next phase chooses to broaden the
32-bit backend correctness effort.

### Remaining Phase 1 Work

- Run the expanded example matrix and triage only failures in the scoped
  optimization areas: SoA layout, mutable cursors, loopification, selective
  sharing, vectorization, 32-bit mode, and 32-bit vectorization.
- Improve the layout-testing story further. The current suite uses existing
  AOS/SOA source pairs where available and baseline comparison. The longer-term
  request is a smarter pre-processing path that can inject or rewrite layout
  annotations programmatically so factored/flat variants do not need duplicated
  source files.
- If full-suite runtime is too high because some benchmark sources use large
  hard-coded inputs, add a principled test-only source preprocessor or separate
  reduced-size examples rather than weakening output comparison.

## Latest Handoff: SIMD Vectorization Audit Complete For Annotated SoA Maps (2026-05-23)

This section supersedes the older SIMD prototype notes below. The vectorization
pass is now implemented and has been audited against the default
`gibbon_benchmark.py` programs that contain `OPT:CanVectorize` annotations.

### What Changed In This Round

`gibbon-compiler/src/Gibbon/Passes/VectorizeTraversals.hs` was generalized from
simple add/sub loops to a register-DAG vectorizer that now handles:

- multiple input scalar buffers in one expression DAG;
- multiple top-level scalar writes in one loop body;
- loop-fusion unit wrappers around several scalar-buffer loop bodies;
- invariant scalar expressions, including non-trivial expressions such as
  `k + 1`, by binding the scalar temporary before `VecBroadcast`;
- 64-bit `IntS` arithmetic: add, subtract, multiply, divide, and modulo;
- `FloatS` arithmetic: add, subtract, multiply, and divide;
- statement-level conditional scalar writes of the form:

```text
if cond then WriteScalar out a else WriteScalar out b
```

  when both branches write the same scalar cursor. The recognizer canonicalizes
  this only for analysis/vector code generation as a value-level select; the
  original scalar loop body remains the tail loop.

New explicit vector-register L3/L4 primitives were added:

- existing: `VecBroadcast`, `VecLoad`, `VecAdd`, `VecSub`, `VecMul`, `VecDiv`,
  `VecStore`;
- new: `VecMod`, `VecEq`, `VecSelect`.

The C backend lowers these through static inline helper functions in
`Codegen.hs`:

- `IntS`/64-bit uses 2-lane `__m128i` groups. A logical stride of 4 is still
  represented as two 2-lane groups.
- `FloatS` uses 4-lane `__m128` groups.
- `VecMul`, `VecDiv`, `VecMod`, and 64-bit equality are helper-lowered for
  64-bit integers because SSE2 does not provide native packed 64-bit integer
  multiply/divide/modulo/equality. This is correct for the prototype and keeps
  the IR general, but it should not be read as a peak-performance SIMD lowering.
- `VecSelect` uses mask-and/or selection for supported vector shapes.

The pass remains conservative: if a loop has scalar writes that cannot all be
represented by supported vector DAGs, that loop stays scalar.

### Validation Performed

Compiler build:

```text
cabal build exe:gibbon
```

Focused smoke tests:

- `SOA/VectorExprSmoke.hs` produced `'#(1009000 1018000)`.
- `SOA/VectorCrossFieldSmoke.hs` produced `'#(1018000 17000)`.
- Generated C for the smokes contains `gib_vec_load_*`, arithmetic helpers, and
  `gib_vec_store_*` inside the transformed loops.

No-loop-fusion audit over default annotated SoA benchmark programs:

- `Compiler.stripSideEffectsPass` vectorized
- `Compiler.targetRetunePass` vectorized
- `DBQuery.clearQueryFlags` vectorized
- `DBQuery.scaleCosts` vectorized
- `DomTree.scaleLayout` vectorized
- `List.add1` vectorized
- `MonoTree.add1Tree` vectorized
- `ObjectGraph.sweepUnmarked` vectorized
- `ObjectGraph.touchHotObjects` vectorized
- `OctTree_scaleEnergy.scaleEnergy` vectorized
- `OctTree_clearFlags.clearFlags` vectorized
- `PiecewiseFunctions.addConstPW` vectorized
- `PiecewiseFunctions.diffPW` vectorized
- `TernaryTree.add1Tree` vectorized
- `Trie.decayTrieStats` vectorized
- `Trie.resetTraversalState` vectorized

Loop-fusion-enabled audit produced the same vectorization coverage. In the
OctTree split-driver programs, imported sibling maps that are not called by that
specific driver may be absent from the generated C; those are reported as
`missing` by the audit script but are not failures for that benchmark.

Benchmark-harness smoke run:

```text
python3 gibbon_benchmark.py \
  --programs Compiler.hs DBQuery.hs DomTree.hs List.hs MonoTree.hs \
             ObjectGraph.hs OctTree_scaleEnergy.hs OctTree_clearFlags.hs \
             PiecewiseFunctions.hs TernaryTree.hs Trie.hs \
  --iterations 1 --warmup-runs 0 --cooldown-seconds 0 --clean \
  --store-scalar-field-counts \
  --enable-loopification \
  --enable-selective-buffer-sharing \
  --enable-loop-fusion \
  --enable-vectorization
```

Run from `gibbon-compiler/examples/soa_examples`. Result:

```text
DONE - 11/11 succeeded | 11/11 output matches
```

This checked AoS vs optimized SoA output equality through the benchmark script.

### Current Vectorization Limitations / Next Steps

- Integer `VecMul`/`VecDiv`/`VecMod` and integer equality are helper-lowered in
  SSE2 for correctness/general IR coverage. For performance, add AVX2/AVX512 or
  a better lowering strategy where hardware supports the operation.
- Conditional vectorization currently handles equality-based masks and same-cursor
  scalar writes. It does not yet handle arbitrary nested statement control flow,
  less-than/greater-than masks, boolean conjunction/disjunction masks, or
  branch bodies with side effects beyond the matched scalar write.
- Mixed-width condition/output cases are not fully generalized. Current audited
  benchmark conditionals are `IntS`-based.
- Reductions, gathers/scatters, math-library calls, casts, and true parent-child
  dependent traversals remain intentionally out of scope.
- Future TODO: keep `GibInt` 64-bit for now, but later test a 32-bit integer
  configuration where SIMD lanes and expected speedups are more favorable.
- Future TODO: add selectable vector backends. The IR is now explicit enough to
  lower the same vector DAGs to SSE2, AVX2, or AVX512 later.

## Latest Handoff: Loopification, Selective Sharing, Benchmarking, And SIMD Next Step (2026-05-18)

This older handoff remains useful for pipeline context, but the 2026-05-23
SIMD vectorization handoff above is now the latest state. Older "next step"
notes in this section may have since been completed or superseded.

### Live Compiler Pipeline State

The active packed pipeline around cursorized L3 is currently:

```text
cursorize
-> reorderScalarWrites
-> loopifyFlatTraversals        -- AoS / flat heterogeneous layout
-> loopifyTraversals            -- fully factored SoA layout
-> propagateScalarCounts        -- preserve footer metadata across producers
-> selectiveBufferSharing       -- SoA loopified maps only, opt-in
-> fuseLoopifiedTraversals      -- SoA scalar-loop fusion, opt-in
-> vectorizeTraversals          -- SoA SIMD vectorization, opt-in
-> L3.flatten
-> L3.typecheck
-> hoistNewBuf
-> L3.typecheck
-> unariser / lower / codegen ...
```

Relevant implementation files:

- `gibbon-compiler/src/Gibbon/Passes/LoopifyFlatTraversals.hs`
  - flat AoS map loopification;
  - walks one heterogeneous packed buffer from input start to packed-value end;
  - does not use scalar-count footers, selective sharing, loop fusion, or SIMD.

- `gibbon-compiler/src/Gibbon/Passes/LoopifyTraversals.hs`
  - fully factored SoA loopification for `OPT:CanVectorize` map traversals;
  - emits chunk loops and inner counted field loops;
  - consumes cyclic footer metadata for per-chunk loop bounds;
  - copies the dcon stream from input rather than synthesizing constructor tags;
  - supports loop-invariant scalar arguments, same-shape conditional writes,
    cross-buffer scalar dependencies, multi-chunk walking, and output footer
    count maintenance.

- `gibbon-compiler/src/Gibbon/Passes/ScalarCountPropagation.hs`
  - copies footer-count metadata from source SoA buffers to destination SoA
    buffers after materialized shape-preserving producer calls;
  - fixes pipelines where a non-loopified producer, such as `computeWidths`,
    feeds a later loopified consumer, such as `scaleLayout`.

- `gibbon-compiler/src/Gibbon/Passes/SelectiveBufferSharing.hs`
  - post-loopification SoA-only pass;
  - shares copied/dead buffers with a single selective-indirection wrapper;
  - normalizes selective wrappers at consumer call sites rather than at
    recursive function entries;
  - hoists normalization outside `TimeIt` where applicable so measured traversal
    time does not include wrapper cleanup.

- `gibbon-compiler/src/Gibbon/Passes/LoopifiedTraversalFusion.hs`
  - SoA-only post-sharing pass;
  - fuses remaining loopified scalar-buffer loops by constructor group;
  - relies on the fully factored SoA invariant that redirection boundaries are
    aligned across peer buffers for the same logical value.

- `gibbon-compiler/src/Gibbon/Passes/VectorizeTraversals.hs`
  - opt-in SIMD nano-pass behind `--enable-vectorization`;
  - runs after selective sharing and after optional loop fusion;
  - conservatively recognizes loopified scalar-buffer vector DAGs in
    `OPT:CanVectorize` functions, including supported arithmetic, invariant
    broadcasts, multi-input expressions, and equality/select conditionals;
  - rewrites only exact supported loops into explicit vector-register L3 ops
    (`VecBroadcast`, `VecLoad`, `VecAdd`, `VecSub`, `VecMul`, `VecDiv`,
     `VecMod`, `VecEq`, `VecSelect`, `VecStore`) plus a scalar tail loop;
  - leaves unsupported loops unchanged.

### Current Flag Semantics

The confusing old `--SoA` / `Opt_Packed_SoA` flag has been removed. Layout is
chosen by source annotations on datatype definitions:

- `ANN type T "Linear"` means flat AoS / linear layout.
- `ANN type T "FullyFactored"` means fully factored SoA layout.

Optimization flags are one-way opt-in flags:

- `--enable-loopification`
  - enables map loopification;
  - AoS gets flat heterogeneous while-loop traversal;
  - SoA gets per-buffer chunk/for traversal when count metadata is available.

- `--store-scalar-field-counts`
  - required for SoA loopification because SoA loop bounds come from footer
    metadata;
  - not needed for AoS loopification and the benchmark harness does not pass it
    to AoS variants.

- `--enable-selective-buffer-sharing`
  - SoA-only;
  - applies after loopification;
  - shares dcon/copied scalar buffers through selective-indirection wrappers.

- `--enable-loop-fusion`
  - SoA-only;
  - applies after selective sharing;
  - fuses remaining scalar loops by constructor group.

- `--enable-vectorization` / `--vectorize-traversals`
  - SoA SIMD target;
  - applies after selective sharing and after loop fusion when fusion is enabled;
  - currently vectorizes clearly supported loopified scalar-buffer arithmetic DAGs;
  - unsupported loops are intentionally left as scalar loopified code.

Current conceptual split:

```text
AoS / flat linear:
  maps can be loopified by walking one heterogeneous buffer;
  no scalar-count footers needed;
  no selective buffer sharing;
  no loop fusion;
  SIMD is not the main target because data is heterogeneous.

Fully factored SoA:
  maps can be loopified over homogeneous buffers;
  scalar-count footer metadata supplies O(1) per-chunk loop bounds;
  selective buffer sharing can remove copied/dead buffers;
  loop fusion can reduce loop overhead for remaining mutated buffers;
  SIMD vectorization can operate over homogeneous scalar buffers after sharing;
  this is the SIMD-friendly representation.
```

### Current Representation / Metadata Invariants

The scalar-count/footer work is now used as runtime loop-bound metadata for SoA
buffers. The important invariant for future vectorization is:

- the end-of-region/footer for a buffer stores the count for that buffer's first
  chunk;
- each redirection/chunk-boundary footer stores the count for the next chunk;
- therefore a traversal can get the first chunk count in O(1) from the input end
  footer and later chunk counts in O(1) from the preceding boundary footer;
- loopified shape-preserving maps copy/set output footer counts once per chunk,
  not once per element.

For SoA loopification, the generated code shape is intentionally:

```text
while chunks remain:
  read chunk count from footer metadata
  for i in 0 .. count-1:
    run scalar operation(s) over homogeneous field buffers
  advance input/output cursors and footer cursors
```

Selective sharing happens before loop fusion so copied/dead buffers can be
removed entirely before remaining loops are grouped.

### Historical SIMD Vectorization Prototype State (2026-05-19; Superseded)

This section records the earlier prototype. The current vectorization state is the 2026-05-23 handoff above.

The first compiler-driven SIMD path now uses explicit vector-register IR instead
of a high-level semantic map primitive.  This supersedes the earlier
`SimdMapAddConst` prototype.

Implemented compiler pieces:

- Shared language type support:
  - `UrTy` now has `SimdTy element_ty lanes`;
  - L3/L4 conversion, pretty-printing, cursorization type plumbing, and C
    codegen know about this internal register type.

- L3 IR now has explicit vector primitives:
  - `VecBroadcast Scalar lanes value`;
  - `VecLoad Scalar lanes cursor_ref`;
  - `VecAdd Scalar lanes lhs rhs`;
  - `VecSub Scalar lanes lhs rhs`;
  - `VecMul Scalar lanes lhs rhs`;
  - `VecStore Scalar lanes cursor_ref value`.

- L4 IR has matching backend primitives.

- The C backend lowers the current supported register shapes to SSE/SSE2 helper
  calls emitted as static inline C helpers:
  - `IntS` / `SymS`, 2 lanes, `__m128i`;
  - `FloatS`, 4 lanes, `__m128`;
  - `CharS` / `BoolS`, 16 lanes, `__m128i` byte operations;
  - helper names have the form `gib_vec_{broadcast,load,add,sub,mul,store}_...`.
  - `VecMul` is currently emitted only for `FloatS` because SSE2 has no general
    64-bit integer multiply.

- `VectorizeTraversals.hs` now rewrites supported scalar loop bodies by first
  extracting parallel expression DAGs:

  ```text
  leaves:
    scalar reads from one or more input buffer cursor refs
    loop-invariant scalar expressions, broadcast to vector registers

  internal nodes:
    supported arithmetic ops, currently Add/Sub for Int/Sym/Char/Bool/Float
    and Mul for Float
  ```

  The pass is deliberately whole-loop conservative: if a `ForE` contains multiple
  top-level scalar writes, every write must be represented by a supported DAG or
  the loop is left unchanged. This avoids vectorizing one field while silently
  dropping another field into only the scalar tail. The matcher also flattens
  unit-valued wrappers introduced by loop fusion for recognition, while keeping
  the original scalar body as the tail loop.

  The generated loop shape is:

  ```text
  vec_count  = scalar_count / stride
  tail_count = scalar_count % stride
  broadcast loop-invariant leaves once before the vector loop

  for _ in 0 .. vec_count-1:
    VecLoad each needed input cursor ref
    bump each input cursor ref by vector bytes
    evaluate each vector DAG into vector registers
    VecStore each output cursor ref result
    bump each output cursor ref by vector bytes
    ...repeat once more for 64-bit Int/Sym to cover stride 4...

  for _ in 0 .. tail_count-1:
    original scalar loop body
  ```

  This preserves the existing 64-bit `GibInt` ABI.  For 64-bit `IntS` / `SymS`,
  stride 4 is represented as two 2-lane SSE2 groups.  For `FloatS`, stride 4 is
  represented as one 4-lane SSE group.  Byte-sized `CharS` / `BoolS` vector
  primitives are available as 16-lane SSE2 register operations.

- The retired high-level `SimdMapAddConst` IR/backend primitive has been removed
  from the compiler source; the remaining SIMD surface is register-oriented.

Validated target:

- `SOA/List.hs` with `add1` under:
  `--packed --to-exe --use-mutable-cursors --store-scalar-field-counts --enable-loopification --enable-selective-buffer-sharing --enable-vectorization --no-ran`.
- Generated C contains vector-register helper calls such as
  `gib_vec_broadcast_int64x2`, `gib_vec_load_int64x2`,
  `gib_vec_add_int64x2`, and `gib_vec_store_int64x2`.
- A temporary small copy with `mkList 1000` produced the expected result
  `'#(501500 501500 1000)`.

- `SOA/VectorExprSmoke.hs` validates a more general vector DAG:
  - field 0 computes `(i + k) + (i + 3)`, using the input vector twice;
  - field 1 computes `(j - k) + (j + 2)`, using both vector subtraction and
    vector addition;
  - generated C contains `gib_vec_sub_int64x2` and multiple vector-register DAG
    temporaries;
  - the executable produced `'#(1009000 1018000)`.

- `SOA/VectorCrossFieldSmoke.hs` validates multi-input DAGs:
  - field 0 computes `i + (j + k)` from two input scalar buffers plus a
    loop-invariant argument;
  - field 1 computes `(j - i) + k`;
  - with loop fusion disabled and enabled, generated C contains vector loads from
    multiple cursor refs, `gib_vec_add_int64x2`, `gib_vec_sub_int64x2`, and
    vector stores for both output fields;
  - the executable produced `'#(1018000 17000)`.

Current limitations / next steps:

- The recognizer handles pure arithmetic DAGs over scalar buffer reads and
  loop-invariant scalar expressions.
- It does not yet vectorize conditionals inside the scalar expression,
  comparisons, casts, math-library calls, reductions, gathers/scatters, or mixed
  scalar widths in one loop.
- It currently hoists broadcasts for loop-invariant leaves, but does not CSE
  duplicate invariant expressions across different output DAGs.
- Next steps: validate tree maps, add richer expression forms, and then run the
  broader benchmark suite with vectorization enabled.
- Future TODO: evaluate a 32-bit `GibInt` configuration.  The current prototype
  deliberately keeps `GibInt` 64-bit.
- Future TODO: add selectable SIMD backends, likely SSE2 first-class today,
  AVX2 stride-8 for 32-bit / stride-4 for 64-bit, and eventually AVX512.


### Current Benchmarking And Reporting State

Benchmark scripts have been updated to reduce noise and make uncertainty easier
to read:

- `gibbon-compiler/examples/soa_examples/gibbon_benchmark.py`
  - default timed iterations are now `20`;
  - supports untimed warmups via `--warmup-runs` and `--warmup-iterations`;
  - supports configurable cooldowns via `--cooldown-seconds`;
  - reports median, mean, and a two-sided 95% confidence interval for the mean;
  - console and text report output now include `median`, `mean`, `95%CI`,
    `min`, `max`, and sample count where useful;
  - benchmark command construction respects the AoS/SoA split: scalar counts,
    selective sharing, loop fusion, and vectorization are passed only to SoA
    variants.

- `benchmark_layout_versions.py`
  - top-level driver for side-by-side version comparison;
  - runs these variants:
    - AoS non-mutable recursive,
    - AoS mutable recursive,
    - AoS mutable loopified,
    - SoA non-mutable recursive,
    - SoA mutable recursive,
    - SoA mutable loopified,
    - SoA mutable loopified + selective sharing;
  - forwards warmup/cooldown/iteration options to `gibbon_benchmark.py`;
  - writes both `layout_version_comparison.txt` and
    `layout_version_comparison.md`;
  - runtime tables now expand each program/pass into clean sub-rows:
    `median`, `mean`, and `error`, where `error` is the 95% CI;
  - `n=...` was intentionally removed from cells to keep tables readable;
  - in the Markdown report only, map pass entries are visually marked:
    - `SoA mut loopified`: dotted blue border;
    - `SoA mut loop+share`: solid purple border;
  - total rows and fold rows are not bordered, so the visual emphasis is only
    on map optimizations.

The current `layout_version_comparison.md` was regenerated from the existing
JSON in `layout_version_benchmark_output/`; it was not a fresh full benchmark
rerun. For a fresh publication-style comparison run:

```bash
python3 benchmark_layout_versions.py \
  --clean \
  --iterations 30 \
  --warmup-runs 1 \
  --warmup-iterations 1 \
  --cooldown-seconds 3 \
  --verbose
```

For quick smoke/debug runs, lower the iterations and disable warmup, e.g.:

```bash
python3 benchmark_layout_versions.py \
  --programs List.hs MonoTree.hs \
  --iterations 2 \
  --warmup-runs 0 \
  --cooldown-seconds 0 \
  --verbose
```

### Latest Validation Known In This Handoff

Recently checked during the benchmark/reporting updates:

```text
python3 -m py_compile benchmark_layout_versions.py
python3 -m py_compile gibbon-compiler/examples/soa_examples/gibbon_benchmark.py
```

A small `gibbon_benchmark.py` smoke on `LinearListReduction.hs` also succeeded
with CI output in the console and report. The larger layout comparison report
was regenerated from existing JSON, not rerun from scratch.

Older compiler validation notes below include successful focused checks for:

- `cabal build exe:gibbon -j1`;
- `cabal run test-gibbon` / targeted pass tests;
- DomTree scalar-count propagation;
- PiecewiseFunctions loopification;
- DBQuery selective sharing and unwrap placement;
- full or partial benchmark sweeps at earlier checkpoints.

Before making performance claims from the current code, rerun
`benchmark_layout_versions.py --clean` so the JSON, Markdown, and text reports
all come from one fresh automated run.

### Current Known Limitations

- Older note: `VectorizeTraversals.hs` used to be unimplemented; it is now implemented as described in the 2026-05-23 handoff above.
- SoA loopification is still conservative; unsupported non-map traversals remain recursive.
- Selective sharing is opt-in and still experimental, though the current design
  is call-site normalized rather than recursive-entry normalized.
- Loop fusion is opt-in and should remain separable for correctness/performance
  comparisons.
- Existing CI/error calculations are based on the executable's timed samples;
  if we later want stronger statistics, add process-level repetitions in
  addition to in-process `--iterate` samples.
- The generated scalar loops are correctness-oriented. Some remaining overheads
  are expected until SIMD/vectorization and further code cleanup land.

### Older Superseded Plan: SIMD For Fully Factored Loopified Maps

The next substantial compiler step should be SIMD vectorization for fully
factored SoA maps after loopification, selective sharing, and optionally loop
fusion. The reason to run it late is that selective sharing removes dead/copy
buffers and fusion exposes the final hot loops over the remaining mutated
homogeneous buffers.

Recommended implementation direction:

1. Keep SIMD separate from loopification and selective sharing.
   Implement it in `Gibbon.Passes.VectorizeTraversals`, not inside
   `LoopifyTraversals`.

2. Start with the final loopified SoA shape:

```text
WhileCursor/chunk loop
  ScalarCountSet / footer maintenance
  ForE loop over chunk count
    scalar loads from one or more homogeneous input buffers
    pure scalar primitive operation
    scalar store to homogeneous output buffer
```

3. First SIMD target should be simple, local scalar maps:

```text
out[i] = in[i] + constant
out[i] = in[i] * invariant
out[i] = f(in1[i], in2[i], scalar_invariant)
```

Where all vectorized buffers are:

- fully factored SoA scalar buffers;
- same constructor group / same chunk count;
- contiguous within the chunk;
- not selectively shared;
- already in a loopified map pass.

4. Add explicit IR/codegen support rather than relying entirely on C compiler
   auto-vectorization. A conservative first target is SSE2 for `GibInt` because
   earlier manual experiments showed AVX2 was not automatically better for the
   end-to-end benchmark mix. AVX2 can be a later backend flag.

5. Required lowering/codegen pieces will likely include:

- vector load from scalar buffer cursor;
- vector splat/broadcast for loop-invariant constants;
- vector arithmetic primitive(s), initially add/mul/sub for integer scalars;
- vector store to output buffer cursor;
- scalar remainder loop for `count % vector_width`;
- feature gating for SSE2/AVX2 C intrinsics.

6. Validation plan for SIMD:

- unit tests over generated IR shape: vector pass fires only on valid loopified
  SoA map loops;
- generated C inspection for representative maps;
- correctness comparisons with SIMD off/on for:
  - `List.add1`,
  - `MonoTree.add1Tree`,
  - `TernaryTree.add 1 tree`,
  - `DBQuery.scaleCosts` / `clearQueryFlags`,
  - `OctTree_scaleEnergy`,
  - `PiecewiseFunctions.addConstPW` and `diffPW`;
- benchmark comparisons using `benchmark_layout_versions.py --clean` and the
  manual experiments under `experiments/scalar_count_smoke/` as intuition, not
  as compiler truth.

7. Keep the performance questions separate:

- loopification speedup vs recursive backend;
- selective sharing speedup from removing copy/dead buffers;
- loop fusion speedup from reducing per-buffer loop overhead;
- SIMD speedup within the hot inner loop;
- end-to-end program speedup after all overheads.

This separation matters because earlier manual C experiments showed that a
vectorized inner loop can improve locally while end-to-end speedup is smaller
when chunk walking, copying, allocation, or benchmark overhead dominates.

The latest handoff above is the current source of truth. The sections below preserve implementation history and may describe older or superseded per-tag-slot, per-field, and pass-order designs.

## Scalar Count Propagation Update (2026-05-16)

This entry documents the current solution for preserving scalar-count footer
metadata across pipelines of packed SoA values. It supersedes the older idea
that every intermediate producer/map must be annotated with
`OPT:StoreScalarCounts`.

### Motivation

The bug that exposed this was `DomTree`: `computeWidths` is shape-preserving
but not loopifiable because it has a parent-child dependency. Its output is
then consumed by `scaleLayout`, which is loopified and therefore reads chunk
bounds from scalar-count footer metadata. Before this fix, `computeWidths`
could produce a fresh packed output whose footer counts were missing unless it
was manually annotated with `OPT:StoreScalarCounts`. That was the wrong
abstraction: once a packed SoA buffer has valid footer counts, those counts
should remain part of the packed value as it is copied or shape-preservingly
rewritten into fresh output buffers.

### Current Design

The implementation now uses an explicit footer-chain propagation primitive:

```text
ScalarCountCopyAll Int dstEnds srcEnds
```

Meaning:

- `Int` is the SoA cursor-array length.
- `dstEnds` is the output end-cursor array.
- `srcEnds` is the input end-cursor array.
- The runtime copies count metadata buffer-by-buffer from the source footer
  chains to the destination footer chains.

Complexity:

```text
O(number_of_buffers * number_of_chunks)
```

The helper walks footer chains only. It does not scan scalar payloads,
constructor tags, or individual elements.

Selective buffer sharing remains naturally compatible with this design. A
selectively shared output buffer points at an input buffer that already has
valid counts, so no count copy is needed for that shared buffer.

### Implementation Locations

Compiler syntax and checking:

- `gibbon-compiler/src/Gibbon/L3/Syntax.hs`
  - adds `ScalarCountCopyAll Int Var Var`
  - wires free variables, type recovery, substitution, and renaming
- `gibbon-compiler/src/Gibbon/L3/Typecheck.hs`
  - checks both cursor arrays have type `CursorArrayTy len`
- `gibbon-compiler/src/Gibbon/L4/Syntax.hs`
  - adds target primitive `ScalarCountCopyAll Int`
- `gibbon-compiler/src/Gibbon/Passes/Lower.hs`
  - lowers L3 `ScalarCountCopyAll` to the L4 primitive
  - treats it as effectful/impure
- `gibbon-compiler/src/Gibbon/Passes/Codegen.hs`
  - emits:

```c
gib_scalar_count_copy_all(dstEnds, srcEnds, len);
```

Runtime support:

- `gibbon-rts/rts-c/gibbon_rts.h`
  - declares:
    - `gib_scalar_count_copy_chain`
    - `gib_scalar_count_copy_all`
- `gibbon-rts/rts-c/gibbon_rts.c`
  - implements footer-chain copying
  - oldgen case walks `reg_info->first_chunk_footer` and follows `next`
  - nursery case copies the available single footer metadata directly
  - debug builds report a source/destination chunk-count mismatch if footer
    chains have different lengths

Compiler pass:

- `gibbon-compiler/src/Gibbon/Passes/ScalarCountPropagation.hs`
  - new L3 nano-pass
  - enabled only when `--store-scalar-field-counts` is enabled
  - conservatively recognizes simple fully-factored SoA producer ABI:
    `input ends`, `output ends`, `output cursors`, `input cursors`
  - skips functions that already write scalar-count metadata
  - does not rewrite recursive function bodies, avoiding repeated
    O(chunks) propagation at recursive self-calls
  - inserts the copy after materialized producer calls in pipeline-level code
    such as `gibbon_main`

Pipeline:

- `gibbon-compiler/src/Gibbon/Compiler.hs`
  - pass order is now:

```text
cursorize
-> reorderScalarWrites
-> loopifyTraversals
-> propagateScalarCounts
-> selectiveBufferSharing
-> fuseLoopifiedTraversals
```

Build/test registration:

- `gibbon-compiler/gibbon.cabal`
  - exposes `Gibbon.Passes.ScalarCountPropagation`
  - registers `tests/ScalarCountPropagation.hs`
- `gibbon-compiler/tests/Main.hs`
  - includes the new test group
- `gibbon-compiler/tests/ScalarCountPropagation.hs`
  - verifies:
    - propagation is disabled by default
    - one footer-copy primitive is inserted after a producer call when counts
      are enabled
    - recursive producer bodies are not rewritten

Source annotation cleanup:

- `gibbon-compiler/examples/soa_examples/programs/SOA/DomTree.hs`
  - removed `OPT:CanVectorize` from `computeWidths`
  - reason: `computeWidths` has parent-child dependencies and is not a true
    vectorizable/loopifiable map
  - no `OPT:StoreScalarCounts` annotation was added to `computeWidths`; count
    preservation is handled by propagation instead

### Validation

Focused validation completed after this change:

```text
cabal build exe:gibbon -j1
cabal run test-gibbon
```

Result:

```text
All 62 tests passed
```

DomTree direct validation:

```text
GIBBONDIR=/workdisk/git/gibbon cabal run gibbon -- \
  --packed --to-exe --use-mutable-cursors \
  --store-scalar-field-counts \
  --cfile /tmp/DomTree_scalar_count_prop.c \
  --exefile /tmp/DomTree_scalar_count_prop.exe \
  examples/soa_examples/programs/SOA/DomTree.hs

/tmp/DomTree_scalar_count_prop.exe --iterate 1
```

Result:

```text
'#(42278584320 230 1052688 2348810240 5284823040 21139292160)
exit=0
```

Generated C sanity check:

- `/tmp/DomTree_scalar_count_prop.c` contains:

```c
gib_scalar_count_copy_all(reg_cursor_ptr_13635, reg_cursor_ptr_13398, 14);
```

- The copy is emitted after the top-level `computeWidths(...)` call.
- It is not emitted inside recursive `computeWidths` self-calls.

Benchmark-driver smoke:

```text
cd gibbon-compiler/examples/soa_examples
python3 gibbon_benchmark.py \
  --programs DomTree.hs \
  --iterations 1 \
  --clean \
  --store-scalar-field-counts \
  --enable-loopification \
  --output-dir /tmp/gibbon_benchmark_scalar_count_prop
```

Result:

```text
DONE - 1/1 succeeded | 1/1 output matches
```

The DomTree AoS and SoA outputs matched. This specifically resolves the
previous DomTree loopification crash caused by missing count metadata after
the non-loopified `computeWidths` producer.

### Current Caveats

The propagation pass is intentionally conservative:

- It currently recognizes the simple one-input/one-output SoA cursor-array ABI.
- It does not yet perform whole-program dataflow to prove count validity.
- It does not rewrite recursive bodies; this avoids repeated metadata-chain
  copies but means recursive internal producer calls are not individually
  annotated.
- General multi-input producers will need an explicit buffer-to-buffer mapping
  before this should be extended.

This is the correct first step for the current benchmark pipeline shape:
builders establish counts, non-loopified shape-preserving producers preserve
them at materialization boundaries, loopified traversals consume and maintain
them chunk-by-chunk, and selective sharing simply points at already-counted
input buffers.

## Loopification Effort Status (2026-05-14)

This section summarizes the `OPT:CanVectorize` loopification effort as of
2026-05-14. For scalar-count propagation details, trust the newer
`Scalar Count Propagation Update (2026-05-16)` section above.

### Current Implementation

The compiler now has a real loopification path for a useful class of
fully-factored SoA map traversals:

- pass: `Gibbon.Passes.LoopifyTraversals`
- placement: after `reorderScalarWrites` in the L3 pipeline
- trigger: functions marked `OPT:CanVectorize`
- required flags: `--enable-loopification`; for fully factored SoA, also `--store-scalar-field-counts`
- optional follow-on flag: `--enable-loop-fusion` / `--loop-fusion`
- layout restriction: fully factored SoA only
- IR shape: outer chunk `WhileCursor`, inner counted `ForE`
- bounds source: cyclic scalar-count footer metadata

Rejected candidates are left unchanged. This is important: the pass is meant
to be conservative while the optimization is still being generalized.

### Current Invariants

The pass now relies on the following invariants. These are also documented in
comments in `gibbon-compiler/src/Gibbon/Passes/LoopifyTraversals.hs`.

1. `OPT:CanVectorize` is the user promise that recursive calls are independent.
   The pass still rejects obvious parent-child dependencies syntactically: if
   a value derived from a recursive self-call is used by a parent write,
   conditional, or case scrutinee, the function remains recursive.

2. The cursor ABI is inferred, not matched by fixed argument positions.
   The accepted ABI has four cursor arrays of the expected SoA length:
   input ends, output ends, output cursors, and input cursors. Extra scalar
   arguments are loop-invariant values and may appear in scalar update
   expressions.

3. Buffer 0 is the dcon/tag stream. Scalar buffers are discovered from the
   fully-factored `DDef` by walking constructors and scalar fields in layout
   order, skipping packed recursive fields.

4. Each scalar output buffer may be written at most once per constructor
   branch. The write must target the buffer for that constructor field, and
   the scalar type must match the field type.

5. Scalar update expressions must be pure and may mention only scalar inputs
   from the same constructor instance or loop-invariant scalar arguments.
   Cross-constructor dependencies are rejected.

6. Conditional scalar updates are allowed when both arms write the same set of
   constructor/field buffers. The generated loop emits unit-valued write
   branches rather than scalar-valued `if` expressions, because loop bodies
   lower as unit tails.

7. Cross-buffer scalar dependencies use separate dependency cursors initialized
   from the original input cursor arrays. They do not reuse another buffer
   loop's main cursor, because that cursor may already have advanced.

8. Scalar buffers are fused by constructor group. One representative scalar
   buffer supplies the chunk count, and the inner `ForE` performs the
   operations for every scalar field buffer belonging to that constructor.
   This relies on the fully-factored SoA invariant that redirection
   boundaries are aligned across buffers: when any buffer grows, the peer
   buffers receive corresponding redirections. The first chunk count comes
   from the end-of-region footer; later chunk counts come from redirection
   boundary footers using the cyclic next-chunk-count invariant.

9. The dcon stream is copied from the input tag buffer. The pass does not
   synthesize tags or assume list/tree-specific constructor ordering.

10. Loopified maps write scalar-count metadata for their output buffers.
    This is required so chained loopified maps can read valid footer counts
    from the result of the previous map.

11. Shape-preserving loopified maps set output footer counts once per chunk,
    not once per element. The first implementation used per-element
    `ScalarCountBump` in every generated loop, which made simple tree maps
    slower than the recursive SOA backend. The current implementation uses a
    `ScalarCountSet` primitive to copy the input chunk count to the
    corresponding output footer in O(chunks) metadata work.

### Important Fixes Now Landed

1. Real L3 loop constructs were introduced and wired through typechecking,
   lowering, and C code generation.

2. Mutable-cursor and non-mutable-cursor loopification both work. The mutable
   path is unit-returning; the non-mutable path uses local mutable cursor refs
   internally and reconstructs the expected returned cursor arrays.

3. Multi-chunk loop walking is implemented using cyclic scalar-count footers.

4. The dcon copy path was fixed to read tags from the input tag stream instead
   of hardcoding constructor tags.

5. `scaleEnergy` was fixed. Its update for one field depends on another scalar
   field buffer. The pass now gives such cross-buffer dependencies their own
   cursors and advances those cursors across chunk boundaries independently.

6. `PiecewiseFunctions.diffPW` now loopifies. The additional invariant needed
   here was support for same-shape conditional scalar writes.

7. Chained loopified maps now work. The bug was that a loopified map wrote a
   fresh packed value but did not populate scalar-count footer metadata for
   that output. The loopified path now emits `ScalarCountSet` for dcon and
   scalar buffers once per chunk.

8. The selective-buffer-sharing design was corrected. It should happen after
   loopification as an `L3 -> L3` pass. The earlier recursive L2 approach was
   abandoned because one-shot whole-buffer sharing is not principled for
   recursive traversals that still need to walk the dcon stream.

9. The tree-map runtime regression was traced to per-element output
   scalar-count bumps in loopified maps. Since these maps preserve shape, the
   output chunk counts are exactly the input chunk counts. The pass now emits
   one `ScalarCountSet` per output buffer chunk instead of one
   `ScalarCountBump` per output element.

10. Loop fusion for scalar buffers is now implemented. The pass emits one
    scalar chunk loop per constructor group instead of one loop per scalar
    buffer. The dcon/tag stream remains a separate loop because its footer
    count is the total number of tags in the chunk, not the count of any one
    constructor.

11. Loop fusion is an independent opt-in pass enabled with
    `--enable-loop-fusion` / `--loop-fusion`. Leaving it off keeps the
    loopified chunk/for structure but preserves the one-loop-per-scalar-buffer
    baseline for correctness and performance comparisons.

12. Selective-buffer-sharing unwraps are now call-site normalization, not
    function-entry checks. The pass records which loopified producers wrote
    selective wrappers, then rewrites later consumer calls so copied SoA input
    cursor arrays are unwrapped before the call. This deliberately handles the
    benchmark shape where a consumer argument is an inline cursor-array copy:
    `let copy = InitCursor; MemCpy copy start; copy`. Recursive folds such as
    `sumCost` must not contain `gib_unwrap_selective_indirections` at entry,
    because that would repeat the wrapper check at every recursive call.
    These normalization binds are hoisted outside `TimeIt` when the timed body
    is a direct traversal call or starts with a let-bound traversal call, so
    benchmark timings do not include the selective-wrapper cleanup.

### Validation Snapshot

Most recent focused validation:

- `cabal build exe:gibbon -j1`: passed
- `cabal run exe:gibbon -- --help`: shows the one-way opt-in flags
  `--enable-loopification`, `--enable-loop-fusion`, and
  `--enable-selective-buffer-sharing`; it does not show old disable flags.
- `python3 gibbon-compiler/examples/soa_examples/gibbon_benchmark.py --help`:
  shows the same enable-only optimization interface.
- benchmark-script smoke on `List.hs`, one iteration with
  `--enable-loopification --store-scalar-field-counts --enable-selective-buffer-sharing --enable-loop-fusion`:
  AoS compiled as `AOS mut-cursors,loopify`; SoA compiled as
  `SOA mut-cursors,loopify,scalar-counts,selective-sharing,loop-fusion`;
  outputs matched.
- focused runtime regression check after `ScalarCountSet`:
  - `MonoTree.hs`, 5 iterations: loopified SOA `add1Tree` median improved
    from about `0.0578s` to `0.0211s`; recursive SOA baseline was about
    `0.0436s`
  - `TernaryTree.hs`, 5 iterations: loopified SOA `add 1 tree` median
    improved from about `0.1163s` to `0.0498s`; recursive SOA baseline was
    about `0.0778s`
  - generated C now uses `gib_scalar_count_footer_set` once per chunk in the
    loopified map body; remaining `gib_scalar_count_footer_bump` calls are
    from annotated builders
- `cabal run test-gibbon -- --pattern LoopifyTraversals`: passed, 12/12
- after scalar-buffer loop fusion:
  - `DBQuery.hs` generated one dcon loop plus three constructor scalar-group
    loops for each loopified map, rather than one loop per scalar buffer
  - `DBQuery.hs` loopified and non-loopified final outputs matched
  - `OctTree_scaleEnergy.hs` generated one dcon loop plus two constructor
    scalar-group loops for `scaleEnergy`
  - `OctTree_scaleEnergy.hs` loopified and non-loopified final outputs
    matched (`300158116707`)
- after call-site selective unwraps:
  - `cabal run test-gibbon -- --pattern SelectiveBufferSharing`: passed, 4/4
  - `cabal run test-gibbon -- --pattern LoopifyTraversals`: passed, 14/14
  - `DBQuery.hs` with `--enable-selective-buffer-sharing` compiled and ran
    with exit code 0 for `--iterate 1`
  - generated DBQuery C had `gib_unwrap_selective_indirections` in
    `gibbon_main` before the `clearQueryFlags` and `sumCost` consumer calls,
    and no unwrap at the entries of `sumCost`, `clearQueryFlags`, or
    `scaleCosts`
- after TimeIt normalization hoisting:
  - generated DBQuery C moves the `clearQueryFlags` selective unwrap before
    the timing loop's `clock_gettime(... begin ...)`, while the timed region
    contains the traversal call itself
  - `DBQuery.hs` with `--enable-selective-buffer-sharing` compiled and ran
    with exit code 0 for `--iterate 1`
  - historical full SOA benchmark script command with `--iterations 1 --clean
    --store-scalar-field-counts --enable-selective-buffer-sharing` produced
    `21/22` successful programs and `21/21` output matches; the remaining
    failure at that time was `DomTree.soa`
- after scalar-count propagation:
  - `DomTree.soa` no longer crashes in the loopified `scaleLayout` pipeline
  - the root cause was missing footer metadata after non-loopified,
    shape-preserving `computeWidths`
  - `computeWidths` is not annotated with `OPT:CanVectorize` or
    `OPT:StoreScalarCounts`; propagation copies footer metadata after the
    materialized top-level producer call
  - focused DomTree benchmark-driver smoke with `--store-scalar-field-counts`
    and loopification enabled produced `1/1` successful programs and `1/1`
    output matches
- `PiecewiseFunctions.hs` with `--store-scalar-field-counts`: AoS/SOA output
  matched, and both `addConstPW` and `diffPW` generated chunk/for loops
- historical full `gibbon_benchmark.py` run with `--store-scalar-field-counts`
  before scalar-count propagation:
  - `21/22` benchmark programs succeeded
  - `21/21` successful AoS/SOA output comparisons matched
  - the one failure was `DomTree.soa`; this specific failure is now believed
    fixed by `ScalarCountPropagation` and should be rechecked in the next full
    benchmark sweep

### Current Limitations

The loopification effort is not complete. The major missing pieces are:

1. Broader scalar-expression support.
   The accepted expression language is intentionally small: variables,
   literals, projections, primitive scalar operations, and the same-shape
   conditional described above.

2. Better handling of richer packed/non-scalar fields.
   The current loopification work focuses on scalar buffers in fully-factored
   layouts. Non-scalar field operations are not vectorized and remain a larger
   design area.

3. Post-loopification selective dead-buffer sharing.
   This has been reintroduced as a separate opt-in `L3 -> L3` pass after
   loopification: `Gibbon.Passes.SelectiveBufferSharing`. It is enabled with
   `--enable-selective-buffer-sharing` / `--selective-buffer-sharing`.

   Current behavior:
   - for loopified `OPT:CanVectorize` functions, the dcon/tag stream and pure
     copy scalar buffers can be replaced by one selective-indirection wrapper
     per shared buffer;
   - scalar buffers with real update expressions remain in the loop.
   - consumer calls are normalized at the call site by
     `UnwrapSelectiveIndirections`, including inline cursor-array copy
     arguments generated around benchmark calls.

   Important caveat: the pass is still experimental and default-off. It is now
   correct for the DBQuery-style pipeline because callers unwrap selectively
   shared inputs before passing them to recursive folds or loopified maps, but
   broader benchmark validation is still needed before enabling it by default.

4. Compiler-driven SIMD vectorization.
   Manual SSE2/AVX2 experiments exist, but the compiler still does not emit
   explicit SIMD IR/code. That work belongs in `VectorizeTraversals` after the
   loop form is stable.

5. Performance cleanup.
   The current loopified code prioritizes correctness. It now sets output
   footer metadata once per chunk and fuses scalar buffers by constructor
   group, but further cleanup can still reduce redundant dependency reads,
   share unchanged buffers, and vectorize hot loops.

6. More regression coverage.
   Current tests cover the pass shape and lowering, but more end-to-end tests
   should cover chained loopified maps, conditionals, cross-buffer
   dependencies, and large multi-chunk examples.

### Manual Experiment Status

The manual experiments were useful and remain relevant, but they are not the
compiler implementation.

- `experiments/scalar_count_smoke/`
  - preserves the manual SoA chunked C experiments
  - includes timing harnesses, SSE2/AVX2 modes, end-to-end timings, and
    hot-loop timings

- `experiments/simple_test/`
  - contains simpler array-style experiments (`simple.c`, `simple2.c`)
  - useful for understanding isolated loop/vector behavior
  - not part of the compiler pipeline itself

These experiments helped shape the current loopified code generation strategy,
especially the outer chunk loop / inner counted loop structure.

### Recommended Next Steps

If continuing this effort, the highest-value next steps are:

1. Add stronger end-to-end regression tests for the current loopified baseline.
2. Reintroduce `SelectiveBufferSharing` as a post-loopification `L3 -> L3`
   pass.
3. Keep `VectorizeTraversals` separate and add SIMD explicitly only after the
   structural loop form is stable.
4. Improve the generated loop code's performance without weakening the current
   correctness invariants.

### LLM Handoff Instructions

If continuing this work in a new chat, first read this `Current Snapshot`
section and treat it as the source of truth. Historical notes below
`Archived Previous Notes` may conflict with the current implementation.

Repository and environment:

- Work from repo root:

```text
/workdisk/git/gibbon
```

- Set `GIBBONDIR` for compiler runs:

```text
GIBBONDIR=/workdisk/git/gibbon
```

- Prefer `rg` for code search. Useful files:
  - `gibbon-compiler/src/Gibbon/Passes/LoopifyTraversals.hs`
  - `gibbon-compiler/src/Gibbon/Passes/ScalarCountPropagation.hs`
  - `gibbon-compiler/src/Gibbon/Passes/SelectiveBufferSharing.hs`
  - `gibbon-compiler/src/Gibbon/Passes/LoopifiedTraversalFusion.hs`
  - `gibbon-compiler/src/Gibbon/Passes/Cursorize.hs`
  - `gibbon-compiler/src/Gibbon/L3/Syntax.hs`
  - `gibbon-compiler/src/Gibbon/Passes/Lower.hs`
  - `gibbon-compiler/src/Gibbon/Passes/Codegen.hs`
  - `gibbon-rts/rts-c/gibbon_rts.h`
  - `gibbon-rts/rts-c/gibbon_rts.c`

Build the compiler:

```text
cabal build exe:gibbon
```

Compile the main non-mutable scalar-count smoke. This is the important command
for the current task because it intentionally omits `--use-mutable-cursors`:

```text
GIBBONDIR=/workdisk/git/gibbon cabal run exe:gibbon -- \
  --packed --to-exe --debug-rts --store-scalar-field-counts --no-ran \
  gibbon-compiler/examples/soa_examples/programs/SOA/ScalarCountMultiIntSmoke.hs
```

Run the generated executable:

```text
gibbon-compiler/examples/soa_examples/programs/SOA/ScalarCountMultiIntSmoke.exe
```

Expected final result:

```text
2000012000000
```

The executable is compiled with `--debug-rts`, so it prints a lot of region
growth and scalar-count footer debugging before the final result. The final line
must be `2000012000000` for the current checked-in
`ScalarCountMultiIntSmoke.hs`, whose `gibbon_main` builds `mkMultiList 1000000`
and applies `iterate (add1MultiList xs)`. Older smoke variants that used
`mkMultiList 8000` directly produced `128096000`; do not use that older value
for the current file.

Use `-v4` when inspecting generated IR. Redirect the output because it is very
large:

```text
GIBBONDIR=/workdisk/git/gibbon cabal run exe:gibbon -- \
  --packed --to-exe --debug-rts --store-scalar-field-counts --no-ran -v4 \
  gibbon-compiler/examples/soa_examples/programs/SOA/ScalarCountMultiIntSmoke.hs \
  > /tmp/gibbon_loopify_nonmutable_v4.log 2>&1
```

Search the `-v4` log for the important non-mutable checks:

```text
rg -n "loop_count_footer|WhileCursor|ReadScalarCountNextFooter|loop_next_next_footer|chk_end_.*IndexCursorArray|Running pass, L3.typecheck" /tmp/gibbon_loopify_nonmutable_v4.log
```

What to verify in the `-v4` log:

- L3 typechecking completes.
- SoA call-boundary checks index end cursor arrays, for example
  `chk_end_* = IndexCursorArray "reg_cursor_ptr_*" ...`.
- The loopified traversal lowers through `WhileCursorT` with
  `loop_count_footer_loc`.
- The loop advances chunk metadata with `loop_next_next_footer`.

Inspect the generated C after compiling the non-mutable smoke:

```text
rg -n "while \\(\\*loop_count_footer_loc|loop_next_next_footer|loop_overwrite_reg|gib_scalar_count_footer_(get|next)|gib_grow_region\\(loop_" \
  gibbon-compiler/examples/soa_examples/programs/SOA/ScalarCountMultiIntSmoke.c
```

Expected generated C shape in `add1MultiList`:

- `while (*loop_count_footer_loc != NULL) { ... }`
- `gib_scalar_count_footer_get(loop_current_count_footer)`
- `gib_scalar_count_footer_next(loop_current_next_footer)`
- output `gib_grow_region(loop_out_*_loc, loop_out_*_end_loc)` calls at chunk
  boundaries
- final cursor-array returns:
  - `loop_overwrite_reg`
  - `loop_in_final_arr`
  - `loop_out_final_arr`
- no `loop_fast_ok` variable and no runtime branch back to the original
  recursive body. The remaining internal `if (loop_is_last_chunk) ... else ...`
  is chunk-boundary handling, not a recursive fallback.

Optional mutable sanity check:

```text
GIBBONDIR=/workdisk/git/gibbon cabal run exe:gibbon -- \
  --packed --to-exe --store-scalar-field-counts --no-ran \
  --use-mutable-cursors \
  gibbon-compiler/examples/soa_examples/programs/SOA/ScalarCountMultiIntSmoke.hs

gibbon-compiler/examples/soa_examples/programs/SOA/ScalarCountMultiIntSmoke.exe
```

Expected final result is also:

```text
2000012000000
```

Important implementation pitfall from the non-mutable fix:

- `LoopifyTraversals` can use local mutable cursor refs (`AddrOfCursor`,
  `DerefMutCursor`, `BumpCursorMutable`, `WriteCursorMutable`) even in the
  non-mutable cursorized function. These refs are local loop state, not a change
  to the function ABI.
- The non-mutable ABI must still return the full cursor-array tuple:
  `(input ends, output ends, input final cursors, (output starts, output final cursors))`.
- `Cursorize` call-boundary assertions for SoA values must compare
  `Cursor` against `Cursor`, not `Cursor` against `CursorArray`. If generated
  L3 contains a check like `chk_loc < reg_cursor_ptr`, it is wrong; it should
  index the end array first.

Important scalar-count construction pitfall from the `List.hs` segfault fix:

- Repro command from `gibbon-compiler/examples/soa_examples/programs/SOA`:

```text
GIBBONDIR=/workdisk/git/gibbon gibbon --packed --to-exe \
  --use-mutable-cursors --store-scalar-field-counts \
  List.hs --cfile List.c --exefile List.exe

./List.exe
```

- Before the fix, the 100,000,000-element `List.hs` crashed with exit code 139.
  `gdb` showed the crash while building the input, not in `add1`:

```text
gib_scalar_count_footer_bump
mkList.isra.0
mkList.isra.0
...
```

- The immediate cause was scalar-count begin/end instrumentation around the
  recursive `OPT:StoreScalarCounts` builder. The inserted
  `gib_scalar_count_footer_end("mkList")` after the recursive call prevented
  GCC from turning the large recursive builder into the loop-like code shape
  that the no-scalar-count build gets, so the input construction exhausted the
  C stack.
- Normal, non-debug scalar-count builds now do not emit
  `gib_scalar_count_footer_begin/end` around builders. They still emit
  `gib_scalar_count_footer_bump(...)`, and the RTS bump/grow bookkeeping no
  longer depends on a dynamic begin/end depth guard.
- `--debug-rts` builds still keep begin/end instrumentation for footer tracing.
  Avoid using `--debug-rts` for the 100,000,000-element `List.hs` run unless
  that debug path is redesigned; use non-debug builds for the large List
  validation.
- Successful fixed output:

```text
'#(5000000150000000 5000000150000000 100000000)
exit=0
```

### Selective Sharing Placement Update

The previous direction of implementing dead-buffer indirection sharing as a
standalone recursive L2 pass is now rejected as the main path forward.

Base-state reset:

- `SelectiveBufferSharing` is no longer part of the live L2 compiler pipeline.
- Existing L2 selective-sharing code should be treated as exploratory history,
  not as the implementation path to continue extending.
- The next implementation work should start from loopification, not from trying
  to repair recursive whole-buffer sharing.

Why:

- For recursive traversals, the dcon stream still drives control flow.
- Sharing a dead SoA buffer exactly once, in a principled way, becomes awkward:
  the function is still re-entered recursively, output cursors are threaded
  incrementally, and one-time whole-buffer sharing does not fit naturally into
  the current recursive design.
- The ad hoc alternatives, such as per-recursive-call checks or wrapper tricks,
  make the optimization harder to reason about than it should be.

New placement decision:

- `LoopifyTraversals` should be implemented first as an `L3 -> L3` pass for
  functions marked `OPT:CanVectorize`.
- `SelectiveBufferSharing` should move after loopification and also become an
  `L3 -> L3` pass.
- `VectorizeTraversals` should then run after loopification and selective
  sharing, still in `L3 -> L3`.

Planned ordering:

```text
Cursorize
-> LoopifyTraversals        (L3 -> L3)
-> SelectiveBufferSharing   (L3 -> L3)
-> VectorizeTraversals      (L3 -> L3)
```

This is the cleaner design because once recursion is eliminated:

- the traversal no longer depends on the dcon buffer as a recursive control
  spine,
- field buffers can be handled independently,
- dead-buffer sharing becomes a simple loopified-buffer transformation rather
  than a recursive special case,
- dcon sharing itself becomes possible in the loopified setting.

Practical consequence:

- Do not continue investing in standalone recursive selective sharing as an L2
  pass.
- Treat the earlier L2 selective-sharing work as exploratory/archived rather
  than the path to extend.
- Shift implementation effort to loopification first.

Loopification status as of 2026-04-25:

- `LoopifyTraversals` now has multi-chunk walking for both cursor ABIs:
  - mutable cursorized functions, whose loopified body returns `()`, and
  - non-mutable cursorized functions, whose loopified body rebuilds and
    returns the normal cursor-array tuple.
- The non-mutable loopified body uses local mutable cursor refs for loop state, just
  like the mutable implementation, but it does not mutate the incoming cursor
  arrays in place. At the end of the loop it materializes:
  - updated output end cursor array,
  - final input cursor array,
  - final output cursor array, and
  - the packed result pair expected by the non-mutable cursorized ABI.
- The non-mutable path now walks chunks using:
  - the final scalar-buffer footer for the first chunk count,
  - `ReadScalarCountFirstFooter` for the first linked footer,
  - `ReadScalarCountNextFooter` for later linked footers, and
  - a `WhileCursor` loop that terminates by setting the count-footer cursor ref
    to null after the final data chunk.
- `Cursorize` also needed a small SoA bounds-check repair for non-mutable calls:
  when the location side of an inserted call-boundary assertion is a
  `CursorArrayTy`, the end side must be treated as the matching cursor array
  even if the local type environment has only the parent end variable. Without
  this, generated L3 compared a cursor to an entire cursor array, such as
  `chk_loc < reg_cursor_ptr`, and failed L3 typechecking.
- `Lower`/RTS scalar-count construction was also adjusted so normal builds do
  not wrap recursive builders with scalar-count begin/end calls. This preserves
  tail-call optimization for very large recursive builders such as
  `programs/SOA/List.hs` while still recording scalar-count bumps and chunk
  growth metadata.

Validation:

```text
cabal build exe:gibbon
GIBBONDIR=/workdisk/git/gibbon cabal run exe:gibbon -- \
  --packed --to-exe --debug-rts --store-scalar-field-counts --no-ran \
  gibbon-compiler/examples/soa_examples/programs/SOA/ScalarCountMultiIntSmoke.hs
gibbon-compiler/examples/soa_examples/programs/SOA/ScalarCountMultiIntSmoke.exe
```

The non-mutable executable prints its final stdout line:

```text
2000012000000
```

The mutable scalar-count smoke was also checked without `--debug-rts` and
prints the same final result.

Large mutable `List.hs` validation:

```text
cd gibbon-compiler/examples/soa_examples/programs/SOA
GIBBONDIR=/workdisk/git/gibbon gibbon --packed --to-exe \
  --use-mutable-cursors --store-scalar-field-counts \
  List.hs --cfile List.c --exefile List.exe
./List.exe
```

The executable now exits successfully and prints:

```text
'#(5000000150000000 5000000150000000 100000000)
```

The `-v4` compiler trace was also checked. The saved log at
`/tmp/gibbon_loopify_nonmutable_v4.log` shows:

- SoA call-boundary checks now index end cursor arrays, for example
  `chk_end_* = IndexCursorArray "reg_cursor_ptr_*" ...`.
- The loopified function lowers through `WhileCursorT` with
  `loop_count_footer_loc`.
- The loop body reads `loop_chunk_count` from the current footer and advances
  with `loop_next_next_footer`.

Generated C for non-mutable `add1MultiList` now contains:

```text
while (*loop_count_footer_loc != NULL) { ... }
gib_scalar_count_footer_get(loop_current_count_footer)
gib_scalar_count_footer_next(loop_current_next_footer)
gib_grow_region(loop_out_dcon_loc, loop_out_dcon_end_loc)
gib_grow_region(loop_out_loc_i, loop_out_end_loc_i)
```

It does not contain `loop_fast_ok` or an `if (loop_fast_ok)` wrapper. Accepted
`OPT:CanVectorize` candidates are replaced by loop-only code; the original
recursive function body is kept only when the pass rejects a candidate at
compile time.

It also returns the final non-mutable cursor arrays:

```text
loop_overwrite_reg
loop_in_final_arr
loop_out_final_arr
```

### Clear Next Steps

Current implemented baseline:

- `LoopifyTraversals` is an `L3 -> L3` pass after cursorization.
- It handles a narrow but real class of `OPT:CanVectorize` traversals:
  - fully factored SoA list-like datatypes,
  - one recursive constructor and one nullary base constructor,
  - scalar field updates that are field-local,
  - multi-chunk input walking through scalar-count footers,
  - mutable and non-mutable cursorized function ABIs.
- Accepted `OPT:CanVectorize` candidates now emit loop-only code. There is no
  runtime `loop_fast_ok` conditional and no recursive fallback branch inside the
  generated function. If the pass cannot accept the function at compile time,
  it leaves the original recursive body unchanged.

Immediate engineering steps:

1. Add focused regression tests for scalar-count construction and large
   loopified List runs. Include the normal non-debug mutable `List.hs` command
   above so the tail-call/stack regression is covered.
2. Add focused regression tests for non-mutable multi-chunk loopification.
   The current smoke validation is manual. Add a compiler test that checks the
   generated L3/L4 contains the footer-driven loop and an executable smoke that
   verifies the `2000012000000` result without `--use-mutable-cursors` for the
   current `ScalarCountMultiIntSmoke.hs`.
3. Audit output-growth behavior in the loopified body now that the pre-loop
   fallback guard is gone. The loop calls `GrowRegion` at input chunk
   boundaries; stress-test with smaller initial buffer sizes and chunks near
   capacity to make sure the loop-only path always grows output regions before
   writing.
4. Deduplicate mutable and non-mutable loopification builders. They share most
   of the chunk-walking logic but differ in entry/exit ABI. A shared chunk-loop
   generator would reduce drift before more optimizations are layered on top.
5. Run broader compiler verification after each substantial change. At minimum:
   - `cabal build exe:gibbon`
   - the non-mutable `ScalarCountMultiIntSmoke.hs` compile/run above
   - the mutable `ScalarCountMultiIntSmoke.hs` compile/run above
   - the large mutable `List.hs` compile/run above
   Then expand to the existing compiler test suite or representative examples
   before treating the optimization as stable.

Future optimization TODOs:

1. Implement selective dead-buffer sharing by adding indirections to output
   streams. This should happen after loopification, as an `L3 -> L3` pass over
   loopified traversals. The expected target is dead SoA buffers such as dcon or
   unchanged scalar/float streams where the output can share the input through
   an indirection instead of copying.
2. Add manual SIMD support through IR, starting at L3. Introduce explicit SIMD
   operations/intrinsics in the IR, lower them through L4/target code, and emit
   Intel intrinsics in C codegen. Keep this separate from structural
   loopification and selective sharing so each effect remains measurable.
3. Generalize loopification beyond the current list-like map traversal.
   Extend candidate discovery and field-plan extraction to more map-like
   traversals over complex ADTs, including trees and datatypes with multiple
   recursive or packed fields. The pass needs better recognition of key
   operations and dependencies.
4. Consider non-scalar fields later. Current work should stay focused on scalar
   field loops because scalar-count footers provide the loop bounds directly.
   Loopification for non-scalar fields may be useful eventually, but it is not
   the immediate priority.
5. Perform total verification before upstreaming or relying on the optimization:
   make sure existing compiler behavior and examples do not break, especially
   non-`OPT:CanVectorize` programs and programs compiled without
   `--store-scalar-field-counts`.

The current design is:

- Store one count in each scalar-buffer footer.
- Preserve the cyclic next-chunk encoding:
  - the final end-of-region footer stores the count for the first scalar-buffer chunk,
  - each non-final footer stores the count for the next scalar-buffer chunk.
- Maintain the cyclic encoding eagerly in the RTS:
  - first-chunk writes increment both `first_counts` and the current final footer,
  - on every grow, the old final footer is cleared and becomes the boundary footer for the fresh chunk,
  - the fresh final footer is immediately seeded with `first_counts`,
  - later writes to the fresh chunk increment the previous/boundary footer,
  - `gib_scalar_count_footer_end` no longer performs a normal-path final repair loop.
- Do not emit per-field scalar write bumps in L3.
- Emit one constructor-level L3 event when a constructor is created:
  - `ScalarCountBump DataCon [Var]`
  - the `DataCon` records the logical constructor event,
  - the `[Var]` contains the scalar-buffer cursors derived from that constructor's scalar fields.
- Lower/codegen expands that one constructor event to bump the current footer for each affected scalar buffer.
- The stored metadata still lives in the scalar buffer footers, so future vectorized traversals can read scalar-buffer loop bounds in O(1).

Current validated placement in generated `mkMultiList`:

```c
*(GibPackedTag *) deref_1870 = 0;
GibCursor writetag_1916 = deref_1870 + 1;

gib_scalar_count_footer_bump(deref_1867);
gib_scalar_count_footer_bump(deref_1865);
gib_scalar_count_footer_bump(deref_1863);
gib_scalar_count_footer_bump(deref_1861);
gib_scalar_count_footer_bump(deref_1859);

/* bounds checks and recursive call happen after this */
```

For `ScalarCountMultiIntSmoke.hs` with `mkMultiList 8000`, debug RTS output now shows per-chunk scalar-buffer counts. There are five scalar fields in `MCons`, so each chunk count appears five times. This does not mean the compiler inserts scalar-write instrumentation; it means the single constructor event fans out to the scalar-buffer footers implied by the constructor fields:

```text
249, 249, 249, 249, 249
505, 505, 505, 505, 505
1017, 1017, 1017, 1017, 1017
2041, 2041, 2041, 2041, 2041
4067, 4067, 4067, 4067, 4067
121, 121, 121, 121, 121
```

The scalar-buffer chunk counts sum to 8000:

```text
249 + 505 + 1017 + 2041 + 4067 + 121 = 8000
```

Validation completed:

```text
cabal build exe:gibbon
make -C gibbon-rts GIBBONDIR=/workdisk/git/gibbon
GIBBONDIR=/workdisk/git/gibbon cabal run exe:gibbon -- --packed --to-exe --debug-rts --store-scalar-field-counts --no-ran --use-mutable-cursors /tmp/ScalarCountSingleCountSmoke.hs
/tmp/ScalarCountSingleCountSmoke.exe
```

The negative/gating case was also checked by compiling the same smoke without `--store-scalar-field-counts`; the generated C contained no `gib_scalar_count_footer_begin`, `gib_scalar_count_footer_bump`, or `gib_scalar_count_footer_end` calls.

Debug/probe output is gated on `--debug-rts` / `_GIBBON_DEBUG`. Normal builds with `--store-scalar-field-counts` still maintain footer metadata, but do not print `SCALAR_COUNT_*` lines or maintain the debug touched-footer list.

After removing the end-of-build repair loop, temporary debug-only probes checked direct O(1) reads:

```text
single chunk, mkMultiList 10:
  int0/int1/int2/int3/float0 seq=10 sum=10

multi chunk, mkMultiList 8000:
  int0/int1/int2/int3/float0 seq=121,249,505,1017,2041,4067 sum=8000
```

For the multi-chunk probe, `chunk=0` was read from the end footer and chunks `1..n` were read from the previous footer chain using `gib_scalar_count_first_footer` / `gib_scalar_count_footer_next`.

Immediate next step:

- Keep using manual C experiments to understand the eventual `OPT:CanVectorize` compiler transformation before automating it.

## Manual Vectorization Experiment

The manual C experiments now cover both `add1List` and `add1MultiList` with the
same five benchmark variants. The generated recursive functions remain as the
baselines. The loopified variants read O(1) chunk counts from the scalar-buffer
footers, skip recursive dcon traversal for independent work, and use indirection
headers for dead dcon/float buffers in the indirection variants.

For `add1MultiList`, the manual variants now include:

- recursive generated `add1MultiList`,
- loopified scalar with copied dead dcon/float buffers,
- loopified scalar with dead-buffer indirections,
- loopified auto-vectorized int-field loops with dead-buffer indirections,
- loopified manual SSE2 int-field loops with dead-buffer indirections.

This keeps the main comparison focused on structural loopification,
dead-buffer indirections, compiler auto-vectorization, and manual SSE2 SIMD as
separate effects.

The scalar-count smoke benchmark suite now preserves the manual C artifacts in:

```text
experiments/scalar_count_smoke/sources/
```

The driver can benchmark either the one-int `add1List` smoke or the multi-int
`add1MultiList` smoke:

```text
experiments/scalar_count_smoke/benchmark_scalar_count_smoke.py
```

Both smoke tests report the same five variants:

- generated recursive `add1`,
- loopified `add1` using copies for dead dcon/float buffers with vectorization disabled,
- loopified `add1` using indirections for dead dcon/float buffers with vectorization disabled,
- loopified `add1` using indirections for dead dcon/float buffers with compiler auto-vectorization,
- loopified `add1` using indirections for dead dcon/float buffers with manual SSE2 SIMD.

One-int example:

```text
python3 experiments/scalar_count_smoke/benchmark_scalar_count_smoke.py \
  --program list \
  --iterations 100 \
  --list-len 50000
```

Multi-int example:

```text
python3 experiments/scalar_count_smoke/benchmark_scalar_count_smoke.py \
  --program multi-list \
  --iterations 100 \
  --list-len 8000 \
  --inner-iterations 10
```

The driver compiles the selected saved C smoke test, runs the variants, checks
`sums_match=yes`, and prints average timing and speedup tables. The manual SIMD
path is SSE2-only; `--build poc` is kept as an alias for the default
`--build sse2`.

The driver also has a graphing mode:

```text
python3 experiments/scalar_count_smoke/benchmark_scalar_count_smoke.py \
  --program list \
  --mode sweep \
  --iterations 20
```

`--mode sweep` runs the same five variants across input sizes and emits both a
CSV and SVG graph. The built-in default x-axis sizes are:

```text
10000,50000,100000,250000,500000,1000000
```

The SVG plots input size on the x axis and speedup over recursive `add1` on the
y axis. Output defaults to:

```text
experiments/scalar_count_smoke/results/<program>_speedups.csv
experiments/scalar_count_smoke/results/<program>_speedups.svg
```

Recent driver smoke validation:

```text
python3 experiments/scalar_count_smoke/benchmark_scalar_count_smoke.py \
  --program list --iterations 2 --list-len 5000

ScalarCountSmoke add1List:
  runs=2 sums_ok=2 failures=0

python3 experiments/scalar_count_smoke/benchmark_scalar_count_smoke.py \
  --program multi-list --iterations 2 --list-len 1000 \
  --inner-iterations 2

ScalarCountMultiIntSmoke add1MultiList:
  runs=2 sums_ok=2 failures=0
```

For the one-int smoke, the indirection plus loopified structure is consistently
faster than the recursive traversal. The explicit SIMD path is SSE2 now; the
eventual compiler pass should still keep measuring structural loopification and
SIMD vectorization separately.

## Optimization Proof Sketch

Assume a function is annotated `OPT:CanVectorize` and its input/output layout is fully factored SoA.

The annotation is a user/compiler contract that the traversal has no parent-child dependencies. Therefore, for each constructor case, the work performed for one constructor instance depends only on that instance's fields and not on the result of recursively processing its children.

In AoS or cursor-recursive form, the traversal order is expressed by recursive case analysis over the dcon stream. In fully factored SoA, scalar fields are stored in separate buffers. For a constructor `C`, the scalar field buffers for `C` have exactly one scalar element for each occurrence of `C`. The scalar-buffer footer count for a chunk therefore gives the loop bound for the field operations in that chunk.

The loopified transformation is correct when:

- every scalar field operation in the original case body is mapped to the corresponding scalar buffer,
- the operation has no dependence on recursive child results,
- chunk boundaries in any freshly written scalar buffers preserve the redirection structure expected by existing generated consumers,
- dead buffers are represented by indirections to semantically equivalent input buffers,
- the dcon buffer can be skipped when no operation depends on dcon traversal order, with the output dcon buffer represented by an indirection to the input dcon buffer.

For each chunk, the transformed code reads `n = count(chunk)` in O(1), then executes the original per-field scalar operation for `i = 0..n-1`. This produces the same field values as the recursive traversal because the recursive traversal also executes the case body once per constructor occurrence, in the same field-buffer order, and the annotation rules out dependencies that would make the recursive call result observable inside the per-field computation.

For unused fields/buffers, an indirection is semantics-preserving because generated readers already treat indirection as transparent: they follow the pointer and continue traversal at the target buffer. Avoiding copies of dead buffers therefore preserves observable results while reducing work.

## Compiler Vectorization Implementation Plan

The earlier plan was still too monolithic. Following the nano-pass spirit
described in Jeremy Siek's work and the TU Delft lecture notes, the
implementation should be split into three separate passes, each with one clear
responsibility:

1. selective buffer sharing for dead input buffers,
2. loop introduction for `OPT:CanVectorize` traversals,
3. vectorization of those loops.

The key point is that these should not all live in one large
`VectorizeTraversals.hs` pass. Each pass should do one transformation, introduce
only the new structure it needs, and keep reasoning local.

### Revised Pass Structure

Preferred module split:

- `Gibbon.Passes.SelectiveBufferSharing`
  - better name than `EliminateCopyingDeadField`, because the transformation is
    really buffer-level selective sharing, not field-level dead-code removal.
- `Gibbon.Passes.LoopifyTraversals`
  - introduces loop-oriented IR for `OPT:CanVectorize`.
- `Gibbon.Passes.VectorizeTraversals`
  - recognizes vectorizable loop bodies and rewrites them to explicit SIMD-ish
    IR operations.

If a shared analysis datatype becomes necessary, it can live in a small helper
module under `Gibbon.Language`, but the transformation logic should still stay
segregated by pass.

### Global Scope

The overall optimization target remains:

```haskell
{-# ANN add1 OPT:CanVectorize #-}
```

and the first compiler prototype remains intentionally narrow:

- fully factored SoA layout only,
- one structure-preserving traversal,
- one packed input and one packed output of the same datatype,
- no parent-child dependencies by annotation contract,
- scalar field operations such as `x + 1`,
- dead buffers represented by indirections instead of copies,
- no constructor filtering, no shape change, no AVX2.

Unsupported annotated functions should keep the existing recursive code path.

## Pass 1: Selective Buffer Sharing

### Current Direction

The old L2/pre-loopification selective-sharing plan has been rejected. It tried
to reason about dead buffers while the traversal was still recursive, which
pushes the implementation toward per-element sharing or repeated conditionals
inside recursive calls. That is the wrong granularity for fully factored SoA
layouts.

Selective sharing now belongs after loopification as an `L3 -> L3` nano-pass:

```text
... -> reorderScalarWrites
    -> loopifyTraversals              -- unfused per-buffer loops
    -> selectiveBufferSharing         -- one wrapper per copied buffer
    -> fuseLoopifiedTraversals        -- post-selective loop fusion
    -> L3.flatten -> ...
```

At that point the recursive traversal has already become chunk/for loops over
SoA buffers. Whole-buffer sharing is then straightforward:

- the dcon/tag stream can be replaced by one buffer-level indirection, because
  loopified maps do not need to traverse tags recursively;
- scalar buffers whose generated loop body is a pure copy can be replaced by one
  buffer-level indirection;
- scalar buffers with real update expressions remain in the loop.

The pass is implemented in `Gibbon.Passes.SelectiveBufferSharing` and is
opt-in:

- enable: `--enable-selective-buffer-sharing` or
  `--selective-buffer-sharing`
The old `selectiveBufferSharingL2` entry point is no longer part of the
pipeline. The remaining L2 `SelectiveBufferShareE` syntax is legacy plumbing
from the abandoned prototype and is not constructed by the current pass.

### Current Representation

Selective sharing now uses a distinct `SelectiveIndirection` wrapper rather
than the ordinary packed indirection tag. The dcon wrapper carries a bit mask
describing exactly which peer buffers are selectively wrapped. Consumers call
`UnwrapSelectiveIndirections` at function entry; it checks the dcon stream and
then unwraps only the masked buffers. Mutated output buffers are left as raw
buffers.

The wrapper stores the shared source start and source end pointers explicitly.
This is important: whole-buffer sharing can span more than the 16-bit offset
available in ordinary tagged pointers.

### Fusion Ordering

Loopification deliberately emits unfused per-buffer scalar loops. This lets
selective sharing remove every pure-copy buffer loop without falling back to
copying a buffer merely because it was selected as the representative fused
chunk walker. The new `Gibbon.Passes.LoopifiedTraversalFusion` pass runs after
selective sharing and fuses only the remaining adjacent loopified scalar loops
with the same generated constructor label. Leaving `--enable-loop-fusion` off
keeps the unfused per-buffer loopified baseline.

## Pass 2: Loopify Traversals

### Purpose

This pass should remove recursion from functions marked `OPT:CanVectorize` and
replace it with explicit loop-oriented IR over buffers.

This pass should not do SIMD. Its job is only:

- recognize the traversal shape,
- identify per-buffer work,
- introduce `ForE`-style IR,
- use footer counts to drive scalar loops.

### Pipeline Placement

This pass should run after `Cursorize`. More concretely, the cleanest placement
is after `cursorize` and preferably after `reorderScalarWrites`, so we do not
need to complicate either of those existing passes with loop syntax.

Recommended placement:

```text
... -> cursorize -> reorderScalarWrites -> loopifyTraversals -> flattenL3 -> ...
```

This keeps cursorization untouched and localizes new control-flow syntax to the
post-cursorize part of the pipeline.

### IR Changes

This pass requires a new L3 IR construct for loops.

The first design can be simple, for example:

```haskell
ForE bounds body
```

where the exact shape of `bounds` can be refined later. In practice, we will
likely want a loop variable and a bound expression, but the important point is
that loop structure becomes explicit in L3 rather than being encoded indirectly
in C codegen.

We will also likely need a small primitive for reading chunk counts from the
footer metadata in O(1), but that should remain separate from SIMD.

### What This Pass Should Do

For a supported `CanVectorize` traversal:

- do not recurse over the dcon stream,
- use footer metadata to recover per-chunk loop bounds,
- create `ForE` loops over live buffers,
- treat dead buffers as already handled by the earlier selective-sharing pass,
- preserve the scalar semantics of the original traversal.

The pass should exploit the annotation contract:

- no parent-child dependencies,
- recursive calls are independent,
- operations can be regrouped per buffer.

### First Milestones For This Pass

1. Done: add `ForE` to L3 syntax and typecheck/plumbing.
2. Done: add footer-count primitives to L3/L4/lowering/codegen:
   - read current/footer count,
   - read the first/footer for chunk 0,
   - read the next/footer for later chunks.
3. Done: add a no-op `LoopifyTraversals` pass after `Cursorize`.
4. Done: recognize a small class of one-input/one-output SoA traversals marked
   `CanVectorize`.
5. Next: rewrite `add1List`-style traversals to scalar loops over the live scalar
   buffers.
6. Leave SIMD entirely out of this stage.

## Pass 3: Vectorize Traversals

### Purpose

Once loops exist explicitly in the IR, a separate pass can recognize key
operations inside those loops and rewrite them to vector instructions.

This pass should operate on loops, not on raw recursion.

### Pipeline Placement

This pass should run after `LoopifyTraversals` and before lowering/codegen.

Recommended placement:

```text
... -> cursorize -> reorderScalarWrites -> loopifyTraversals
    -> vectorizeTraversals -> flattenL3 -> ...
```

### What This Pass Should Do

For each `ForE` introduced by `LoopifyTraversals`:

- identify key scalar-buffer operations,
- detect operations that have a clean vector form,
- rewrite them to explicit vector IR instructions,
- leave unsupported loops in scalar `ForE` form.

The important design rule is:

- loop introduction and SIMD rewriting must remain separate.

That separation makes it possible to test:

1. recursive baseline,
2. loopified scalar baseline,
3. loopified vectorized version.

### IR Changes

This pass will likely need new vector-oriented IR instructions in L3 or a later
language stage, for example vector load/add/store operations. The exact
instruction set can stay minimal at first and should be driven by the manual
SSE2 proof-of-concept.

### First Milestones For This Pass

1. Add no-op `VectorizeTraversals` pass.
2. Recognize a tiny subset of `ForE` loop bodies, starting with `Int + const`.
3. Introduce explicit vector IR for that subset only.
4. Lower it to SSE2 in codegen.
5. Compare against the existing manual smoke benchmarks.

## Downstream Change Policy

The new passes will necessarily require touching some shared files, especially:

- `Gibbon.Compiler`
- `Gibbon.L3.Syntax`
- `Gibbon.L3.Typecheck`
- `flattenL3`
- `lower`
- `codegen`

But the transformation logic itself should stay isolated in the new pass
modules. The goal is:

- localize meaning-changing transformations in new files,
- keep edits to existing passes mostly to syntax plumbing,
- avoid complicating `Cursorize`,
- avoid putting traversal analysis directly into `Codegen`.

## Revised Milestone Plan

### Milestone A: Selective Buffer Sharing

Implement only the new L2 pass:

- create `Gibbon.Passes.SelectiveBufferSharing`,
- wire it after `RemoveCopies`,
- support the SoA selective-sharing case,
- add correctness tests.

This is the immediate next implementation step.

### Milestone B: Add Loop IR

- add `ForE` and any minimal count-reading primitive to L3,
- update downstream syntax plumbing,
- no optimization yet.

### Milestone C: Loopify `CanVectorize` Traversals

- implement `Gibbon.Passes.LoopifyTraversals`,
- rewrite a very small class of traversals to scalar loops,
- validate against the manual scalar loop smoke tests.

### Milestone D: Vectorize Loops

- implement `Gibbon.Passes.VectorizeTraversals`,
- introduce minimal vector IR,
- lower to SSE2,
- compare with the manual SIMD smoke tests.

### Milestone E: Metadata Cleanup For Optimized Outputs

- improve output footer maintenance for loopified/vectorized code,
- add RTS helper support if needed,
- ensure optimized outputs can feed later optimized traversals.

## Non-Goals For The First Compiler Prototype

- no AoS layout support,
- no mixed layout support,
- no shape-changing traversals,
- no constructor filtering or reordering,
- no parent-child dependent traversals,
- no AVX2 path,
- no attempt to fold all three transformations into one pass,
- no `Cursorize` changes for loopification logic,
- no codegen-only implementation of traversal vectorization.

## Archived Previous Notes

The notes below are historical and include older design directions. Prefer the `Current Snapshot` above when continuing implementation.

## Historical Goal

We are prototyping metadata support for future vectorization of recursive traversals over fully factored SoA packed layouts.

The optimization target is a traversal annotated with `OPT:CanVectorize`. That annotation is intended to mean the traversal has no parent-child dependencies, so recursive calls are independent. In that case, a future compiler pass should be able to replace recursive traversal with loops over packed SoA buffers.

The current metadata goal is no longer per-field scalar counts. The intended direction is now per-data-constructor counts:

- For a constructor such as `Cons`, all fields belonging to that constructor have the same logical count.
- In a fully factored SoA layout, scalar fields for a constructor can therefore use the constructor count as the loop bound.
- A vectorized traversal can run the work for each `case` branch `count(tag)` times instead of recursively walking every constructor tag in order.

## Desired Footer Layout

The desired representation is a cyclic next-chunk count encoding:

- Each chunk footer has fixed metadata slots keyed by data-constructor tag.
- The boundary/footer after chunk `i` stores constructor counts for chunk `i + 1`.
- The final end-of-region footer stores constructor counts for the first chunk.

More precisely, if a logical region has chunk footers:

- `F0 -> F1 -> ... -> Fn`

then:

- `Fn` stores counts for chunk `0`
- `F0` stores counts for chunk `1`
- `F1` stores counts for chunk `2`
- ...
- `F(n-1)` stores counts for chunk `n`

This is meant to provide O(1) loop-bound access before processing each chunk:

- Before processing the first chunk, read counts from the end-of-region footer.
- For later chunks, walk the footer linked list starting at `end_footer->reg_info->first_chunk_footer`; each footer in that list gives the count for the next chunk to process.

A vectorized traversal can therefore maintain two O(1) metadata cursors:

```c
GibOldgenChunkFooter *end_footer = (GibOldgenChunkFooter *) end_footer_ptr;
GibOldgenChunkFooter *next_count_footer =
    (GibOldgenChunkFooter *) end_footer->reg_info->first_chunk_footer;

// chunk 0
count0 = gib_scalar_count_footer_get((char *) end_footer, tag);

// chunk 1, chunk 2, ...
count_i = gib_scalar_count_footer_get((char *) next_count_footer, tag);
next_count_footer = next_count_footer->next;
```

## Current Implementation State

The code has been partially converted from per-field scalar counts to per-constructor tag counts.

Changed areas:

- `gibbon-rts/rts-c/gibbon_rts.h`
  - Footer slots are now keyed by constructor tag rather than `(constructor tag, field index)`.
  - `GibScalarCountFooterSlot` stores `count`, `dcon_tag`, and `is_touched`.
  - `gib_scalar_count_footer_bump` now takes `(footer_ptr, dcon_tag)`.
  - `gib_scalar_count_footer_get` now takes `(footer_ptr, dcon_tag)`.

- `gibbon-rts/rts-c/gibbon_rts.c`
  - Fixed scalar-count slots now map directly from constructor tag to slot.
  - Debug printing now reports `SCALAR_COUNT tag=<tag> count=<count> slot=<slot>`.
  - The RTS has a first-count/current-footer state machine intended to implement the cyclic next-chunk layout.

- `gibbon-rts/rts-ng/src/ffi.rs`
  - Rust FFI mirror of the footer slot was updated to match the C layout.

- `gibbon-compiler/src/Gibbon/L3/Syntax.hs`
  - `ScalarCountBump` now carries only `DataCon` and footer cursor.

- `gibbon-compiler/src/Gibbon/L4/Syntax.hs`
  - `ScalarCountBump` now carries only the lowered tag.

- `gibbon-compiler/src/Gibbon/L3/Typecheck.hs`
  - Typechecking updated for the new `ScalarCountBump` shape.

- `gibbon-compiler/src/Gibbon/Passes/Lower.hs`
  - Lowers `DataCon` to a numeric constructor tag for `ScalarCountBump`.

- `gibbon-compiler/src/Gibbon/Passes/Codegen.hs`
  - Emits `gib_scalar_count_footer_bump(footer, tag)`.

- `gibbon-compiler/src/Gibbon/Passes/Cursorize.hs`
  - Per-field bump insertion was removed.
  - Constructor-count bumps are now inserted near `WriteTag`.
  - Bumps are gated by the compile-time flag and the relevant function annotation path.

## Current Validation

A temporary generated smoke test was produced from:

`gibbon-compiler/examples/soa_examples/programs/SOA/ScalarCountMultiIntSmoke.hs`

The generated C contained only constructor-tag bumps, for example:

```c
gib_scalar_count_footer_bump(deref_1873, 1);
gib_scalar_count_footer_bump(deref_1873, 0);
```

This confirms the compiler is no longer generating per-field scalar-count bumps for the smoke test.

Runtime debug output showed constructor-tag counts per chunk. For an 8000-element `MCons` list plus one `MNil`, observed tag counts were:

```text
SCALAR_COUNT tag=0 count=187 slot=0
SCALAR_COUNT tag=0 count=443 slot=0
SCALAR_COUNT tag=0 count=955 slot=0
SCALAR_COUNT tag=0 count=1979 slot=0
SCALAR_COUNT tag=0 count=4027 slot=0
SCALAR_COUNT tag=0 count=350 slot=0
SCALAR_COUNT tag=1 count=1 slot=1
SCALAR_COUNT tag=0 count=59 slot=0
```

The `tag=0` counts sum to 8000, and `tag=1` appears once. This is a good sign: constructor-count instrumentation is happening and the chunk-level counts are plausible.

Important correction: the earlier expectation that the final footer should return `187` for this test was wrong. The first physical chunk is the small initial chunk, and its constructor count is `59`. The `187` count belongs to the second physical chunk.

A temporary cyclic-footer probe checked the dcon final/end footer with:

```c
gib_scalar_count_footer_get(reg_cursor_ptr_2245[0], 0)
```

Observed and now expected result:

```text
FIRST_CHUNK_TAG0=59
```

The same probe also validated the footer-list mapping for the first six chunks:

```text
CYCLIC_CHUNK index=0 actual_tag0=59 stored_tag0=59 actual_tag1=0 stored_tag1=0
CYCLIC_CHUNK index=1 actual_tag0=187 stored_tag0=187 actual_tag1=0 stored_tag1=0
CYCLIC_CHUNK index=2 actual_tag0=443 stored_tag0=443 actual_tag1=0 stored_tag1=0
CYCLIC_CHUNK index=3 actual_tag0=955 stored_tag0=955 actual_tag1=0 stored_tag1=0
CYCLIC_CHUNK index=4 actual_tag0=1979 stored_tag0=1979 actual_tag1=0 stored_tag1=0
CYCLIC_CHUNK index=5 actual_tag0=4027 stored_tag0=4027 actual_tag1=0 stored_tag1=0
```

This confirms the core cyclic invariant:

- the final footer stores the first chunk count, and
- the footer linked list stores subsequent chunk counts in order.

The temporary dcon-byte walker still needs refinement for the final chunk because constructor tag `0` is indistinguishable from zero-filled unused bytes if the walker scans until it sees a redirection or nil tag. A future validation should use the stored count as the scan bound for each chunk rather than treating zero bytes as evidence of additional constructors.

## Remaining Design Questions

The cyclic footer metadata design is now believed to be correct for oldgen chunks in the current prototype, but a few design choices still need to be cleaned up before building compiler vectorization on top:

- Expose helper APIs for generated/vectorized code rather than reaching into `GibOldgenChunkFooter` fields directly.
  - For example: get first count footer from an end footer, get next footer, get count by tag.
- Decide how much nursery support is needed. The current prototype mostly targets oldgen chunks; nursery scalar/tag-count metadata remains deliberately conservative.
- Rename the `scalar_count` API and compiler IR names to constructor/tag-count terminology once the prototype stops moving.
- Add a permanent validation test that checks the cyclic footer invariant using counts as scan bounds, so tag `0` does not collide with unused zero-filled bytes.

The generated bump placement that captures a pre-grow footer is intentional for this design: when a grow happens, the first write in the new chunk bumps the previous chunk's footer, which is exactly where the next-chunk count should live.

## Manual Examples Status

The manual proof-of-concept examples are not finished for the new tag-count design.

Earlier manual C work existed for:

- scalar recursive traversal,
- structurally flattened scalar loops,
- SSE/AVX vectorized loops,
- AVX on/off comparisons,
- and avoiding copies for unused buffers using indirections.

However, that work was based on the old per-field scalar-count metadata. After switching to constructor-tag counts, the manual C examples need to be updated or regenerated.

In particular:

- `gibbon-compiler/examples/soa_examples/programs/SOA/ScalarCountSmoke.c` may still contain old manual code and stale calls expecting per-field count APIs.
- `gibbon-compiler/examples/soa_examples/programs/SOA/ScalarCountMultiIntSmoke.c` should be treated as a manual/ignored smoke artifact that needs to be reconciled with the new tag-count footer API.

## Important Naming Debt

Several names still say `scalar_count`, including:

- RTS functions such as `gib_scalar_count_footer_bump`
- IR node `ScalarCountBump`
- flag `--store-scalar-field-counts`

The concept has changed to constructor/tag counts. Once the layout is correct, consider renaming these to avoid confusion:

- `gib_tag_count_footer_bump`
- `TagCountBump`
- `--store-constructor-counts`

For now, keeping the old names may be useful while the prototype is in motion, but it is already becoming semantically misleading.

## Milestones

### Milestone 1: Correct Constructor-Count Metadata Layout

Success criteria:

- Generated code emits one bump per constructor tag write, not per scalar field write.
- Single-chunk smoke test reports correct tag counts.
- Multi-chunk smoke test reports correct tag counts per chunk.
- For a multi-chunk value:
  - final/current end footer returns the first chunk count in O(1),
  - each redirection boundary/footer returns the next chunk count in O(1).

Current status:

- Bump shape and compiler generation are mostly done.
- Per-chunk tag counts are visible and plausible.
- Final/current footer returns the first chunk count.
- Footer linked-list counts match the subsequent chunk counts checked by the temporary probe.
- Milestone 1 still needs a permanent regression test and helper API cleanup, but the core cyclic layout is no longer blocked.

### Milestone 2: Rebuild the Manual POC Around Tag Counts

Success criteria:

- Update or regenerate `ScalarCountMultiIntSmoke.c`.
- Manually write an `add1MultiList` variant that:
  - reads constructor counts from footers,
  - loops by tag count,
  - applies `+1` to each `Int` field buffer,
  - does not recursively traverse the dcon buffer for independent work.
- Compare:
  - recursive scalar traversal,
  - flattened scalar loop with vectorization disabled,
  - vectorized loop using SSE2.

### Milestone 3: Clean Runtime and Compiler Naming

Success criteria:

- Rename the prototype from scalar-field counts to constructor/tag counts.
- Update debug output.
- Update flags and annotations.
- Keep backward compatibility only if needed for existing experiments.

### Milestone 4: Compiler-Generated Vectorized Traversal Prototype

Success criteria:

- For a small class of `OPT:CanVectorize` traversals, generate the flattened tag-count loop automatically.
- Start with simple list-like SoA types.
- Require no parent-child dependencies.
- Preserve normal recursive code path when the flag or annotation is absent.

### Milestone 5: Robustness and Layout Coverage

Success criteria:

- Validate redirections and indirections.
- Validate multiple constructors.
- Validate multiple scalar fields per constructor.
- Validate multi-region/multi-buffer SoA layouts.
- Decide what to do for more than 32 constructor tags.
- Decide whether nursery chunks need full support or can remain out of scope for the first prototype.

## Immediate Next Steps

1. Add small RTS helper functions for cyclic tag-count consumption.
2. Add a permanent validation test for single-chunk and multi-chunk cyclic footer metadata.
3. Update or regenerate `ScalarCountMultiIntSmoke.c` for the new tag-count API.
4. Rebuild the manual vectorization proof of concept on top of constructor counts.
5. Re-run recursive/scalar-loop/vectorized manual benchmarks only after the validation test is stable.

## Short Answer to the Current Status Question

Yes, the current prototype appears to have reached the intended cyclic footer layout for the oldgen multi-chunk smoke test.

What is working:

- The implementation is moving from per-field counts to per-constructor tag counts.
- Generated code can emit constructor-tag bumps.
- Runtime debug output shows plausible constructor counts per chunk.
- The final end-of-region footer returns the first chunk count.
- The footer linked list returns the following chunk counts in order.

What is not working yet:

- There is not yet a permanent regression test for the cyclic invariant.
- There are not yet helper APIs for vectorized traversal code to consume the footer list cleanly.
- The manual vectorization examples have not yet been completed for the new constructor-count design.

## 2026-05-16: Flat AoS Loopification Checkpoint

### What changed

- Added a separate flat-layout loopification pass in `gibbon-compiler/src/Gibbon/Passes/LoopifyFlatTraversals.hs`.
  - This pass is intentionally independent from the existing fully factored SoA loopifier in `LoopifyTraversals.hs`.
  - It fires only for functions annotated with `OPT:CanVectorize` whose mentioned datatype is not `FullyFactored`.
  - It reuses the existing parent-child dependency check from `LoopifyTraversals.hs`; if self-call-derived values affect parent writes, tags, conditions, or later traversal decisions, the function remains recursive.
  - It currently targets the mutable-cursor AoS cursorized shape.

- Added a new statement-like loop primitive:
  - L3: `WhileCursorEnd cur end body`
  - L4: `WhileCursorEndT ref endRef loopBody bod`
  - Codegen emits:
    `while (*cur != *end) { ... }`
  - This is distinct from existing `WhileCursor`, which means `while (*ref != NULL)` and is still used by SoA footer-chain loops.

- Wired the new pass into the compiler pipeline after `reorderScalarWrites` and before the existing SoA `loopifyTraversals` pass:
  1. `reorderScalarWrites`
  2. `loopifyFlatTraversals`
  3. `loopifyTraversals`
  4. `propagateScalarCounts`
  5. `selectiveBufferSharing`
  6. `fuseLoopifiedTraversals`

### AoS loopification invariant

For flat AoS, all constructor tags and fields are in one heterogeneous buffer. The pass therefore cannot use fixed-stride field loops, scalar-count footers, selective buffer sharing, or SIMD-friendly homogeneous buffers. Instead, it removes recursion by walking the packed value from its start cursor to its packed value end cursor.

The cursor-end fix in `Cursorize.hs` is essential here: for mutable calls, the input end argument now corresponds to the packed value end, not merely the current region/chunk end. The flat loop can therefore stop at `*input_cursor == *input_end`.

Each iteration executes the original one-node switch body with recursive self-calls erased to unit. Normal constructor cases consume one node and leave child nodes to be processed by later loop iterations. Redirection and indirection cases update the input cursor to the pointed-to target and then continue the loop.

### Normalization detail

`LoopifyFlatTraversals.hs` has a small pass-local normalizer, `exposeRhsLets`, because cursorized/reordered L3 can leave cursor temporaries inside a let RHS while later writes refer to those temporaries. Lowering flattens those RHS lets into C statements, but an L3 loop body is typechecked before lowering, so the pass makes the same sequencing explicit before inserting `WhileCursorEnd`.

### Validation performed

- Compiler build:
  - `cabal build exe:gibbon -j1`

- Temporary AoS list smoke:
  - Source: `/tmp/AOSListLoopifySmoke.hs`
  - Compiled with `--packed --to-exe --use-mutable-cursors`
  - Generated C contains `while (*lst_... != *end_r_...)` in `add1`.
  - Small output: `'#(44 44 8)`.
  - Large multi-chunk variant with `mkList 100000` output: `'#(5000150000 5000150000 100000)`.

- Temporary AoS ternary tree smoke:
  - Source: `/tmp/AOSTreeLoopifySmoke.hs`
  - `add1Tree` generated a flat cursor-end loop.
  - Loopified and recursive outputs both matched: `19682`.

- Full benchmark suite from `gibbon-compiler/examples/soa_examples`:
  - Command:
    `python3 gibbon_benchmark.py --clean --iterations 1 --store-scalar-field-counts --dump-raw --json /tmp/gibbon_benchmark_aos_loopification.json --report /tmp/gibbon_benchmark_aos_loopification.md`
  - Result: `22/22 succeeded | 22/22 output matches`.

### Remaining work

- Generalize flat AoS role inference beyond the current mutable-cursor shape if we want immutable-cursor AoS loopification too.
- Add dedicated regression tests for the flat AoS pass instead of relying only on temporary `/tmp` smoke files and the benchmark suite.
- Inspect generated AoS loopified C for complex maps and compare performance against recursive AoS; correctness is now stable, but the loop body still executes a switch per node and will not get the SoA/vectorization benefits.
- Keep selective buffer sharing and SIMD/vector IR SoA-only. They do not naturally apply to the flat heterogeneous AoS buffer.

## 2026-05-16: AoS Source Annotations And Benchmark Verification

### Confirmation

The AoS benchmark sources were missing `OPT:CanVectorize` annotations for the map traversals, so earlier full-suite runs were not fully exercising the new flat AoS loopification path. I mirrored the SoA map annotations into the corresponding AoS programs and intentionally left fold/non-map traversals unannotated.

Annotated AoS map functions:

- `AOS/List.hs`: `add1`
- `AOS/MonoTree.hs`: `add1Tree`
- `AOS/TernaryTree.hs`: `add1Tree`
- `AOS/Compiler.hs`: `targetRetunePass`, `stripSideEffectsPass`
- `AOS/DBQuery.hs`: `scaleCosts`, `clearQueryFlags`
- `AOS/DomTree.hs`: `scaleLayout`
- `AOS/ObjectGraph.hs`: `sweepUnmarked`, `touchHotObjects`
- `AOS/OctTree.hs`: `scaleEnergy`, `clearFlags`
- `AOS/OctTreeBase.hs`: `scaleEnergy`, `clearFlags`
- `AOS/PiecewiseFunctions.hs`: `addConstPW`, `diffPW`
- `AOS/Trie.hs`: `decayTrieStats`, `resetTraversalState`

No `OPT:CanVectorize` annotation was added to `AOS/ColorOctree.hs` because its benchmarked passes are folds, not maps.

### Lowering fix exposed by AoS annotations

After the annotations were added, the full benchmark suite exposed an AoS lowering failure in `ObjectGraph`: `unitTail` rejected value returns from scalar conditional bindings inside a statement loop, for example a loop body containing `let size_prime = if ... then ... else ...`.

The fix is in `gibbon-compiler/src/Gibbon/Passes/Lower.hs`: when `unitTail` sees `LetIfT` with non-empty bindings, it now preserves the branch value returns and only forces the continuation to unit. For statement-only conditionals with no bindings, it still requires unit branches. This keeps loop bodies statement-like without erasing values needed by local scalar bindings.

### Verification

- Rebuilt the compiler with `cabal build exe:gibbon -j1`.
- Targeted rerun:
  `python3 gibbon_benchmark.py --clean --iterations 1 --programs ObjectGraph.hs --store-scalar-field-counts --dump-raw --json /tmp/gibbon_benchmark_objectgraph_fix.json --report /tmp/gibbon_benchmark_objectgraph_fix.md`
  Result: `1/1 succeeded | 1/1 output matches`.
- Full rerun:
  `python3 gibbon_benchmark.py --clean --iterations 1 --store-scalar-field-counts --dump-raw --json /tmp/gibbon_benchmark_aos_annotations_after_fix.json --report /tmp/gibbon_benchmark_aos_annotations_after_fix.md`
  Result: `22/22 succeeded | 22/22 output matches`.

Generated AoS C now visibly contains flat cursor-end loops for representative annotated maps, for example:

- `benchmark_output/List.aos.c`: `while (*lst_... != *end_r_...)`
- `benchmark_output/MonoTree.aos.c`: `while (*t_... != *end_r_...)`
- `benchmark_output/ObjectGraph.aos.c`: two loopified map traversals
- `benchmark_output/OctTree_scaleEnergy.aos.c`: loopified `scaleEnergy`
- `benchmark_output/PiecewiseFunctions.aos.c`: loopified `addConstPW` and `diffPW`
- `benchmark_output/Trie.aos.c`: loopified `decayTrieStats` and `resetTraversalState`

## 2026-05-16: Removed Dead `--SoA` Flag

### Confirmation

The old compiler flag `--SoA` / `Opt_Packed_SoA` was a dead or misleading layout switch. Packed layout is selected by source annotations on datatype definitions, not by this command-line flag:

- `ANN type T "Factored"` sets the datatype memory layout to `FullyFactored`.
- `ANN type T "Linear"` keeps the datatype in the flat linear/AoS layout.
- Unannotated datatypes default to `Linear`.

The audit found that `--SoA` no longer controlled source layout. Its only remaining semantic use was an old compiler-pipeline guard that skipped `parAlloc`. That guard now checks the actual datatype definitions instead: if any `DDef` has `memLayout == FullyFactored`, the pipeline skips `parAlloc`; otherwise it runs as before.

### Flag cleanup

Removed from the compiler:

- `Opt_Packed_SoA`
- the `--SoA` command-line parser entry
- stale benchmark/script references to `--SoA`

The optimization flags are now one-way opt-in flags, all defaulting off:

- `--enable-loopification` / `--loopify-traversals`
- `--enable-loop-fusion` / `--loop-fusion`
- `--enable-selective-buffer-sharing` / `--selective-buffer-sharing`
- `--store-scalar-field-counts`

There are no paired disable flags in the compiler or benchmark driver.

### Layout/Optimization split

AoS/linear layout:

- can use flat map loopification when a traversal is annotated `OPT:CanVectorize`;
- does not need scalar-count footers;
- does not use selective buffer sharing;
- does not use loop fusion;
- is not the SIMD-friendly path because fields live in one heterogeneous buffer.

Fully factored SoA layout:

- can use scalar-counted per-buffer loopification;
- needs `--store-scalar-field-counts` for footer loop bounds;
- can use selective buffer sharing after loopification;
- can use loop fusion after selective sharing;
- is the vectorization-friendly representation because scalar buffers are homogeneous.

The benchmark driver enforces this split at command construction time: scalar counts, selective sharing, and loop fusion are passed only to SoA variants, while loopification can be passed to both AoS and SoA variants. Benchmark labels now print the effective optimization set for each compiled variant, e.g. `AOS mut-cursors,loopify` versus `SOA mut-cursors,loopify,scalar-counts,selective-sharing,loop-fusion`.

### Validation

- `rg` sweep over `gibbon-compiler/src` and `gibbon-compiler/examples` found no remaining `Opt_Packed_SoA`, `--SoA`, or `Packed_SoA` references.
- `cabal build exe:gibbon -j1` succeeded.
- `cabal run exe:gibbon -- --help` shows no `--SoA` option and only the enable-style optimization flags.
- `python3 gibbon-compiler/examples/soa_examples/gibbon_benchmark.py --help` shows no `--SoA` or disable-style optimization flags.
- Paper-mode smoke:
  `python3 gibbon_benchmark.py --clean --iterations 1 --programs List.hs --enable-loopification --store-scalar-field-counts --enable-selective-buffer-sharing --enable-loop-fusion --generate-paper --report /tmp/gibbon_list_opt_report.txt --json /tmp/gibbon_list_opt_results.json --latex-table /tmp/gibbon_list_opt_table.tex --figures-dir /tmp/gibbon_list_opt_figures`
  Result: `1/1 succeeded | 1/1 output matches`; LaTeX table generation succeeded. Figures were skipped only because matplotlib/numpy are not installed in this environment.


## 2026-05-25: Prototype `--int32` Backend Mode and SSE2 Int32 Vectorization

### Goal

Add an opt-in compiler mode that represents Gibbon `Int` values as 32-bit payloads in generated C and packed layouts, while preserving the existing 64-bit `Int` mode as the default. This is intended to let fully factored loopified maps use four 32-bit lanes with SSE2 instead of two 64-bit lanes.

### Compiler flag

Added a one-way opt-in flag:

- `--int32`
- alias: `--gibbon-int32`

The flag is represented as `Opt_Int32` in `gibbon-compiler/src/Gibbon/DynFlags.hs`.

### Runtime / generated C representation

Implemented in `gibbon-rts/rts-c/gibbon_rts.h`:

- default: `typedef int64_t GibInt;`
- with generated `#define GIBBON_INT32 1`: `typedef int32_t GibInt;`

`Codegen.hs` now emits `#define GIBBON_INT32 1` before including `gibbon_rts.h` when the flag is enabled. RTS print helpers use `GIBBON_PRIdInt` for `GibInt` values; `GibSym` remains 64-bit and still prints with `PRIu64`.

### Width-aware packed layout

Added `sizeOfTyD :: DynFlags -> UrTy a -> Maybe Int` in `gibbon-compiler/src/Gibbon/Language.hs`. The legacy `sizeOfTy` remains 64-bit for compatibility. `sizeOfTyD` changes only `IntTy` from 8 bytes to 4 bytes under `Opt_Int32`; pointer-sized things, symbols, cursors, redirection payloads, and region metadata stay 8 bytes.

The int-width-aware helper is now used in layout-sensitive paths:

- `InferLocations.hs`: constructor scalar field offsets.
- `Cursorize.hs`: explicit scalar cursor bumps and `RequestSizeOf`.
- `LoopifyTraversals.hs`: loopified scalar-buffer cursor steps.
- `Lower.hs`: info table scalar byte sizes.
- `CalculateBounds.hs`, `RouteEnds.hs`, `ThreadRegions.hs`, `ThreadRegions2.hs`: bounds/jump calculations that depend on scalar byte width.

### SSE2 vector backend

`Codegen.hs` now has SSE2 helper families for both integer widths:

- default `Int`: `int64x2`, two lanes in `__m128i`.
- `--int32`: `int32x4`, four lanes in `__m128i`.

Efficient SSE2 lowering exists for `broadcast`, `load`, `store`, `add`, `sub`, and equality. Multiplication/division/modulo are present as scalar fallback helpers because SSE2 does not provide general packed 32-bit integer division/modulo, and packed low 32-bit multiply is not available until later SIMD extensions.

`VectorizeTraversals.hs` now selects `Int` vector lanes from the dynamic integer width:

- 64-bit `Int`: 2 lanes per vector group.
- 32-bit `Int`: 4 lanes per vector group.

The high-level vectorizer still only rewrites clearly supported loop bodies and leaves unsupported loops unchanged.

### Validation

Compiler build:

- `cabal build exe:gibbon` succeeds.

Flag visibility:

- `cabal run gibbon-compiler:exe:gibbon -- --help` shows `--gibbon-int32,--int32`.

SoA/vectorized smoke:

- Compiled `programs/SOA/List.hs` with `--packed --to-exe --use-mutable-cursors --store-scalar-field-counts --enable-loopification --enable-vectorization --int32`.
- Generated C contains `#define GIBBON_INT32 1`.
- Generated C uses 4-byte `Int` field offsets and `gib_vec_*_int32x4` in the hot loop.
- Running the executable succeeds. The printed sums overflow relative to the 64-bit baseline, which is expected because this mode intentionally changes `Int` semantics to 32-bit.

Default 64-bit regression smoke:

- Compiled the same `SOA/List.hs` command without `--int32`.
- Generated C uses 8-byte `Int` field offsets and `gib_vec_*_int64x2`.
- Running the executable succeeds and preserves the old 64-bit sum output.

AoS/flat smoke:

- Compiled `programs/AOS/List.hs` with `--packed --to-exe --use-mutable-cursors --int32`.
- Generated C uses `sizeof(GibInt)` or 4-byte cursor bumps for integer payloads, while pointer/redirection movement remains 8 bytes.
- Running the executable succeeds, again with expected 32-bit overflow in sum results.

### Remaining work

- Audit `gibbon-rts/rts-ng/src/ffi.rs` if the Rust RTS path is needed; it still assumes `GibInt = i64`.
- Run a broader benchmark sweep under `--int32`. Many fold outputs will legitimately differ from 64-bit due to overflow, so correctness checks need an int32-aware baseline.
- Consider adding explicit `Int32Ty` / `Int64Ty` later if mixed-width programs become useful. The current design is deliberately simpler: one source-level `IntTy`, with backend width selected by flag.
- Future SIMD backend work: AVX2/AVX512 lane families can reuse the same vector IR and lane-selection layer.


## 2026-05-26: `--int32` Benchmark Coverage And Layout-Comparison Variant

The benchmark scripts now expose the 32-bit backend mode directly.

### `gibbon_benchmark.py`

- Added `--int32` / `--gibbon-int32`.
- The flag is threaded through every Gibbon compile task and appends `--int32`
  to the compiler command for both AoS and SoA Gibbon variants.
- Compile labels include `int32`, so logs make the active integer width visible.
- The run header prints `Int width: 32-bit (--int32)` or `64-bit default`.
- Correctness checks compare AoS-int32 output against SoA-int32 output. They do
  not compare against 64-bit output, because 32-bit `GibInt` intentionally
  changes overflow behavior.

Validation:

```text
cd gibbon-compiler/examples/soa_examples
python3 gibbon_benchmark.py \
  --clean \
  --iterations 1 \
  --warmup-runs 0 \
  --cooldown-seconds 0 \
  --int32 \
  --output-dir /tmp/gibbon_benchmark_int32_all \
  --json /tmp/gibbon_benchmark_int32_all.json \
  --report /tmp/gibbon_benchmark_int32_all.txt
```

Result:

```text
DONE - 22/22 succeeded | 22/22 output matches
```

This verifies the default benchmark corpus under 32-bit `GibInt` for the
standard mutable AoS/SoA Gibbon variants.


A second full-suite run validated the optimized int32 path used by the parent
layout comparison variant:

```text
cd gibbon-compiler/examples/soa_examples
python3 gibbon_benchmark.py \
  --clean \
  --iterations 1 \
  --warmup-runs 0 \
  --cooldown-seconds 0 \
  --store-scalar-field-counts \
  --enable-loopification \
  --enable-selective-buffer-sharing \
  --enable-vectorization \
  --int32 \
  --output-dir /tmp/gibbon_benchmark_int32_opt_all \
  --json /tmp/gibbon_benchmark_int32_opt_all.json \
  --report /tmp/gibbon_benchmark_int32_opt_all.txt
```

Result:

```text
DONE - 22/22 succeeded | 22/22 output matches
```

This checks the `loopification + scalar counts + selective sharing +
vectorization + int32` path across the default benchmark corpus.

### `benchmark_layout_versions.py`

The parent layout-comparison script now uses one integer-width mode for the
entire comparison matrix:

- default: normal 64-bit `GibInt` backend;
- `--32-bit` / `--int32`: run the same recursive, loopified, selective-sharing,
  and vectorized comparison matrix with 32-bit `GibInt`.

The script no longer adds separate int32-only columns to the normal 64-bit
report. Instead, generate a 32-bit report explicitly, for example:

```text
python3 benchmark_layout_versions.py \
  --32-bit \
  --clean \
  --iterations 1 \
  --warmup-runs 0 \
  --cooldown-seconds 0 \
  --programs List.hs \
  --output-dir /tmp/layout_versions_width_smoke \
  --results-file /tmp/layout_versions_width32.md
```

The default 64-bit mode uses the same version columns and omits `--int32`:

```text
python3 benchmark_layout_versions.py \
  --clean \
  --iterations 1 \
  --warmup-runs 0 \
  --cooldown-seconds 0 \
  --programs List.hs \
  --output-dir /tmp/layout_versions_width_smoke \
  --results-file /tmp/layout_versions_width64.md
```

Implementation notes:

- child `gibbon_benchmark.py` commands receive `--int32` only when the parent
  receives `--32-bit` / `--int32`;
- outputs are namespaced under `int32/` or `int64/` inside the chosen output
  directory to avoid stale executable reuse across integer-width modes;
- generated Markdown reports include an `Int width: ...` line near the top;
- the table columns are the same in both modes: AoS recursive, AoS loopified,
  SoA recursive, SoA loopified, SoA loop+share, and SoA loop+share+vec.

Validation smoke:

- 64-bit default `List.hs` parent run wrote `/tmp/layout_versions_width64.md`
  and reported `Int width: 64-bit GibInt`.
- 32-bit `List.hs` parent run wrote `/tmp/layout_versions_width32.md`, passed
  `--int32` to every child benchmark configuration, and reported
  `Int width: 32-bit GibInt`.
- In both smokes, the known immutable-cursor `List.hs` failures remain isolated
  to historical non-mutable variants; successful mutable variants still match.


## Latest Update: Layout Benchmark Runtime Answers Added (2026-05-28)

The `examples/layout_benchmarks` directory is now represented in the examples
suite, and the subset that currently runs under the vanilla packed baseline now
has reduced runtime tests with golden answer files.

### Runnable Layout Benchmarks

Five root layout benchmark programs currently execute successfully under
vanilla packed Gibbon after source reduction:

- `Adts.hs`
- `Contents.hs`
- `calcAdtLengthAc.hs`
- `calcAdtLengthCa.hs`
- `processAdtContentCA.hs`

For these, `gibbon-compiler/tests/test-gibbon-examples.yaml` now removes the old
`compile-only` marker and adds:

- `answer-file: examples/layout_benchmarks/reduced_answers/<name>.ans`
- `source-replacements` to shrink benchmark-sized inputs to unit-test sizes
- `compare-with-baseline: true`

The generated answer files live in:

```text
gibbon-compiler/examples/layout_benchmarks/reduced_answers/
```

The source reductions used for these layout tests include large list/tree/string
sizes such as `3000000`, `1000000`, `100000`, `80000`, `10000`, `3000`, `2000`,
`1000`, `100`, `50`, and `10`, reducing them to small values while leaving the
original benchmark sources untouched. The test runner applies these rewrites to
a temporary copy before compiling/running the test.

### Validation Performed

Focused runtime validation was run for the five runnable layout benchmarks in
both 64-bit and 32-bit packed modes. Each reduced program matched its stored
answer file:

```text
PASS Adts.hs gibbon2
PASS Adts.hs int32
PASS Contents.hs gibbon2
PASS Contents.hs int32
PASS calcAdtLengthAc.hs gibbon2
PASS calcAdtLengthAc.hs int32
PASS calcAdtLengthCa.hs gibbon2
PASS calcAdtLengthCa.hs int32
PASS processAdtContentCA.hs gibbon2
PASS processAdtContentCA.hs int32
```

A broader `gibbon2` examples-suite slice was also run with `--skip-failing` and
`GIBBONDIR=/workdisk/git/gibbon`. It completed answer generation and executed
the suite; none of the new layout answer-file tests appeared in the unexpected
failures. The remaining unexpected failures in that broad slice were unrelated
pre-existing examples/SoA benchmark cases such as `AnonLambdas.hs`, `SS.hs`,
`T64_1.gib`, several OctTree benchmark entries, and a few import examples.
Those are not part of the current layout-benchmark answer-file change.

### Non-Runnable Layout Cases

The rest of `examples/layout_benchmarks` remains listed in the YAML, but is
skipped or expected-failing for this phase when vanilla packed mode already
fails before the optimization flags matter. Reasons observed during reduced
classification include:

- missing/import-side failures in `blog_management/marmoset` examples
  (`Gibbon.Maybe`);
- unsupported memory-layout frontend paths (`Memory Layout not yet supported!`);
- existing cursor/typechecking failures such as `CursorTy <> MutCursorTy` or
  `StartOfPkdCursor` over non-packed values;
- baseline packed runtime segfaults in `processAdtTagsCat2.hs` and
  `processAdtTagsCta.hs`, even with tiny source reductions.

Those are Phase 3 packed-field/layout/mutable-cursor issues or historical bug
reproducers, so they were not fixed here. The important invariant for Phase 1 is
that layout benchmarks which can currently run under the vanilla packed baseline
now run on small inputs and check stored answers.


## Latest Update: Phase 2 Auto Loopification Completed (2026-05-28)

Phase 2 added an opt-in automatic loopification discovery mode. The goal was to stop relying exclusively on manual `OPT:CanVectorize` annotations while still preserving the safety boundary: only map-like traversals with no parent-child dependencies should be rewritten.

### Compiler Flag

A new general flag was added in `gibbon-compiler/src/Gibbon/DynFlags.hs`:

```text
--auto-loopification
--infer-can-vectorize
```

This flag is intentionally separate from `--enable-loopification`. Loopification still only runs when `--enable-loopification` is set. Automatic discovery is enabled only when the new flag is also set.

The benchmark/test harnesses now pass this flag automatically for loopification-oriented modes:

- `gibbon-compiler/examples/soa_examples/gibbon_benchmark.py`
- `benchmark_layout_versions.py`
- `gibbon-compiler/tests/TestRunner.hs`

The benchmark banner now reports loopification as:

```text
Loopification: enabled (--enable-loopification + --auto-loopification)
```

### SoA Loopification Changes

Implemented in `gibbon-compiler/src/Gibbon/Passes/LoopifyTraversals.hs`.

Key changes:

- exported `loopifyCandidateInfoWith`;
- preserved the old manual behavior through `loopifyCandidateInfo = loopifyCandidateInfoWith False`;
- added auto mode through `loopifyCandidateInfoWith True`;
- when a function is successfully inferred and rewritten, the pass stamps `CanVectorize` onto the function metadata so later passes such as selective sharing, loop fusion, and vectorization can reuse the same signal;
- automatic mode skips generated packed helper functions:
  - `_copy_*`
  - `_copy_without_ptrs_*`
  - `_print_*`
  - `_traverse_*`
  - `_unpack_*`
  - `_add_size_and_rel_offsets_*`

The generated-helper exclusion fixed a real corpus bug: `DecisionTree.hs` contains only folds, but auto mode was previously rewriting generated `_copy_DTree`, which changed successful output comparison. After the exclusion, `DecisionTree.hs` has no accidental loopification markers and its AoS/SoA outputs match again.

### AoS Flat Loopification Changes

Implemented in `gibbon-compiler/src/Gibbon/Passes/LoopifyFlatTraversals.hs`.

The flat AoS pass now follows the same auto-discovery policy:

- manual `OPT:CanVectorize` still works;
- `--auto-loopification` may infer unannotated source-level candidates;
- generated packed helpers are ignored in auto mode;
- parent-child dependency checks still reject fold-like traversals.

AoS loopification remains structural and does not use scalar-count footers, selective sharing, loop fusion, or SIMD.

### Parent-Child Dependency Fix

The syntactic dependency check in `LoopifyTraversals.hs` was tightened. Before this fix, a fold-like function could slip through if a recursive child result was only used inside a primitive expression. For example:

```haskell
child_sum = sumList ...
total = child_sum + 1
```

The checker now treats child-derived variables as parent-child dependencies when they appear in:

- function-call arguments;
- primitive-call arguments;
- product construction;
- spawn arguments;
- return values;
- conditionals and case scrutinees;
- scalar/tag/cursor writes;
- loop bounds.

A dedicated unit test now covers primitive RHS use of a child result.

### Unit Tests

Updated `gibbon-compiler/tests/LoopifyTraversals.hs`.

New coverage includes:

- auto mode detects an unannotated source candidate;
- auto mode rewrites an unannotated cursorized fast path;
- auto mode stamps `CanVectorize` after a successful rewrite;
- auto mode skips generated helpers such as `_copy_List`;
- primitive use of a child-derived value is rejected as a parent-child dependency.

The test-suite Cabal stanza was also cleaned up in `gibbon-compiler/gibbon.cabal` by removing stale missing test modules that blocked `test-gibbon` from building.

Validation:

```text
cd gibbon-compiler
cabal run test-gibbon
```

Result:

```text
All 66 tests passed
```

### End-to-End Validation

A temporary unannotated copy of `examples/vectorization/SOA/VectorListMap.hs` was compiled with:

```text
--run --packed --use-mutable-cursors \
--store-scalar-field-counts \
--enable-loopification --auto-loopification
```

Result:

- output was correct: `2272`;
- generated C for `add3` contained counted loopification markers:
  - `loop_mut...`
  - `while`
  - counted `for`
  - `gib_scalar_count_footer_get`.

The same temporary source compiled without `--auto-loopification` stayed recursive, confirming the new behavior is opt-in.

The default SoA benchmark corpus was then run with auto loopification enabled:

```text
cd gibbon-compiler/examples/soa_examples
python3 gibbon_benchmark.py \
  --iterations 1 \
  --warmup-runs 0 \
  --cooldown-seconds 0 \
  --clean \
  --store-scalar-field-counts \
  --enable-loopification \
  --output-dir /tmp/gibbon_phase2_loopify_full_after_fix \
  --json /tmp/gibbon_phase2_loopify_full_after_fix.json \
  --report /tmp/gibbon_phase2_loopify_full_after_fix.txt
```

Result:

```text
DONE - 21/22 succeeded | 21/21 output matches
```

The one compile failure is `DomTree.hs` in the AoS mutable-cursor variant:

```text
gibbon: lower/triv, expected trivial in one of app rands, got LetE (... DerefMutCursor ...)
```

This is the known mutable-cursor packed-field/lower-trivialization class of issue and belongs to Phase 3. The successful variants all matched their AoS/SoA output checks after the Phase 2 fixes.

Spot checks of generated C confirmed:

- map examples such as `List.add1`, `MonoTree.add1Tree`, `OctTree_scaleEnergy.scaleEnergy`, `PiecewiseFunctions.addConstPW`/`diffPW`, and Trie map passes contain loopified counted-buffer code in SoA;
- fold-only examples such as `DecisionTree`, `KDTree`, and the OctTree fold drivers no longer show accidental `loop_mut` / scalar-count loopification markers.

### Phase 2 Status

Phase 2 is complete enough to proceed to Phase 3:

- automatic source-candidate discovery exists behind an explicit flag;
- manual annotation behavior is preserved;
- generated helpers are protected from accidental inference;
- parent-child dependency rejection was strengthened;
- test coverage was added;
- corpus validation passes for all successful benchmark variants.

Next phase should address the mutable-cursor packed-field/lower-trivialization bug, starting with the `DomTree.hs` AoS failure.
