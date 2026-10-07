# Gibbon Benchmark Suite v2.4

Benchmarks **AoS** (Array of Structs) vs **SoA** (Struct of Arrays) Gibbon
compiler programs and produces publication-quality figures and LaTeX tables for
conference papers.

---

## Integer width is a source property

There is no whole-program width mode.  `--int32`/`--gibbon-int32`/`--32-bit`
were removed from the compiler and from these drivers; the old spellings are
recognized only to reject them with an actionable message.

Width is declared by the source program: `Int8`, `Int16`, `Int32`, `Int64`, and
bare `Int`, which means `Int64`.  A program may mix widths in one datatype, in
which case it has no single width at all.  To compare widths, write explicit
width variants as separate source programs.

`programs/{AOS,SOA}/MixedWidthSmoke.hs` is the paired explicit-width driver
smoke fixture (Int8 + Int16 + Int32 + Int64 in one constructor).

## SSE2 and SSE4.1

* Gibbon's explicit SIMD baseline is **SSE2**.
* `--sse4.1` raises the selected instruction set to `sse4.1`, equivalently
  `--simd-isa=sse4.1`.  It adds `-msse4.1` to the generated C translation unit,
  so it is still an ISA permission for the C compiler and its own
  auto-vectorizer -- independent of `--opt-vectorization` (Gibbon's SIMD pass)
  and of `--no-gcc-vectorize` -- but it now also changes what Gibbon emits.
* W32 multiplication is emitted as `_mm_mullo_epi32` at `sse4.1` and above, and
  as an equivalent `_mm_mul_epu32` plus shuffle/interleave sequence at baseline
  SSE2.  Gibbon picks the one that matches the selected ISA; the generated C
  contains only that one.
* W64 equality is the same: `_mm_cmpeq_epi64` at `sse4.1` and above, a
  lane-at-a-time comparison at baseline SSE2.
* W64 ordered comparisons need SSE4.2 (`_mm_cmpgt_epi64`) or an emulation, and
  remain scalar.
* General packed integer division/modulus does not exist in SSE4 and remains
  scalar.

## Quick Start

```bash
# 1 – install Python deps (once)
pip install matplotlib numpy

# 2 – run all programs, generate paper materials
./gibbon_benchmark.py --generate-paper

# 3 – single program, lots of iterations
./gibbon_benchmark.py --programs DomTree.hs --iterations 50 --generate-paper

# 4 – force recompile everything then generate paper
./gibbon_benchmark.py --clean --generate-paper
```

---

## Directory Layout

```
project/
├── gibbon_benchmark.py             # ← main script (Python ≥ 3.8)
├── gibbon_benchmark.sh             # ← bash wrapper / convenience shortcuts
├── benchmark_layout_versions.py    # ← layout-version comparison driver (wraps
│                                   #   gibbon_benchmark.py)
├── check_intensity_codegen.py      # ← acceptance check for the arithmetic-
│                                   #   intensity programs (see below)
├── plot_scalar_count_smoke_sweep.py# ← ScalarCountSmoke sweep + SVG plot
├── clean.sh                        # ← remove compiled outputs & paper materials
├── README.md
├── experiments/                    # ← manual C experiments that shaped the
│   ├── scalar_count_smoke/         #   loopified codegen strategy
│   ├── simple_test/                #   (chunked-array prototypes)
│   └── replot_benchmark_figures.py
├── microbench/                     # ← standalone SoA C microbenchmarks
│   ├── soa/
│   ├── manual_soa_examples/
│   └── factored_out/
└── programs/
    ├── AoS/
    │   ├── DomTree.hs
    │   ├── Compiler.hs
    │   └── ...
    └── SoA/
        ├── DomTree.hs
        ├── Compiler.hs
        └── ...
```

After running the benchmark:

```
project/
├── benchmark_output/         # compiled .exe and .c files
├── benchmark_report.txt      # human-readable summary
├── benchmark_results.json    # machine-readable full results
├── performance_table.tex     # LaTeX tables (multiple)
└── figures/
    ├── speedup_comparison.pdf/png   # fold vs map overall speedup
    ├── pass_breakdown_all.pdf/png   # stacked bars all programs
    ├── table_preview.pdf            # rendered table (needs pdflatex)
    ├── per_program/
    │   ├── DomTree.pdf/png          # all passes + error bars + geomean
    │   ├── Compiler.pdf/png
    │   └── ...
    └── heatmaps/
        ├── DomTree_heatmap.pdf/png  # per-pass speedup heatmap
        └── ...
```

---

## Arithmetic-Intensity Programs — run the acceptance check

`programs/{SOA,AoS}/MapIntensityV2.hs` sweeps arithmetic intensity while holding
memory traffic fixed. It only measures intensity if the arithmetic it declares
actually survives into the generated code, and **it repeatedly has not**:

- constant multipliers were strength-reduced to shift+add (zero multiplies emitted);
- `sum_k (i + c_k) * m` was reassociated to `m * (N*i + sum c_k)` — one multiply
  at every N;
- seeding extra chains from affine offsets of `i` collapsed again under CSE.

Every one of these collapses is **silent**. The benchmark still runs, still
produces a table, and the table means nothing. Before citing any intensity
number, run:

```bash
./check_intensity_codegen.py                 # SoA (width read from the source)
./check_intensity_codegen.py --layout AOS
./check_intensity_codegen.py --int64
```

It builds scalar and `--sse4.1` configurations, disassembles each map function's
innermost multiply-carrying loop, and asserts the multiply counts declared in
`EXPECTED_MULTIPLIES` — plus no `pslld` (strength reduction), no scalarized
`imul` inside a vector loop, and a 16-byte pointer stride (real cross-element
SIMD rather than SLP within a single element). Or fold it into a benchmark run:

```bash
./benchmark_layout_versions.py --verify-intensity-codegen ...   # verify only
./benchmark_layout_versions.py --intensity-report ...            # verify + detailed report
```

The three families in that program are **not** interchangeable:

| Family | Multiplies/element | ILP | What it measures |
|---|---|---|---|
| `mapSer<N>` | N | 1 | latency ceiling — one serial Horner chain |
| `mapChain<D>` | 2D+2 | 2 | effect of added ILP at matched intensity |
| `mapPar<N>` | **1, at every N** | — | reassociation **control**, not an intensity point |

`mapPar` is retained deliberately, and the checker asserts its collapse. Do not
cite it as evidence about arithmetic intensity.

---

## Fold / Map Classification

The script automatically detects whether each pass is a **fold** or **map**
by reading the print statements already in your source code.

**Required format** (already in your programs):

```haskell
_ = printsym (quote "Running pass SumArea (fold): ")
_ = printsym (quote "Running pass scaleLayout (map): ")
_ = printsym (quote "Running pass nearestDist (fold like): ")
```

The keyword inside parentheses can be:
- `fold`, `fold like`, `fold-like` → classified as **fold**
- `map`, `map like`, `map-like` → classified as **map**

When you run the script you will see:

```
======================================================================
Detecting fold/map classification from source print statements ...
======================================================================
  ✓ DomTree.hs: 'SumArea' → fold  (keys e.g. ['SumArea', 'sumarea', 'SumAreaPass'])
  ✓ DomTree.hs: 'scaleLayout' → map
  ⚠  OtherProg.hs: no fold/map annotations found
======================================================================
```

If a pass cannot be matched it shows `?` in the table — check that your
print-statement name matches the pass key printed in benchmark output.

### Folds and maps are reported separately

`benchmark_layout_versions.py` emits each program's passes in **separate map and
fold sections**, because they are not comparable: only map passes are eligible
for loopification, selective buffer sharing and SIMD vectorization, so only they
carry the vectorizer columns. A program with only folds gets only a fold section.

### Two report modes

By default the sweep runs and reports **one** vectorized configuration —
`loop+share both vec`: both vectorizers on, i.e. every vectorization capability
the selected ISA offers. Splitting that into the full 2x2 (GCC's
auto-vectorizer and Gibbon's SIMD pass varied independently) exists to
*attribute* a speedup between them, which is the point of the
arithmetic-intensity experiment and noise on application traversals — measured
over the suite's 17 map passes, the configurations differ by ~9% end to end
and mostly reflect code layout. The rest are therefore neither built nor
reported.

The SSE4.1 axis (`ls_gibvec_sse41`, `ls_both_sse41`) is built only at
`--simd-isa=sse2`. Every wider ISA already includes SSE4.1, so at the driver's
`avx2` default those two configurations compiled identically to their
non-SSE4.1 twins. **Any recorded number attributed to that axis at an ISA other
than `sse2` — including the "fastest of the six" headline of 0.2773s against
0.2800s — is two measurements of the same compile and needs re-measuring.**

`--intensity-report` switches to **arithmetic-intensity mode** (and implies
`--verify-intensity-codegen`): the full
vectorizer matrix, plus a per-map **vectorization vs loop+share scalar** table —
`(pass, mul/el, ILP, scalar, SSE4.1, speedup)`. Read *that* table for what
vectorization bought you, not the AoS-baseline tables: those divide by AoS
recursive, whose cost also grows with arithmetic intensity, so their ratio
*shrinks* as intensity rises even while vectorization is helping more.

`ILP` comes from an optional `ilp=N` pass annotation (see `ANNOTATIONS.md`);
`mul/el` is measured from the generated assembly, not declared.

Fold sections carry **only the layout and traversal columns** (AoS/SoA x
immutable/mutable recursive). The loopification, buffer-sharing and vectorizer
columns are omitted because those flags fire exclusively on `OPT:MayVectorize`
passes -- a fold-only program compiles to byte-identical C in all of them
(verified by diffing the generated code), so any difference in those columns is
code layout and allocator state, not an optimization.

### Fold-only programs skip the map configurations

For the same reason, a program declaring no map pass is **not built or run** in
the loopification/sharing/vectorization configurations at all. Half the default
suite is fold-only (11 of 22), so this removes ~44% of the builds and runs from
a full sweep.

The three whole-program summary tables (Total Timed Pass Runtime, Speedup, Run
Status) are split the same way: a **Programs with map passes** table with all
columns, and a **Fold-only programs** table with just the four layout/traversal
columns. `missing` in Run Status means a configuration ran but produced no row —
worth investigating — since configurations that were deliberately skipped are no
longer shown as columns at all.

Pass `--no-skip-mapless` to run them anyway -- e.g. to measure the
representation cost that `--store-scalar-field-counts` imposes on folds, which
is a real effect (it adds scalar-count footers that fold traversals must step
over) and the one thing the skip hides.

---

## Choosing PLDI configurations (`--pldi-config`)

`--pldi-submission` compiles and runs a fixed matrix of configurations per
program. To run only some of them, or to add an opt-in configuration, list them
in a TOML file and pass it with `--pldi-config`:

```toml
[pldi]
configs = ["aos_imm", "aos_mut", "soa_mut", "ptr"]
```

```bash
./gibbon_benchmark.py --pldi-submission --pldi-config my_configs.toml --generate-paper
```

`pldi_configs.example.toml` lists every name with a one-line description; copy
it and delete what you do not want. Without `--pldi-config` the default matrix
runs, unchanged.

- **Order** does not matter: columns keep the standard order.
- **Delta columns** appear only when both configurations they compare are
  selected. A summary table whose two configurations were not both selected is
  replaced by a one-line note.
- **The `-av` twins** (`*_navec`) are not named in the file. `--av-variants`
  still adds them, for whichever of their bases are selected.
- **Replotting** (`--figures-from-json`) takes the same `--pldi-config`, so
  stored results render with the columns they were collected for.
- Unknown names, duplicates, unknown keys and an empty list are errors, reported
  before anything is compiled.

### The pointer-based configuration (`ptr`)

`ptr` is opt-in. It compiles the **AoS** source with `gibbon --pointer` instead
of `--packed`: one heap object per node, allocated with `malloc` (the runtime
links the Boehm GC but pointer mode does not use it, so `--no-gc` changes
nothing), which is how an ordinary functional program represents a tree. It appears in its own
**Pointer** column group ($P$), checked against the same oracle as every other
configuration. It is not a packed layout, so it takes no part in the
$A^{\min}/S^{\min}$ column. Its delta column $\Delta^{P}_{pk}$ compares it
against vanilla Gibbon ($A_{ri}$), and is positive when packed is faster.

### Tree traversals across input sizes and languages (`--tree-sweep`)

MonoTree's three traversals, `buildTree`, `add1Tree` and `sumTree` (the three
panels of Figure 4 in the ECOOP 2017 Gibbon paper), at every tree depth from a
cache-resident tree to one far past the last-level cache, for Gibbon and for the
same program in other languages:

```bash
python3 gibbon_benchmark.py --tree-sweep --iterations 21 --cc gcc-16 \
  --output-dir tree_sweep_out --figures-dir tree_sweep_out/figures
```

- **Gibbon:** `tree_sweep/programs/{AOS,SOA}/MonoTree{BuildTree,Add1Tree,SumTree}.hs`,
  each timing one traversal. All three run the same configurations: every
  recursive and loopified one (vectorized SoA included) and the pointer build
  (`ptr`), so every legend line appears in every panel. A build or a fold has
  nothing to loopify, so there the loopified configurations compile to their
  recursive counterparts; they are measured, not assumed equal.
  `--pldi-config` narrows the set. The depth is the executable's
  `--size-param`, so each configuration is compiled once.
- **Other languages:** `tree_sweep/langs/` holds GHC, MLton, OCaml, Rust,
  Racket, Java and Chez Scheme versions, ported from the 2017 BintreeBench
  suite and aligned with MonoTree: 64-bit leaves, `mkTree d 0`, every subtree
  built separately. Each takes the same arguments as a Gibbon executable and
  prints the same timing lines and answer. They are compiled with standard
  optimization (`ghc -O2`, MLton, `ocamlopt`, `rustc -O`, Racket CS, `javac` with
  the default JIT, Chez `optimize-level 3`) and run with their runtime's default
  settings. A language whose compiler is missing is left out and named in the
  caption. `--tree-sweep-languages` picks a subset (or `none`).
- **Same measurement for every line:** each point is run in interleaved rounds
  and checked against the oracle model for its depth, the way a
  `--pldi-submission` cell is. `--pin-cpu` applies as usual, so on x86 add
  `--pin-cpu auto`.
- **Memory:** the pointer build never frees, so its `buildTree` and `add1Tree`
  iterations are capped to fit `--tree-sweep-pointer-gb` (default 6). Another
  language's run is stopped if its resident memory passes
  `--tree-sweep-memory-gb` (default 60% of the machine's memory, at most 24 GB):
  at default settings GHC, Java, MLton, Chez and Racket need several times the
  tree's size, and on a 16 GB machine depth 26 would otherwise end in swap. Both
  are named in the caption where they apply.
- **Output:** `tree_sweep.json` and `tree_sweep.csv` (every configuration) in
  `--output-dir`, and `tree_sweep.pdf` in `--figures-dir`: one panel per
  traversal, median time per traversal against depth, with vanilla Gibbon, the
  best recursive AoS and SoA, the loopified vectorized SoA, the pointer build and
  every language drawn. LaTeX (pgfplots) draws it, so no matplotlib is needed;
  `--tree-sweep-from-json FILE` redraws it without running anything.
- **Toolchains:** each language uses the first compiler it finds on `PATH`:
  `ghc` (or `~/.ghcup/bin/ghc-9.4.6`), `mlton`, `ocamlopt`, `rustc` (a working
  one on `PATH`, else a rustup toolchain, stable first), `racket`,
  `javac`/`java`, and `chez`, `chezscheme` or `scheme` for Chez. On Debian or
  Ubuntu, for example: `sudo apt install mlton ocaml-nox racket default-jdk
  chezscheme texlive-pictures` (pgfplots, for the figure), plus GHC through
  ghcup and Rust through rustup. The run prints the version it found for each.
- **Subsets:** `--tree-sweep-depths` (default `10:26`; also `LO:HI:STEP` or
  `12,16,20`), `--tree-sweep-traversals` (any of `build,add1,sum`).
  `--sumtree-size-sweep` is `sumTree` with Gibbon only.

### Vanilla Gibbon is shaded

Vanilla Gibbon, $A_{ri}^{+av}$ (AoS, immutable cursors, the C auto-vectorizer
on, i.e. plain Gibbon at `-O3`), is shaded pale yellow in every table that shows
it: its column in the per-pass, counter and alignment tables, its group columns in
the summary-versus-vanilla table, and its row in the configuration key. Shading
needs `\usepackage{colortbl}` in the document that `\input`s the tables; without
it the tables compile unshaded. The preview PDF loads it.

### Input sizes (`--pldi-sizes`)

Every sizable program fixes its input with one literal in `gibbon_main`
(`mkList 100000000`, `mkTree 23 0`, ...). To run some programs at a different
size, list them in a TOML file and pass it with `--pldi-sizes`:

```toml
[sizes]
List = 10000000      # n, list elements
MonoTree = 20        # depth
```

`pldi_sizes.example.toml` lists every sizable program and its shipped size.
Programs you don't list keep their shipped size.

- **The shipped sources are never edited.** The literal is rewritten in a copy
  under `<output-dir>/resized_src/`, which is what gets compiled, and the same
  rewrite applies to the build-timing copy.
- **Results stay verified.** The expected answer is recomputed at the new size
  by the program's independent model in `oracles/`, the same model the
  committed oracle came from.
- **Resized runs are labelled.** Every resized program's tables say so in
  their caption, with the shipped size. The summary tables and reading notes
  list all resized programs, and the results JSON records the sizes, which a
  `--figures-from-json` replot restores.
- **Sizable programs:** List, MonoTree, TernaryTree, reduceNestedList,
  Add1TreeInt{8,16,32,64} and ArithmeticIntensityInt{8,16,32,64}. Naming any
  other program is an error.
- **Not combinable with `--benchmark-ghc` or `--benchmark-mlton`,** since
  their sources have their own size literals. Sizes are also not applied to
  `--include-build-pass`'s build-only sources.

**Stack depth.** A configuration that recurses once per element needs a deep C
stack. On Linux the runtime raises the stack limit to 4 GB. macOS fixes the main
thread's stack at 8 MB when the process starts, so there the generated `main`
runs the program on a thread with the same 4 GB stack (reserved, not committed).
Both machines therefore run the same sizes.

**Memory.** `reduceNestedList` at its shipped size builds about 3×10⁹ list
cells (~26 GB packed), and the pointer build keeps every build iteration's copy.
`pldi_sizes.crossplatform.toml` sets it, MonoTree and Add1TreeInt* to sizes that
fit a 16 GB machine; use the same file on every machine you compare.

### Hardware counters on macOS (`--pldi-kperf-counters`)

`--pldi-cache-counters` reads counters through PAPI, which only exists on
Linux. On Apple silicon, `--pldi-kperf-counters` runs the same counter phase
but reads the counters through Apple's private kperf framework, the interface
Instruments uses. It's opt-in: without it, no command, binary or table
changes.

- **Counters:** see "What the counters count" below. The M1's event
  database (`/usr/share/kpep/a14.plist`, 60 events) has **no L2 or last-level
  cache miss event**: the L2 is shared by a core cluster and its counters are
  outside the core PMU. Those rows are absent rather than filled with a
  substitute.
- **Needs root.** The driver asks for your sudo password once at start, then
  runs only the counter executables with `sudo -n`, keeping the sudo
  timestamp fresh in the background. Everything else, including compiling and
  the output files, runs as you.
- **No core pinning:** macOS can't pin a thread to a core, so `--pin-cpu` is
  not needed. The runtime asks for the performance cores (user-interactive QoS)
  instead, and the notes say so.
- **Under the hood:** it compiles with `gibbon --enable-kperf`, which emits the
  counter reads only when given and builds the RTS with `KPERF=1`. See
  Note [kperf counters] in `gibbon-rts/rts-c/gibbon_rts.c`.

**Misaligned accesses (kperf runs).** At the start of the kperf phase the driver
compiles and runs `alignment_probe.c`, which measures what an 8-byte load costs on
this machine when it is aligned, unaligned, crossing 64 bytes or crossing a 128-byte
block. The report prints that as a calibration table. Each program then gets a table
with, per pass and configuration, the counted 64-byte-crossing accesses per 1000
instructions and an upper bound on the share of the pass's time they could cost: the
crossings times the probe's largest extra latency, divided by the pass's time. The
bound deliberately over-charges, treating every 64-byte crossing as a 128-byte-block
crossing on the critical path.

### What the counters count

Both backends report five counters under the same names, so an M1 table and an
x86 table line up row for row. Every counter table lists them first, under
"Counted the same way on the M1 and x86":

| Counter | M1 (kperf) | x86 (PAPI) |
|---|---|---|
| Cycles | `FIXED_CYCLES` | core cycles |
| Instructions | `FIXED_INSTRUCTIONS` | instructions retired |
| L1D load misses (retired) | `L1D_CACHE_MISS_LD_NONSPEC` | `MEM_LOAD_RETIRED:L1_MISS` |
| L1I misses | `L1I_CACHE_MISS_DEMAND` (demand only) | `perf::L1-ICACHE-LOAD-MISSES` (includes prefetch) |
| Data TLB misses | `L2_TLB_MISS_DATA` (loads and stores) | `DTLB_LOAD_MISSES:WALK_COMPLETED` (loads) |

The last two are the closest each machine offers, not identical. Then, under
"This machine only": on x86, L2 and LLC misses of retired loads
(`MEM_LOAD_RETIRED:L2_MISS`, `:L3_MISS`); on the M1, L1D load misses including
speculative ones, dispatch-stall cycles, data page walks and 64-byte-crossing
accesses.

- **Window.** The runtime reads the counters immediately around the timed
  region of each iteration, so a count covers exactly what that iteration's
  time covers, not the region save and reclaim around it.
- **Two runs on x86.** A P-core of the i7-12700K counts four programmable
  events beside cycles and instructions, one short of the x86 set. The counter
  phase therefore runs each executable twice, once per event group
  (`GIBBON_PAPI_GROUP=1`: L1D, L2, LLC; `=2`: L1I, DTLB), and merges them.
- **Exact events.** The counter notes name the event behind every counter.
  Each counter's alternative event names are spellings of the same event, never
  a different one: a counter the CPU cannot count is listed as "Not counted",
  and one read from more than one event is flagged.
- **Noise.** A row whose largest count is under 1000 per iteration gets no
  green/red marks and no AoS/SoA ratio, and a counter that is under that
  everywhere is reduced to one line.

Both counter backends now also produce a **per-configuration counter table**
for each program. It has one column per measured configuration, grouped
AoS / SoA / Pointer like the timing tables, one block of rows per counter, and
one row per timed pass. The existing AoS-versus-SoA counter tables are
unchanged. They are produced only when both configurations of the layout step
were measured.

---

## Smart Recompilation

The script compares the **modification timestamp** of each `.hs` source file
against its compiled `.exe`.  If the exe is newer than the source, compilation
is skipped.

- Recompilation runs **in parallel** (one thread per CPU core).
- **Execution always runs sequentially** to avoid benchmark interference.

Use `--clean` to force full recompilation regardless of timestamps.

---

## Generated LaTeX Tables

`performance_table.tex` contains:

| Table | Contents |
|-------|----------|
| Table 1 – Summary | End-to-end time split into Fold / Map columns, total AoS time, speedup |
| Tables 2 – N | One table per program: pass name, type (F/M/?), AoS (s), SoA (s), speedup |

Times use **scientific notation** (`3.27e-03`) so nothing rounds to `0.00`.

Bold highlights the faster variant when the difference exceeds 10%.

Each per-program table ends with **Total** and **Geomean** rows.

**Include in your paper:**

```latex
\usepackage{booktabs}   % preamble

\input{performance_table.tex}

% reference as \ref{tab:summary}, \ref{tab:DomTree}, ...
```

---

## Generated Figures

### `speedup_comparison.pdf`
Horizontal bar chart with two bars per program:
- **Blue** — speedup across fold passes
- **Orange** — speedup across map passes

Dashed reference line at 1.0×.

### `per_program/<Program>.pdf`  ← main result figure
One figure per program showing **every pass** side-by-side:
- **Error bars** = standard deviation across iterations
- **Geomean bar** at the right (dark blue AoS / purple SoA), value labelled
- Width scales automatically with number of passes

### `heatmaps/<Program>_heatmap.pdf`
Single-row heatmap for that program showing only the passes it actually
has (no 1× noise from absent passes).  Red = SoA slower, green = SoA faster.

### `pass_breakdown_all.pdf`
All programs stacked.  Each pass uses a distinct **colour + hatch pattern**
for accessibility.  Horizontal legend below the plots.

---

## Command-Line Reference

```
./gibbon_benchmark.py [options]

  --programs-dir DIR    Root of AoS/SoA source tree  (default: programs/)
  --output-dir   DIR    Where to put compiled exes    (default: benchmark_output/)
  --iterations   N      Timed iterations per exe      (default: 20)
  --programs     FILES  Restrict to listed .hs files
  --clean               Force recompile (ignore timestamps)
  --generate-paper      Write LaTeX tables + all figures after benchmarking
  --latex-table  FILE   LaTeX output path  (default: performance_table.tex)
  --figures-dir  DIR    Figure output dir  (default: figures/)
  --report       FILE   Text report path   (default: benchmark_report.txt)
  --json         FILE   JSON results path  (default: benchmark_results.json)
  --pldi-config  FILE   TOML file choosing --pldi-submission configurations
  --pldi-sizes   FILE   TOML file overriding --pldi-submission input sizes
  --pldi-kperf-counters  macOS: counter phase via Apple kperf (needs sudo)
```

---

## Requirements

| Requirement | Notes |
|-------------|-------|
| Python ≥ 3.8 | `matplotlib`, `numpy` via pip |
| `gibbon` | Must be on `$PATH` |
| `pdflatex` | Optional – only for PDF table preview |

---

## Changelog

### v2.4
- Automatic fold/map detection from print statements (no manual annotation)
- Debug output shows exactly what was detected and stored
- Parallel compilation via `ThreadPoolExecutor` (as many threads as CPU cores)
- Per-program figures: **all passes** in one plot, error bars, geomean bar
- Per-program heatmaps (only own passes — no 1× noise)
- `--generate-paper` **always** regenerates tables and figures on every run
- Scientific notation for small execution times
- GC/allocator metadata filtered from output comparison
- Removed confusing all-programs heatmap and grid figure

### v2.3
- Per-program LaTeX tables with speedup column
- Fold/map summary table
- Scientific notation formatting

### v2.2
- GC metadata filtering, comprehensive heatmaps, PDF table preview

### v2.1
- Smart recompilation with timestamp checking, `--clean` flag, `clean.sh`

### v2.0
- Full Python rewrite with matplotlib figures and LaTeX output

### v1.0
- Initial bash-only benchmarking script
