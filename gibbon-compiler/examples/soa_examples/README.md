# Gibbon Benchmark Suite v2.4

Benchmarks **AoS** (Array of Structs) vs **SoA** (Struct of Arrays) Gibbon
compiler programs and produces publication-quality figures and LaTeX tables for
conference papers.

> **Design / context / verification documents live outside this repository.**
> Handoff notes, verification plans, defect and benchmark analyses for the
> packed fully-factored layout work (loopification, selective buffer sharing,
> SIMD vectorization, and the source-declared integer widths) are maintained in
> `git@github.com:vidsinghal/llm-notes.git` under `gibbon-soa-layout/`.
> Start with
> `gibbon-soa-layout/current/variable_width_integer_implementation_progress.md`,
> the canonical living ledger (the older `Context.md` is historical and its
> `--int32` model is superseded).  Only user-facing documentation for
> the shipped artifact — this file, `ANNOTATIONS.md`, `GETTING_STARTED.txt` —
> stays here.

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
