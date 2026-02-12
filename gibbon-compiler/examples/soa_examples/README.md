# Gibbon Benchmark Suite v2.4

Benchmarks **AoS** (Array of Structs) vs **SoA** (Struct of Arrays) Gibbon
compiler programs and produces publication-quality figures and LaTeX tables for
conference papers.

---

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
├── gibbon_benchmark.py      # ← main script (Python ≥ 3.8)
├── gibbon_benchmark.sh      # ← bash wrapper / convenience shortcuts
├── clean.sh                 # ← remove compiled outputs & paper materials
├── README.md
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
