# Gibbon Compiler Benchmarking Suite

Comprehensive benchmarking tools for comparing AoS (Array of Structs) vs SoA (Struct of Arrays) implementations compiled with the Gibbon compiler.

## Overview

This suite provides two benchmarking scripts:
1. **Python script** (`gibbon_benchmark.py`) - Full-featured with detailed analysis, JSON output, and performance comparisons
2. **Bash script** (`gibbon_benchmark.sh`) - Lightweight alternative for quick benchmarking

Both scripts:
- Compile programs in both AoS and SoA variants
- Run benchmarks with configurable iterations
- Verify output correctness between variants
- Extract and compare performance metrics
- Generate detailed reports

## Directory Structure

Your project should be organized as follows:

```
your-project/
├── programs/
│   ├── AoS/
│   │   ├── Compiler.hs
│   │   ├── DBQuery.hs
│   │   ├── DecisionTree.hs
│   │   ├── DomTree.hs
│   │   ├── KDTree.hs
│   │   ├── LinearListReduction.hs
│   │   ├── List.hs
│   │   ├── MonoTree.hs
│   │   ├── ObjectGraph.hs
│   │   ├── OctTree.hs
│   │   ├── PiecewiseFunctions.hs
│   │   ├── TernaryTree.hs
│   │   └── Trie.hs
│   └── SoA/
│       ├── Compiler.hs
│       ├── DBQuery.hs
│       └── ... (same files as AoS)
├── gibbon_benchmark.py
└── gibbon_benchmark.sh
```

## Prerequisites

- Gibbon compiler installed and available in PATH
- Python 3.6+ (for Python script)
- Python packages: matplotlib, numpy (for paper generation feature)
  - Install with: `pip install matplotlib numpy`
- Bash shell (for Bash script)

## Usage

### Python Script (Recommended)

#### Basic Usage

```bash
# Make executable (first time only)
chmod +x gibbon_benchmark.py

# Run all benchmarks with default settings
./gibbon_benchmark.py

# Run with custom iterations
./gibbon_benchmark.py --iterations 50

# Specify custom programs directory
./gibbon_benchmark.py --programs-dir /path/to/programs
```

#### Advanced Options

```bash
# Benchmark specific programs only
./gibbon_benchmark.py --programs Compiler.hs List.hs Trie.hs

# Custom output locations
./gibbon_benchmark.py \
  --output-dir ./build \
  --report my_report.txt \
  --json my_results.json

# Full example
./gibbon_benchmark.py \
  --programs-dir ./programs \
  --output-dir ./benchmark_output \
  --iterations 30 \
  --report detailed_report.txt \
  --json results.json \
  --programs Compiler.hs DBQuery.hs
```

#### Command-line Options

| Option | Description | Default |
|--------|-------------|---------|
| `--programs-dir` | Directory containing AoS and SoA subdirectories | `programs` |
| `--output-dir` | Directory for compiled files and temporary outputs | `benchmark_output` |
| `--iterations` | Number of iterations for each benchmark | `20` |
| `--report` | Output text report file | `benchmark_report.txt` |
| `--json` | JSON output file | `benchmark_results.json` |
| `--programs` | Specific programs to benchmark (space-separated) | All programs |
| `--generate-paper` | Generate LaTeX tables and publication figures | `False` |
| `--latex-table` | Output LaTeX table file (with --generate-paper) | `performance_table.tex` |
| `--figures-dir` | Directory for figures (with --generate-paper) | `figures` |
| `--clean` | Force recompilation even if executables are up-to-date | `False` |

#### Smart Recompilation (NEW!)

The scripts now include smart recompilation (like `make`) that only recompiles when necessary:

**How it works:**
- Checks if executable exists and is newer than source file
- Skips compilation if executable is up-to-date
- Saves significant time during iterative development

**Usage:**

```bash
# Normal run - only recompiles changed programs
./gibbon_benchmark.py

# Force recompilation of everything
./gibbon_benchmark.py --clean

# Clean all compiled files
./clean.sh
```

**Example output:**
```
Compiler (AOS) is up-to-date, skipping compilation
Compiler (SOA) is up-to-date, skipping compilation
Compiling List (AOS)... ✓  (only this one changed!)
List (SOA) is up-to-date, skipping compilation
```

**When to use --clean:**
- Preparing final benchmarks for publication
- After changing compiler flags
- When you want to ensure everything is fresh

**For complete details:** See `SMART_RECOMPILATION_GUIDE.txt`

#### Conference Paper Generation

**NEW: Automatically generate publication-quality materials for your paper!**

Generate LaTeX tables and figures for top-tier conferences:

```bash
./gibbon_benchmark.py --generate-paper
```

This creates:
- **performance_table.tex** - Professional LaTeX tables with:
  - Performance comparison (AoS vs SoA)
  - Per-pass breakdown
  - Speedup statistics
  - Ready to `\input{}` into your paper
  
- **figures/** directory with publication-quality figures:
  - speedup_comparison.pdf - Bar chart of speedups
  - performance_comparison.pdf - Grouped bar chart
  - pass_breakdown.pdf - Stacked bars showing time per pass
  - iteration_distributions.pdf - Box plots of timing variance
  - speedup_heatmap.pdf - Heatmap of per-pass speedups
  - PNG versions of all figures

**Using in your LaTeX paper:**

```latex
% In preamble
\usepackage{booktabs}
\usepackage{graphicx}

% In document
\input{performance_table.tex}

\begin{figure}[t]
  \centering
  \includegraphics[width=\columnwidth]{figures/speedup_comparison.pdf}
  \caption{Performance speedup of SoA vs AoS.}
  \label{fig:speedup}
\end{figure}
```

**For complete paper generation guide, see:** `PAPER_GENERATION_GUIDE.txt`

**Quick reference:** `PAPER_QUICK_REFERENCE.txt`

### Bash Script

#### Basic Usage

```bash
# Make executable (first time only)
chmod +x gibbon_benchmark.sh

# Run with default settings (programs dir: ./programs, iterations: 20)
./gibbon_benchmark.sh

# Custom programs directory
./gibbon_benchmark.sh /path/to/programs

# Custom programs directory and iterations
./gibbon_benchmark.sh /path/to/programs 50
```

## Output Files

### Python Script Outputs

1. **Text Report** (`benchmark_report.txt`):
   - Summary table with compile/run status
   - Detailed results for each program
   - Output verification results
   - Performance comparisons between AoS and SoA
   - Pass-by-pass timing analysis

2. **JSON Results** (`benchmark_results.json`):
   - Machine-readable format for further analysis
   - Complete timing data for all passes
   - Structured error messages
   - Can be imported for custom analysis

3. **Compiled Files** (in `benchmark_output/`):
   - `*.aos.c` / `*.soa.c` - Generated C files
   - `*.aos.exe` / `*.soa.exe` - Compiled executables

### Bash Script Outputs

1. **Text Report** (`benchmark_report.txt`):
   - Summary of results
   - Output comparisons
   - Performance metrics (SELFTIMED values)

2. **Output Files** (in `benchmark_output/`):
   - `*.aos.output.txt` / `*.soa.output.txt` - Full program outputs
   - Compiled executables and C files

## Understanding the Output

### Sample Report Section

```
────────────────────────────────────────────────────────────────────────────────
Program: Compiler.hs
────────────────────────────────────────────────────────────────────────────────

AoS (Array of Structs):
  Compile time: 15.23s
  Compile status: Success
  Runtime: 65.58s
  Run status: Success
  Output: '#(8571429 1428571 1071429 535714 25714287 #t 17142858)
  Passes analyzed: 10
    instCountPass: 0.003269s
    blockCountPass: 0.003091s
    memoryOpStatsPass: 0.006116s
    ...

SoA (Struct of Arrays):
  Compile time: 16.01s
  Compile status: Success
  Runtime: 61.89s
  Run status: Success
  Output: '#(8571429 1428571 1071429 535714 25714287 #t 17142858)
  Passes analyzed: 10
    instCountPass: 0.003269s
    blockCountPass: 0.003091s
    memoryOpStatsPass: 0.006116s
    ...

Output Match: ✓ PASS

Performance Comparison:
  instCountPass:
    AoS: 0.003269s
    SoA: 0.003091s
    SoA is 1.06x faster
  ...
```

### Key Metrics

- **SELFTIMED**: Median execution time for a pass across all iterations
- **BATCHTIME**: Total time for all iterations of a pass
- **ITER TIMES**: Sorted array of individual iteration times

### Output Verification

The final output (e.g., `'#(8571429 1428571 1071429 535714 25714287 #t 17142858)`) represents the program's result. The script verifies that AoS and SoA produce identical outputs, ensuring correctness.

## Troubleshooting

### Common Issues

1. **Gibbon not found**
   ```
   Error: gibbon: command not found
   ```
   Solution: Ensure Gibbon is installed and in your PATH:
   ```bash
   which gibbon
   export PATH=$PATH:/path/to/gibbon/bin
   ```

2. **Source files not found**
   ```
   Warning: programs/AoS/Compiler.hs not found
   ```
   Solution: Verify your directory structure matches the expected layout.

3. **Execution timeout**
   ```
   Running Compiler.aos.exe... ✗ (timeout)
   ```
   Solution: The script has a 10-minute execution timeout. Reduce iterations or increase timeout in the script.

### Debugging

For the Python script, add verbose output by modifying the script to enable debug logging:

```python
# Add at the top of main()
import logging
logging.basicConfig(level=logging.DEBUG)
```

For the Bash script, enable debug mode:

```bash
bash -x gibbon_benchmark.sh
```

## Analyzing Results

### Python JSON Output

The JSON file can be imported for custom analysis:

```python
import json

with open('benchmark_results.json', 'r') as f:
    data = json.load(f)

for result in data['results']:
    program = result['program']
    if result['outputs_match']:
        aos_time = sum(result['aos']['passes']['instCountPass']['iter_times'])
        soa_time = sum(result['soa']['passes']['instCountPass']['iter_times'])
        speedup = aos_time / soa_time
        print(f"{program}: SoA is {speedup:.2f}x faster")
```

### Performance Trends

To analyze which variant performs better overall:

1. Look at the performance comparison sections in the report
2. Calculate average speedup across all passes
3. Identify which passes benefit most from SoA

### Output Mismatches

If outputs don't match:

1. Check the detailed report for the specific output values
2. Examine the raw output files in `benchmark_output/`
3. Run individual programs manually to debug
4. Verify the programs are semantically equivalent

## Customization

### Adding New Programs

Simply add the `.hs` file to both `programs/AoS/` and `programs/SoA/` directories. The scripts will automatically detect and benchmark them.

### Modifying Compilation Flags

Edit the compilation command in the scripts:

**Python script** (around line 93):
```python
cmd = [
    "gibbon",
    "--use-mutable-cursors",
    "--packed",
    "--to-exe",
    # Add your custom flags here
    "--cfile", str(c_file),
    "--exefile", str(exe_file),
    str(source_file)
]
```

**Bash script** (around line 48):
```bash
gibbon --use-mutable-cursors --packed --to-exe \
    --cfile "$c_file" --exefile "$exe_file" \
    # Add your custom flags here
    "$source_file"
```

### Adjusting Timeouts

**Python script**:
- Compilation timeout: Line 105 (`timeout=300`)
- Execution timeout: Line 145 (`timeout=600`)

**Bash script**:
- Execution timeout: Line 58 (`timeout 600`)

## Performance Tips

1. **Warm-up runs**: The first iteration is often slower. Consider discarding it or increasing iterations.

2. **System load**: Run benchmarks on an idle system for consistent results.

3. **Multiple runs**: Run the benchmark suite multiple times and average results for statistical significance.

4. **Iteration count**: More iterations provide more stable median values but increase runtime. 20 is a good default.

## Contributing

To extend the benchmarking suite:

1. Add new metrics to the parsing functions
2. Implement additional comparison logic
3. Add visualization capabilities (e.g., matplotlib integration)
4. Create automated regression testing

## Example Workflow

```bash
# 1. Set up your programs
cd /path/to/your/project
mkdir -p programs/{AoS,SoA}
# ... copy your .hs files ...

# 2. Run initial benchmark
./gibbon_benchmark.py --iterations 30

# 3. Review results
cat benchmark_report.txt
# or
less benchmark_report.txt

# 4. Analyze specific programs
./gibbon_benchmark.py --programs Compiler.hs List.hs --iterations 50

# 5. Export for further analysis
python3 -c "
import json
with open('benchmark_results.json') as f:
    data = json.load(f)
    # Your custom analysis here
"
```

## License

This benchmarking suite is provided as-is for use with the Gibbon compiler.

## Support

For issues with:
- **Gibbon compiler**: Check the Gibbon documentation
- **These scripts**: Review this README and troubleshooting section
- **Benchmark interpretation**: Consult the understanding output section
