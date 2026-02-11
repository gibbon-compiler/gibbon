#!/usr/bin/env python3
"""
Gibbon Compiler Benchmarking Script
Compiles and benchmarks AoS (Array of Structs) vs SoA (Struct of Arrays) programs
"""

import os
import sys
import subprocess
import re
import json
import time
from pathlib import Path
from collections import defaultdict
from typing import Dict, List, Tuple, Optional
import statistics

# Import matplotlib for figure generation (with non-interactive backend)
import matplotlib
matplotlib.use('Agg')  # Non-interactive backend for server environments
import matplotlib.pyplot as plt
import numpy as np

# Program files to benchmark
PROGRAMS = [
    "Compiler.hs",
    "DBQuery.hs",
    "DecisionTree.hs",
    "DomTree.hs",
    "KDTree.hs",
    "LinearListReduction.hs",
    "List.hs",
    "MonoTree.hs",
    "ObjectGraph.hs",
    "OctTree.hs",
    "PiecewiseFunctions.hs",
    "TernaryTree.hs",
    "Trie.hs"
]

class BenchmarkResult:
    """Stores benchmark results for a single program run"""
    def __init__(self, program: str, variant: str):
        self.program = program
        self.variant = variant
        self.passes = {}
        self.output = None
        self.compile_time = 0
        self.total_runtime = 0
        self.compile_success = False
        self.run_success = False
        self.error_message = None

    def add_pass_data(self, pass_name: str, data: dict):
        self.passes[pass_name] = data

    def to_dict(self):
        return {
            "program": self.program,
            "variant": self.variant,
            "compile_time": self.compile_time,
            "total_runtime": self.total_runtime,
            "compile_success": self.compile_success,
            "run_success": self.run_success,
            "output": self.output,
            "passes": self.passes,
            "error_message": self.error_message
        }


def needs_recompilation(source_file: Path, exe_file: Path, c_file: Path) -> bool:
    """
    Check if recompilation is needed (like make)
    
    Returns True if:
    - Executable doesn't exist
    - Source file is newer than executable
    - C file doesn't exist
    
    Returns False if executable is up-to-date
    """
    # If executable doesn't exist, need to compile
    if not exe_file.exists():
        return True
    
    # If C file doesn't exist, need to compile
    if not c_file.exists():
        return True
    
    # Compare modification times
    source_mtime = source_file.stat().st_mtime
    exe_mtime = exe_file.stat().st_mtime
    
    # If source is newer than executable, need to recompile
    if source_mtime > exe_mtime:
        return True
    
    # Executable is up-to-date
    return False


def compile_program(source_file: Path, variant: str, output_dir: Path, force_recompile: bool = False) -> Tuple[bool, float, str]:
    """
    Compile a Gibbon program
    
    Args:
        source_file: Path to the .hs source file
        variant: "aos" or "soa"
        output_dir: Directory to place compiled files
        force_recompile: If True, always recompile even if up-to-date
        
    Returns:
        Tuple of (success, compile_time, error_message)
    """
    basename = source_file.stem
    c_file = output_dir / f"{basename}.{variant}.c"
    exe_file = output_dir / f"{basename}.{variant}.exe"
    
    # Ensure output directory exists
    output_dir.mkdir(parents=True, exist_ok=True)
    
    # Check if recompilation is needed
    if not force_recompile and not needs_recompilation(source_file, exe_file, c_file):
        print(f"  {basename} ({variant.upper()}) is up-to-date, skipping compilation")
        return True, 0.0, None
    
    cmd = [
        "gibbon",
        "--use-mutable-cursors",
        "--packed",
        "--to-exe",
        "--cfile", str(c_file),
        "--exefile", str(exe_file),
        str(source_file)
    ]
    
    print(f"  Compiling {basename} ({variant.upper()})...", end=" ", flush=True)
    
    start_time = time.time()
    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True
            # No timeout - some programs take a very long time to compile
        )
        compile_time = time.time() - start_time
        
        if result.returncode == 0:
            print(f"✓ ({compile_time:.2f}s)")
            return True, compile_time, None
        else:
            error_msg = result.stderr or result.stdout
            print(f"✗ (failed)")
            return False, compile_time, error_msg
            
    except Exception as e:
        compile_time = time.time() - start_time
        print(f"✗ (error)")
        return False, compile_time, str(e)


def parse_pass_output(pass_text: str) -> dict:
    """Parse the output of a single pass"""
    data = {}
    
    # Extract ITER TIMES
    iter_times_match = re.search(r'ITER TIMES: \[([\d\., ]+)\]', pass_text)
    if iter_times_match:
        times_str = iter_times_match.group(1)
        data['iter_times'] = [float(x) for x in times_str.split(', ')]
    
    # Extract ITERS
    iters_match = re.search(r'ITERS: (\d+)', pass_text)
    if iters_match:
        data['iters'] = int(iters_match.group(1))
    
    # Extract BATCHTIME
    batchtime_match = re.search(r'BATCHTIME: ([\d\.e\-\+]+)', pass_text)
    if batchtime_match:
        data['batchtime'] = float(batchtime_match.group(1))
    
    # Extract SELFTIMED
    selftimed_match = re.search(r'SELFTIMED: ([\d\.e\-\+]+)', pass_text)
    if selftimed_match:
        data['selftimed'] = float(selftimed_match.group(1))
        data['median_time'] = data['selftimed']  # SELFTIMED appears to be the median
    
    return data


def run_program(exe_file: Path, iterations: int = 20) -> Tuple[bool, float, str, str]:
    """
    Run a compiled program
    
    Returns:
        Tuple of (success, runtime, output, error_message)
    """
    if not exe_file.exists():
        return False, 0, "", "Executable not found"
    
    cmd = [str(exe_file), "--iterate", str(iterations)]
    
    print(f"  Running {exe_file.name}...", end=" ", flush=True)
    
    start_time = time.time()
    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=600  # 10 minute timeout
        )
        runtime = time.time() - start_time
        
        if result.returncode == 0:
            print(f"✓ ({runtime:.2f}s)")
            return True, runtime, result.stdout, None
        else:
            error_msg = result.stderr or result.stdout
            print(f"✗ (failed)")
            return False, runtime, result.stdout, error_msg
            
    except subprocess.TimeoutExpired:
        runtime = time.time() - start_time
        print(f"✗ (timeout)")
        return False, runtime, "", "Execution timeout"
    except Exception as e:
        runtime = time.time() - start_time
        print(f"✗ (error)")
        return False, runtime, "", str(e)


def parse_benchmark_output(output: str) -> Tuple[Dict[str, dict], Optional[str]]:
    """
    Parse the benchmark output to extract pass data and final output
    
    Returns:
        Tuple of (passes_dict, final_output)
    """
    passes = {}
    
    # Split by "Running pass"
    pass_sections = re.split(r'Running pass ([^:]+):', output)
    
    # Process each pass (skip the first empty element)
    for i in range(1, len(pass_sections), 2):
        if i + 1 < len(pass_sections):
            pass_name = pass_sections[i].strip()
            pass_output = pass_sections[i + 1]
            
            # Find the "End" marker
            end_idx = pass_output.find("End")
            if end_idx != -1:
                pass_output = pass_output[:end_idx]
            
            passes[pass_name] = parse_pass_output(pass_output)
    
    # Extract final output by removing all timing-related lines
    # This handles various output formats (tuples, numbers, etc.)
    final_output = extract_program_output(output)
    
    return passes, final_output


def extract_program_output(output: str) -> Optional[str]:
    """
    Extract the actual program output by filtering out all timing data.
    This allows comparison of program results regardless of format.
    """
    lines = output.split('\n')
    filtered_lines = []
    
    # Patterns to exclude (timing and benchmark metadata)
    exclude_patterns = [
        r'^itertime:',
        r'^ITER TIMES:',
        r'^ITERS:',
        r'^SIZE:',
        r'^BATCHTIME:',
        r'^SELFTIMED:',
        r'^Running pass',
        r'^Running program',
        r'^Running the Compiler',
        r'^End$',
        r'^\s*$',  # Empty lines
    ]
    
    for line in lines:
        # Check if line matches any exclude pattern
        should_exclude = False
        for pattern in exclude_patterns:
            if re.match(pattern, line.strip()):
                should_exclude = True
                break
        
        if not should_exclude and line.strip():
            filtered_lines.append(line.strip())
    
    # Join the remaining lines and return
    result = '\n'.join(filtered_lines)
    return result if result else None


def benchmark_program(program_name: str, programs_dir: Path, output_dir: Path, 
                      iterations: int = 20, force_recompile: bool = False) -> Tuple[BenchmarkResult, BenchmarkResult]:
    """
    Benchmark both AoS and SoA versions of a program
    
    Args:
        program_name: Name of the program file
        programs_dir: Directory containing AoS and SoA subdirectories
        output_dir: Directory for compiled outputs
        iterations: Number of iterations to run
        force_recompile: If True, always recompile even if up-to-date
        
    Returns:
        Tuple of (aos_result, soa_result)
    """
    print(f"\n{'='*70}")
    print(f"Benchmarking: {program_name}")
    print(f"{'='*70}")
    
    results = {}
    
    for variant in ["aos", "soa"]:
        result = BenchmarkResult(program_name, variant)
        
        # Compile
        source_file = programs_dir / variant.upper() / program_name
        
        if not source_file.exists():
            print(f"  Warning: {source_file} not found, skipping {variant.upper()}")
            result.error_message = f"Source file not found: {source_file}"
            results[variant] = result
            continue
        
        success, compile_time, error = compile_program(source_file, variant, output_dir, force_recompile)
        result.compile_time = compile_time
        result.compile_success = success
        
        if not success:
            result.error_message = error
            results[variant] = result
            continue
        
        # Run
        exe_file = output_dir / f"{Path(program_name).stem}.{variant}.exe"
        success, runtime, output, error = run_program(exe_file, iterations)
        result.total_runtime = runtime
        result.run_success = success
        
        if not success:
            result.error_message = error
            results[variant] = result
            continue
        
        # Parse output
        passes, final_output = parse_benchmark_output(output)
        result.passes = passes
        result.output = final_output
        
        results[variant] = result
    
    return results.get("aos"), results.get("soa")


def compare_outputs(aos_result: BenchmarkResult, soa_result: BenchmarkResult) -> bool:
    """Compare the final outputs of AoS and SoA versions"""
    if not aos_result.run_success or not soa_result.run_success:
        return None  # Can't compare if either failed
    
    if aos_result.output is None or soa_result.output is None:
        return None
    
    # Normalize whitespace for comparison (handle multiline outputs)
    aos_normalized = ' '.join(aos_result.output.split())
    soa_normalized = ' '.join(soa_result.output.split())
    
    return aos_normalized == soa_normalized


def generate_report(all_results: List[Tuple[BenchmarkResult, BenchmarkResult]], 
                   output_file: Path):
    """Generate a comprehensive benchmark report"""
    
    with open(output_file, 'w') as f:
        f.write("=" * 80 + "\n")
        f.write("GIBBON COMPILER BENCHMARK REPORT\n")
        f.write("=" * 80 + "\n\n")
        f.write(f"Timestamp: {time.strftime('%Y-%m-%d %H:%M:%S')}\n")
        f.write(f"Total programs benchmarked: {len(all_results)}\n\n")
        
        # Summary table
        f.write("\n" + "=" * 80 + "\n")
        f.write("SUMMARY\n")
        f.write("=" * 80 + "\n\n")
        f.write(f"{'Program':<25} {'AoS Compile':<12} {'AoS Run':<10} {'SoA Compile':<12} {'SoA Run':<10} {'Match':<8}\n")
        f.write("-" * 80 + "\n")
        
        for aos_result, soa_result in all_results:
            program = aos_result.program if aos_result else soa_result.program
            
            aos_compile = "✓" if aos_result and aos_result.compile_success else "✗"
            aos_run = "✓" if aos_result and aos_result.run_success else "✗"
            soa_compile = "✓" if soa_result and soa_result.compile_success else "✗"
            soa_run = "✓" if soa_result and soa_result.run_success else "✗"
            
            match = compare_outputs(aos_result, soa_result)
            match_str = "✓" if match else ("✗" if match is False else "N/A")
            
            f.write(f"{program:<25} {aos_compile:<12} {aos_run:<10} {soa_compile:<12} {soa_run:<10} {match_str:<8}\n")
        
        # Detailed results
        f.write("\n\n" + "=" * 80 + "\n")
        f.write("DETAILED RESULTS\n")
        f.write("=" * 80 + "\n")
        
        for aos_result, soa_result in all_results:
            program = aos_result.program if aos_result else soa_result.program
            
            f.write(f"\n\n{'─' * 80}\n")
            f.write(f"Program: {program}\n")
            f.write(f"{'─' * 80}\n\n")
            
            # AoS results
            if aos_result:
                f.write("AoS (Array of Structs):\n")
                f.write(f"  Compile time: {aos_result.compile_time:.2f}s\n")
                f.write(f"  Compile status: {'Success' if aos_result.compile_success else 'Failed'}\n")
                if aos_result.compile_success:
                    f.write(f"  Runtime: {aos_result.total_runtime:.2f}s\n")
                    f.write(f"  Run status: {'Success' if aos_result.run_success else 'Failed'}\n")
                    if aos_result.run_success:
                        f.write(f"  Output: {aos_result.output}\n")
                        f.write(f"  Passes analyzed: {len(aos_result.passes)}\n")
                        for pass_name, pass_data in aos_result.passes.items():
                            if 'median_time' in pass_data:
                                f.write(f"    {pass_name}: {pass_data['median_time']:.6f}s\n")
                if aos_result.error_message:
                    f.write(f"  Error: {aos_result.error_message[:200]}...\n")
                f.write("\n")
            
            # SoA results
            if soa_result:
                f.write("SoA (Struct of Arrays):\n")
                f.write(f"  Compile time: {soa_result.compile_time:.2f}s\n")
                f.write(f"  Compile status: {'Success' if soa_result.compile_success else 'Failed'}\n")
                if soa_result.compile_success:
                    f.write(f"  Runtime: {soa_result.total_runtime:.2f}s\n")
                    f.write(f"  Run status: {'Success' if soa_result.run_success else 'Failed'}\n")
                    if soa_result.run_success:
                        f.write(f"  Output: {soa_result.output}\n")
                        f.write(f"  Passes analyzed: {len(soa_result.passes)}\n")
                        for pass_name, pass_data in soa_result.passes.items():
                            if 'median_time' in pass_data:
                                f.write(f"    {pass_name}: {pass_data['median_time']:.6f}s\n")
                if soa_result.error_message:
                    f.write(f"  Error: {soa_result.error_message[:200]}...\n")
                f.write("\n")
            
            # Comparison
            match = compare_outputs(aos_result, soa_result)
            if match is not None:
                f.write(f"Output Match: {'✓ PASS' if match else '✗ FAIL - Outputs differ!'}\n")
                
                # Show the actual outputs if they don't match
                if not match and aos_result.output and soa_result.output:
                    f.write("\n*** OUTPUT MISMATCH DETAILS ***\n")
                    f.write(f"AoS output:\n  {aos_result.output}\n")
                    f.write(f"SoA output:\n  {soa_result.output}\n")
                    f.write("*** END MISMATCH DETAILS ***\n\n")
                
                # Performance comparison
                if aos_result.run_success and soa_result.run_success:
                    f.write("\nPerformance Comparison:\n")
                    
                    # Compare common passes
                    common_passes = set(aos_result.passes.keys()) & set(soa_result.passes.keys())
                    for pass_name in sorted(common_passes):
                        aos_time = aos_result.passes[pass_name].get('median_time', 0)
                        soa_time = soa_result.passes[pass_name].get('median_time', 0)
                        
                        if aos_time > 0 and soa_time > 0:
                            speedup = aos_time / soa_time
                            faster = "SoA" if speedup > 1 else "AoS"
                            f.write(f"  {pass_name}:\n")
                            f.write(f"    AoS: {aos_time:.6f}s\n")
                            f.write(f"    SoA: {soa_time:.6f}s\n")
                            f.write(f"    {faster} is {abs(speedup):.2f}x faster\n")


def save_json_results(all_results: List[Tuple[BenchmarkResult, BenchmarkResult]], 
                     output_file: Path):
    """Save results in JSON format for further analysis"""
    data = {
        "timestamp": time.strftime('%Y-%m-%d %H:%M:%S'),
        "results": []
    }
    
    for aos_result, soa_result in all_results:
        program_data = {
            "program": aos_result.program if aos_result else soa_result.program,
            "aos": aos_result.to_dict() if aos_result else None,
            "soa": soa_result.to_dict() if soa_result else None,
            "outputs_match": compare_outputs(aos_result, soa_result)
        }
        data["results"].append(program_data)
    
    with open(output_file, 'w') as f:
        json.dump(data, f, indent=2)


def generate_latex_table(all_results: List[Tuple[BenchmarkResult, BenchmarkResult]], 
                         output_file: Path):
    """Generate LaTeX table for conference paper"""
    
    with open(output_file, 'w') as f:
        # Main performance comparison table
        f.write("% Performance Comparison Table - AoS vs SoA\n")
        f.write("% Include in your LaTeX document with: \\input{" + output_file.name + "}\n\n")
        
        f.write("\\begin{table}[t]\n")
        f.write("\\centering\n")
        f.write("\\caption{Performance comparison of AoS vs SoA implementations. ")
        f.write("Times shown are median execution times in milliseconds. ")
        f.write("Speedup values greater than 1.0 indicate SoA is faster.}\n")
        f.write("\\label{tab:performance}\n")
        f.write("\\begin{tabular}{l r r r c}\n")
        f.write("\\toprule\n")
        f.write("\\textbf{Program} & \\textbf{AoS (ms)} & \\textbf{SoA (ms)} & \\textbf{Speedup} & \\textbf{Match} \\\\\n")
        f.write("\\midrule\n")
        
        speedups = []
        for aos_result, soa_result in all_results:
            if not aos_result or not soa_result:
                continue
            if not aos_result.run_success or not soa_result.run_success:
                continue
            
            program = aos_result.program.replace('.hs', '').replace('_', '\\_')
            
            # Calculate total runtime (sum of all passes)
            aos_time = sum(p.get('median_time', 0) for p in aos_result.passes.values()) * 1000
            soa_time = sum(p.get('median_time', 0) for p in soa_result.passes.values()) * 1000
            
            if soa_time > 0:
                speedup = aos_time / soa_time
                speedups.append(speedup)
            else:
                speedup = 0
            
            match = compare_outputs(aos_result, soa_result)
            match_symbol = "$\\checkmark$" if match else "$\\times$"
            
            # Highlight best performer
            if speedup > 1.05:  # SoA is significantly faster
                f.write(f"{program} & {aos_time:.2f} & \\textbf{{{soa_time:.2f}}} & {speedup:.2f}$\\times$ & {match_symbol} \\\\\n")
            elif speedup < 0.95:  # AoS is significantly faster
                f.write(f"{program} & \\textbf{{{aos_time:.2f}}} & {soa_time:.2f} & {speedup:.2f}$\\times$ & {match_symbol} \\\\\n")
            else:
                f.write(f"{program} & {aos_time:.2f} & {soa_time:.2f} & {speedup:.2f}$\\times$ & {match_symbol} \\\\\n")
        
        f.write("\\midrule\n")
        if speedups:
            avg_speedup = statistics.mean(speedups)
            geomean_speedup = statistics.geometric_mean(speedups)
            f.write(f"\\textbf{{Arithmetic Mean}} & & & {avg_speedup:.2f}$\\times$ & \\\\\n")
            f.write(f"\\textbf{{Geometric Mean}} & & & {geomean_speedup:.2f}$\\times$ & \\\\\n")
        
        f.write("\\bottomrule\n")
        f.write("\\end{tabular}\n")
        f.write("\\end{table}\n\n")
        
        # Per-pass breakdown table
        f.write("\n% Per-Pass Performance Breakdown\n")
        f.write("\\begin{table}[t]\n")
        f.write("\\centering\n")
        f.write("\\caption{Per-pass performance breakdown showing median execution times (ms) for selected compiler passes.}\n")
        f.write("\\label{tab:passes}\n")
        f.write("\\small\n")
        
        # Collect all unique passes
        all_passes = set()
        for aos_result, soa_result in all_results:
            if aos_result and aos_result.run_success:
                all_passes.update(aos_result.passes.keys())
        
        # Select most important passes (or top N by time)
        important_passes = ['instCountPass', 'blockCountPass', 'memoryOpStatsPass', 
                           'latencyModelPass', 'throughputModelPass']
        passes_to_show = [p for p in important_passes if p in all_passes]
        
        if passes_to_show:
            num_cols = len(passes_to_show) + 1
            col_spec = "l" + "r" * len(passes_to_show)
            f.write(f"\\begin{{tabular}}{{{col_spec}}}\n")
            f.write("\\toprule\n")
            f.write("\\textbf{Program}")
            for pass_name in passes_to_show:
                display_name = pass_name.replace('Pass', '').replace('_', '\\_')
                f.write(f" & \\textbf{{{display_name}}}")
            f.write(" \\\\\n")
            f.write("\\midrule\n")
            
            for aos_result, soa_result in all_results:
                if not aos_result or not soa_result:
                    continue
                if not aos_result.run_success or not soa_result.run_success:
                    continue
                
                program = aos_result.program.replace('.hs', '').replace('_', '\\_')
                f.write(f"{program} (AoS)")
                
                for pass_name in passes_to_show:
                    time_ms = aos_result.passes.get(pass_name, {}).get('median_time', 0) * 1000
                    f.write(f" & {time_ms:.2f}")
                f.write(" \\\\\n")
                
                f.write(f"\\hspace{{0.5em}} (SoA)")
                for pass_name in passes_to_show:
                    time_ms = soa_result.passes.get(pass_name, {}).get('median_time', 0) * 1000
                    aos_time = aos_result.passes.get(pass_name, {}).get('median_time', 0) * 1000
                    
                    # Bold if SoA is faster
                    if time_ms > 0 and aos_time > 0 and time_ms < aos_time * 0.95:
                        f.write(f" & \\textbf{{{time_ms:.2f}}}")
                    else:
                        f.write(f" & {time_ms:.2f}")
                f.write(" \\\\\n")
                f.write("\\midrule\n")
            
            f.write("\\bottomrule\n")
            f.write("\\end{tabular}\n")
        
        f.write("\\end{table}\n")


def generate_figures(all_results: List[Tuple[BenchmarkResult, BenchmarkResult]], 
                     output_dir: Path):
    """Generate publication-quality figures"""
    
    output_dir.mkdir(parents=True, exist_ok=True)
    
    # Set publication-quality defaults
    plt.rcParams.update({
        'font.size': 10,
        'font.family': 'serif',
        'figure.figsize': (7, 4),
        'figure.dpi': 300,
        'savefig.dpi': 300,
        'savefig.bbox': 'tight',
        'axes.labelsize': 10,
        'axes.titlesize': 11,
        'xtick.labelsize': 9,
        'ytick.labelsize': 9,
        'legend.fontsize': 9,
        'lines.linewidth': 1.5,
        'axes.grid': True,
        'grid.alpha': 0.3
    })
    
    # Filter successful results
    successful_results = [
        (aos, soa) for aos, soa in all_results
        if aos and soa and aos.run_success and soa.run_success
    ]
    
    if not successful_results:
        print("No successful results to plot")
        return
    
    # Figure 1: Speedup comparison (bar chart)
    generate_speedup_chart(successful_results, output_dir / "speedup_comparison.pdf")
    generate_speedup_chart(successful_results, output_dir / "speedup_comparison.png")
    
    # Figure 2: Performance comparison (grouped bar chart)
    generate_performance_comparison(successful_results, output_dir / "performance_comparison.pdf")
    generate_performance_comparison(successful_results, output_dir / "performance_comparison.png")
    
    # Figure 3: Per-pass breakdown (stacked bar chart)
    generate_pass_breakdown(successful_results, output_dir / "pass_breakdown.pdf")
    generate_pass_breakdown(successful_results, output_dir / "pass_breakdown.png")
    
    # Figure 4: Iteration time distributions (box plots)
    generate_iteration_boxplots(successful_results, output_dir / "iteration_distributions.pdf")
    generate_iteration_boxplots(successful_results, output_dir / "iteration_distributions.png")
    
    # Figure 5: Heatmap of speedups per pass
    generate_speedup_heatmap(successful_results, output_dir / "speedup_heatmap.pdf")
    generate_speedup_heatmap(successful_results, output_dir / "speedup_heatmap.png")
    
    print(f"\n{'='*70}")
    print("Generated publication figures:")
    print(f"{'='*70}")
    print(f"  • {output_dir / 'speedup_comparison.pdf'}")
    print(f"  • {output_dir / 'performance_comparison.pdf'}")
    print(f"  • {output_dir / 'pass_breakdown.pdf'}")
    print(f"  • {output_dir / 'iteration_distributions.pdf'}")
    print(f"  • {output_dir / 'speedup_heatmap.pdf'}")
    print(f"(PNG versions also generated)")


def generate_speedup_chart(results: List[Tuple[BenchmarkResult, BenchmarkResult]], 
                           output_file: Path):
    """Generate speedup bar chart"""
    programs = []
    speedups = []
    colors = []
    
    for aos_result, soa_result in results:
        program = aos_result.program.replace('.hs', '')
        
        aos_time = sum(p.get('median_time', 0) for p in aos_result.passes.values())
        soa_time = sum(p.get('median_time', 0) for p in soa_result.passes.values())
        
        if soa_time > 0:
            speedup = aos_time / soa_time
            programs.append(program)
            speedups.append(speedup)
            
            # Color code: green if SoA faster, red if AoS faster
            colors.append('#2ecc71' if speedup > 1.0 else '#e74c3c')
    
    fig, ax = plt.subplots(figsize=(10, 6))
    
    y_pos = np.arange(len(programs))
    bars = ax.barh(y_pos, speedups, color=colors, alpha=0.7, edgecolor='black', linewidth=0.5)
    
    ax.set_yticks(y_pos)
    ax.set_yticklabels(programs)
    ax.set_xlabel('Speedup (AoS time / SoA time)')
    ax.set_title('Performance Speedup: SoA vs AoS\n(>1.0 means SoA is faster)')
    ax.axvline(x=1.0, color='black', linestyle='--', linewidth=1, label='No speedup')
    
    # Add value labels on bars
    for i, (bar, speedup) in enumerate(zip(bars, speedups)):
        width = bar.get_width()
        label_x = width + 0.02 if width < 1.0 else width - 0.02
        ha = 'left' if width < 1.0 else 'right'
        ax.text(label_x, bar.get_y() + bar.get_height()/2, 
                f'{speedup:.2f}×', ha=ha, va='center', fontsize=8, fontweight='bold')
    
    # Add geometric mean line
    if speedups:
        geomean = statistics.geometric_mean(speedups)
        ax.axvline(x=geomean, color='blue', linestyle=':', linewidth=2, 
                  label=f'Geometric mean: {geomean:.2f}×')
    
    ax.legend(loc='best')
    ax.grid(True, alpha=0.3, axis='x')
    
    plt.tight_layout()
    plt.savefig(output_file)
    plt.close()


def generate_performance_comparison(results: List[Tuple[BenchmarkResult, BenchmarkResult]], 
                                    output_file: Path):
    """Generate grouped bar chart comparing AoS vs SoA times"""
    programs = []
    aos_times = []
    soa_times = []
    
    for aos_result, soa_result in results:
        program = aos_result.program.replace('.hs', '')
        programs.append(program)
        
        aos_time = sum(p.get('median_time', 0) for p in aos_result.passes.values()) * 1000
        soa_time = sum(p.get('median_time', 0) for p in soa_result.passes.values()) * 1000
        
        aos_times.append(aos_time)
        soa_times.append(soa_time)
    
    x = np.arange(len(programs))
    width = 0.35
    
    fig, ax = plt.subplots(figsize=(12, 6))
    
    bars1 = ax.bar(x - width/2, aos_times, width, label='AoS', 
                   color='#3498db', alpha=0.8, edgecolor='black', linewidth=0.5)
    bars2 = ax.bar(x + width/2, soa_times, width, label='SoA', 
                   color='#e67e22', alpha=0.8, edgecolor='black', linewidth=0.5)
    
    ax.set_xlabel('Program')
    ax.set_ylabel('Total Execution Time (ms)')
    ax.set_title('Performance Comparison: AoS vs SoA')
    ax.set_xticks(x)
    ax.set_xticklabels(programs, rotation=45, ha='right')
    ax.legend()
    ax.grid(True, alpha=0.3, axis='y')
    
    plt.tight_layout()
    plt.savefig(output_file)
    plt.close()


def generate_pass_breakdown(results: List[Tuple[BenchmarkResult, BenchmarkResult]], 
                            output_file: Path):
    """Generate stacked bar chart showing per-pass breakdown"""
    programs = []
    
    # Collect all unique passes
    all_passes = set()
    for aos_result, soa_result in results:
        all_passes.update(aos_result.passes.keys())
    
    # Select important passes
    important_passes = ['instCountPass', 'blockCountPass', 'memoryOpStatsPass', 
                       'castInstCountPass', 'branchStatsPass', 'latencyModelPass',
                       'throughputModelPass', 'targetRetunePass', 'stripSideEffectsPass']
    passes_to_show = [p for p in important_passes if p in all_passes][:6]  # Top 6
    
    # Collect data
    aos_data = {pass_name: [] for pass_name in passes_to_show}
    soa_data = {pass_name: [] for pass_name in passes_to_show}
    
    for aos_result, soa_result in results:
        program = aos_result.program.replace('.hs', '')
        programs.append(program)
        
        for pass_name in passes_to_show:
            aos_time = aos_result.passes.get(pass_name, {}).get('median_time', 0) * 1000
            soa_time = soa_result.passes.get(pass_name, {}).get('median_time', 0) * 1000
            
            aos_data[pass_name].append(aos_time)
            soa_data[pass_name].append(soa_time)
    
    # Create subplots for AoS and SoA
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))
    
    x = np.arange(len(programs))
    width = 0.6
    
    # Colors for different passes
    colors = plt.cm.Set3(np.linspace(0, 1, len(passes_to_show)))
    
    # AoS stacked bars
    bottom = np.zeros(len(programs))
    for i, pass_name in enumerate(passes_to_show):
        ax1.bar(x, aos_data[pass_name], width, label=pass_name.replace('Pass', ''), 
               bottom=bottom, color=colors[i], edgecolor='black', linewidth=0.3)
        bottom += np.array(aos_data[pass_name])
    
    ax1.set_xlabel('Program')
    ax1.set_ylabel('Execution Time (ms)')
    ax1.set_title('AoS: Per-Pass Breakdown')
    ax1.set_xticks(x)
    ax1.set_xticklabels(programs, rotation=45, ha='right')
    ax1.legend(bbox_to_anchor=(1.05, 1), loc='upper left', fontsize=8)
    ax1.grid(True, alpha=0.3, axis='y')
    
    # SoA stacked bars
    bottom = np.zeros(len(programs))
    for i, pass_name in enumerate(passes_to_show):
        ax2.bar(x, soa_data[pass_name], width, label=pass_name.replace('Pass', ''), 
               bottom=bottom, color=colors[i], edgecolor='black', linewidth=0.3)
        bottom += np.array(soa_data[pass_name])
    
    ax2.set_xlabel('Program')
    ax2.set_ylabel('Execution Time (ms)')
    ax2.set_title('SoA: Per-Pass Breakdown')
    ax2.set_xticks(x)
    ax2.set_xticklabels(programs, rotation=45, ha='right')
    ax2.grid(True, alpha=0.3, axis='y')
    
    plt.tight_layout()
    plt.savefig(output_file)
    plt.close()


def generate_iteration_boxplots(results: List[Tuple[BenchmarkResult, BenchmarkResult]], 
                                output_file: Path):
    """Generate box plots showing iteration time distributions"""
    # Select one important pass to analyze
    pass_name = 'instCountPass'
    
    # Collect iteration times
    data_to_plot = []
    labels = []
    
    for aos_result, soa_result in results[:6]:  # Limit to first 6 programs for readability
        program = aos_result.program.replace('.hs', '')
        
        aos_times = aos_result.passes.get(pass_name, {}).get('iter_times', [])
        soa_times = soa_result.passes.get(pass_name, {}).get('iter_times', [])
        
        if aos_times and soa_times:
            data_to_plot.extend([
                [t * 1000 for t in aos_times],
                [t * 1000 for t in soa_times]
            ])
            labels.extend([f'{program}\n(AoS)', f'{program}\n(SoA)'])
    
    if not data_to_plot:
        return
    
    fig, ax = plt.subplots(figsize=(12, 6))
    
    bp = ax.boxplot(data_to_plot, labels=labels, patch_artist=True,
                    medianprops=dict(color='red', linewidth=2),
                    boxprops=dict(facecolor='lightblue', alpha=0.7),
                    whiskerprops=dict(linewidth=1.5),
                    capprops=dict(linewidth=1.5))
    
    # Color AoS and SoA differently
    for i, box in enumerate(bp['boxes']):
        if i % 2 == 0:  # AoS
            box.set_facecolor('#3498db')
        else:  # SoA
            box.set_facecolor('#e67e22')
    
    ax.set_xlabel('Program and Variant')
    ax.set_ylabel('Execution Time (ms)')
    ax.set_title(f'Iteration Time Distribution: {pass_name.replace("Pass", "")}')
    ax.grid(True, alpha=0.3, axis='y')
    
    plt.xticks(rotation=0, ha='center')
    plt.tight_layout()
    plt.savefig(output_file)
    plt.close()


def generate_speedup_heatmap(results: List[Tuple[BenchmarkResult, BenchmarkResult]], 
                             output_file: Path):
    """Generate heatmap of speedups across programs and passes"""
    programs = []
    
    # Collect all unique passes
    all_passes = set()
    for aos_result, soa_result in results:
        all_passes.update(aos_result.passes.keys())
    
    passes_to_show = sorted(list(all_passes))[:8]  # Show top 8 passes
    
    # Build speedup matrix
    speedup_matrix = []
    
    for aos_result, soa_result in results:
        program = aos_result.program.replace('.hs', '')
        programs.append(program)
        
        row = []
        for pass_name in passes_to_show:
            aos_time = aos_result.passes.get(pass_name, {}).get('median_time', 0)
            soa_time = soa_result.passes.get(pass_name, {}).get('median_time', 0)
            
            if soa_time > 0 and aos_time > 0:
                speedup = aos_time / soa_time
            else:
                speedup = 1.0
            
            row.append(speedup)
        
        speedup_matrix.append(row)
    
    speedup_matrix = np.array(speedup_matrix)
    
    fig, ax = plt.subplots(figsize=(10, 8))
    
    # Use diverging colormap centered at 1.0
    im = ax.imshow(speedup_matrix, cmap='RdYlGn', aspect='auto', 
                   vmin=0.8, vmax=1.2, interpolation='nearest')
    
    # Set ticks and labels
    ax.set_xticks(np.arange(len(passes_to_show)))
    ax.set_yticks(np.arange(len(programs)))
    ax.set_xticklabels([p.replace('Pass', '') for p in passes_to_show], rotation=45, ha='right')
    ax.set_yticklabels(programs)
    
    # Add colorbar
    cbar = plt.colorbar(im, ax=ax)
    cbar.set_label('Speedup (AoS/SoA)', rotation=270, labelpad=20)
    
    # Add text annotations
    for i in range(len(programs)):
        for j in range(len(passes_to_show)):
            text = ax.text(j, i, f'{speedup_matrix[i, j]:.2f}',
                          ha='center', va='center', color='black', fontsize=7)
    
    ax.set_title('Speedup Heatmap: Per-Pass Performance (SoA vs AoS)')
    ax.set_xlabel('Compiler Pass')
    ax.set_ylabel('Program')
    
    plt.tight_layout()
    plt.savefig(output_file)
    plt.close()


def save_json_results(all_results: List[Tuple[BenchmarkResult, BenchmarkResult]], 
                     output_file: Path):
    """Save results in JSON format for further analysis"""
    data = {
        "timestamp": time.strftime('%Y-%m-%d %H:%M:%S'),
        "results": []
    }
    
    for aos_result, soa_result in all_results:
        program_data = {
            "program": aos_result.program if aos_result else soa_result.program,
            "aos": aos_result.to_dict() if aos_result else None,
            "soa": soa_result.to_dict() if soa_result else None,
            "outputs_match": compare_outputs(aos_result, soa_result)
        }
        data["results"].append(program_data)
    
    with open(output_file, 'w') as f:
        json.dump(data, f, indent=2)


def main():
    import argparse
    
    parser = argparse.ArgumentParser(description="Benchmark Gibbon compiler programs")
    parser.add_argument("--programs-dir", type=Path, default=Path("programs"),
                       help="Directory containing AoS and SoA subdirectories")
    parser.add_argument("--output-dir", type=Path, default=Path("benchmark_output"),
                       help="Directory for compiled files")
    parser.add_argument("--iterations", type=int, default=20,
                       help="Number of iterations for each benchmark")
    parser.add_argument("--report", type=Path, default=Path("benchmark_report.txt"),
                       help="Output report file")
    parser.add_argument("--json", type=Path, default=Path("benchmark_results.json"),
                       help="JSON output file")
    parser.add_argument("--programs", nargs="+", 
                       help="Specific programs to benchmark (default: all)")
    parser.add_argument("--generate-paper", action="store_true",
                       help="Generate LaTeX tables and figures for conference paper")
    parser.add_argument("--latex-table", type=Path, default=Path("performance_table.tex"),
                       help="Output LaTeX table file (when --generate-paper is used)")
    parser.add_argument("--figures-dir", type=Path, default=Path("figures"),
                       help="Directory for generated figures (when --generate-paper is used)")
    parser.add_argument("--clean", action="store_true",
                       help="Force recompilation even if executables are up-to-date")
    
    args = parser.parse_args()
    
    # Determine which programs to benchmark
    programs_to_run = args.programs if args.programs else PROGRAMS
    
    print("\n" + "=" * 70)
    print("GIBBON COMPILER BENCHMARK SUITE")
    print("=" * 70)
    print(f"Programs directory: {args.programs_dir}")
    print(f"Output directory: {args.output_dir}")
    print(f"Iterations: {args.iterations}")
    print(f"Programs to benchmark: {len(programs_to_run)}")
    print(f"Force recompilation: {'Yes' if args.clean else 'No (smart recompilation)'}")
    print("=" * 70)
    
    # Create output directory
    args.output_dir.mkdir(parents=True, exist_ok=True)
    
    # Benchmark all programs
    all_results = []
    
    for program in programs_to_run:
        aos_result, soa_result = benchmark_program(
            program, 
            args.programs_dir, 
            args.output_dir,
            args.iterations,
            args.clean  # Pass the clean flag
        )
        all_results.append((aos_result, soa_result))
    
    # Generate reports
    print(f"\n\n{'='*70}")
    print("Generating reports...")
    print(f"{'='*70}")
    
    generate_report(all_results, args.report)
    print(f"✓ Text report saved to: {args.report}")
    
    save_json_results(all_results, args.json)
    print(f"✓ JSON results saved to: {args.json}")
    
    # Generate paper materials if requested
    if args.generate_paper:
        print(f"\n{'='*70}")
        print("Generating conference paper materials...")
        print(f"{'='*70}")
        
        generate_latex_table(all_results, args.latex_table)
        print(f"✓ LaTeX table saved to: {args.latex_table}")
        
        generate_figures(all_results, args.figures_dir)
        
        print(f"\n{'='*70}")
        print("PAPER MATERIALS GENERATED")
        print(f"{'='*70}")
        print("Include in your LaTeX paper:")
        print(f"  1. Add to preamble:")
        print(f"     \\usepackage{{booktabs}}")
        print(f"     \\usepackage{{graphicx}}")
        print(f"  2. Include table with:")
        print(f"     \\input{{{args.latex_table}}}")
        print(f"  3. Include figures with:")
        print(f"     \\includegraphics[width=\\columnwidth]{{{args.figures_dir}/speedup_comparison.pdf}}")
        print(f"     \\includegraphics[width=\\columnwidth]{{{args.figures_dir}/performance_comparison.pdf}}")
        print(f"     ... etc.")
        print(f"{'='*70}")
    
    # Summary
    print(f"\n{'='*70}")
    print("BENCHMARK COMPLETE")
    print(f"{'='*70}")
    
    successful_runs = sum(1 for aos, soa in all_results 
                         if aos and aos.run_success and soa and soa.run_success)
    matching_outputs = sum(1 for aos, soa in all_results 
                          if compare_outputs(aos, soa) is True)
    
    print(f"Total programs: {len(all_results)}")
    print(f"Successful runs (both AoS and SoA): {successful_runs}")
    print(f"Matching outputs: {matching_outputs}")
    
    if matching_outputs < successful_runs:
        print("\n⚠ WARNING: Some programs produced different outputs between AoS and SoA!")
        print("   Check the detailed report for more information.")
    
    print(f"\nDetailed results in: {args.report}")
    print(f"JSON data in: {args.json}")


if __name__ == "__main__":
    main()
