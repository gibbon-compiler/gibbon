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
    Extract the actual program output by filtering out all timing data and GC/allocation metadata.
    This allows comparison of program results regardless of format.
    """
    lines = output.split('\n')
    filtered_lines = []
    
    # Patterns to exclude (timing, benchmark metadata, GC/allocation info)
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
        r'^INFO_TABLE:',  # GC metadata
        r'^Initialized footer at',  # GC region info
        r'^GibOldgenChunkFooter',  # GC chunk info
        r'^GibRegionInfo',  # GC region info
        r'.*refcount:.*outset:.*first_chunk_footer:',  # GC details
        r'^Total allocated bytes:',  # Allocation stats
        r'^Total copied bytes:',  # GC stats
        r'^ALLOC_TOTAL:',  # Allocation metadata
        r'^GC_TOTAL:',  # GC metadata
        r'^region.*size.*next:',  # Region info (case insensitive pattern)
    ]
    
    for line in lines:
        # Check if line matches any exclude pattern
        should_exclude = False
        line_stripped = line.strip()
        
        for pattern in exclude_patterns:
            if re.match(pattern, line_stripped, re.IGNORECASE):
                should_exclude = True
                break
        
        # Also exclude lines that look like GC debug output (contain memory addresses)
        if re.search(r'0x[0-9a-fA-F]+', line_stripped):
            # But keep lines that are actual program output with hex numbers
            # Only exclude if it looks like GC output (has keywords like footer, chunk, region)
            if any(keyword in line_stripped.lower() for keyword in 
                   ['footer', 'chunk', 'region', 'refcount', 'outset']):
                should_exclude = True
        
        if not should_exclude and line_stripped:
            filtered_lines.append(line_stripped)
    
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


def read_fold_map_classification(programs_dir: Path) -> Dict[str, Dict[str, str]]:
    """
    Read fold/map classification from print statements in source files.
    Looks for patterns like: printsym (quote "Running pass PassName (fold): ")
    
    Returns dict: {program: {pass_name: 'fold' or 'map'}}
    """
    classification = {}
    
    for variant_dir in ['AoS', 'SoA']:
        variant_path = programs_dir / variant_dir
        if not variant_path.exists():
            continue
            
        for source_file in variant_path.glob('*.hs'):
            program = source_file.name
            if program not in classification:
                classification[program] = {}
            
            try:
                with open(source_file, 'r') as f:
                    content = f.read()
                    
                    # Look for print statements that indicate pass type
                    # Pattern: printsym (quote "Running pass PassName (fold): ")
                    # or: printsym (quote "Running pass PassName (map): ")
                    # or: printsym (quote "Running pass PassName (fold like): ")
                    
                    # Regex to match: Running pass <name> (<type>):
                    pattern = r'printsym\s*\(\s*quote\s*"Running pass\s+([^(]+?)\s*\(([^)]+)\)\s*:'
                    
                    for match in re.finditer(pattern, content):
                        pass_name_raw = match.group(1).strip()
                        pass_type_raw = match.group(2).strip().lower()
                        
                        # Normalize pass type
                        if 'fold' in pass_type_raw:
                            pass_type = 'fold'
                        elif 'map' in pass_type_raw:
                            pass_type = 'map'
                        else:
                            pass_type = 'unknown'
                        
                        # Convert pass name to match benchmark output
                        # "SumArea" stays as "SumArea"
                        # "find max Bottom" might need cleaning
                        # We'll try to match against actual pass names in results
                        
                        # Store both the raw name and cleaned versions
                        pass_name_clean = pass_name_raw.replace(' ', '')
                        
                        classification[program][pass_name_clean] = pass_type
                        classification[program][pass_name_raw] = pass_type
                        
                        # Also store common variations
                        pass_name_lower = pass_name_clean.lower()
                        classification[program][pass_name_lower] = pass_type
                        
            except Exception as e:
                # Skip files that can't be read
                print(f"  Note: Could not parse {source_file}: {e}")
                pass
    
    return classification


def format_time_scientific(time_seconds: float) -> str:
    """Format time in scientific notation if very small, otherwise use milliseconds"""
    time_ms = time_seconds * 1000
    
    if time_ms < 0.01:  # Very small, use scientific notation
        return f"{time_seconds:.2e}"
    elif time_ms < 1.0:  # Small but readable in ms
        return f"{time_ms:.3f}"
    else:  # Normal range
        return f"{time_ms:.2f}"


def generate_latex_table(all_results: List[Tuple[BenchmarkResult, BenchmarkResult]], 
                         output_file: Path, programs_dir: Path = None):
    """Generate LaTeX tables for conference paper"""
    
    # Read fold/map classification if available
    fold_map_class = {}
    if programs_dir:
        fold_map_class = read_fold_map_classification(programs_dir)
    
    with open(output_file, 'w') as f:
        f.write("% Performance Tables - Generated by Gibbon Benchmark Suite\n")
        f.write("% Include in your LaTeX document with: \\input{" + output_file.name + "}\n\n")
        
        # Table 1: End-to-end performance by fold/map classification
        generate_fold_map_summary_table(f, all_results, fold_map_class)
        
        # Tables 2+: Per-program detailed breakdown
        generate_per_program_tables(f, all_results, fold_map_class)


def generate_fold_map_summary_table(f, all_results, fold_map_class):
    """Generate summary table showing end-to-end times classified by fold vs map"""
    
    f.write("\\begin{table}[t]\n")
    f.write("\\centering\n")
    f.write("\\caption{End-to-end performance comparison classified by pass types. ")
    f.write("Times shown are total execution time in seconds (scientific notation). ")
    f.write("Speedup $>1.0$ indicates SoA is faster.}\n")
    f.write("\\label{tab:endtoend}\n")
    f.write("\\small\n")
    f.write("\\begin{tabular}{l r r r r r r}\n")
    f.write("\\toprule\n")
    f.write("\\textbf{Program} & \\multicolumn{2}{c}{\\textbf{Fold Passes}} & \\multicolumn{2}{c}{\\textbf{Map Passes}} & \\multicolumn{2}{c}{\\textbf{Total}} \\\\\n")
    f.write("\\cmidrule(lr){2-3} \\cmidrule(lr){4-5} \\cmidrule(lr){6-7}\n")
    f.write(" & \\textbf{AoS} & \\textbf{SoA} & \\textbf{AoS} & \\textbf{SoA} & \\textbf{Time} & \\textbf{Speedup} \\\\\n")
    f.write("\\midrule\n")
    
    for aos_result, soa_result in all_results:
        if not aos_result or not soa_result:
            continue
        if not aos_result.run_success or not soa_result.run_success:
            continue
        
        program = aos_result.program.replace('.hs', '').replace('_', '\\_')
        prog_class = fold_map_class.get(aos_result.program, {})
        
        # Separate fold and map passes
        aos_fold_time = 0
        aos_map_time = 0
        soa_fold_time = 0
        soa_map_time = 0
        
        for pass_name, pass_data in aos_result.passes.items():
            # Try multiple variations to find pass type
            pass_type = 'unknown'
            if pass_name in prog_class:
                pass_type = prog_class[pass_name]
            else:
                # Try without "Pass" suffix
                pass_name_no_suffix = pass_name.replace('Pass', '')
                if pass_name_no_suffix in prog_class:
                    pass_type = prog_class[pass_name_no_suffix]
                else:
                    # Try lowercase variations
                    for variant in [pass_name.lower(), pass_name_no_suffix.lower()]:
                        if variant in prog_class:
                            pass_type = prog_class[variant]
                            break
            
            time = pass_data.get('median_time', 0)
            
            if pass_type == 'fold':
                aos_fold_time += time
            elif pass_type == 'map':
                aos_map_time += time
        
        for pass_name, pass_data in soa_result.passes.items():
            # Try multiple variations to find pass type
            pass_type = 'unknown'
            if pass_name in prog_class:
                pass_type = prog_class[pass_name]
            else:
                # Try without "Pass" suffix
                pass_name_no_suffix = pass_name.replace('Pass', '')
                if pass_name_no_suffix in prog_class:
                    pass_type = prog_class[pass_name_no_suffix]
                else:
                    # Try lowercase variations
                    for variant in [pass_name.lower(), pass_name_no_suffix.lower()]:
                        if variant in prog_class:
                            pass_type = prog_class[variant]
                            break
            
            time = pass_data.get('median_time', 0)
            
            if pass_type == 'fold':
                soa_fold_time += time
            elif pass_type == 'map':
                soa_map_time += time
        
        # Total times
        aos_total = sum(p.get('median_time', 0) for p in aos_result.passes.values())
        soa_total = sum(p.get('median_time', 0) for p in soa_result.passes.values())
        
        speedup = aos_total / soa_total if soa_total > 0 else 0
        
        # Format times
        aos_fold_str = format_time_scientific(aos_fold_time) if aos_fold_time > 0 else '--'
        soa_fold_str = format_time_scientific(soa_fold_time) if soa_fold_time > 0 else '--'
        aos_map_str = format_time_scientific(aos_map_time) if aos_map_time > 0 else '--'
        soa_map_str = format_time_scientific(soa_map_time) if soa_map_time > 0 else '--'
        total_str = format_time_scientific(aos_total)
        
        # Highlight best total time
        if speedup > 1.05:
            f.write(f"{program} & {aos_fold_str} & {soa_fold_str} & {aos_map_str} & {soa_map_str} & \\textbf{{{total_str}}} & {speedup:.2f}$\\times$ \\\\\n")
        else:
            f.write(f"{program} & {aos_fold_str} & {soa_fold_str} & {aos_map_str} & {soa_map_str} & {total_str} & {speedup:.2f}$\\times$ \\\\\n")
    
    f.write("\\bottomrule\n")
    f.write("\\end{tabular}\n")
    f.write("\\end{table}\n\n")


def generate_per_program_tables(f, all_results, fold_map_class):
    """Generate detailed per-program tables showing all passes"""
    
    for aos_result, soa_result in all_results:
        if not aos_result or not soa_result:
            continue
        if not aos_result.run_success or not soa_result.run_success:
            continue
        
        program = aos_result.program.replace('.hs', '')
        program_clean = program.replace('_', '\\_')
        prog_class = fold_map_class.get(aos_result.program, {})
        
        # Get all passes for this program
        all_passes = sorted(set(list(aos_result.passes.keys()) + list(soa_result.passes.keys())))
        
        if not all_passes:
            continue
        
        f.write(f"\\begin{{table}}[t]\n")
        f.write("\\centering\n")
        f.write(f"\\caption{{Per-pass performance breakdown for {program_clean}. ")
        f.write("Times in seconds (scientific notation). ")
        f.write("Type: fold (F) or map (M).}}\n")
        f.write(f"\\label{{tab:{program}}}\n")
        f.write("\\small\n")
        f.write("\\begin{tabular}{l c r r r}\n")
        f.write("\\toprule\n")
        f.write("\\textbf{Pass} & \\textbf{Type} & \\textbf{AoS} & \\textbf{SoA} & \\textbf{Speedup} \\\\\n")
        f.write("\\midrule\n")
        
        for pass_name in all_passes:
            aos_time = aos_result.passes.get(pass_name, {}).get('median_time', 0)
            soa_time = soa_result.passes.get(pass_name, {}).get('median_time', 0)
            
            if aos_time == 0 and soa_time == 0:
                continue
            
            # Get pass type - try multiple variations
            pass_type = 'unknown'
            
            # Try direct lookup
            if pass_name in prog_class:
                pass_type = prog_class[pass_name]
            else:
                # Try without "Pass" suffix
                pass_name_no_suffix = pass_name.replace('Pass', '')
                if pass_name_no_suffix in prog_class:
                    pass_type = prog_class[pass_name_no_suffix]
                else:
                    # Try lowercase
                    pass_name_lower = pass_name.lower()
                    if pass_name_lower in prog_class:
                        pass_type = prog_class[pass_name_lower]
                    else:
                        # Try lowercase without Pass
                        pass_name_lower_no_suffix = pass_name_no_suffix.lower()
                        if pass_name_lower_no_suffix in prog_class:
                            pass_type = prog_class[pass_name_lower_no_suffix]
            
            type_str = 'F' if pass_type == 'fold' else ('M' if pass_type == 'map' else '?')
            
            # Calculate speedup
            speedup = aos_time / soa_time if soa_time > 0 else 0
            
            # Format times
            aos_str = format_time_scientific(aos_time) if aos_time > 0 else '--'
            soa_str = format_time_scientific(soa_time) if soa_time > 0 else '--'
            
            # Clean pass name
            pass_display = pass_name.replace('Pass', '').replace('_', '\\_')
            
            # Highlight if significant speedup
            if speedup > 1.1:
                f.write(f"{pass_display} & {type_str} & {aos_str} & \\textbf{{{soa_str}}} & {speedup:.2f}$\\times$ \\\\\n")
            elif speedup < 0.9 and speedup > 0:
                f.write(f"{pass_display} & {type_str} & \\textbf{{{aos_str}}} & {soa_str} & {speedup:.2f}$\\times$ \\\\\n")
            else:
                f.write(f"{pass_display} & {type_str} & {aos_str} & {soa_str} & {speedup:.2f}$\\times$ \\\\\n")
        
        f.write("\\midrule\n")
        # Add totals
        aos_total = sum(p.get('median_time', 0) for p in aos_result.passes.values())
        soa_total = sum(p.get('median_time', 0) for p in soa_result.passes.values())
        total_speedup = aos_total / soa_total if soa_total > 0 else 0
        
        f.write(f"\\textbf{{Total}} & & {format_time_scientific(aos_total)} & {format_time_scientific(soa_total)} & {total_speedup:.2f}$\\times$ \\\\\n")
        f.write("\\bottomrule\n")
        f.write("\\end{tabular}\n")
        f.write("\\end{table}\n\n\n")


def generate_fold_map_summary_table(f, all_results, fold_map_class):
    """Generate summary table showing end-to-end times classified by fold vs map"""
    
    f.write("\\begin{table}[t]\n")
    f.write("\\centering\n")
    f.write("\\caption{End-to-end performance comparison classified by pass types. ")
    f.write("Times shown are total execution time in seconds (scientific notation). ")
    f.write("Speedup $>1.0$ indicates SoA is faster.}\n")
    f.write("\\label{tab:endtoend}\n")
    f.write("\\small\n")
    f.write("\\begin{tabular}{l r r r r r r}\n")
    f.write("\\toprule\n")
    f.write("\\textbf{Program} & \\multicolumn{2}{c}{\\textbf{Fold Passes}} & \\multicolumn{2}{c}{\\textbf{Map Passes}} & \\multicolumn{2}{c}{\\textbf{Total}} \\\\\n")
    f.write("\\cmidrule(lr){2-3} \\cmidrule(lr){4-5} \\cmidrule(lr){6-7}\n")
    f.write(" & \\textbf{AoS} & \\textbf{SoA} & \\textbf{AoS} & \\textbf{SoA} & \\textbf{Time} & \\textbf{Speedup} \\\\\n")
    f.write("\\midrule\n")
    
    for aos_result, soa_result in all_results:
        if not aos_result or not soa_result:
            continue
        if not aos_result.run_success or not soa_result.run_success:
            continue
        
        program = aos_result.program.replace('.hs', '').replace('_', '\\_')
        prog_class = fold_map_class.get(aos_result.program, {})
        
        # Separate fold and map passes
        aos_fold_time = 0
        aos_map_time = 0
        soa_fold_time = 0
        soa_map_time = 0
        
        for pass_name, pass_data in aos_result.passes.items():
            pass_type = prog_class.get(pass_name, 'unknown')
            time = pass_data.get('median_time', 0)
            
            if pass_type == 'fold':
                aos_fold_time += time
            elif pass_type == 'map':
                aos_map_time += time
        
        for pass_name, pass_data in soa_result.passes.items():
            pass_type = prog_class.get(pass_name, 'unknown')
            time = pass_data.get('median_time', 0)
            
            if pass_type == 'fold':
                soa_fold_time += time
            elif pass_type == 'map':
                soa_map_time += time
        
        # Total times
        aos_total = sum(p.get('median_time', 0) for p in aos_result.passes.values())
        soa_total = sum(p.get('median_time', 0) for p in soa_result.passes.values())
        
        speedup = aos_total / soa_total if soa_total > 0 else 0
        
        # Format times
        aos_fold_str = format_time_scientific(aos_fold_time) if aos_fold_time > 0 else '--'
        soa_fold_str = format_time_scientific(soa_fold_time) if soa_fold_time > 0 else '--'
        aos_map_str = format_time_scientific(aos_map_time) if aos_map_time > 0 else '--'
        soa_map_str = format_time_scientific(soa_map_time) if soa_map_time > 0 else '--'
        total_str = format_time_scientific(aos_total)
        
        # Highlight best total time
        if speedup > 1.05:
            f.write(f"{program} & {aos_fold_str} & {soa_fold_str} & {aos_map_str} & {soa_map_str} & \\textbf{{{total_str}}} & {speedup:.2f}$\\times$ \\\\\n")
        else:
            f.write(f"{program} & {aos_fold_str} & {soa_fold_str} & {aos_map_str} & {soa_map_str} & {total_str} & {speedup:.2f}$\\times$ \\\\\n")
    
    f.write("\\bottomrule\n")
    f.write("\\end{tabular}\n")
    f.write("\\end{table}\n\n")


def generate_figures(all_results: List[Tuple[BenchmarkResult, BenchmarkResult]], 
                     output_dir: Path, programs_dir: Path = None):
    """Generate publication-quality figures"""
    
    output_dir.mkdir(parents=True, exist_ok=True)
    
    # Read fold/map classification
    fold_map_class = {}
    if programs_dir:
        fold_map_class = read_fold_map_classification(programs_dir)
    
    # Set publication-quality defaults
    plt.rcParams.update({
        'font.size': 9,
        'font.family': 'serif',
        'figure.figsize': (7, 4),
        'figure.dpi': 300,
        'savefig.dpi': 300,
        'savefig.bbox': 'tight',
        'axes.labelsize': 9,
        'axes.titlesize': 10,
        'xtick.labelsize': 8,
        'ytick.labelsize': 8,
        'legend.fontsize': 8,
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
    
    # Figure 1: Overall speedup comparison separated by fold/map
    generate_fold_map_speedup_chart(successful_results, fold_map_class, output_dir / "speedup_comparison.pdf")
    generate_fold_map_speedup_chart(successful_results, fold_map_class, output_dir / "speedup_comparison.png")
    
    # Figure 2: Per-program heatmaps (one per program)
    generate_per_program_heatmaps(successful_results, output_dir)
    
    # Figure 3: Complete pass breakdown with horizontal legend and patterns
    generate_complete_pass_breakdown_improved(successful_results, output_dir / "pass_breakdown_all.pdf")
    generate_complete_pass_breakdown_improved(successful_results, output_dir / "pass_breakdown_all.png")
    
    # Figure 4: Individual program figures (separate file for each program with all passes)
    generate_per_program_figures(successful_results, output_dir)
    
    # Figure 5: Per-pass speedup comparison (all programs for each pass)
    generate_per_pass_speedup_figures(successful_results, output_dir)
    
    print(f"\n{'='*70}")
    print("Generated publication figures:")
    print(f"{'='*70}")
    print(f"  • {output_dir / 'speedup_comparison.pdf'} (fold/map separated)")
    print(f"  • {output_dir / 'pass_breakdown_all.pdf'} (improved)")
    print(f"  • Per-program heatmaps in {output_dir}/heatmaps/")
    print(f"  • Individual program figures in {output_dir}/per_program/")
    print(f"  • Per-pass speedup figures in {output_dir}/per_pass/")
    print(f"(PNG versions also generated)")

    
    # Set publication-quality defaults
    plt.rcParams.update({
        'font.size': 9,
        'font.family': 'serif',
        'figure.figsize': (7, 4),
        'figure.dpi': 300,
        'savefig.dpi': 300,
        'savefig.bbox': 'tight',
        'axes.labelsize': 9,
        'axes.titlesize': 10,
        'xtick.labelsize': 8,
        'ytick.labelsize': 8,
        'legend.fontsize': 8,
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
    
    # Figure 1: Overall speedup comparison (bar chart)
    generate_speedup_chart(successful_results, output_dir / "speedup_comparison.pdf")
    generate_speedup_chart(successful_results, output_dir / "speedup_comparison.png")
    
    # Figure 2: Comprehensive speedup heatmap (ALL programs x ALL passes)
    generate_comprehensive_speedup_heatmap(successful_results, output_dir / "speedup_heatmap.pdf")
    generate_comprehensive_speedup_heatmap(successful_results, output_dir / "speedup_heatmap.png")
    
    # Figure 3: Per-program breakdown (one figure with all programs showing all passes)
    generate_complete_pass_breakdown(successful_results, output_dir / "pass_breakdown_all.pdf")
    generate_complete_pass_breakdown(successful_results, output_dir / "pass_breakdown_all.png")
    
    # Figure 4: Individual program figures (separate file for each program with all passes)
    generate_per_program_figures(successful_results, output_dir)
    
    # Figure 5: Per-pass speedup comparison (all programs for each pass)
    generate_per_pass_speedup_figures(successful_results, output_dir)
    
    # Figure 6: Comprehensive program-pass speedup grid
    generate_program_pass_speedup_grid(successful_results, output_dir / "program_pass_speedup_grid.pdf")
    generate_program_pass_speedup_grid(successful_results, output_dir / "program_pass_speedup_grid.png")
    
    print(f"\n{'='*70}")
    print("Generated publication figures:")
    print(f"{'='*70}")
    print(f"  • {output_dir / 'speedup_comparison.pdf'}")
    print(f"  • {output_dir / 'speedup_heatmap.pdf'} (comprehensive)")
    print(f"  • {output_dir / 'pass_breakdown_all.pdf'} (all programs)")
    print(f"  • {output_dir / 'program_pass_speedup_grid.pdf'}")
    print(f"  • Individual program figures in {output_dir}/per_program/")
    print(f"  • Per-pass speedup figures in {output_dir}/per_pass/")
    print(f"(PNG versions also generated)")



def generate_fold_map_speedup_chart(results: List[Tuple[BenchmarkResult, BenchmarkResult]],
                                    fold_map_class: Dict, output_file: Path):
    """Generate speedup chart separated by fold vs map passes"""
    fold_data = []
    map_data = []
    programs = []
    
    for aos_result, soa_result in results:
        program = aos_result.program.replace('.hs', '')
        programs.append(program)
        prog_class = fold_map_class.get(aos_result.program, {})
        
        # Helper function to get pass type with multiple lookups
        def get_pass_type(pass_name, class_dict):
            if pass_name in class_dict:
                return class_dict[pass_name]
            pass_name_no_suffix = pass_name.replace('Pass', '')
            if pass_name_no_suffix in class_dict:
                return class_dict[pass_name_no_suffix]
            for variant in [pass_name.lower(), pass_name_no_suffix.lower()]:
                if variant in class_dict:
                    return class_dict[variant]
            return 'unknown'
        
        # Calculate fold and map times separately
        aos_fold = sum(p.get('median_time', 0) for name, p in aos_result.passes.items()
                      if get_pass_type(name, prog_class) == 'fold')
        soa_fold = sum(p.get('median_time', 0) for name, p in soa_result.passes.items()
                      if get_pass_type(name, prog_class) == 'fold')
        
        aos_map = sum(p.get('median_time', 0) for name, p in aos_result.passes.items()
                     if get_pass_type(name, prog_class) == 'map')
        soa_map = sum(p.get('median_time', 0) for name, p in soa_result.passes.items()
                     if get_pass_type(name, prog_class) == 'map')
        
        fold_speedup = aos_fold / soa_fold if soa_fold > 0 else 1.0
        map_speedup = aos_map / soa_map if soa_map > 0 else 1.0
        
        fold_data.append(fold_speedup)
        map_data.append(map_speedup)
    
    y_pos = np.arange(len(programs))
    height = 0.35
    
    fig, ax = plt.subplots(figsize=(10, max(6, len(programs) * 0.4)))
    
    # Bars for fold and map
    bars1 = ax.barh(y_pos - height/2, fold_data, height, label='Fold passes',
                   color='#3498db', alpha=0.8, edgecolor='black', linewidth=0.5)
    bars2 = ax.barh(y_pos + height/2, map_data, height, label='Map passes',
                   color='#e67e22', alpha=0.8, edgecolor='black', linewidth=0.5)
    
    ax.set_yticks(y_pos)
    ax.set_yticklabels(programs, fontsize=8)
    ax.set_xlabel('Speedup (AoS time / SoA time)', fontsize=10)
    ax.set_title('End-to-End Speedup: Fold vs Map Passes\n(>1.0 means SoA is faster)', fontsize=11)
    ax.axvline(x=1.0, color='black', linestyle='--', linewidth=1, alpha=0.7)
    ax.legend(loc='best', fontsize=9)
    ax.grid(True, alpha=0.3, axis='x')
    
    plt.tight_layout()
    plt.savefig(output_file)
    plt.close()


def generate_per_program_heatmaps(results: List[Tuple[BenchmarkResult, BenchmarkResult]], 
                                   output_dir: Path):
    """Generate individual heatmap for each program showing its passes"""
    heatmap_dir = output_dir / "heatmaps"
    heatmap_dir.mkdir(parents=True, exist_ok=True)
    
    for aos_result, soa_result in results:
        program = aos_result.program.replace('.hs', '')
        
        # Get all passes for this specific program
        program_passes = sorted(set(list(aos_result.passes.keys()) + list(soa_result.passes.keys())))
        
        if not program_passes:
            continue
        
        # Build speedup array for this program only
        speedups = []
        pass_labels = []
        
        for pass_name in program_passes:
            aos_time = aos_result.passes.get(pass_name, {}).get('median_time', 0)
            soa_time = soa_result.passes.get(pass_name, {}).get('median_time', 0)
            
            if aos_time > 0 and soa_time > 0:
                speedup = aos_time / soa_time
                speedups.append(speedup)
                pass_labels.append(pass_name.replace('Pass', '').replace('_', ' '))
        
        if not speedups:
            continue
        
        # Create heatmap for this program
        speedup_array = np.array([speedups])  # Single row
        
        fig, ax = plt.subplots(figsize=(max(10, len(speedups) * 0.8), 3))
        
        im = ax.imshow(speedup_array, cmap='RdYlGn', aspect='auto',
                      vmin=0.5, vmax=1.5, interpolation='nearest')
        
        ax.set_xticks(np.arange(len(pass_labels)))
        ax.set_xticklabels(pass_labels, rotation=45, ha='right', fontsize=8)
        ax.set_yticks([0])
        ax.set_yticklabels([program])
        
        # Add colorbar
        cbar = plt.colorbar(im, ax=ax, orientation='horizontal', pad=0.15)
        cbar.set_label('Speedup (AoS/SoA)', fontsize=9)
        
        # Add text annotations
        for i, (label, speedup) in enumerate(zip(pass_labels, speedups)):
            ax.text(i, 0, f'{speedup:.2f}',
                   ha='center', va='center', color='black', fontsize=8, fontweight='bold')
        
        ax.set_title(f'{program}: Per-Pass Speedup\n(Green = SoA faster)', fontsize=10)
        
        plt.tight_layout()
        plt.savefig(heatmap_dir / f"{program}_heatmap.pdf")
        plt.savefig(heatmap_dir / f"{program}_heatmap.png")
        plt.close()


def generate_complete_pass_breakdown_improved(results: List[Tuple[BenchmarkResult, BenchmarkResult]], 
                                              output_file: Path):
    """Generate complete pass breakdown with horizontal legend and patterns"""
    programs = []
    
    # Collect ALL unique passes
    all_passes = set()
    for aos_result, soa_result in results:
        all_passes.update(aos_result.passes.keys())
    
    passes_to_show = sorted(list(all_passes))
    
    # Collect data for ALL passes
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
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(16, max(8, len(programs) * 0.5)))
    
    x = np.arange(len(programs))
    width = 0.6
    
    # Colors and patterns for different passes
    colors = plt.cm.tab20(np.linspace(0, 1, len(passes_to_show)))
    patterns = ['', '/', '\\', '|', '-', '+', 'x', 'o', 'O', '.', '*']
    
    # AoS stacked bars
    bottom = np.zeros(len(programs))
    handles = []
    labels = []
    for i, pass_name in enumerate(passes_to_show):
        pass_label = pass_name.replace('Pass', '').replace('_', ' ')
        pattern = patterns[i % len(patterns)]
        
        bars = ax1.barh(x, aos_data[pass_name], width,
                       left=bottom, color=colors[i], edgecolor='black', linewidth=0.3,
                       hatch=pattern, label=pass_label)
        bottom += np.array(aos_data[pass_name])
        
        if i < 15:  # Only add to legend if not too many
            handles.append(bars)
            labels.append(pass_label)
    
    ax1.set_yticks(x)
    ax1.set_yticklabels(programs, fontsize=8)
    ax1.set_xlabel('Execution Time (ms)', fontsize=10)
    ax1.set_title('AoS: Complete Pass Breakdown', fontsize=11)
    ax1.grid(True, alpha=0.3, axis='x')
    
    # SoA stacked bars
    bottom = np.zeros(len(programs))
    for i, pass_name in enumerate(passes_to_show):
        pattern = patterns[i % len(patterns)]
        ax2.barh(x, soa_data[pass_name], width,
                left=bottom, color=colors[i], edgecolor='black', linewidth=0.3,
                hatch=pattern)
        bottom += np.array(soa_data[pass_name])
    
    ax2.set_yticks(x)
    ax2.set_yticklabels(programs, fontsize=8)
    ax2.set_xlabel('Execution Time (ms)', fontsize=10)
    ax2.set_title('SoA: Complete Pass Breakdown', fontsize=11)
    ax2.grid(True, alpha=0.3, axis='x')
    
    # Add horizontal legend below the plots
    if handles:
        fig.legend(handles, labels, loc='lower center', ncol=min(5, len(labels)),
                  bbox_to_anchor=(0.5, -0.05), fontsize=7, frameon=True)
    
    plt.suptitle('Complete Compiler Pass Breakdown: All Passes for All Programs', 
                fontsize=12, y=0.98)
    plt.tight_layout(rect=[0, 0.05, 1, 0.96])
    plt.savefig(output_file, bbox_inches='tight')
    plt.close()


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


def generate_complete_pass_breakdown(results: List[Tuple[BenchmarkResult, BenchmarkResult]], 
                                    output_file: Path):
    """Generate complete pass breakdown showing ALL passes for ALL programs"""
    programs = []
    
    # Collect ALL unique passes
    all_passes = set()
    for aos_result, soa_result in results:
        all_passes.update(aos_result.passes.keys())
    
    passes_to_show = sorted(list(all_passes))
    
    # Collect data for ALL passes
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
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(16, max(8, len(programs) * 0.5)))
    
    x = np.arange(len(programs))
    width = 0.6
    
    # Colors for different passes
    colors = plt.cm.tab20(np.linspace(0, 1, len(passes_to_show)))
    
    # AoS stacked bars
    bottom = np.zeros(len(programs))
    for i, pass_name in enumerate(passes_to_show):
        pass_label = pass_name.replace('Pass', '').replace('_', ' ')
        ax1.barh(x, aos_data[pass_name], width, label=pass_label,
               left=bottom, color=colors[i], edgecolor='black', linewidth=0.3)
        bottom += np.array(aos_data[pass_name])
    
    ax1.set_yticks(x)
    ax1.set_yticklabels(programs)
    ax1.set_xlabel('Execution Time (ms)', fontsize=10)
    ax1.set_title('AoS: Complete Pass Breakdown', fontsize=11)
    ax1.legend(bbox_to_anchor=(1.02, 1), loc='upper left', fontsize=7, ncol=1)
    ax1.grid(True, alpha=0.3, axis='x')
    
    # SoA stacked bars
    bottom = np.zeros(len(programs))
    for i, pass_name in enumerate(passes_to_show):
        ax2.barh(x, soa_data[pass_name], width,
               left=bottom, color=colors[i], edgecolor='black', linewidth=0.3)
        bottom += np.array(soa_data[pass_name])
    
    ax2.set_yticks(x)
    ax2.set_yticklabels(programs)
    ax2.set_xlabel('Execution Time (ms)', fontsize=10)
    ax2.set_title('SoA: Complete Pass Breakdown', fontsize=11)
    ax2.grid(True, alpha=0.3, axis='x')
    
    plt.suptitle('Complete Compiler Pass Breakdown: All Passes for All Programs', fontsize=12, y=0.995)
    plt.tight_layout()
    plt.savefig(output_file, bbox_inches='tight')
    plt.close()


def generate_per_program_figures(results: List[Tuple[BenchmarkResult, BenchmarkResult]], 
                                 output_dir: Path):
    """Generate individual figure for each program showing all its passes"""
    per_program_dir = output_dir / "per_program"
    per_program_dir.mkdir(parents=True, exist_ok=True)
    
    for aos_result, soa_result in results:
        program = aos_result.program.replace('.hs', '')
        
        # Get all passes for this program
        all_passes = sorted(set(list(aos_result.passes.keys()) + list(soa_result.passes.keys())))
        
        aos_times = []
        soa_times = []
        pass_labels = []
        
        for pass_name in all_passes:
            aos_time = aos_result.passes.get(pass_name, {}).get('median_time', 0) * 1000
            soa_time = soa_result.passes.get(pass_name, {}).get('median_time', 0) * 1000
            
            aos_times.append(aos_time)
            soa_times.append(soa_time)
            pass_labels.append(pass_name.replace('Pass', '').replace('_', ' '))
        
        # Create grouped bar chart
        x = np.arange(len(pass_labels))
        width = 0.35
        
        fig, ax = plt.subplots(figsize=(max(10, len(pass_labels) * 0.6), 6))
        
        bars1 = ax.bar(x - width/2, aos_times, width, label='AoS',
                      color='#3498db', alpha=0.8, edgecolor='black', linewidth=0.5)
        bars2 = ax.bar(x + width/2, soa_times, width, label='SoA',
                      color='#e67e22', alpha=0.8, edgecolor='black', linewidth=0.5)
        
        ax.set_xlabel('Compiler Pass', fontsize=10)
        ax.set_ylabel('Execution Time (ms)', fontsize=10)
        ax.set_title(f'{program}: All Passes Performance', fontsize=11)
        ax.set_xticks(x)
        ax.set_xticklabels(pass_labels, rotation=45, ha='right', fontsize=8)
        ax.legend(fontsize=9)
        ax.grid(True, alpha=0.3, axis='y')
        
        plt.tight_layout()
        plt.savefig(per_program_dir / f"{program}_all_passes.pdf")
        plt.savefig(per_program_dir / f"{program}_all_passes.png")
        plt.close()


def generate_per_pass_speedup_figures(results: List[Tuple[BenchmarkResult, BenchmarkResult]], 
                                      output_dir: Path):
    """Generate speedup figures showing all programs for each pass"""
    per_pass_dir = output_dir / "per_pass"
    per_pass_dir.mkdir(parents=True, exist_ok=True)
    
    # Collect all unique passes
    all_passes = set()
    for aos_result, soa_result in results:
        all_passes.update(aos_result.passes.keys())
    
    for pass_name in sorted(all_passes):
        programs = []
        speedups = []
        colors = []
        
        for aos_result, soa_result in results:
            aos_time = aos_result.passes.get(pass_name, {}).get('median_time', 0)
            soa_time = soa_result.passes.get(pass_name, {}).get('median_time', 0)
            
            if aos_time > 0 and soa_time > 0:
                program = aos_result.program.replace('.hs', '')
                speedup = aos_time / soa_time
                
                programs.append(program)
                speedups.append(speedup)
                colors.append('#2ecc71' if speedup > 1.0 else '#e74c3c')
        
        if not programs:
            continue
        
        # Create horizontal bar chart
        y_pos = np.arange(len(programs))
        
        fig, ax = plt.subplots(figsize=(10, max(6, len(programs) * 0.4)))
        
        bars = ax.barh(y_pos, speedups, color=colors, alpha=0.7, 
                      edgecolor='black', linewidth=0.5)
        
        ax.set_yticks(y_pos)
        ax.set_yticklabels(programs, fontsize=8)
        ax.set_xlabel('Speedup (AoS time / SoA time)', fontsize=10)
        pass_label = pass_name.replace('Pass', '').replace('_', ' ')
        ax.set_title(f'{pass_label}: Speedup Across All Programs\n(>1.0 means SoA is faster)', 
                    fontsize=11)
        ax.axvline(x=1.0, color='black', linestyle='--', linewidth=1, label='No speedup')
        
        # Add value labels
        for i, (bar, speedup) in enumerate(zip(bars, speedups)):
            width = bar.get_width()
            label_x = width + 0.02 if width < 1.0 else width - 0.02
            ha = 'left' if width < 1.0 else 'right'
            ax.text(label_x, bar.get_y() + bar.get_height()/2,
                   f'{speedup:.2f}×', ha=ha, va='center', fontsize=7, fontweight='bold')
        
        if speedups:
            geomean = statistics.geometric_mean(speedups)
            ax.axvline(x=geomean, color='blue', linestyle=':', linewidth=2,
                      label=f'Geomean: {geomean:.2f}×')
        
        ax.legend(loc='best', fontsize=8)
        ax.grid(True, alpha=0.3, axis='x')
        
        plt.tight_layout()
        safe_pass_name = pass_name.replace('/', '_').replace(' ', '_')
        plt.savefig(per_pass_dir / f"{safe_pass_name}_speedup.pdf")
        plt.savefig(per_pass_dir / f"{safe_pass_name}_speedup.png")
        plt.close()


def generate_program_pass_speedup_grid(results: List[Tuple[BenchmarkResult, BenchmarkResult]], 
                                       output_file: Path):
    """Generate comprehensive grid showing speedup for every program-pass combination"""
    programs = []
    
    # Collect ALL passes
    all_passes = set()
    for aos_result, soa_result in results:
        all_passes.update(aos_result.passes.keys())
    
    passes_to_show = sorted(list(all_passes))
    
    # Build data
    program_data = []
    
    for aos_result, soa_result in results:
        program = aos_result.program.replace('.hs', '')
        programs.append(program)
        
        for pass_name in passes_to_show:
            aos_time = aos_result.passes.get(pass_name, {}).get('median_time', 0)
            soa_time = soa_result.passes.get(pass_name, {}).get('median_time', 0)
            
            if aos_time > 0 and soa_time > 0:
                speedup = aos_time / soa_time
                program_data.append({
                    'program': program,
                    'pass': pass_name.replace('Pass', '').replace('_', ' '),
                    'speedup': speedup
                })
    
    # Create grouped bar chart
    unique_passes = sorted(set(d['pass'] for d in program_data))
    
    fig, ax = plt.subplots(figsize=(max(14, len(programs) * 1.2), 8))
    
    x = np.arange(len(programs))
    width = 0.8 / len(unique_passes) if unique_passes else 0.8
    
    colors = plt.cm.tab20(np.linspace(0, 1, len(unique_passes)))
    
    for i, pass_name in enumerate(unique_passes):
        speedups = []
        for program in programs:
            matching = [d['speedup'] for d in program_data 
                       if d['program'] == program and d['pass'] == pass_name]
            speedups.append(matching[0] if matching else 1.0)
        
        ax.bar(x + i * width - width * len(unique_passes) / 2, speedups, width,
              label=pass_name, color=colors[i], alpha=0.8, edgecolor='black', linewidth=0.3)
    
    ax.set_xlabel('Program', fontsize=10)
    ax.set_ylabel('Speedup (AoS / SoA)', fontsize=10)
    ax.set_title('Comprehensive Speedup Grid: All Programs × All Passes', fontsize=12)
    ax.set_xticks(x)
    ax.set_xticklabels(programs, rotation=45, ha='right', fontsize=8)
    ax.axhline(y=1.0, color='black', linestyle='--', linewidth=1, alpha=0.5)
    ax.legend(bbox_to_anchor=(1.02, 1), loc='upper left', fontsize=7, ncol=2)
    ax.grid(True, alpha=0.3, axis='y')
    
    plt.tight_layout()
    plt.savefig(output_file, bbox_inches='tight')
    plt.close()


def generate_latex_table_pdf(latex_file: Path, output_dir: Path):
    """Compile the LaTeX table to PDF to show rendered output"""
    try:
        # Create a complete LaTeX document
        pdf_source = f"""\\documentclass{{article}}
\\usepackage{{booktabs}}
\\usepackage{{graphicx}}
\\usepackage[margin=0.5in]{{geometry}}
\\begin{{document}}
\\pagestyle{{empty}}
\\input{{{latex_file.name}}}
\\end{{document}}
"""
        
        # Write temporary tex file
        temp_tex = output_dir / "table_preview.tex"
        with open(temp_tex, 'w') as f:
            f.write(pdf_source)
        
        # Copy the table file to output dir if needed
        if latex_file.parent != output_dir:
            import shutil
            shutil.copy(latex_file, output_dir / latex_file.name)
        
        # Try to compile with pdflatex
        result = subprocess.run(
            ['pdflatex', '-interaction=nonstopmode', '-output-directory', str(output_dir), str(temp_tex)],
            capture_output=True,
            text=True,
            timeout=30
        )
        
        pdf_output = output_dir / "table_preview.pdf"
        if pdf_output.exists():
            print(f"✓ Generated table PDF preview: {pdf_output}")
            return True
        else:
            print(f"  Note: Could not generate table PDF (pdflatex might not be installed)")
            return False
            
    except FileNotFoundError:
        print(f"  Note: pdflatex not found - skipping PDF table generation")
        print(f"        Install TeX Live to enable this feature")
        return False
    except Exception as e:
        print(f"  Note: Could not generate table PDF: {e}")
        return False


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


def generate_comprehensive_speedup_heatmap(results: List[Tuple[BenchmarkResult, BenchmarkResult]], 
                                          output_file: Path):
    """Generate comprehensive heatmap of ALL programs x ALL passes"""
    programs = []
    
    # Collect ALL unique passes across all programs
    all_passes = set()
    for aos_result, soa_result in results:
        all_passes.update(aos_result.passes.keys())
        all_passes.update(soa_result.passes.keys())
    
    # Sort passes for consistent ordering
    passes_to_show = sorted(list(all_passes))
    
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
            elif aos_time > 0 and soa_time == 0:
                speedup = 2.0  # Show as significant speedup
            elif aos_time == 0 and soa_time > 0:
                speedup = 0.5  # Show as slowdown
            else:
                speedup = 1.0  # No data
            
            row.append(speedup)
        
        speedup_matrix.append(row)
    
    speedup_matrix = np.array(speedup_matrix)
    
    # Calculate figure size based on number of passes
    fig_width = max(12, len(passes_to_show) * 0.6)
    fig_height = max(8, len(programs) * 0.4)
    
    fig, ax = plt.subplots(figsize=(fig_width, fig_height))
    
    # Use diverging colormap centered at 1.0
    im = ax.imshow(speedup_matrix, cmap='RdYlGn', aspect='auto', 
                   vmin=0.5, vmax=1.5, interpolation='nearest')
    
    # Set ticks and labels
    ax.set_xticks(np.arange(len(passes_to_show)))
    ax.set_yticks(np.arange(len(programs)))
    
    # Clean up pass names for display
    pass_labels = [p.replace('Pass', '').replace('_', ' ') for p in passes_to_show]
    ax.set_xticklabels(pass_labels, rotation=45, ha='right')
    ax.set_yticklabels(programs)
    
    # Add colorbar
    cbar = plt.colorbar(im, ax=ax)
    cbar.set_label('Speedup (AoS time / SoA time)', rotation=270, labelpad=20)
    
    # Add text annotations (only if not too many cells)
    if len(programs) * len(passes_to_show) < 300:  # Don't annotate if too dense
        for i in range(len(programs)):
            for j in range(len(passes_to_show)):
                text = ax.text(j, i, f'{speedup_matrix[i, j]:.2f}',
                              ha='center', va='center', color='black', fontsize=6)
    
    ax.set_title(f'Comprehensive Speedup Heatmap: All Programs × All Passes\n(Green = SoA faster, Red = AoS faster)', 
                 fontsize=11)
    ax.set_xlabel('Compiler Pass', fontsize=10)
    ax.set_ylabel('Program', fontsize=10)
    
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
        
        generate_latex_table(all_results, args.latex_table, args.programs_dir)
        print(f"✓ LaTeX tables saved to: {args.latex_table}")
        
        # Try to generate PDF preview of the table
        generate_latex_table_pdf(args.latex_table, args.figures_dir)
        
        generate_figures(all_results, args.figures_dir, args.programs_dir)
        
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
