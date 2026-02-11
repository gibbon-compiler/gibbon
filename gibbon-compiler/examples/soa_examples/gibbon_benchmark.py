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


def compile_program(source_file: Path, variant: str, output_dir: Path) -> Tuple[bool, float, str]:
    """
    Compile a Gibbon program
    
    Args:
        source_file: Path to the .hs source file
        variant: "aos" or "soa"
        output_dir: Directory to place compiled files
        
    Returns:
        Tuple of (success, compile_time, error_message)
    """
    basename = source_file.stem
    c_file = output_dir / f"{basename}.{variant}.c"
    exe_file = output_dir / f"{basename}.{variant}.exe"
    
    # Ensure output directory exists
    output_dir.mkdir(parents=True, exist_ok=True)
    
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
            text=True,
            timeout=300  # 5 minute timeout
        )
        compile_time = time.time() - start_time
        
        if result.returncode == 0:
            print(f"✓ ({compile_time:.2f}s)")
            return True, compile_time, None
        else:
            error_msg = result.stderr or result.stdout
            print(f"✗ (failed)")
            return False, compile_time, error_msg
            
    except subprocess.TimeoutExpired:
        compile_time = time.time() - start_time
        print(f"✗ (timeout)")
        return False, compile_time, "Compilation timeout"
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
                      iterations: int = 20) -> Tuple[BenchmarkResult, BenchmarkResult]:
    """
    Benchmark both AoS and SoA versions of a program
    
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
        
        success, compile_time, error = compile_program(source_file, variant, output_dir)
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
            args.iterations
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
