import subprocess
import re
import os
from tabulate import tabulate
import pandas as pd
import numpy as np

# Function to run the executable and capture the output
def run_executable(executable_path):
    result = subprocess.run([executable_path], capture_output=True, text=True)
    return result.stdout

# Function to parse the runtime from the output
def parse_runtime(output):
    match = re.search(r"([Tt]ime taken.*?)([\d.]+)(\s*seconds?)", output)
    if match:
        return float(match.group(2))
    return None

# Function to parse total instructions from the output
def parse_total_instructions(output):
    match = re.search(r"Total Instructions:\s*(\d+)", output)
    if match:
        return int(match.group(1))
    return None

# Function to parse L2 data cache misses from the output
def parse_l2_cache_misses(output):
    match = re.search(r"L2 data cache misses:\s*(\d+)", output)
    if match:
        return int(match.group(1))
    return None

# Function to extract details from the filename
def extract_info(filename):
    match = re.match(
        r"(soa|aos)_(iterative|recursive)_(in_place|out_of_place)"  
        r"(?:_optimized_O(\d+)(?:_([\w_]+))*)?"  
        r"(?:_manually_vectorized)?\.(gcc|clang)\.exe",  
        filename
    )
    if match:
        groups = match.groups()
        
        layout = groups[0]
        method = groups[1]
        placement = groups[2]

        optimization_level = "O3"  
        flags = groups[4] if groups[4] else "N/A"
        
        manual_vec = "manually_vectorized" if '_manually_vectorized' in filename else ""
        
        compiler = groups[5] if groups[5] else "N/A"
        
        optimization = f"skips tag buffer" if "optimized" in filename else "traverses all buffers"   
        compiler_flags = ""

        if flags == "disable_autovec":
            compiler_flags = "clang: -O3 -fno-tree-vectorize -fno-tree-loop-vectorize -fno-tree-slp-vectorize \ngcc:   -O3 -fno-vectorize -fno-slp-vectorize"
        elif flags == "enable_arch_rpass_autovec":
            compiler_flags = "clang: -O3 -march=native -Rpass=loop-vectorize \ngcc:   -O3 -march=native -ftree-vectorize"
        elif flags == "manually_vectorized":
            compiler_flags = "-O3 -march=native -mavx2"
        else: 
            compiler_flags = "Just -O3"

        description = f"{optimization}".strip()
        
        return method, placement, description, layout, compiler, optimization_level, compiler_flags
    return None, None, None, None, None, None, None

# Function to format numbers in scientific notation
def format_scientific(number):
    return round(number * 1000, 3) if number is not None else "N/A"

def format_scientific_2(number):
    return np.format_float_scientific(number, precision=2) if number is not None else "N/A"


def main():
    exe_files = [f for f in os.listdir() if f.endswith('.exe')]
    results = {}

    for exe_file in exe_files:
        method, placement, description, layout, compiler, optimization_level, compiler_flags = extract_info(exe_file)
        if not method:
            print(f"Skipping unrecognized file: {exe_file}")
            continue
        
        opt = ""
        if description == "skips tag buffer":
            opt = "optimized"
        elif description == "traverses all buffers":
            opt = "standard"

        category = f"{method} - {placement} - {opt}"
        key = (category, description, compiler_flags)

        runtimes = []
        total_instructions_list = []
        l2_cache_misses_list = []
        
        for _ in range(51):
            output = run_executable(exe_file)
            runtime = parse_runtime(output)
            total_instructions = parse_total_instructions(output)
            l2_cache_misses = parse_l2_cache_misses(output)
            
            if runtime is not None:
                runtimes.append(runtime)
            if total_instructions is not None:
                total_instructions_list.append(total_instructions)
            if l2_cache_misses is not None:
                l2_cache_misses_list.append(l2_cache_misses)

        if runtimes:
            avg_runtime = sum(runtimes) / len(runtimes)
            avg_total_instructions = sum(total_instructions_list) / len(total_instructions_list) if total_instructions_list else None
            avg_l2_cache_misses = sum(l2_cache_misses_list) / len(l2_cache_misses_list) if l2_cache_misses_list else None

            if key not in results:
                results[key] = {
                    "aos_gcc": {"runtime": "N/A", "total_instructions": "N/A", "l2_cache_misses": "N/A"},
                    "aos_clang": {"runtime": "N/A", "total_instructions": "N/A", "l2_cache_misses": "N/A"},
                    "soa_gcc": {"runtime": "N/A", "total_instructions": "N/A", "l2_cache_misses": "N/A"},
                    "soa_clang": {"runtime": "N/A", "total_instructions": "N/A", "l2_cache_misses": "N/A"},
                    "optimization_level": optimization_level,
                    "compiler_flags": compiler_flags
                }

            results[key][f"{layout}_{compiler}"]["runtime"] = format_scientific(avg_runtime)
            results[key][f"{layout}_{compiler}"]["total_instructions"] = format_scientific_2(avg_total_instructions)
            results[key][f"{layout}_{compiler}"]["l2_cache_misses"] = format_scientific_2(avg_l2_cache_misses)
            
        else:
            print(f"Failed to parse runtime for {exe_file}")

    results = dict(sorted(results.items()))
    table = []
    for (category, description, compiler_flags), times in sorted(results.items()):
        table.append([
            category, 
            description, 
            times.get("compiler_flags", "N/A"),       
            times["aos_gcc"]["runtime"], 
            times["aos_gcc"]["total_instructions"], 
            times["aos_gcc"]["l2_cache_misses"], 
            times["aos_clang"]["runtime"], 
            times["aos_clang"]["total_instructions"], 
            times["aos_clang"]["l2_cache_misses"], 
            times["soa_gcc"]["runtime"], 
            times["soa_gcc"]["total_instructions"], 
            times["soa_gcc"]["l2_cache_misses"], 
            times["soa_clang"]["runtime"], 
            times["soa_clang"]["total_instructions"], 
            times["soa_clang"]["l2_cache_misses"]
        ])

    print(tabulate(table, headers=["Category", "Description", "Compiler Optimization Used", 
                                   "AOS GCC (ms)", "Ins.", "L2 Miss", 
                                   "AOS Clang (ms)", "Ins.", "L2 Miss", 
                                   "SOA GCC (ms)", "Ins.", "L2 Miss", 
                                   "SOA Clang (ms)", "Ins.", "L2 Miss"], tablefmt="grid"))

    # Write the table to an Excel file
    df = pd.DataFrame(table, columns=["Category", "Description", "Compiler Optimization Used", 
                                      "AOS GCC (ms)", "Ins.", "L2 Miss", 
                                      "AOS Clang (ms)", "Ins.", "L2 Miss", 
                                      "SOA GCC (ms)", "Ins.", "L2 Miss", 
                                      "SOA Clang (ms)", "Ins.", "L2 Miss"])
    df.to_excel("results.xlsx", index=False)

if __name__ == "__main__":
    main()
