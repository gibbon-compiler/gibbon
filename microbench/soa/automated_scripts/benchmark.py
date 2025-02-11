import subprocess
import re
import os
import sys
import statistics

import numpy as np
import scipy.stats as stats

# Function to run your script and compile the C file
def run_and_compile(k, l, list_size, function, outFile, script_name):
    # Run your existing script with the given parameters
    command = ["python3", script_name, "--k", str(k), "--l", str(l), "--listSize", str(list_size), "--function", function, "--outFile", outFile]
    print(" ".join(command))
    
    subprocess.run(command, capture_output=True, text=True)

    # Compile the generated C file (assuming the generated file is named 'generated_file.c')
    compile_result = subprocess.run(['clang', "-O3", "-I/local/scratch/a/singhav/env/include/", "-L/local/scratch/a/singhav/env/lib/", outFile, '-o', outFile + ".exe", "-lpapi"], capture_output=True, text=True)
    
    if compile_result.returncode != 0:
        print(f"Compilation failed: {compile_result.stderr}")
        return None
    
    return True

# Function to benchmark the compiled program
def benchmark_program(binary):
    runtimes = []
    total_instructions = []
    l2_cache_misses = []
    
    for _ in range(21):
        # Run the compiled program and capture the output
        run_result = subprocess.run(["./" + binary], capture_output=True, text=True)
        
        if run_result.returncode != 0:
            print(f"Execution failed: {run_result.stderr}")
            return None
        
        # Extract the runtime, total instructions, and L2 data cache misses from the output
        time_match = re.search(r'The time taken by add1 was (\d+\.\d+) seconds', run_result.stdout)
        instructions_match = re.search(r'Total Instructions: (\d+)', run_result.stdout)
        cache_misses_match = re.search(r'L2 total cache misses: (\d+)', run_result.stdout)
        
        if time_match and instructions_match and cache_misses_match:
            runtimes.append(float(time_match.group(1)))
            total_instructions.append(int(instructions_match.group(1)))
            l2_cache_misses.append(int(cache_misses_match.group(1)))
    
    if runtimes and total_instructions and l2_cache_misses:
        #print(runtimes)
        mean_time = np.mean(runtimes)
        sem_time = stats.sem(runtimes)
        median_runtime = statistics.median(runtimes)
        confidence = 0.95
        h_time = sem_time * stats.t.ppf((1 + confidence) / 2, len(runtimes) - 1)
        lower_bound_time = mean_time - h_time
        upper_bound_time = mean_time + h_time

        mean_instructions = np.mean(total_instructions)
        mean_cache_misses = np.mean(l2_cache_misses)

        return (f"{mean_time:.3e}", f"{median_runtime:.3e}", (f"{lower_bound_time:.3e}", f"{upper_bound_time:.3e}"), mean_instructions, mean_cache_misses)
    return None

# Function to generate the table
def generate_table(mode):
    results = []
    functions = []
    if mode == "soa":
        functions = ['add1RecursiveInPlace', 'add1RecursiveOutOfPlace', 'add1IterativeInPlace', 'add1IterativeOutOfPlace', 'add1IterativeOptInPlace', 'add1IterativeOptOutOfPlace']
    elif mode == "aos":
        functions = ['add1RecursiveInPlace', 'add1IterativeInPlace', 'add1RecursiveOutOfPlace', 'add1IterativeOutOfPlace']

    for k in range(1, 10):
        for l in range(1, k+1):
            for list_size in range(10000000, 100000000, 10000000):
                for function in functions:
                    out_file = mode + "." + str(k) + "." + str(l) + "." + str(list_size) + "." + function + ".c"
                    if run_and_compile(k, l, list_size, function, out_file, script_name):
                        average_runtime = benchmark_program(out_file + ".exe")
                        if average_runtime is not None:
                            results.append((k, l, list_size, function, average_runtime))
    
    # Print the results in a table format
    with open (mode + "_results.txt", 'w') as file:
        file.write("k\tl\tlist_size\tfunction\t(average, median, (lower_bound, upper_bound))\tTotal Instructions\tL2 Data Cache Misses\n")
        for result in results:
            file.write(f"{result[0]}\t{result[1]}\t{result[2]}\t{result[3]}\t{result[4][0]}, {result[4][1]}, ({result[4][2][0]}, {result[4][2][1]})\t{result[4][3]}\t{result[4][4]}\n")


if __name__ == "__main__":

    mode = str(sys.argv[1])

    global script_name
    # Run the table generation

    if mode == "soa":
        script_name = "gen_packed_soa.py"
    elif mode == "aos":
        script_name = "gen_packed_aos.py" 

    generate_table(mode)
