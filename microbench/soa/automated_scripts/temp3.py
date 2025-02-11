import subprocess
import re
import os 
import sys
import statistics

import numpy as np
import scipy.stats as stats

# Function to run your script and compile the C file
def run_and_compile(k, l, list_size, function, outFile):
    # Run your existing script with the given parameters
    command = "python3 " +  script_name + " --k " + str(k) +  " --l "+ str(l) +  " --list_size " + str(list_size) +  " --function " + function + " --outFile " + outFile
    print(command)

    #subprocess.run(['python3', script_name, "--k "+ str(k), "--l "+ str(l), "--list_size " + str(list_size), "--function " + function, "--outFile " + outFile])
    
    subprocess.run(command, shell=True, capture_output=True, text=True)


    # Compile the generated C file (assuming the generated file is named 'generated_file.c')
    compile_result = subprocess.run(['clang', "-O3", outFile, '-o', outFile + ".exe"], capture_output=True, text=True)
    
    if compile_result.returncode != 0:
        print(f"Compilation failed: {compile_result.stderr}")
        return None
    
    return True

# Function to benchmark the compiled program
def benchmark_program(binary):
    runtimes = []
    for _ in range(21):
        # Run the compiled program and capture the output
        run_result = subprocess.run(["./" + binary], capture_output=True, text=True)
        
        if run_result.returncode != 0:
            print(f"Execution failed: {run_result.stderr}")
            return None
        
        # Extract the runtime from the output
        match = re.search(r'The time taken by add1 was (\d+\.\d+) seconds', run_result.stdout)
        if match:
            runtimes.append(float(match.group(1)))
    
    if runtimes:
        print(runtimes)
        mean = np.mean(runtimes)
        sem = stats.sem(runtimes)
        median_runtime = statistics.median(runtimes)
        confidence = 0.95
        h = sem * stats.t.ppf((1 + confidence) / 2, len(runtimes) - 1)
        lower_bound = mean - h
        upper_bound = mean + h

        return (f"{mean:.3e}", f"{median_runtime:.3e}", (f"{lower_bound:.3e}", f"{upper_bound:.3e}"))
    return None

# Function to generate the table
def generate_table(mode):
    results = []
    functions = []
    if mode == "soa":
        functions = ['add1Recursive', 'add1Iterative', 'add1IterativeOpt']
    elif mode == "aos":
        functions =  ['add1Recursive', 'add1Iterative']

    for k in range(1, 10):
        for l in range(1, k+1):
            for list_size in range(10000000, 100000000, 10000000):
                for function in functions:
                    out_file = mode + "." + str(k) + "." + str(l) + "." + str(list_size) + "." + function + ".c"
                    if run_and_compile(k, l, list_size, function, out_file):
                        average_runtime = benchmark_program(out_file + ".exe")
                        if average_runtime is not None:
                            results.append((k, l, list_size, function, average_runtime))
    
    # Print the results in a table format
    with open (mode + "_results.txt", 'w') as file:
        file.write("k\tl\tlist_size\tfunction\t(average, median,(lower_bound, upper_bound))\n")
        #f'{number:.2e}
        for result in results:
            file.write(f"{result[0]}\t{result[1]}\t{result[2]}\t{result[3]}\t{result[4]}\n")


if __name__ == "__main__":

    mode = str(sys.argv[1])

    global script_name
    # Run the table generation

    if mode == "soa":
        script_name = "gen_packed_soa.py"
    elif mode == "aos":
        script_name = "gen_packed_aos.py" 


    generate_table(mode)
