import subprocess
import statistics
import matplotlib.pyplot as plt
import os
import numpy as np 

# Define the parameters
k = 1
l = 1
list_size = 300000000
functions_soa = ["add1RecursiveInPlace", "add1RecursiveOutOfPlace", "add1IterativeInPlace", "add1IterativeOutOfPlace", 
        "add1IterativeOptInPlace", "add1IterativeOptOutOfPlace"]
out_file_template_soa = "generated_code_soa_{}.c"
exec_file_template_gcc_soa = "executable_gcc_soa_{}"
exec_file_template_clang_soa = "executable_clang_soa_{}"

# Function to run the python script and compile the generated .c file with GCC for SOA
def generate_and_compile_gcc_soa(function):
    out_file = out_file_template_soa.format(function)
    exec_file = exec_file_template_gcc_soa.format(function)
    
    # Run the python script to generate the .c file
    subprocess.run(["python3", "gen_packed_soa.py", "--k", str(k), "--l", str(l), "--outFile", out_file, "--function", function, "--listSize", str(list_size)])
    
    # Compile the .c file to an executable with optimization level O3 using GCC
    subprocess.run(["gcc", "-O3", out_file, "-o", exec_file, "-lpapi"])

# Function to run the python script and compile the generated .c file with Clang for SOA
def generate_and_compile_clang_soa(function):
    out_file = out_file_template_soa.format(function)
    exec_file = exec_file_template_clang_soa.format(function)
    
    # Run the python script to generate the .c file
    subprocess.run(["python3", "gen_packed_soa.py", "--k", str(k), "--l", str(l), "--outFile", out_file, "--function", function, "--listSize", str(list_size)])
    
    # Compile the .c file to an executable with optimization level O3 using Clang
    subprocess.run(["clang", "-O3", out_file, "-o", exec_file, "-lpapi"])


def format_scientific(number):
    return np.format_float_scientific(number, precision=2) if number is not None else "N/A"

# Function to run the executable 31 times and collect the data for SOA
def run_executable(exec_file_template, function):
    exec_file = exec_file_template.format(function)
    if not os.path.isfile(exec_file):
        raise FileNotFoundError(f"Executable file {exec_file} not found.")
    
    times = []
    instructions = []
    l2_misses = []
    l3_misses = []
    prefetch_data_misses = []
    l1_instruction_cache_misses = []
    load_instructions = []
    store_instructions = []
    l3_load_misses = []
    l3_store_misses = []
    l2_load_misses = []
    l2_store_misses = []
    
    for _ in range(31):
        result = subprocess.run(["./" + exec_file], capture_output=True, text=True)
        output = result.stdout
        
        # Parse the output to extract the data
        time_taken = float(output.split("The time taken by")[1].split("was")[1].split("seconds")[0].strip())
        total_instructions = int(output.split("Total Instructions:")[1].split("\n")[0].strip())
        l2_total_cache_misses = int(output.split("L2 total cache misses:")[1].split("\n")[0].strip())
        l3_total_cache_misses = int(output.split("L3 total cache misses:")[1].split("\n")[0].strip())
        data_prefetch_cache_misses = int(output.split("Data prefetch cache misses:")[1].split("\n")[0].strip())
        l1_instruction_cache_misses_value = int(output.split("L1 instruction cache misses:")[1].split("\n")[0].strip())
        load_instructions_value = int(output.split("Load instructions:")[1].split("\n")[0].strip())
        store_instructions_value = int(output.split("Store instructions:")[1].split("\n")[0].strip())
        l3_load_misses_value = int(output.split("L3 load misses:")[1].split("\n")[0].strip())
        l3_store_misses_value = int(output.split("L3 store misses:")[1].split("\n")[0].strip())
        l2_load_misses_value = int(output.split("L2 load misses:")[1].split("\n")[0].strip())
        l2_store_misses_value = int(output.split("L2 store misses:")[1].split("\n")[0].strip())
        
        times.append(time_taken)
        instructions.append(total_instructions)
        l2_misses.append(l2_total_cache_misses)
        l3_misses.append(l3_total_cache_misses)
        prefetch_data_misses.append(data_prefetch_cache_misses)
        l1_instruction_cache_misses.append(l1_instruction_cache_misses_value)
        load_instructions.append(load_instructions_value)
        store_instructions.append(store_instructions_value)
        l3_load_misses.append(l3_load_misses_value)
        l3_store_misses.append(l3_store_misses_value)
        l2_load_misses.append(l2_load_misses_value)
        l2_store_misses.append(l2_store_misses_value)
    
    return times, instructions, l2_misses, l3_misses, prefetch_data_misses, l1_instruction_cache_misses, load_instructions, store_instructions, l3_load_misses, l3_store_misses, l2_load_misses, l2_store_misses

# Generate and compile the .c files for each function using GCC and Clang for SOA
for function in functions_soa:
    generate_and_compile_gcc_soa(function)
    generate_and_compile_clang_soa(function)

# Run the executables and collect the data for GCC and Clang for SOA
data_gcc_soa = {}
data_clang_soa = {}
for function in functions_soa:
    times, instructions, l2_misses, l3_misses, prefetch_data_misses, l1_instruction_cache_misses, load_instructions, store_instructions, l3_load_misses, l3_store_misses, l2_load_misses, l2_store_misses = run_executable(exec_file_template_gcc_soa, function)
    data_gcc_soa[function] = {
        "times": times,
        "instructions": instructions,
        "l2_misses": l2_misses,
        "l3_misses": l3_misses,
        "prefetch_data_misses": prefetch_data_misses,
        "l1_instruction_cache_misses": l1_instruction_cache_misses,
        "load_instructions": load_instructions,
        "store_instructions": store_instructions,
        "l3_load_misses": l3_load_misses,
        "l3_store_misses": l3_store_misses,
        "l2_load_misses": l2_load_misses,
        "l2_store_misses": l2_store_misses,
        "median_time": format_scientific(statistics.mean(times)),
        "median_instructions": format_scientific(statistics.mean(instructions)),
        "median_l2_misses": format_scientific(statistics.mean(l2_misses)),
        "median_l3_misses": format_scientific(statistics.mean(l3_misses)),
        "median_prefetch_data_misses": format_scientific(statistics.mean(prefetch_data_misses)),
        "median_l1_instruction_cache_misses": format_scientific(statistics.mean(l1_instruction_cache_misses)),
        "median_load_instructions": format_scientific(statistics.mean(load_instructions)),
        "median_store_instructions": format_scientific(statistics.mean(store_instructions)),
        "median_l3_load_misses": format_scientific(statistics.mean(l3_load_misses)),
        "median_l3_store_misses": format_scientific(statistics.mean(l3_store_misses)),
        "median_l2_load_misses": format_scientific(statistics.mean(l2_load_misses)),
        "median_l2_store_misses": format_scientific(statistics.mean(l2_store_misses))
    }
    
    times, instructions, l2_misses, l3_misses, prefetch_data_misses, l1_instruction_cache_misses, load_instructions, store_instructions, l3_load_misses, l3_store_misses, l2_load_misses, l2_store_misses = run_executable(exec_file_template_clang_soa, function)
    data_clang_soa[function] = {
        "times": times,
        "instructions": instructions,
        "l2_misses": l2_misses,
        "l3_misses": l3_misses,
        "prefetch_data_misses": prefetch_data_misses,
        "l1_instruction_cache_misses": l1_instruction_cache_misses,
        "load_instructions": load_instructions,
        "store_instructions": store_instructions,
        "l3_load_misses": l3_load_misses,
        "l3_store_misses": l3_store_misses,
        "l2_load_misses": l2_load_misses,
        "l2_store_misses": l2_store_misses,
        "median_time": format_scientific(statistics.mean(times)),
        "median_instructions": format_scientific(statistics.mean(instructions)),
        "median_l2_misses": format_scientific(statistics.mean(l2_misses)),
        "median_l3_misses": format_scientific(statistics.mean(l3_misses)),
        "median_prefetch_data_misses": format_scientific(statistics.mean(prefetch_data_misses)),
        "median_l1_instruction_cache_misses": format_scientific(statistics.mean(l1_instruction_cache_misses)),
        "median_load_instructions": format_scientific(statistics.mean(load_instructions)),
        "median_store_instructions": format_scientific(statistics.mean(store_instructions)),
        "median_l3_load_misses": format_scientific(statistics.mean(l3_load_misses)),
        "median_l3_store_misses": format_scientific(statistics.mean(l3_store_misses)),
        "median_l2_load_misses": format_scientific(statistics.mean(l2_load_misses)),
        "median_l2_store_misses": format_scientific(statistics.mean(l2_store_misses))
    }

# Special compilation options for 'add1IterativeOpt'
special_options_gcc = [
    ["-O3", "-fno-tree-vectorize", "-fno-tree-loop-vectorize", "-fno-tree-slp-vectorize"],
    ["-O3", "-march=native", "-ftree-vectorize"]
]

special_options_keys = ["vecoff", "256bitvec"]

special_options_clang = [
    ["-O3", "-fno-vectorize", "-fno-slp-vectorize"],
    ["-O3", "-march=native", "-Rpass=loop-vectorize"]
]

# Function to compile 'add1IterativeOpt' with special options using GCC
def compile_special_gcc():
    out_file = out_file_template_soa.format("add1IterativeOptInPlace")

    for i, options in enumerate(special_options_gcc):
        exec_file = f"executable_gcc_special_in_place{i}"

        # Compile with special options using GCC
        subprocess.run(["gcc"] + options + [out_file, "-o", exec_file, "-lpapi"])

# Function to compile 'add1IterativeOpt' with special options using GCC
def compile_special_gcc_out_of_place():
    out_file = out_file_template_soa.format("add1IterativeOptOutOfPlace")

    for i, options in enumerate(special_options_gcc):
        exec_file = f"executable_gcc_special_out_of_place{i}"

        # Compile with special options using GCC
        subprocess.run(["gcc"] + options + [out_file, "-o", exec_file, "-lpapi"])

# Function to compile 'add1IterativeOpt' with special options using Clang
def compile_special_clang():
    out_file = out_file_template_soa.format("add1IterativeOptInPlace")

    for i, options in enumerate(special_options_clang):
        exec_file = f"executable_clang_special_in_place{i}"

        # Compile with special options using Clang
        subprocess.run(["clang"] + options + [out_file, "-o", exec_file, "-lpapi"])

def compile_special_clang_out_of_place():
    out_file = out_file_template_soa.format("add1IterativeOptOutOfPlace")

    for i, options in enumerate(special_options_clang):
        exec_file = f"executable_clang_special_out_of_place{i}"

        # Compile with special options using Clang
        subprocess.run(["clang"] + options + [out_file, "-o", exec_file, "-lpapi"])

# Compile 'add1IterativeOpt' with special options using GCC and Clang
compile_special_gcc()
compile_special_clang()

compile_special_gcc_out_of_place()
compile_special_clang_out_of_place()

# Run the executables and collect the data for special options of 'add1IterativeOpt'
data_special_gcc = {}
data_special_clang = {}

for i, options in enumerate(special_options_gcc):
    exec_file_gcc_in_place   = f"executable_gcc_special_in_place{i}"
    exec_file_clang_in_place = f"executable_clang_special_in_place{i}"

    exec_file_gcc_out_of_place = f"executable_gcc_special_out_of_place{i}"
    exec_file_clang_out_of_place = f"executable_clang_special_out_of_place{i}"

    times, instructions, l2_misses, l3_misses, prefetch_data_misses, l1_instruction_cache_misses, load_instructions, store_instructions, l3_load_misses, l3_store_misses, l2_load_misses, l2_store_misses = run_executable(exec_file_gcc_in_place, "add1IterativeOptInPlace")
    data_special_gcc["add1IterOptInPlace" + "-" + special_options_keys[i]] = {
        "times": times,
        "instructions": instructions,
        "l2_misses": l2_misses,
        "l3_misses": l3_misses,
        "prefetch_data_misses": prefetch_data_misses,
        "l1_instruction_cache_misses": l1_instruction_cache_misses,
        "load_instructions": load_instructions,
        "store_instructions": store_instructions,
        "l3_load_misses": l3_load_misses,
        "l3_store_misses": l3_store_misses,
        "l2_load_misses": l2_load_misses,
        "l2_store_misses": l2_store_misses,
        "median_time": format_scientific(statistics.mean(times)),
        "median_instructions": format_scientific(statistics.mean(instructions)),
        "median_l2_misses": format_scientific(statistics.mean(l2_misses)),
        "median_l3_misses": format_scientific(statistics.mean(l3_misses)),
        "median_prefetch_data_misses": format_scientific(statistics.mean(prefetch_data_misses)),
        "median_l1_instruction_cache_misses": format_scientific(statistics.mean(l1_instruction_cache_misses)),
        "median_load_instructions": format_scientific(statistics.mean(load_instructions)),
        "median_store_instructions": format_scientific(statistics.mean(store_instructions)),
        "median_l3_load_misses": format_scientific(statistics.mean(l3_load_misses)),
        "median_l3_store_misses": format_scientific(statistics.mean(l3_store_misses)),
        "median_l2_load_misses": format_scientific(statistics.mean(l2_load_misses)),
        "median_l2_store_misses": format_scientific(statistics.mean(l2_store_misses)),
        "compile_command": "gcc " + " ".join(options)
    }

    times, instructions, l2_misses, l3_misses, prefetch_data_misses, l1_instruction_cache_misses, load_instructions, store_instructions, l3_load_misses, l3_store_misses, l2_load_misses, l2_store_misses = run_executable(exec_file_gcc_out_of_place, "add1IterativeOptOutOfPlace")
    data_special_gcc["add1IterOptOutOfPlace" + "-" + special_options_keys[i]] = {
        "times": times,
        "instructions": instructions,
        "l2_misses": l2_misses,
        "l3_misses": l3_misses,
        "prefetch_data_misses": prefetch_data_misses,
        "l1_instruction_cache_misses": l1_instruction_cache_misses,
        "load_instructions": load_instructions,
        "store_instructions": store_instructions,
        "l3_load_misses": l3_load_misses,
        "l3_store_misses": l3_store_misses,
        "l2_load_misses": l2_load_misses,
        "l2_store_misses": l2_store_misses,
        "median_time": format_scientific(statistics.mean(times)),
        "median_instructions": format_scientific(statistics.mean(instructions)),
        "median_l2_misses": format_scientific(statistics.mean(l2_misses)),
        "median_l3_misses": format_scientific(statistics.mean(l3_misses)),
        "median_prefetch_data_misses": format_scientific(statistics.mean(prefetch_data_misses)),
        "median_l1_instruction_cache_misses": format_scientific(statistics.mean(l1_instruction_cache_misses)),
        "median_load_instructions": format_scientific(statistics.mean(load_instructions)),
        "median_store_instructions": format_scientific(statistics.mean(store_instructions)),
        "median_l3_load_misses": format_scientific(statistics.mean(l3_load_misses)),
        "median_l3_store
