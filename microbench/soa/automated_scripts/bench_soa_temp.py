import subprocess
import statistics
import matplotlib.pyplot as plt
import os
import numpy as np 
from matplotlib.gridspec import GridSpec

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
'''def run_executable(exec_file_template, function):
    exec_file = exec_file_template.format(function)
    if not os.path.isfile(exec_file):
        raise FileNotFoundError(f"Executable file {exec_file} not found.")
    
    times = []
    instructions = []
    l2_misses = []
    l3_misses = []
    prefetch_data_misses = []
    l1_instruction_cache_misses = []
    
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
        
        times.append(time_taken)
        instructions.append(total_instructions)
        l2_misses.append(l2_total_cache_misses)
        l3_misses.append(l3_total_cache_misses)
        prefetch_data_misses.append(data_prefetch_cache_misses)
        l1_instruction_cache_misses.append(l1_instruction_cache_misses_value)
    
    return times, instructions, l2_misses, l3_misses, prefetch_data_misses, l1_instruction_cache_misses'''

def run_executable(exec_file_template, function):
    exec_file = exec_file_template.format(function)
    if not os.path.isfile(exec_file):
        raise FileNotFoundError(f"Executable file {exec_file} not found.")

    times = []
    instructions = []
    cycles = []
    l2_misses = []
    l3_misses = []
    prefetch_data_misses = []
    l1_instruction_cache_misses = []
    l2_instruction_cache_misses = []
    l3_instruction_cache_misses = []
    load_instructions = []
    store_instructions = []
    l2_load_misses = []
    l2_store_misses = []
    cycles_no_ins_compl = []
    cycles_no_ins_issue = []

    for _ in range(31):
        result = subprocess.run(["./" + exec_file], capture_output=True, text=True)
        output = result.stdout

        # Parse the output to extract the data
        time_taken = float(output.split("The time taken by")[1].split("was")[1].split("seconds")[0].strip())
        total_instructions = int(output.split("Total Instructions:")[1].split("\n")[0].strip())
        total_cycles = int(output.split("Total Cycles:")[1].split("\n")[0].strip())
        l2_total_cache_misses = int(output.split("L2 total cache misses:")[1].split("\n")[0].strip())
        l3_total_cache_misses = int(output.split("L3 total cache misses:")[1].split("\n")[0].strip())
        data_prefetch_cache_misses = int(output.split("Data prefetch cache misses:")[1].split("\n")[0].strip())
        l1_instruction_cache_misses_value = int(output.split("L1 instruction cache misses:")[1].split("\n")[0].strip())
        l2_instruction_cache_misses_value = int(output.split("L2 instruction cache misses:")[1].split("\n")[0].strip())
        l3_instruction_cache_misses_value = int(output.split("Cycles waiting on any resource:")[1].split("\n")[0].strip())
        load_instructions_value = int(output.split("Load instructions:")[1].split("\n")[0].strip())
        store_instructions_value = int(output.split("Store instructions:")[1].split("\n")[0].strip())
        l2_load_misses_value = int(output.split("L2 load misses:")[1].split("\n")[0].strip())
        l2_store_misses_value = int(output.split("L2 store misses:")[1].split("\n")[0].strip())
        cycles_no_ins_comp_value = int(output.split("Cycles with no instructions completed:")[1].split("\n")[0].strip())
        cycles_no_ins_issue_value = int(output.split("Cycles with no instruction issue:")[1].split("\n")[0].strip())

        times.append(time_taken)
        instructions.append(total_instructions)
        cycles.append(total_cycles)
        l2_misses.append(l2_total_cache_misses)
        l3_misses.append(l3_total_cache_misses)
        prefetch_data_misses.append(data_prefetch_cache_misses)
        l1_instruction_cache_misses.append(l1_instruction_cache_misses_value)
        l2_instruction_cache_misses.append(l2_instruction_cache_misses_value)
        l3_instruction_cache_misses.append(l3_instruction_cache_misses_value)
        load_instructions.append(load_instructions_value)
        store_instructions.append(store_instructions_value)
        l2_load_misses.append(l2_load_misses_value)
        l2_store_misses.append(l2_store_misses_value)
        cycles_no_ins_compl.append(cycles_no_ins_comp_value)
        cycles_no_ins_issue.append(cycles_no_ins_issue_value)

    return times, instructions, cycles, l2_misses, l3_misses, prefetch_data_misses, l1_instruction_cache_misses, l2_instruction_cache_misses, l3_instruction_cache_misses, load_instructions, store_instructions, l2_load_misses, l2_store_misses, cycles_no_ins_compl, cycles_no_ins_issue


# Generate and compile the .c files for each function using GCC and Clang for SOA
for function in functions_soa:
    generate_and_compile_gcc_soa(function)
    generate_and_compile_clang_soa(function)

# Run the executables and collect the data for GCC and Clang for SOA
data_gcc_soa = {}
data_clang_soa = {}
for function in functions_soa:
    times, instructions, cycles, l2_misses, l3_misses, prefetch_data_misses, l1_instruction_cache_misses, l2_instruction_cache_misses, l3_instruction_cache_misses, load_instructions, store_instructions, l2_load_misses, l2_store_misses, cycles_no_ins_compl, cycles_no_ins_issue = run_executable(exec_file_template_gcc_soa, function)
    data_gcc_soa[function] = {
        "median_time": format_scientific(statistics.mean(times)),
        "median_instructions": format_scientific(statistics.mean(instructions)),
        "median_cycles" : format_scientific(statistics.mean(cycles)),
        "median_l2_misses": format_scientific(statistics.mean(l2_misses)),
        "median_l3_misses": format_scientific(statistics.mean(l3_misses)),
        "median_prefetch_data_misses": format_scientific(statistics.mean(prefetch_data_misses)),
        "median_l1_instruction_cache_misses": format_scientific(statistics.mean(l1_instruction_cache_misses)),
        "median_l2_instruction_cache_misses": format_scientific(statistics.mean(l2_instruction_cache_misses)),
        "median_l3_instruction_cache_misses": format_scientific(statistics.mean(l3_instruction_cache_misses)),
        "load_instructions": format_scientific(statistics.mean(load_instructions)),
        "store_instructions": format_scientific(statistics.mean(store_instructions)),
        "l2_load_misses": format_scientific(statistics.mean(l2_load_misses)),
        "l2_store_misses": format_scientific(statistics.mean(l2_store_misses)),
        "cycles_no_ins_compl": format_scientific(statistics.mean(cycles_no_ins_compl)),
        "cycles_no_ins_issue": format_scientific(statistics.mean(cycles_no_ins_issue))
    }
    
    times, instructions, cycles, l2_misses, l3_misses, prefetch_data_misses, l1_instruction_cache_misses, l2_instruction_cache_misses, l3_instruction_cache_misses, load_instructions, store_instructions, l2_load_misses, l2_store_misses, cycles_no_ins_compl, cycles_no_ins_issue = run_executable(exec_file_template_clang_soa, function)
    data_clang_soa[function] = {
        "median_time": format_scientific(statistics.mean(times)),
        "median_instructions": format_scientific(statistics.mean(instructions)),
        "median_cycles" : format_scientific(statistics.mean(cycles)),
        "median_l2_misses": format_scientific(statistics.mean(l2_misses)),
        "median_l3_misses": format_scientific(statistics.mean(l3_misses)),
        "median_prefetch_data_misses": format_scientific(statistics.mean(prefetch_data_misses)),
        "median_l1_instruction_cache_misses": format_scientific(statistics.mean(l1_instruction_cache_misses)),
        "median_l2_instruction_cache_misses": format_scientific(statistics.mean(l2_instruction_cache_misses)),
        "median_l3_instruction_cache_misses": format_scientific(statistics.mean(l3_instruction_cache_misses)),
        "load_instructions": format_scientific(statistics.mean(load_instructions)),
        "store_instructions": format_scientific(statistics.mean(store_instructions)),
        "l2_load_misses": format_scientific(statistics.mean(l2_load_misses)),
        "l2_store_misses": format_scientific(statistics.mean(l2_store_misses)),
        "cycles_no_ins_compl": format_scientific(statistics.mean(cycles_no_ins_compl)),
        "cycles_no_ins_issue": format_scientific(statistics.mean(cycles_no_ins_issue))
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
    
    times, instructions, cycles, l2_misses, l3_misses, prefetch_data_misses, l1_instruction_cache_misses, l2_instruction_cache_misses, l3_instruction_cache_misses, load_instructions, store_instructions, l2_load_misses, l2_store_misses, cycles_no_ins_compl, cycles_no_ins_issue = run_executable(exec_file_gcc_in_place, "add1IterativeOptInPlace")
    data_special_gcc["add1IterOptInPlace" + "-" + special_options_keys[i]] = {
        "median_time": format_scientific(statistics.mean(times)),
        "median_instructions": format_scientific(statistics.mean(instructions)),
        "median_cycles" : format_scientific(statistics.mean(cycles)),
        "median_l2_misses": format_scientific(statistics.mean(l2_misses)),
        "median_l3_misses": format_scientific(statistics.mean(l3_misses)),
        "median_prefetch_data_misses": format_scientific(statistics.mean(prefetch_data_misses)),
        "median_l1_instruction_cache_misses": format_scientific(statistics.mean(l1_instruction_cache_misses)),
        "median_l2_instruction_cache_misses": format_scientific(statistics.mean(l2_instruction_cache_misses)),
        "median_l3_instruction_cache_misses": format_scientific(statistics.mean(l3_instruction_cache_misses)),
        "load_instructions": format_scientific(statistics.mean(load_instructions)),
        "store_instructions": format_scientific(statistics.mean(store_instructions)),
        "l2_load_misses": format_scientific(statistics.mean(l2_load_misses)),
        "l2_store_misses": format_scientific(statistics.mean(l2_store_misses)),
        "cycles_no_ins_compl": format_scientific(statistics.mean(cycles_no_ins_compl)),
        "cycles_no_ins_issue": format_scientific(statistics.mean(cycles_no_ins_issue)),
        "compile_command": "gcc " + " ".join(options)
    }

    times, instructions, cycles, l2_misses, l3_misses, prefetch_data_misses, l1_instruction_cache_misses, l2_instruction_cache_misses, l3_instruction_cache_misses, load_instructions, store_instructions, l2_load_misses, l2_store_misses, cycles_no_ins_compl, cycles_no_ins_issue = run_executable(exec_file_gcc_out_of_place, "add1IterativeOptOutOfPlace")
    data_special_gcc["add1IterOptOutOfPlace" + "-" + special_options_keys[i]] = {
        "median_time": format_scientific(statistics.mean(times)),
        "median_instructions": format_scientific(statistics.mean(instructions)),
        "median_cycles" : format_scientific(statistics.mean(cycles)),
        "median_l2_misses": format_scientific(statistics.mean(l2_misses)),
        "median_l3_misses": format_scientific(statistics.mean(l3_misses)),
        "median_prefetch_data_misses": format_scientific(statistics.mean(prefetch_data_misses)),
        "median_l1_instruction_cache_misses": format_scientific(statistics.mean(l1_instruction_cache_misses)),
        "median_l2_instruction_cache_misses": format_scientific(statistics.mean(l2_instruction_cache_misses)),
        "median_l3_instruction_cache_misses": format_scientific(statistics.mean(l3_instruction_cache_misses)),
        "load_instructions": format_scientific(statistics.mean(load_instructions)),
        "store_instructions": format_scientific(statistics.mean(store_instructions)),
        "l2_load_misses": format_scientific(statistics.mean(l2_load_misses)),
        "l2_store_misses": format_scientific(statistics.mean(l2_store_misses)),
        "cycles_no_ins_compl": format_scientific(statistics.mean(cycles_no_ins_compl)),
        "cycles_no_ins_issue": format_scientific(statistics.mean(cycles_no_ins_issue)),
        "compile_command": "gcc " + " ".join(options)
    }
    
    times, instructions, cycles, l2_misses, l3_misses, prefetch_data_misses, l1_instruction_cache_misses, l2_instruction_cache_misses, l3_instruction_cache_misses, load_instructions, store_instructions, l2_load_misses, l2_store_misses, cycles_no_ins_compl, cycles_no_ins_issue = run_executable(exec_file_clang_in_place, "add1IterativeOptInPlace")
    data_special_clang["add1IterOptInPlace" + "-" + special_options_keys[i]] = {
        "median_time": format_scientific(statistics.mean(times)),
        "median_instructions": format_scientific(statistics.mean(instructions)),
        "median_cycles" : format_scientific(statistics.mean(cycles)),
        "median_l2_misses": format_scientific(statistics.mean(l2_misses)),
        "median_l3_misses": format_scientific(statistics.mean(l3_misses)),
        "median_prefetch_data_misses": format_scientific(statistics.mean(prefetch_data_misses)),
        "median_l1_instruction_cache_misses": format_scientific(statistics.mean(l1_instruction_cache_misses)),
        "median_l2_instruction_cache_misses": format_scientific(statistics.mean(l2_instruction_cache_misses)),
        "median_l3_instruction_cache_misses": format_scientific(statistics.mean(l3_instruction_cache_misses)),
        "load_instructions": format_scientific(statistics.mean(load_instructions)),
        "store_instructions": format_scientific(statistics.mean(store_instructions)),
        "l2_load_misses": format_scientific(statistics.mean(l2_load_misses)),
        "l2_store_misses": format_scientific(statistics.mean(l2_store_misses)),
        "cycles_no_ins_compl": format_scientific(statistics.mean(cycles_no_ins_compl)),
        "cycles_no_ins_issue": format_scientific(statistics.mean(cycles_no_ins_issue)),
        "compile_command": "clang " + " ".join(options)
    }

    times, instructions, cycles, l2_misses, l3_misses, prefetch_data_misses, l1_instruction_cache_misses, l2_instruction_cache_misses, l3_instruction_cache_misses, load_instructions, store_instructions, l2_load_misses, l2_store_misses, cycles_no_ins_compl, cycles_no_ins_issue = run_executable(exec_file_clang_out_of_place, "add1IterativeOptOutOfPlace")
    data_special_clang["add1IterOptOutOfPlace" + "-" + special_options_keys[i]] = {
        "median_time": format_scientific(statistics.mean(times)),
        "median_instructions": format_scientific(statistics.mean(instructions)),
        "median_cycles" : format_scientific(statistics.mean(cycles)),
        "median_l2_misses": format_scientific(statistics.mean(l2_misses)),
        "median_l3_misses": format_scientific(statistics.mean(l3_misses)),
        "median_prefetch_data_misses": format_scientific(statistics.mean(prefetch_data_misses)),
        "median_l1_instruction_cache_misses": format_scientific(statistics.mean(l1_instruction_cache_misses)),
        "median_l2_instruction_cache_misses": format_scientific(statistics.mean(l2_instruction_cache_misses)),
        "median_l3_instruction_cache_misses": format_scientific(statistics.mean(l3_instruction_cache_misses)),
        "load_instructions": format_scientific(statistics.mean(load_instructions)),
        "store_instructions": format_scientific(statistics.mean(store_instructions)),
        "l2_load_misses": format_scientific(statistics.mean(l2_load_misses)),
        "l2_store_misses": format_scientific(statistics.mean(l2_store_misses)),
        "cycles_no_ins_compl": format_scientific(statistics.mean(cycles_no_ins_compl)),
        "cycles_no_ins_issue": format_scientific(statistics.mean(cycles_no_ins_issue)),
        "compile_command": "clang " + " ".join(options)
    }

# Create a figure with a grid layout
fig = plt.figure(figsize=(20, 14))
gs = GridSpec(2, 1, height_ratios=[1, 10])  # Adjust height ratios to allocate space for the legend

# Create an axis for the legend
ax_legend = fig.add_subplot(gs[0])
ax_legend.axis('off')  # Hide the axis

# Create an axis for the table
ax_table = fig.add_subplot(gs[1])
ax_table.axis('tight')
ax_table.axis('off')

fig.suptitle("Performance Data for SOA Functions (GCC and Clang)", fontsize=16, y=0.95)

# Adjust the layout to create space for the title
plt.subplots_adjust(top=0.85)

table_data_gcc_soa = [
    ["(GCC)", "T(s)", "I", "Cyc", "L2M", "L3M", "PDM", "L1IM", "L2IM", "CSAR", "LDI", "STI",
        "L2LM", "L2SM", "CNIC", "CNII"]
]

table_data_clang_soa = [
     ["(Clang)", "T(s)", "I", "Cyc", "L2M", "L3M", "PDM", "L1IM", "L2IM", "CSAR", "LDI", "STI",
        "L2LM", "L2SM", "CNIC", "CNII"]
]

for function in functions_soa:
    table_data_gcc_soa.append([
        function,
        data_gcc_soa[function]["median_time"],
        data_gcc_soa[function]["median_instructions"],
        data_gcc_soa[function]["median_cycles"],
        data_gcc_soa[function]["median_l2_misses"],
        data_gcc_soa[function]["median_l3_misses"],
        data_gcc_soa[function]["median_prefetch_data_misses"],
        data_gcc_soa[function]["median_l1_instruction_cache_misses"],
        data_gcc_soa[function]["median_l2_instruction_cache_misses"],
        data_gcc_soa[function]["median_l3_instruction_cache_misses"],
        data_gcc_soa[function]["load_instructions"],
        data_gcc_soa[function]["store_instructions"],
        data_gcc_soa[function]["l2_load_misses"],
        data_gcc_soa[function]["l2_store_misses"],
        data_gcc_soa[function]["cycles_no_ins_compl"],
        data_gcc_soa[function]["cycles_no_ins_issue"]
    ])

    table_data_clang_soa.append([
        function,
        data_clang_soa[function]["median_time"],
        data_clang_soa[function]["median_instructions"],
        data_clang_soa[function]["median_cycles"],
        data_clang_soa[function]["median_l2_misses"],
        data_clang_soa[function]["median_l3_misses"],
        data_clang_soa[function]["median_prefetch_data_misses"],
        data_clang_soa[function]["median_l1_instruction_cache_misses"],
        data_clang_soa[function]["median_l2_instruction_cache_misses"],
        data_clang_soa[function]["median_l3_instruction_cache_misses"],
        data_clang_soa[function]["load_instructions"],
        data_clang_soa[function]["store_instructions"],
        data_clang_soa[function]["l2_load_misses"],
        data_clang_soa[function]["l2_store_misses"],
        data_clang_soa[function]["cycles_no_ins_compl"],
        data_clang_soa[function]["cycles_no_ins_issue"]

    ])

for function in special_options_keys:
    for funcs in ["add1IterOptInPlace-", "add1IterOptOutOfPlace-"]:

        function_new = funcs + function

        table_data_gcc_soa.append([
            function_new,
            data_special_gcc[function_new]["median_time"],
            data_special_gcc[function_new]["median_instructions"],
            data_special_gcc[function_new]["median_cycles"],
            data_special_gcc[function_new]["median_l2_misses"],
            data_special_gcc[function_new]["median_l3_misses"],
            data_special_gcc[function_new]["median_prefetch_data_misses"],
            data_special_gcc[function_new]["median_l1_instruction_cache_misses"],
            data_special_gcc[function_new]["median_l2_instruction_cache_misses"],
            data_special_gcc[function_new]["median_l3_instruction_cache_misses"],
            data_special_gcc[function_new]["load_instructions"],
            data_special_gcc[function_new]["store_instructions"],
            data_special_gcc[function_new]["l2_load_misses"],
            data_special_gcc[function_new]["l2_store_misses"],
            data_special_gcc[function_new]["cycles_no_ins_compl"],
            data_special_gcc[function_new]["cycles_no_ins_issue"]

        ])

        table_data_clang_soa.append([
            function_new,
            data_special_clang[function_new]["median_time"],
            data_special_clang[function_new]["median_instructions"],
            data_special_clang[function_new]["median_cycles"],
            data_special_clang[function_new]["median_l2_misses"],
            data_special_clang[function_new]["median_l3_misses"],
            data_special_clang[function_new]["median_prefetch_data_misses"],
            data_special_clang[function_new]["median_l1_instruction_cache_misses"],
            data_special_clang[function_new]["median_l2_instruction_cache_misses"],
            data_special_clang[function_new]["median_l3_instruction_cache_misses"],
            data_special_clang[function_new]["load_instructions"],
            data_special_clang[function_new]["store_instructions"],
            data_special_clang[function_new]["l2_load_misses"],
            data_special_clang[function_new]["l2_store_misses"],
            data_special_clang[function_new]["cycles_no_ins_compl"],
            data_special_clang[function_new]["cycles_no_ins_issue"]

        ])

# Ensure all rows have the same number of columns
empty_row = [""] * 16
table_data_combined = table_data_gcc_soa + [empty_row] + table_data_clang_soa

table = ax_table.table(cellText=table_data_combined, loc='center', cellLoc='center', colWidths=[0.19] + [0.065]*15)  # Increase column width
table.auto_set_font_size(False)
table.set_fontsize(11)  # Increase font size

# Increase row heights
for key, cell in table.get_celld().items():
    cell.set_height(0.05)  # Increase row height

# Custom legend text split into three parts
legend_text_1 = (
    'T(s): Time in seconds, I: Instructions, Cyc: Cycles, L2M: L2 Misses, L3M: L3 Misses, '
    'PDM: Prefetch Data Misses'
)
legend_text_2 = (
    'L1IM: L1 Instruction Cache Misses, L2IM: L2 Instruction Cache Misses, CSAR: Cycles Stalled on Any Resource, '
    'LDI: Load Instructions, STI: Store Instructions'
)
legend_text_3 = (
    'L2LM: L2 Load Misses, L2SM: L2 Store Misses, CNIC: Cycles No Instruction Completion, '
    'CNII: Cycles No Instruction Issue'
)

# Add legend text to the top left
ax_legend.text(0, 0.8, legend_text_1, ha='left', va='center', fontsize=11)
ax_legend.text(0, 0.5, legend_text_2, ha='left', va='center', fontsize=11)
ax_legend.text(0, 0.2, legend_text_3, ha='left', va='center', fontsize=11)

plt.show()
