import subprocess
import statistics
import matplotlib.pyplot as plt
import os

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
    subprocess.run(["python3", "gen_packed_soa.py", "--k", str(k), "--l", str(l), "--outFile", out_file, "--function", function, "--listSize", str(list_size), "--printList", "True"])
    
    # Compile the .c file to an executable with optimization level O3 using GCC
    subprocess.run(["gcc", "-O3", out_file, "-o", exec_file, "-lpapi"])

# Function to run the python script and compile the generated .c file with Clang for SOA
def generate_and_compile_clang_soa(function):
    out_file = out_file_template_soa.format(function)
    exec_file = exec_file_template_clang_soa.format(function)
    
    # Run the python script to generate the .c file
    subprocess.run(["python3", "gen_packed_soa.py", "--k", str(k), "--l", str(l), "--outFile", out_file, "--function", function, "--listSize", str(list_size), "--printList", "True"])
    
    # Compile the .c file to an executable with optimization level O3 using Clang
    subprocess.run(["clang", "-O3", out_file, "-o", exec_file, "-lpapi"])

# Function to run the executable 31 times and collect the data for SOA
def run_executable(exec_file_template, function):
    exec_file = exec_file_template.format(function)
    if not os.path.isfile(exec_file):
        raise FileNotFoundError(f"Executable file {exec_file} not found.")
    
    times = []
    instructions = []
    l2_misses = []
    l3_misses = []
    
    for _ in range(31):
        result = subprocess.run(["./" + exec_file], capture_output=True, text=True)
        output = result.stdout
        
        # Parse the output to extract the data
        time_taken = float(output.split("The time taken by")[1].split("was")[1].split("seconds")[0].strip())
        total_instructions = int(output.split("Total Instructions:")[1].split("\n")[0].strip())
        l2_total_cache_misses = int(output.split("L2 total cache misses:")[1].split("\n")[0].strip())
        l3_total_cache_misses = int(output.split("L3 total cache misses:")[1].split("\n")[0].strip())
        
        times.append(time_taken)
        instructions.append(total_instructions)
        l2_misses.append(l2_total_cache_misses)
        l3_misses.append(l3_total_cache_misses)
    
    return times, instructions, l2_misses, l3_misses

# Generate and compile the .c files for each function using GCC and Clang for SOA
for function in functions_soa:
    generate_and_compile_gcc_soa(function)
    generate_and_compile_clang_soa(function)

# Run the executables and collect the data for GCC and Clang for SOA
data_gcc_soa = {}
data_clang_soa = {}
for function in functions_soa:
    times, instructions, l2_misses, l3_misses = run_executable(exec_file_template_gcc_soa, function)
    data_gcc_soa[function] = {
        "times": times,
        "instructions": instructions,
        "l2_misses": l2_misses,
        "l3_misses": l3_misses,
        "median_time": statistics.median(times),
        "median_instructions": statistics.median(instructions),
        "median_l2_misses": statistics.median(l2_misses),
        "median_l3_misses": statistics.median(l3_misses)
    }
    
    times, instructions, l2_misses, l3_misses = run_executable(exec_file_template_clang_soa, function)
    data_clang_soa[function] = {
        "times": times,
        "instructions": instructions,
        "l2_misses": l2_misses,
        "l3_misses": l3_misses,
        "median_time": statistics.median(times),
        "median_instructions": statistics.median(instructions),
        "median_l2_misses": statistics.median(l2_misses),
        "median_l3_misses": statistics.median(l3_misses)
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
    
    times, instructions, l2_misses, l3_misses = run_executable(exec_file_gcc_in_place, "add1IterativeOptInPlace")
    data_special_gcc["add1IterOptInPlace" + "-" + special_options_keys[i]] = {
        "times": times,
        "instructions": instructions,
        "l2_misses": l2_misses,
        "l3_misses": l3_misses,
        "median_time": statistics.median(times),
        "median_instructions": statistics.median(instructions),
        "median_l2_misses": statistics.median(l2_misses),
        "median_l3_misses": statistics.median(l3_misses),
        "compile_command": "gcc " + " ".join(options)
    }

    times, instructions, l2_misses, l3_misses = run_executable(exec_file_gcc_out_of_place, "add1IterativeOptOutOfPlace")
    data_special_gcc["add1IterOptOutOfPlace" + "-" + special_options_keys[i]] = {
        "times": times,
        "instructions": instructions,
        "l2_misses": l2_misses,
        "l3_misses": l3_misses,
        "median_time": statistics.median(times),
        "median_instructions": statistics.median(instructions),
        "median_l2_misses": statistics.median(l2_misses),
        "median_l3_misses": statistics.median(l3_misses),
        "compile_command": "gcc " + " ".join(options)
    }
    
    times, instructions, l2_misses, l3_misses = run_executable(exec_file_clang_in_place, "add1IterativeOptInPlace")
    data_special_clang["add1IterOptInPlace" + "-" + special_options_keys[i]] = {
        "times": times,
        "instructions": instructions,
        "l2_misses": l2_misses,
        "l3_misses": l3_misses,
        "median_time": statistics.median(times),
        "median_instructions": statistics.median(instructions),
        "median_l2_misses": statistics.median(l2_misses),
        "median_l3_misses": statistics.median(l3_misses),
        "compile_command": "clang " + " ".join(options)
    }

    times, instructions, l2_misses, l3_misses = run_executable(exec_file_clang_out_of_place, "add1IterativeOptOutOfPlace")
    data_special_clang["add1IterOptOutOfPlace" + "-" + special_options_keys[i]] = {
        "times": times,
        "instructions": instructions,
        "l2_misses": l2_misses,
        "l3_misses": l3_misses,
        "median_time": statistics.median(times),
        "median_instructions": statistics.median(instructions),
        "median_l2_misses": statistics.median(l2_misses),
        "median_l3_misses": statistics.median(l3_misses),
        "compile_command": "clang " + " ".join(options)
    }

# Plot the data in a table with increased font size, table size, and column heights
fig, ax = plt.subplots(figsize=(16, 12))  # Increase figure size
ax.axis('tight')
ax.axis('off')

#ax.set_title("Performance Data for SOA Functions (GCC and Clang)", fontsize=16, pad=20)
fig.suptitle("Performance Data for SOA Functions (GCC and Clang)", fontsize=16, y=0.95)

# Adjust the layout to create space for the title
plt.subplots_adjust(top=0.85)

table_data_gcc_soa = [
    ["Function (GCC)", "Median Time (s)", "Median Instructions", "Median L2 Misses", "Median L3 Misses"]
]

table_data_clang_soa = [
    ["Function (Clang)", "Median Time (s)", "Median Instructions", "Median L2 Misses", "Median L3 Misses"]
]

for function in functions_soa:
    table_data_gcc_soa.append([
        function,
        data_gcc_soa[function]["median_time"],
        data_gcc_soa[function]["median_instructions"],
        data_gcc_soa[function]["median_l2_misses"],
        data_gcc_soa[function]["median_l3_misses"]
    ])

    table_data_clang_soa.append([
        function,
        data_clang_soa[function]["median_time"],
        data_clang_soa[function]["median_instructions"],
        data_clang_soa[function]["median_l2_misses"],
        data_clang_soa[function]["median_l3_misses"]
    ])

for function in special_options_keys:
    for funcs in ["add1IterOptInPlace-", "add1IterOptOutOfPlace-"]:

        function_new = funcs + function

        table_data_gcc_soa.append([
            function_new,
            data_special_gcc[function_new]["median_time"],
            data_special_gcc[function_new]["median_instructions"],
            data_special_gcc[function_new]["median_l2_misses"],
            data_special_gcc[function_new]["median_l3_misses"]
        ])

        table_data_clang_soa.append([
            function_new,
            data_special_clang[function_new]["median_time"],
            data_special_clang[function_new]["median_instructions"],
            data_special_clang[function_new]["median_l2_misses"],
            data_special_clang[function_new]["median_l3_misses"]
        ])


# Ensure all rows have the same number of columns
empty_row = [""] * 5
table_data_combined = table_data_gcc_soa + [empty_row] + table_data_clang_soa

table = ax.table(cellText=table_data_combined, loc='center', cellLoc='center', colWidths=[0.22]*5)  # Increase column width
table.auto_set_font_size(False)
table.set_fontsize(12)  # Increase font size

# Increase row heights
for key, cell in table.get_celld().items():
    cell.set_height(0.05)  # Increase row height

plt.show()

