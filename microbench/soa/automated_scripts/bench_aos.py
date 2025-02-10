import subprocess
import statistics
import matplotlib.pyplot as plt

# Define the parameters
k = 1
l = 1
list_size = 30
functions = ["add1RecursiveInPlace", "add1IterativeInPlace", "add1RecursiveOutOfPlace", "add1IterativeOutOfPlace"]
out_file_template = "generated_code_{}.c"
exec_file_template_gcc = "executable_gcc_{}"
exec_file_template_clang = "executable_clang_{}"

# Function to run the python script and compile the generated .c file with GCC
def generate_and_compile_gcc(function):
    out_file = out_file_template.format(function)
    exec_file = exec_file_template_gcc.format(function)
    
    # Run the python script to generate the .c file
    subprocess.run(["python3", "gen_packed_aos.py", "--k", str(k), "--l", str(l), "--outFile", out_file, "--function", function, "--listSize", str(list_size)])
    
    # Compile the .c file to an executable with optimization level O3 using GCC
    subprocess.run(["gcc", "-O3", out_file, "-o", exec_file, "-lpapi"])

# Function to run the python script and compile the generated .c file with Clang
def generate_and_compile_clang(function):
    out_file = out_file_template.format(function)
    exec_file = exec_file_template_clang.format(function)
    
    # Run the python script to generate the .c file
    subprocess.run(["python3", "gen_packed_aos.py", "--k", str(k), "--l", str(l), "--outFile", out_file, "--function", function, "--listSize", str(list_size)])
    
    # Compile the .c file to an executable with optimization level O3 using Clang
    subprocess.run(["clang", "-O3", out_file, "-o", exec_file, "-lpapi"])

# Function to run the executable 31 times and collect the data
def run_executable(exec_file_template, function):
    exec_file = exec_file_template.format(function)
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

# Generate and compile the .c files for each function using GCC and Clang
for function in functions:
    generate_and_compile_gcc(function)
    generate_and_compile_clang(function)

# Run the executables and collect the data for GCC and Clang
data_gcc = {}
data_clang = {}
for function in functions:
    times, instructions, l2_misses, l3_misses = run_executable(exec_file_template_gcc, function)
    data_gcc[function] = {
        "times": times,
        "instructions": instructions,
        "l2_misses": l2_misses,
        "l3_misses": l3_misses,
        "median_time": statistics.median(times),
        "median_instructions": statistics.median(instructions),
        "median_l2_misses": statistics.median(l2_misses),
        "median_l3_misses": statistics.median(l3_misses)
    }
    
    times, instructions, l2_misses, l3_misses = run_executable(exec_file_template_clang, function)
    data_clang[function] = {
        "times": times,
        "instructions": instructions,
        "l2_misses": l2_misses,
        "l3_misses": l3_misses,
        "median_time": statistics.median(times),
        "median_instructions": statistics.median(instructions),
        "median_l2_misses": statistics.median(l2_misses),
        "median_l3_misses": statistics.median(l3_misses)
    }

# Plot the data in a table with increased font size, table size, and column heights
fig, ax = plt.subplots(figsize=(16, 12))  # Increase figure size
ax.axis('tight')
ax.axis('off')

#ax.set_title("Performance Data for SOA Functions (GCC and Clang)", fontsize=16, pad=20)
fig.suptitle("Performance Data for AOS Functions (GCC and Clang)", fontsize=16, y=0.95)

# Adjust the layout to create space for the title
plt.subplots_adjust(top=0.85)


table_data_gcc = [
    ["Function (GCC)", "Median Time (s)", "Median Instructions", "Median L2 Misses", "Median L3 Misses"]
]

table_data_clang = [
    ["Function (Clang)", "Median Time (s)", "Median Instructions", "Median L2 Misses", "Median L3 Misses"]
]

for function in functions:
    table_data_gcc.append([
        function,
        data_gcc[function]["median_time"],
        data_gcc[function]["median_instructions"],
        data_gcc[function]["median_l2_misses"],
        data_gcc[function]["median_l3_misses"]
    ])
    
    table_data_clang.append([
        function,
        data_clang[function]["median_time"],
        data_clang[function]["median_instructions"],
        data_clang[function]["median_l2_misses"],
        data_clang[function]["median_l3_misses"]
    ])

# Ensure all rows have the same number of columns
empty_row = [""] * 5
table_data_combined = table_data_gcc + [empty_row] + table_data_clang

table = ax.table(cellText=table_data_combined, loc='center', cellLoc='center', colWidths=[0.2]*5)  # Increase column width
table.auto_set_font_size(False)
table.set_fontsize(14)  # Increase font size

# Increase row heights
for key, cell in table.get_celld().items():
    cell.set_height(0.1)  # Increase row height

plt.show()
