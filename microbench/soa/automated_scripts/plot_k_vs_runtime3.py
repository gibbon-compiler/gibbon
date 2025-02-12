import pandas as pd
import matplotlib.pyplot as plt
import sys

# Define the column names
columns = ["k", "l", "list_size", "function", "average", "median", "lower_bound", "upper_bound", "total_instructions", "l2_cache_misses"]

input_file = sys.argv[1]

# Read the data from the file, skipping the header row
with open(input_file, 'r') as file:
    data = file.readlines()[1:]  # Skip the header row

# Initialize an empty list to store the processed rows
processed_data = []

# Process each row
for row in data:
    # Split the row into columns
    cols = row.split()
    
    # Check if the row has the expected number of columns
    if len(cols) >= 10:
        # Extract the values for average, median, lower_bound, upper_bound, total_instructions, and l2_cache_misses
        average = cols[4].strip("('),")
        median = cols[5].strip("('),")
        lower_bound = cols[6].strip("('),")
        upper_bound = cols[7].strip("('),")
        total_instructions = cols[8].strip("('),")
        l2_cache_misses = cols[9].strip("('),")
        
        # Append the processed row to the list
        processed_data.append([cols[0], cols[1], cols[2], cols[3], average, median, lower_bound, upper_bound, total_instructions, l2_cache_misses])

# Create a DataFrame from the processed data
df = pd.DataFrame(processed_data, columns=columns)

# Convert relevant columns to numeric types for analysis
df["k"] = pd.to_numeric(df["k"])
df["l"] = pd.to_numeric(df["l"])
df["list_size"] = pd.to_numeric(df["list_size"])
df["average"] = pd.to_numeric(df["average"].str.replace("'", ""))
df["median"] = pd.to_numeric(df["median"].str.replace("'", ""))
df["lower_bound"] = pd.to_numeric(df["lower_bound"].str.replace("'", ""))
df["upper_bound"] = pd.to_numeric(df["upper_bound"].str.replace("'", ""))
df["total_instructions"] = pd.to_numeric(df["total_instructions"].str.replace("'", ""))
df["l2_cache_misses"] = pd.to_numeric(df["l2_cache_misses"].str.replace("'", ""))

# Calculate the percentage of fields used in the cons style list
df["percentage_used"] = (df["l"] / df["k"]) * 100

# Define colors for different l values
colors = {1: 'green', 2: 'blue', 3: 'red', 4: 'cyan', 5: 'magenta', 6: 'brown', 7: 'black', 8: 'orange', 9: 'purple'}

# Define markers for different functions
markers = {
    'add1RecursiveInPlace': 'o',
    'add1RecursiveOutOfPlace': 'x',
    'add1IterativeInPlace': 's',
    'add1IterativeOutOfPlace': '^',
    'add1IterativeOptInPlace': 'd',
    'add1IterativeOptOutOfPlace': '*'
}

# Plot runtime, total instructions, and L2 cache misses vs k values for each (l, list_size) tuple value with 95% confidence intervals as subplots
unique_tuples = df.groupby(['l', 'list_size']).size().reset_index().rename(columns={0:'count'})

for _, row in unique_tuples.iterrows():
    l = row['l']
    list_size = row['list_size']
    
    fig, axs = plt.subplots(3, 1, figsize=(12, 18))
    
    subset_tuple = df[(df['l'] == l) & (df['list_size'] == list_size) & (df['k'] >= l)]
    
    for function in subset_tuple['function'].unique():
        subset_function = subset_tuple[subset_tuple['function'] == function]
        
        # Plot runtime vs k values
        axs[0].errorbar(subset_function['k'], subset_function['median'],
                        fmt=markers[function], linestyle='-', color=colors[int(l)], label=f"{function} - Runtime")
        
        # Plot total instructions vs k values
        axs[1].errorbar(subset_function['k'], subset_function['total_instructions'], 
                        fmt=markers[function], linestyle='--', color=colors[int(l)], label=f"{function} - Instructions")
        
        # Plot L2 cache misses vs k values
        axs[2].errorbar(subset_function['k'], subset_function['l2_cache_misses'], 
                        fmt=markers[function], linestyle=':', color=colors[int(l)], label=f"{function} - Cache Misses")
    
    axs[0].set_xlabel("k Values")
    axs[0].set_ylabel("Median Runtime")
    axs[0].set_title(f"Performance Comparison: Median Runtime vs k Values (l: {l}, List Size: {list_size})")
    axs[0].legend()
    axs[0].grid(True)
    
    axs[1].set_xlabel("k Values")
    axs[1].set_ylabel("Total Instructions")
    axs[1].set_title(f"Performance Comparison: Total Instructions vs k Values (l: {l}, List Size: {list_size})")
    axs[1].legend()
    axs[1].grid(True)
    
    axs[2].set_xlabel("k Values")
    axs[2].set_ylabel("L2 Cache Misses")
    axs[2].set_title(f"Performance Comparison: L2 Cache Misses vs k Values (l: {l}, List Size: {list_size})")
    axs[2].legend()
    axs[2].grid(True)
    
    plt.tight_layout(pad=5.0)
    plt.show()
