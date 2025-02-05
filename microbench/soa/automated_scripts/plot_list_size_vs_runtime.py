import pandas as pd
import matplotlib.pyplot as plt
import sys

# Define the column names
columns = ["k", "l", "list_size", "function", "average", "median", "lower_bound", "upper_bound"]

input_file = sys.argv[1]

# Read the data from the file
with open(input_file, 'r') as file:
    data = file.readlines()

# Initialize an empty list to store the processed rows
processed_data = []

# Process each row
for row in data:
    # Split the row into columns
    cols = row.split()
    
    # Check if the row has the expected number of columns
    if len(cols) >= 8:
        # Extract the values for average, median, lower_bound, and upper_bound
        average = cols[4].strip("('),")
        median = cols[5].strip("('),")
        lower_bound = cols[6].strip("('),")
        upper_bound = cols[7].strip("('),")
        
        # Append the processed row to the list
        processed_data.append([cols[0], cols[1], cols[2], cols[3], average, median, lower_bound, upper_bound])

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

# Calculate the percentage of fields used in the cons style list
df["percentage_used"] = (df["l"] / df["k"]) * 100

# Define colors for different k values
colors = {1: 'green', 2: 'blue', 3: 'red', 4: 'cyan', 5: 'magenta', 6: 'brown', 7: 'black', 8: 'orange', 9: 'purple'}

# Define markers for different functions
markers = {'add1Recursive': 'o', 'add1Iterative': 'x', 'add1IterativeOpt': 's'}

# Plot the runtime vs list size for each (k, percentage_used) tuple value with 95% confidence intervals
unique_tuples = df.groupby(['k', 'percentage_used']).size().reset_index().rename(columns={0:'count'})

for _, row in unique_tuples.iterrows():
    k = row['k']
    percentage_used = row['percentage_used']
    
    plt.figure(figsize=(12, 6))
    subset_tuple = df[(df['k'] == k) & (df['percentage_used'] == percentage_used)]
    
    for function in subset_tuple['function'].unique():
        subset_function = subset_tuple[subset_tuple['function'] == function]
        plt.errorbar(subset_function['median'], subset_function['list_size'], 
                     xerr=[abs(subset_function['median'] - subset_function['lower_bound']), abs(subset_function['upper_bound'] - subset_function['median'])],
                     fmt=markers[function], linestyle='-', color=colors[int(k)], label=function)
    
    plt.ylabel("List Size")
    plt.xlabel("Median Runtime")
    plt.title(f"Performance Comparison: Median Runtime vs List Size (k: {k}, Percentage Used: {percentage_used:.2f}%)")
    plt.legend()
    plt.grid(True)
    plt.show()
