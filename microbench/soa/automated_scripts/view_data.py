import pandas as pd
import matplotlib.pyplot as plt
from io import StringIO

# Read the data from the CSV file
df = pd.read_csv('formatted_data.csv')

# Extract the relevant columns from the combined column
df[['average', 'median', 'lower_bound', 'upper_bound']] = df['(average, median,(lower_bound, upper_bound))'].str.extract(r"\('([^']+)', '([^']+)', \('([^']+)', '([^']+)'\)\)")

# Convert the extracted columns to numeric values
df['average'] = pd.to_numeric(df['average'])
df['median'] = pd.to_numeric(df['median'])
df['lower_bound'] = pd.to_numeric(df['lower_bound'])
df['upper_bound'] = pd.to_numeric(df['upper_bound'])

# Plotting the data
plt.figure(figsize=(12, 8))

# Plot average times for each function
for function in df['function'].unique():
    subset = df[df['function'] == function]
    plt.plot(subset['list_size'], subset['average'], marker='o', label=function)

plt.xlabel('List Size')
plt.ylabel('Average Time (s)')
plt.title('Performance of Different Functions')
plt.legend()
plt.grid(True)

# Save the plot to a file
plt.savefig('performance_plot.png')

# Show the plot
plt.show()

print("The data has been visualized and saved to 'performance_plot.png'.")
