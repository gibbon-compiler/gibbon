import pandas as pd
from io import StringIO

# Read the data from soa_results.txt
with open('soa_results.txt', 'r') as file:
    data = file.read()

# Parse the data into a pandas DataFrame
df = pd.read_csv(StringIO(data), sep='\t')

# Save the DataFrame to a new file in a well-formatted manner
df.to_csv('formatted_data.csv', index=False)

print("Data has been successfully parsed and saved to 'formatted_data.csv'.")
