import pandas as pd
from io import StringIO

# Read the data from soa_results.txt
with open('soa_results.txt', 'r') as file:
        data = file.read()

        # Parse the data into a pandas DataFrame
        df = pd.read_csv(StringIO(data), sep='\t')

        # Save the DataFrame to a CSV file
        df.to_csv('formatted_data.csv', index=False)

        # Write the DataFrame to a text file with nicely formatted columns
        with open('formatted_data.txt', 'w') as file:
                file.write(df.to_string(index=False))

                print("Data has been successfully parsed, saved to 'formatted_data.csv', and written to 'formatted_data.txt' with nicely formatted columns.")
