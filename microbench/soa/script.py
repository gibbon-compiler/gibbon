import subprocess
import re
import os

def run_executable(executable_path):
    result = subprocess.run([executable_path], capture_output=True, text=True)
    return result.stdout

def parse_runtime(output):
    match = re.search(r"The time taken by \w+ was ([\d.]+) seconds", output)
    if match:
        return float(match.group(1))
    return None

def main():
    # List all .exe files in the current directory
    exe_files = [f for f in os.listdir() if f.endswith('.exe')]
    
    for exe_file in exe_files:
        runtimes = []
        for _ in range(31):
            output = run_executable(exe_file)
            runtime = parse_runtime(output)
            if runtime is not None:
                runtimes.append(runtime)
        
        if runtimes:
            average_runtime = sum(runtimes) / len(runtimes)
            print(f"Average runtime for {exe_file}: {average_runtime:.6f} seconds")
        else:
            print(f"Failed to parse runtime for {exe_file}")

if __name__ == "__main__":
    main()
