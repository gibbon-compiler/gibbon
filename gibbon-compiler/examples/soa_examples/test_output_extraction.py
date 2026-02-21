#!/usr/bin/env python3
"""
Test script to demonstrate output extraction from different formats
"""

import re

def extract_program_output(output: str) -> str:
    """
    Extract the actual program output by filtering out all timing data.
    This allows comparison of program results regardless of format.
    """
    lines = output.split('\n')
    filtered_lines = []
    
    # Patterns to exclude (timing and benchmark metadata)
    exclude_patterns = [
        r'^itertime:',
        r'^ITER TIMES:',
        r'^ITERS:',
        r'^SIZE:',
        r'^BATCHTIME:',
        r'^SELFTIMED:',
        r'^Running pass',
        r'^Running program',
        r'^Running the Compiler',
        r'^End$',
        r'^\s*$',  # Empty lines
    ]
    
    for line in lines:
        # Check if line matches any exclude pattern
        should_exclude = False
        for pattern in exclude_patterns:
            if re.match(pattern, line.strip()):
                should_exclude = True
                break
        
        if not should_exclude and line.strip():
            filtered_lines.append(line.strip())
    
    # Join the remaining lines and return
    result = '\n'.join(filtered_lines)
    return result if result else None


# Test Case 1: Tuple output (original Compiler.hs example)
test_output_1 = """Running the Compiler IR Program: 
Running pass instCountPass: 
itertime: 0.003521
itertime: 0.003419
ITER TIMES: [0.003193, 0.003205, 0.003221]
ITERS: 20
SIZE: 1
BATCHTIME: 6.565849e-02
SELFTIMED: 3.269139e-03
End
Running pass blockCountPass: 
itertime: 0.003086
ITER TIMES: [0.003052, 0.003061]
ITERS: 20
SIZE: 1
BATCHTIME: 6.189471e-02
SELFTIMED: 3.091285e-03
End
'#(8571429 1428571 1071429 535714 25714287 #t 17142858)
"""

# Test Case 2: Simple number output (LinearListReduction example)
test_output_2 = """Running program recution on List with 10 Integer elements: 
Running pass reduction: 
itertime: 0.001705
ITER TIMES: [0.001705]
ITERS: 1
SIZE: 1
BATCHTIME: 1.705300e-03
SELFTIMED: 1.705300e-03
End
500000500000
"""

# Test Case 3: Multi-line output
test_output_3 = """Running program test: 
Running pass somePass: 
itertime: 0.001234
ITER TIMES: [0.001234]
ITERS: 1
SIZE: 1
BATCHTIME: 1.234000e-03
SELFTIMED: 1.234000e-03
End
Result:
  Value: 12345
  Status: Success
"""

print("=" * 70)
print("OUTPUT EXTRACTION TEST")
print("=" * 70)

print("\n--- Test Case 1: Tuple Output ---")
result1 = extract_program_output(test_output_1)
print(f"Extracted: {result1}")

print("\n--- Test Case 2: Simple Number Output ---")
result2 = extract_program_output(test_output_2)
print(f"Extracted: {result2}")

print("\n--- Test Case 3: Multi-line Output ---")
result3 = extract_program_output(test_output_3)
print(f"Extracted: {result3}")

print("\n" + "=" * 70)
print("COMPARISON TEST")
print("=" * 70)

# Simulate AoS and SoA outputs with same result but different timings
aos_output = """Running pass test: 
itertime: 0.005000
ITER TIMES: [0.005000]
ITERS: 1
BATCHTIME: 5.000000e-03
SELFTIMED: 5.000000e-03
End
500000500000
"""

soa_output = """Running pass test: 
itertime: 0.003000
ITER TIMES: [0.003000]
ITERS: 1
BATCHTIME: 3.000000e-03
SELFTIMED: 3.000000e-03
End
500000500000
"""

aos_result = extract_program_output(aos_output)
soa_result = extract_program_output(soa_output)

print(f"\nAoS extracted: {aos_result}")
print(f"SoA extracted: {soa_result}")

# Normalize whitespace for comparison
aos_normalized = ' '.join(aos_result.split())
soa_normalized = ' '.join(soa_result.split())

print(f"\nOutputs match: {aos_normalized == soa_normalized}")
print("\n✓ Test shows that timing differences are ignored,")
print("  and only actual program output is compared!")
