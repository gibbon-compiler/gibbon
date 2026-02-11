#!/bin/bash
# Simple Gibbon Benchmarking Script
# Usage: ./gibbon_benchmark.sh [programs_dir] [iterations]

set -e

PROGRAMS_DIR="${1:-programs}"
ITERATIONS="${2:-20}"
OUTPUT_DIR="benchmark_output"
REPORT_FILE="benchmark_report.txt"

# Color codes for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Programs to benchmark
PROGRAMS=(
    "Compiler.hs"
    "DBQuery.hs"
    "DecisionTree.hs"
    "DomTree.hs"
    "KDTree.hs"
    "LinearListReduction.hs"
    "List.hs"
    "MonoTree.hs"
    "ObjectGraph.hs"
    "OctTree.hs"
    "PiecewiseFunctions.hs"
    "TernaryTree.hs"
    "Trie.hs"
)

# Create output directory
mkdir -p "$OUTPUT_DIR"

# Initialize report
echo "================================================================================" > "$REPORT_FILE"
echo "GIBBON COMPILER BENCHMARK REPORT" >> "$REPORT_FILE"
echo "================================================================================" >> "$REPORT_FILE"
echo "Timestamp: $(date)" >> "$REPORT_FILE"
echo "Iterations: $ITERATIONS" >> "$REPORT_FILE"
echo "" >> "$REPORT_FILE"

compile_program() {
    local source_file=$1
    local variant=$2
    local basename=$(basename "$source_file" .hs)
    local c_file="$OUTPUT_DIR/${basename}.${variant}.c"
    local exe_file="$OUTPUT_DIR/${basename}.${variant}.exe"
    
    echo -n "  Compiling ${basename} (${variant^^})... "
    
    if gibbon --use-mutable-cursors --packed --to-exe \
        --cfile "$c_file" --exefile "$exe_file" "$source_file" > /dev/null 2>&1; then
        echo -e "${GREEN}✓${NC}"
        return 0
    else
        echo -e "${RED}✗${NC}"
        return 1
    fi
}

run_program() {
    local exe_file=$1
    local output_file=$2
    
    echo -n "  Running $(basename $exe_file)... "
    
    if timeout 600 "$exe_file" --iterate "$ITERATIONS" > "$output_file" 2>&1; then
        echo -e "${GREEN}✓${NC}"
        return 0
    else
        echo -e "${RED}✗${NC}"
        return 1
    fi
}

extract_output() {
    local file=$1
    
    # Extract program output by filtering out timing lines
    # This handles various output formats (tuples, numbers, etc.)
    grep -v -E '^(itertime:|ITER TIMES:|ITERS:|SIZE:|BATCHTIME:|SELFTIMED:|Running pass|Running program|Running the Compiler|End$|^[[:space:]]*$)' "$file" 2>/dev/null | \
    grep -v -E '^[[:space:]]*$' | \
    tr '\n' ' ' | \
    sed 's/[[:space:]]\+/ /g' | \
    sed 's/^[[:space:]]*//;s/[[:space:]]*$//' || echo ""
}

compare_outputs() {
    local aos_output=$1
    local soa_output=$2
    
    # Normalize whitespace for comparison
    aos_normalized=$(echo "$aos_output" | tr -s '[:space:]' ' ' | sed 's/^[[:space:]]*//;s/[[:space:]]*$//')
    soa_normalized=$(echo "$soa_output" | tr -s '[:space:]' ' ' | sed 's/^[[:space:]]*//;s/[[:space:]]*$//')
    
    if [ -z "$aos_normalized" ] || [ -z "$soa_normalized" ]; then
        echo "N/A"
        return 2
    fi
    
    if [ "$aos_normalized" = "$soa_normalized" ]; then
        echo -e "${GREEN}✓ MATCH${NC}"
        return 0
    else
        echo -e "${RED}✗ MISMATCH${NC}"
        echo "  AoS output: $aos_normalized" >&2
        echo "  SoA output: $soa_normalized" >&2
        return 1
    fi
}

# Main benchmarking loop
echo "================================================================================"
echo "GIBBON COMPILER BENCHMARK SUITE"
echo "================================================================================"
echo "Programs directory: $PROGRAMS_DIR"
echo "Output directory: $OUTPUT_DIR"
echo "Iterations: $ITERATIONS"
echo "================================================================================"
echo ""

total=0
successful=0
matching=0

for program in "${PROGRAMS[@]}"; do
    echo "================================================================================"
    echo "Benchmarking: $program"
    echo "================================================================================"
    
    basename=$(basename "$program" .hs)
    aos_source="$PROGRAMS_DIR/AoS/$program"
    soa_source="$PROGRAMS_DIR/SoA/$program"
    
    aos_success=false
    soa_success=false
    
    # Check if source files exist
    if [ ! -f "$aos_source" ]; then
        echo -e "${YELLOW}Warning: $aos_source not found${NC}"
        continue
    fi
    
    if [ ! -f "$soa_source" ]; then
        echo -e "${YELLOW}Warning: $soa_source not found${NC}"
        continue
    fi
    
    ((total++))
    
    # Compile AoS
    if compile_program "$aos_source" "aos"; then
        aos_exe="$OUTPUT_DIR/${basename}.aos.exe"
        aos_output_file="$OUTPUT_DIR/${basename}.aos.output.txt"
        
        # Run AoS
        if run_program "$aos_exe" "$aos_output_file"; then
            aos_success=true
        fi
    fi
    
    # Compile SoA
    if compile_program "$soa_source" "soa"; then
        soa_exe="$OUTPUT_DIR/${basename}.soa.exe"
        soa_output_file="$OUTPUT_DIR/${basename}.soa.output.txt"
        
        # Run SoA
        if run_program "$soa_exe" "$soa_output_file"; then
            soa_success=true
        fi
    fi
    
    # Compare outputs
    echo ""
    if $aos_success && $soa_success; then
        ((successful++))
        
        aos_result=$(extract_output "$aos_output_file")
        soa_result=$(extract_output "$soa_output_file")
        
        echo -n "  Output comparison: "
        if compare_outputs "$aos_result" "$soa_result"; then
            ((matching++))
        fi
        
        # Add to report
        echo "" >> "$REPORT_FILE"
        echo "────────────────────────────────────────────────────────────────────────────────" >> "$REPORT_FILE"
        echo "Program: $program" >> "$REPORT_FILE"
        echo "────────────────────────────────────────────────────────────────────────────────" >> "$REPORT_FILE"
        echo "AoS Output: $aos_result" >> "$REPORT_FILE"
        echo "SoA Output: $soa_result" >> "$REPORT_FILE"
        
        if [ "$aos_result" = "$soa_result" ]; then
            echo "Match: ✓ PASS" >> "$REPORT_FILE"
        else
            echo "Match: ✗ FAIL" >> "$REPORT_FILE"
            echo "" >> "$REPORT_FILE"
            echo "*** OUTPUT MISMATCH DETAILS ***" >> "$REPORT_FILE"
            echo "The outputs differ. Please review the full output files:" >> "$REPORT_FILE"
            echo "  $aos_output_file" >> "$REPORT_FILE"
            echo "  $soa_output_file" >> "$REPORT_FILE"
            echo "*** END MISMATCH DETAILS ***" >> "$REPORT_FILE"
        fi
        
        # Extract and compare performance metrics
        echo "" >> "$REPORT_FILE"
        echo "AoS Performance:" >> "$REPORT_FILE"
        grep "SELFTIMED:" "$aos_output_file" >> "$REPORT_FILE" 2>/dev/null || true
        
        echo "" >> "$REPORT_FILE"
        echo "SoA Performance:" >> "$REPORT_FILE"
        grep "SELFTIMED:" "$soa_output_file" >> "$REPORT_FILE" 2>/dev/null || true
    fi
    
    echo ""
done

# Summary
echo ""
echo "================================================================================"
echo "BENCHMARK COMPLETE"
echo "================================================================================"
echo "Total programs benchmarked: $total"
echo "Successful runs (both AoS and SoA): $successful"
echo "Matching outputs: $matching"

if [ $matching -lt $successful ]; then
    echo -e "${YELLOW}"
    echo "⚠ WARNING: Some programs produced different outputs between AoS and SoA!"
    echo "   Check $REPORT_FILE for details."
    echo -e "${NC}"
fi

echo ""
echo "Detailed report saved to: $REPORT_FILE"
echo "Output files saved to: $OUTPUT_DIR/"

# Add summary to report
echo "" >> "$REPORT_FILE"
echo "================================================================================" >> "$REPORT_FILE"
echo "SUMMARY" >> "$REPORT_FILE"
echo "================================================================================" >> "$REPORT_FILE"
echo "Total programs benchmarked: $total" >> "$REPORT_FILE"
echo "Successful runs: $successful" >> "$REPORT_FILE"
echo "Matching outputs: $matching" >> "$REPORT_FILE"
