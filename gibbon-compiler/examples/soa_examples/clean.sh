#!/bin/bash
# Clean script - removes all compiled outputs
# Usage: ./clean.sh [output_dir]

OUTPUT_DIR="${1:-benchmark_output}"

echo "Cleaning benchmark outputs..."
echo "Output directory: $OUTPUT_DIR"
echo ""

if [ ! -d "$OUTPUT_DIR" ]; then
    echo "Directory $OUTPUT_DIR does not exist. Nothing to clean."
    exit 0
fi

# Count files before deletion
exe_count=$(find "$OUTPUT_DIR" -name "*.exe" 2>/dev/null | wc -l)
c_count=$(find "$OUTPUT_DIR" -name "*.c" 2>/dev/null | wc -l)
output_count=$(find "$OUTPUT_DIR" -name "*.output.txt" 2>/dev/null | wc -l)

echo "Files to be removed:"
echo "  Executables (.exe): $exe_count"
echo "  C files (.c): $c_count"
echo "  Output files (.output.txt): $output_count"
echo ""

if [ $exe_count -eq 0 ] && [ $c_count -eq 0 ] && [ $output_count -eq 0 ]; then
    echo "Nothing to clean."
    exit 0
fi

read -p "Proceed with deletion? [y/N] " -n 1 -r
echo
if [[ $REPLY =~ ^[Yy]$ ]]; then
    # Remove compiled files
    find "$OUTPUT_DIR" -name "*.exe" -delete
    find "$OUTPUT_DIR" -name "*.c" -delete
    find "$OUTPUT_DIR" -name "*.output.txt" -delete
    
    echo ""
    echo "✓ Cleaned successfully!"
    echo ""
    echo "Next run will recompile all programs."
else
    echo "Cancelled."
fi
