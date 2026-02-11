#!/bin/bash
# Quick Start Example for Gibbon Benchmarking
# This creates a minimal test setup and runs the benchmark

echo "================================================================================"
echo "Gibbon Benchmark Quick Start Example"
echo "================================================================================"
echo ""

# Create example directory structure
echo "Creating example directory structure..."
mkdir -p example_programs/{AoS,SoA}

echo "Directory structure created:"
echo "  example_programs/"
echo "  ├── AoS/"
echo "  └── SoA/"
echo ""

echo "================================================================================"
echo "USAGE EXAMPLES"
echo "================================================================================"
echo ""

echo "1. BASIC USAGE (Python script - recommended):"
echo "   ./gibbon_benchmark.py --programs-dir example_programs"
echo ""

echo "2. BASIC USAGE (Bash script - lightweight):"
echo "   ./gibbon_benchmark.sh example_programs 20"
echo ""

echo "3. BENCHMARK SPECIFIC PROGRAMS:"
echo "   ./gibbon_benchmark.py --programs Compiler.hs List.hs Trie.hs"
echo ""

echo "4. CUSTOM ITERATIONS:"
echo "   ./gibbon_benchmark.py --iterations 50"
echo ""

echo "5. FULL CUSTOM RUN:"
echo "   ./gibbon_benchmark.py \\"
echo "     --programs-dir ./programs \\"
echo "     --output-dir ./build \\"
echo "     --iterations 30 \\"
echo "     --report my_results.txt \\"
echo "     --json my_data.json"
echo ""

echo "================================================================================"
echo "NEXT STEPS"
echo "================================================================================"
echo ""
echo "1. Copy your .hs files into:"
echo "   - example_programs/AoS/     (Array of Structs version)"
echo "   - example_programs/SoA/     (Struct of Arrays version)"
echo ""
echo "2. Run the benchmark:"
echo "   ./gibbon_benchmark.py --programs-dir example_programs"
echo ""
echo "3. Check results:"
echo "   cat benchmark_report.txt"
echo "   cat benchmark_results.json"
echo ""
echo "4. Review compiled outputs:"
echo "   ls -lh benchmark_output/"
echo ""

echo "================================================================================"
echo "EXAMPLE FILE LISTING"
echo "================================================================================"
echo ""
echo "Your programs directory should contain:"
cat << 'EOF'

programs/
├── AoS/
│   ├── Compiler.hs
│   ├── DBQuery.hs
│   ├── DecisionTree.hs
│   ├── DomTree.hs
│   ├── KDTree.hs
│   ├── LinearListReduction.hs
│   ├── List.hs
│   ├── MonoTree.hs
│   ├── ObjectGraph.hs
│   ├── OctTree.hs
│   ├── PiecewiseFunctions.hs
│   ├── TernaryTree.hs
│   └── Trie.hs
└── SoA/
    ├── Compiler.hs
    ├── DBQuery.hs
    ├── DecisionTree.hs
    ├── DomTree.hs
    ├── KDTree.hs
    ├── LinearListReduction.hs
    ├── List.hs
    ├── MonoTree.hs
    ├── ObjectGraph.hs
    ├── OctTree.hs
    ├── PiecewiseFunctions.hs
    ├── TernaryTree.hs
    └── Trie.hs
EOF

echo ""
echo "================================================================================"
echo "For full documentation, see README.md"
echo "================================================================================"
