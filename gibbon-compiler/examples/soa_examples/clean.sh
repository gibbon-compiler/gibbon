#!/usr/bin/env bash
# =============================================================================
# clean.sh  –  Remove all compiled outputs and generated paper materials
# =============================================================================
# Usage:
#   ./clean.sh                  # interactive confirmation
#   ./clean.sh --yes            # no confirmation
#   ./clean.sh --outputs-only   # remove only executables/C files
#   ./clean.sh --paper-only     # remove only LaTeX/figures
# =============================================================================

set -euo pipefail

OUTPUT_DIR="${OUTPUT_DIR:-benchmark_output}"
FIGURES_DIR="${FIGURES_DIR:-figures}"
FORCE=false
OUTPUTS_ONLY=false
PAPER_ONLY=false

RED='\033[0;31m'; GREEN='\033[0;32m'; YELLOW='\033[1;33m'; NC='\033[0m'; BOLD='\033[1m'

while [[ $# -gt 0 ]]; do
    case "$1" in
        --yes)          FORCE=true;        shift ;;
        --outputs-only) OUTPUTS_ONLY=true; shift ;;
        --paper-only)   PAPER_ONLY=true;   shift ;;
        -h|--help)
            sed -n '2,12p' "$0" | sed 's/^# //; s/^#//'
            exit 0 ;;
        *) echo "Unknown option: $1"; exit 1 ;;
    esac
done

echo ""
echo -e "${BOLD}Gibbon Benchmark Suite – Clean${NC}"
echo "================================"

if ! $FORCE; then
    echo -e "${YELLOW}This will remove:${NC}"
    [[ ! $PAPER_ONLY  == true ]] && echo "  • $OUTPUT_DIR/  (compiled executables, .c files, output logs)"
    [[ ! $OUTPUTS_ONLY == true ]] && echo "  • $FIGURES_DIR/ (generated figures)"
    [[ ! $OUTPUTS_ONLY == true ]] && echo "  • performance_table.tex"
    [[ ! $OUTPUTS_ONLY == true ]] && echo "  • benchmark_report.txt"
    [[ ! $OUTPUTS_ONLY == true ]] && echo "  • benchmark_results.json"
    echo ""
    read -rp "Continue? [y/N] " ans
    case "$ans" in
        y|Y|yes|YES) ;;
        *) echo "Aborted."; exit 0 ;;
    esac
fi

removed=0

if ! $PAPER_ONLY; then
    if [[ -d "$OUTPUT_DIR" ]]; then
        rm -rf "$OUTPUT_DIR"
        echo -e "  ${GREEN}✓${NC} Removed $OUTPUT_DIR/"
        (( removed++ )) || true
    else
        echo "  ~ $OUTPUT_DIR/ not found, nothing to remove"
    fi
fi

if ! $OUTPUTS_ONLY; then
    if [[ -d "$FIGURES_DIR" ]]; then
        rm -rf "$FIGURES_DIR"
        echo -e "  ${GREEN}✓${NC} Removed $FIGURES_DIR/"
        (( removed++ )) || true
    fi
    for f in performance_table.tex benchmark_report.txt benchmark_results.json \
              table_preview.tex table_preview.pdf table_preview.aux table_preview.log; do
        if [[ -f "$f" ]]; then
            rm -f "$f"
            echo -e "  ${GREEN}✓${NC} Removed $f"
            (( removed++ )) || true
        fi
    done
fi

echo ""
if (( removed > 0 )); then
    echo -e "${GREEN}Done – removed ${removed} item(s).${NC}"
else
    echo -e "${YELLOW}Nothing was removed.${NC}"
fi
echo ""
echo "To re-run benchmarks:  ./gibbon_benchmark.py --generate-paper"
