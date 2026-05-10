#!/usr/bin/env bash
# =============================================================================
# gibbon_benchmark.sh  –  Bash convenience wrapper for gibbon_benchmark.py
# =============================================================================
# Provides shortcut commands so you don't have to remember all the flags.
#
# Usage:
#   ./gibbon_benchmark.sh                       # full run, all programs
#   ./gibbon_benchmark.sh quick                 # 5 iterations, all programs
#   ./gibbon_benchmark.sh paper                 # full run + generate paper
#   ./gibbon_benchmark.sh one DomTree.hs        # single program
#   ./gibbon_benchmark.sh one DomTree.hs paper  # single program + paper
#   ./gibbon_benchmark.sh clean                 # remove all outputs
#   ./gibbon_benchmark.sh clean-run             # clean then full run + paper
#   ./gibbon_benchmark.sh help                  # show this help
# =============================================================================

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PY="${SCRIPT_DIR}/gibbon_benchmark.py"

# Colours
RED='\033[0;31m'; GREEN='\033[0;32m'; YELLOW='\033[1;33m'
CYAN='\033[0;36m'; BOLD='\033[1m'; NC='\033[0m'

# Defaults (override via environment)
ITERS="${ITERS:-20}"
PROGRAMS_DIR="${PROGRAMS_DIR:-programs}"
OUTPUT_DIR="${OUTPUT_DIR:-benchmark_output}"
FIGURES_DIR="${FIGURES_DIR:-figures}"

die()   { echo -e "${RED}Error: $*${NC}" >&2; exit 1; }
info()  { echo -e "${CYAN}▶ $*${NC}"; }
ok()    { echo -e "${GREEN}✓ $*${NC}"; }
warn()  { echo -e "${YELLOW}⚠ $*${NC}"; }

need_python() {
    command -v python3 &>/dev/null || die "python3 not found"
    python3 -c "import matplotlib, numpy" 2>/dev/null \
        || die "Python deps missing – run: pip install matplotlib numpy"
}

need_gibbon() {
    command -v gibbon &>/dev/null || warn "gibbon not found in PATH – compilation will fail"
}

print_header() {
    echo ""
    echo -e "${BOLD}========================================${NC}"
    echo -e "${BOLD} Gibbon Benchmark Suite v2.4${NC}"
    echo -e "${BOLD}========================================${NC}"
    echo -e "  Programs dir : ${PROGRAMS_DIR}"
    echo -e "  Output dir   : ${OUTPUT_DIR}"
    echo -e "  Figures dir  : ${FIGURES_DIR}"
    echo -e "  Iterations   : ${ITERS}"
    echo ""
}

run_py() {
    info "Running: python3 $PY $*"
    python3 "$PY" "$@"
}

cmd_help() {
    sed -n '2,15p' "$0" | sed 's/^# //; s/^#//'
    echo ""
    echo "Environment variables:"
    echo "  ITERS=N          Number of benchmark iterations  (default: 20)"
    echo "  PROGRAMS_DIR=D   Programs root directory         (default: programs)"
    echo "  OUTPUT_DIR=D     Compiled executables directory  (default: benchmark_output)"
    echo "  FIGURES_DIR=D    Figures output directory        (default: figures)"
}

cmd_full() {
    # Full run: all programs, default iterations
    print_header
    need_python; need_gibbon
    run_py \
        --programs-dir "$PROGRAMS_DIR" \
        --output-dir   "$OUTPUT_DIR" \
        --iterations   "$ITERS"
    ok "Benchmark complete.  See benchmark_report.txt"
}

cmd_quick() {
    # Quick sanity-check run: 5 iterations
    print_header
    need_python; need_gibbon
    info "Quick run (5 iterations per program) ..."
    run_py \
        --programs-dir "$PROGRAMS_DIR" \
        --output-dir   "$OUTPUT_DIR" \
        --iterations   5
    ok "Quick run complete."
}

cmd_paper() {
    # Full run + generate all paper materials
    print_header
    need_python; need_gibbon
    run_py \
        --programs-dir "$PROGRAMS_DIR" \
        --output-dir   "$OUTPUT_DIR" \
        --figures-dir  "$FIGURES_DIR" \
        --iterations   "$ITERS" \
        --generate-paper
    echo ""
    ok "Paper materials generated:"
    echo "   performance_table.tex"
    echo "   ${FIGURES_DIR}/speedup_comparison.pdf"
    echo "   ${FIGURES_DIR}/per_program/  (one figure per program)"
    echo "   ${FIGURES_DIR}/heatmaps/     (one heatmap per program)"
    echo "   ${FIGURES_DIR}/pass_breakdown_all.pdf"
}

cmd_one() {
    # Benchmark a single program
    local prog="${1:-}"
    local extra="${2:-}"
    [[ -z "$prog" ]] && die "Usage: $0 one <Program.hs> [paper]"
    print_header
    need_python; need_gibbon
    info "Benchmarking: $prog"
    local paper_flag=""
    [[ "$extra" == "paper" ]] && paper_flag="--generate-paper"
    run_py \
        --programs-dir "$PROGRAMS_DIR" \
        --output-dir   "$OUTPUT_DIR" \
        --figures-dir  "$FIGURES_DIR" \
        --iterations   "$ITERS" \
        --programs     "$prog" \
        $paper_flag
    ok "$prog benchmark complete."
}

cmd_clean() {
    info "Cleaning compiled outputs and paper materials ..."
    bash "${SCRIPT_DIR}/clean.sh" --yes
}

cmd_clean_run() {
    # Full clean, then full run with paper
    cmd_clean
    cmd_paper
}

# ── Dispatch ────────────────────────────────────────────────────────────────

COMMAND="${1:-full}"
shift || true

case "$COMMAND" in
    help|--help|-h)     cmd_help ;;
    quick)              cmd_quick ;;
    paper)              cmd_paper ;;
    one)                cmd_one "$@" ;;
    clean)              cmd_clean ;;
    clean-run|cleanrun) cmd_clean_run ;;
    full|"")            cmd_full ;;
    *)
        warn "Unknown command: $COMMAND"
        echo ""
        cmd_help
        exit 1
        ;;
esac
