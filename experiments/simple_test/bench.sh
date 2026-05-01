#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"

export PYTHONUNBUFFERED=1

log_dir="results/$(date +%F)/bench_logs"
mkdir -p "$log_dir"
log_file="$log_dir/bench_$(date +%H%M%S_%N).log"

run_bench() {
    printf '\n==> %s\n' "$*" | tee -a "$log_file"
    "$@" 2>&1 | tee -a "$log_file"
}

echo "Logging bench.sh output to $log_file"

run_bench python3 benchmark_simple_test.py --program simple  --mode sweep --iterations 21 --sweep-start 1 --sweep-step 1000 --int-size 32 --sweep-max 5000000
run_bench python3 benchmark_simple_test.py --program simple2 --mode sweep --iterations 21 --sweep-start 1 --sweep-step 1000 --int-size 32 --sweep-max 5000000
run_bench python3 benchmark_simple_test.py --program simple3 --mode sweep --iterations 21 --sweep-start 1 --sweep-step 1000 --int-size 32 --sweep-max 5000000
run_bench python3 benchmark_simple_test.py --program simple  --mode sweep --iterations 21 --sweep-start 1 --sweep-step 1000 --int-size 64 --sweep-max 5000000
run_bench python3 benchmark_simple_test.py --program simple2 --mode sweep --iterations 21 --sweep-start 1 --sweep-step 1000 --int-size 64 --sweep-max 5000000
run_bench python3 benchmark_simple_test.py --program simple3 --mode sweep --iterations 21 --sweep-start 1 --sweep-step 1000 --int-size 64 --sweep-max 5000000

echo "Done. Full log: $log_file"
