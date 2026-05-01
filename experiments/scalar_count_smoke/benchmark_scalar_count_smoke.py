#!/usr/bin/env python3
"""Benchmark the manual scalar-count vectorization experiment suite.

This script compiles a saved generated/manual C smoke test, runs it repeatedly,
parses the timing output, and prints compact tables of medians and speedups.
The reported variants are the five add1 experiments we care about:
recursive, loopified with dead-buffer copies and vectorization disabled,
loopified with dead-buffer indirections and vectorization disabled,
loopified with dead-buffer indirections and compiler auto-vectorization, and
loopified with dead-buffer indirections and manual SSE2 SIMD.

It intentionally does not regenerate the C files. The files under
experiments/scalar_count_smoke/sources are manual experiment artifacts.
"""

from __future__ import annotations

import argparse
import csv
import math
import os
import random
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from statistics import median


REPO_ROOT = Path(__file__).resolve().parents[2]
EXPERIMENT_SOURCE_DIR = Path(__file__).resolve().parent / "sources"
DEFAULT_BUILD_DIR = Path(tempfile.gettempdir()) / "gibbon_scalar_count_smoke_bench"
DEFAULT_SWEEP_SIZES = [10_000, 50_000, 100_000, 250_000, 500_000, 1_000_000]
DEFAULT_RESULTS_DIR = Path(__file__).resolve().parent / "results"


VARIANTS = [
    ("recursive", "Recursive add1", "recursive_add1_seconds"),
    (
        "loop_scalar_copy",
        "Loopified add1, copy dead buffers, vectorization off",
        "loop_scalar_add1_seconds",
    ),
    (
        "indir_loop_scalar",
        "Loopified add1, dead-buffer indirections, vectorization off",
        "indir_loop_scalar_add1_seconds",
    ),
    (
        "indir_loop_auto",
        "Loopified add1, dead-buffer indirections, auto-vectorized",
        "indir_loop_auto_add1_seconds",
    ),
    (
        "indir_loop_explicit_vector",
        "Loopified add1, dead-buffer indirections, manual SSE2 vectorized",
        "indir_loop_vectorized_add1_seconds",
    ),
]

HOT_LOOP_SUFFIXES = ("seconds", "ns_per_element", "calls", "elements")

INT_ONLY_VARIANTS = [
    ("int_only_scalar", "Int-only scalar helper", "int_only_scalar_seconds"),
    ("int_only_auto", "Int-only auto-vector helper", "int_only_auto_seconds"),
    (
        "int_only_explicit_vector",
        "Int-only SSE2 vector helper",
        "int_only_vectorized_seconds",
    ),
]


@dataclass(frozen=True)
class BuildConfig:
    key: str
    label: str
    flags: tuple[str, ...]


@dataclass(frozen=True)
class ProgramConfig:
    key: str
    label: str
    source: Path
    exe_stem: str
    length_define: str
    inner_iterations_define: str | None = None
    int_only_repeats_define: str | None = None


@dataclass(frozen=True)
class SweepRow:
    list_len: int
    averages: dict[str, float]
    hot_loop_averages: dict[str, float]

    def speedup_vs_recursive(self, key: str) -> float:
        return self.averages["recursive"] / self.averages[key]

    def hot_loop_speedup(self, scalar_key: str, vector_key: str) -> float:
        return self.hot_loop_averages[scalar_key] / self.hot_loop_averages[vector_key]


def manual_simd_name(build: BuildConfig) -> str:
    return "AVX2" if build.key == "avx2" else "SSE2"


def variant_display_label(build: BuildConfig, key: str, default_label: str) -> str:
    if key == "indir_loop_explicit_vector":
        return default_label.replace("manual SSE2", f"manual {manual_simd_name(build)}")
    if key == "int_only_explicit_vector":
        return default_label.replace("SSE2", manual_simd_name(build))
    return default_label


def list_hot_loop_prefixes(build: BuildConfig) -> list[tuple[str, str]]:
    return [
        ("loop_scalar_hot_loop", "Copy scalar hot loop"),
        ("indir_loop_scalar_hot_loop", "Indirection scalar hot loop"),
        ("indir_loop_auto_hot_loop", "Indirection auto-vector hot loop"),
        ("indir_loop_vectorized_hot_loop", f"Indirection {manual_simd_name(build)} hot loop"),
    ]


def multi_list_hot_loop_total_prefixes(build: BuildConfig) -> list[tuple[str, str]]:
    return [
        ("loop_scalar_hot_loop_total", "Copy scalar hot loops"),
        ("indir_loop_scalar_hot_loop_total", "Indirection scalar hot loops"),
        ("indir_loop_auto_hot_loop_total", "Indirection auto-vector hot loops"),
        ("indir_loop_vectorized_hot_loop_total", f"Indirection {manual_simd_name(build)} hot loops"),
    ]


BUILDS = [
    BuildConfig(
        key="sse2",
        label="SSE2 manual SIMD",
        flags=("-O3", "-flto", "-ftree-vectorize", "-msse2"),
    ),
    BuildConfig(
        key="avx2",
        label="AVX2 manual SIMD",
        flags=("-O3", "-flto", "-ftree-vectorize", "-mavx2", "-DMANUAL_USE_AVX2=1"),
    ),
]


PROGRAMS = {
    "list": ProgramConfig(
        key="list",
        label="ScalarCountSmoke add1List",
        source=EXPERIMENT_SOURCE_DIR / "ScalarCountSmoke.c",
        exe_stem="ScalarCountSmoke",
        length_define="SCALAR_COUNT_SMOKE_LIST_LEN",
        int_only_repeats_define="SCALAR_COUNT_SMOKE_INT_ONLY_REPEATS",
    ),
    "multi-list": ProgramConfig(
        key="multi-list",
        label="ScalarCountMultiIntSmoke add1MultiList",
        source=EXPERIMENT_SOURCE_DIR / "ScalarCountMultiIntSmoke.c",
        exe_stem="ScalarCountMultiIntSmoke",
        length_define="SCALAR_COUNT_MULTI_LIST_LEN",
        inner_iterations_define="SCALAR_COUNT_MULTI_BENCH_ITERS",
    ),
}


def run_command(cmd: list[str], *, cwd: Path, verbose: bool = False) -> subprocess.CompletedProcess[str]:
    if verbose:
        print("$ " + " ".join(cmd), flush=True)
    return subprocess.run(
        cmd,
        cwd=str(cwd),
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )


def benchmark_cpu_from_args(args: argparse.Namespace) -> int | None:
    if not args.pin_cpu:
        return None
    if args.cpu is not None:
        return args.cpu
    if hasattr(os, "sched_getaffinity"):
        return min(os.sched_getaffinity(0))
    return 0


def run_benchmark_command(cmd: list[str],
                          *,
                          cwd: Path,
                          cpu: int | None) -> subprocess.CompletedProcess[str]:
    preexec_fn = None
    if cpu is not None and hasattr(os, "sched_setaffinity"):
        def pin_child() -> None:
            os.sched_setaffinity(0, {cpu})
        preexec_fn = pin_child

    return subprocess.run(
        cmd,
        cwd=str(cwd),
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
        preexec_fn=preexec_fn,
    )


def require_file(path: Path, description: str) -> None:
    if not path.exists():
        raise SystemExit(f"Missing {description}: {path}")


def maybe_build_rts(args: argparse.Namespace) -> None:
    if not args.build_rts:
        return
    cmd = ["make", "-C", "gibbon-rts", f"GIBBONDIR={REPO_ROOT}"]
    proc = run_command(cmd, cwd=REPO_ROOT, verbose=args.verbose)
    if proc.returncode != 0:
        print(proc.stdout, end="")
        print(proc.stderr, end="", file=sys.stderr)
        raise SystemExit(f"RTS build failed with exit code {proc.returncode}")


def compile_variant(args: argparse.Namespace,
                    build: BuildConfig,
                    program: ProgramConfig) -> Path:
    cc = args.cc or os.environ.get("CC") or "gcc"
    out = args.build_dir / f"{program.exe_stem}_{build.key}_{os.getpid()}.exe"
    rts_build = REPO_ROOT / "gibbon-rts" / "build"
    uthash = REPO_ROOT / "deps" / "uthash"

    require_file(args.source, f"{program.label} C source")
    require_file(rts_build / "gibbon_rts.h", "RTS header")
    require_file(rts_build / "libgibbon_rts.a", "C RTS archive")
    require_file(rts_build / "libgibbon_rts_ng.so", "Rust RTS shared library")
    require_file(uthash / "uthash.h", "uthash header")

    args.build_dir.mkdir(parents=True, exist_ok=True)

    cmd = [
        cc,
        "-std=gnu11",
        *build.flags,
        *((
            f"-D{program.length_define}={args.list_len}",
        ) if args.list_len is not None else ()),
        *((
            f"-D{program.inner_iterations_define}={args.inner_iterations}",
        ) if (
            program.inner_iterations_define is not None and
            args.inner_iterations is not None
        ) else ()),
        *((
            f"-D{program.int_only_repeats_define}={args.int_only_repeats}",
        ) if (
            program.int_only_repeats_define is not None and
            args.int_only_repeats is not None
        ) else ()),
        "-I",
        str(rts_build),
        "-I",
        str(uthash),
        str(args.source),
        str(rts_build / "libgibbon_rts.a"),
        "-L",
        str(rts_build),
        f"-Wl,-rpath,{rts_build}",
        "-lgibbon_rts_ng",
        "-lm",
        "-ldl",
        "-lpthread",
        "-o",
        str(out),
    ]
    proc = run_command(cmd, cwd=REPO_ROOT, verbose=args.verbose)
    if proc.returncode != 0:
        print(proc.stdout, end="")
        print(proc.stderr, end="", file=sys.stderr)
        raise SystemExit(f"Compile failed for {build.label} with exit code {proc.returncode}")
    if args.verbose and proc.stderr:
        print(proc.stderr, end="", file=sys.stderr)
    return out


def parse_run_output(output: str) -> dict[str, float | bool]:
    parsed: dict[str, float | bool] = {}
    for line in output.splitlines():
        if "=" not in line:
            continue
        key, value = line.strip().split("=", 1)
        if key == "sums_match":
            parsed[key] = value == "yes"
        elif key.endswith(("_seconds", "_ns_per_element")):
            try:
                parsed[key] = float(value)
            except ValueError:
                pass
        elif key.endswith(("_calls", "_elements")):
            try:
                parsed[key] = float(value)
            except ValueError:
                pass
    return parsed


def hot_loop_metric_keys(program: ProgramConfig, build: BuildConfig) -> list[str]:
    prefixes: list[str] = []

    if program.key == "list":
        prefixes.extend(prefix for prefix, _ in list_hot_loop_prefixes(build))
    elif program.key == "multi-list":
        prefixes.extend(prefix for prefix, _ in multi_list_hot_loop_total_prefixes(build))
        for field_ix in range(4):
            prefixes.extend([
                f"loop_scalar_hot_loop_field{field_ix}",
                f"indir_loop_scalar_hot_loop_field{field_ix}",
                f"indir_loop_auto_hot_loop_field{field_ix}",
                f"indir_loop_vectorized_hot_loop_field{field_ix}",
            ])

    return [
        f"{prefix}_{suffix}"
        for prefix in prefixes
        for suffix in HOT_LOOP_SUFFIXES
    ]


def hot_loop_sweep_series(program: ProgramConfig,
                          build: BuildConfig) -> list[tuple[str, str, str, str]]:
    if program.key == "list":
        return [
            (
                "Indirection auto-vector hot loop / scalar hot loop",
                "#9467bd",
                "indir_loop_scalar_hot_loop_seconds",
                "indir_loop_auto_hot_loop_seconds",
            ),
            (
                f"Indirection {manual_simd_name(build)} hot loop / scalar hot loop",
                "#d62728",
                "indir_loop_scalar_hot_loop_seconds",
                "indir_loop_vectorized_hot_loop_seconds",
            ),
        ]

    if program.key == "multi-list":
        return [
            (
                "Indirection auto-vector hot loops / scalar hot loops",
                "#9467bd",
                "indir_loop_scalar_hot_loop_total_seconds",
                "indir_loop_auto_hot_loop_total_seconds",
            ),
            (
                f"Indirection {manual_simd_name(build)} hot loops / scalar hot loops",
                "#d62728",
                "indir_loop_scalar_hot_loop_total_seconds",
                "indir_loop_vectorized_hot_loop_total_seconds",
            ),
        ]

    return []


def runtime_sweep_series(build: BuildConfig) -> list[tuple[str, str, str]]:
    return [
        ("Recursive add1", "#7f7f7f", "recursive"),
        ("Loopified add1, copy dead buffers, vectorization off", "#1f77b4", "loop_scalar_copy"),
        ("Loopified add1, dead-buffer indirections, vectorization off", "#2ca02c", "indir_loop_scalar"),
        ("Loopified add1, dead-buffer indirections, auto-vectorized", "#9467bd", "indir_loop_auto"),
        (variant_display_label(build, "indir_loop_explicit_vector",
                               "Loopified add1, dead-buffer indirections, manual SSE2 vectorized"),
         "#d62728",
         "indir_loop_explicit_vector"),
    ]


def run_benchmark(args: argparse.Namespace,
                  exe: Path,
                  build: BuildConfig,
                  program: ProgramConfig) -> dict[str, object]:
    all_variants = [*VARIANTS]
    if program.int_only_repeats_define is not None and args.int_only_repeats is not None:
        all_variants.extend(INT_ONLY_VARIANTS)
    samples: dict[str, list[float]] = {key: [] for key, _, _ in all_variants}
    hot_loop_keys = hot_loop_metric_keys(program, build)
    hot_loop_samples: dict[str, list[float]] = {key: [] for key in hot_loop_keys}
    sums_ok = 0
    failures = 0
    exe_cmd = [str(exe)]
    benchmark_cpu = benchmark_cpu_from_args(args)
    if args.inf_buffer_size is not None:
        exe_cmd.extend(["--inf-buffer-size", str(args.inf_buffer_size)])

    for i in range(args.iterations):
        proc = run_benchmark_command(exe_cmd, cwd=REPO_ROOT, cpu=benchmark_cpu)
        output = proc.stdout + proc.stderr
        if proc.returncode != 0:
            failures += 1
            if args.verbose:
                print(output, end="")
            continue

        parsed = parse_run_output(output)
        if parsed.get("sums_match") is True:
            sums_ok += 1
        else:
            failures += 1
            if args.verbose:
                print(output, end="")

        for key, _, output_key in all_variants:
            value = parsed.get(output_key)
            if isinstance(value, float):
                samples[key].append(value)
        for output_key in hot_loop_keys:
            value = parsed.get(output_key)
            if isinstance(value, float):
                hot_loop_samples[output_key].append(value)

        if args.progress and (i + 1) % args.progress == 0:
            print(
                f"{program.label} / {build.label}: "
                f"completed {i + 1}/{args.iterations}",
                flush=True,
            )

    averages = {
        key: median(vals) if vals else float("nan")
        for key, vals in samples.items()
    }
    return {
        "build": build,
        "averages": averages,
        "hot_loop_averages": {
            key: median(vals) if vals else float("nan")
            for key, vals in hot_loop_samples.items()
        },
        "runs": args.iterations,
        "sums_ok": sums_ok,
        "failures": failures,
        "cpu": benchmark_cpu,
    }


def fmt_seconds(value: float) -> str:
    if value != value:
        return "n/a"
    return f"{value:.9f}"


def fmt_speedup(value: float) -> str:
    if value != value:
        return "n/a"
    return f"{value:.3f}x"


def fmt_ns_per_element(value: float) -> str:
    if value != value:
        return "n/a"
    return f"{value:.3f}"


def fmt_count(value: float) -> str:
    if value != value:
        return "n/a"
    return f"{int(round(value))}"


def markdown_table(headers: list[str], rows: list[list[str]]) -> str:
    widths = [
        max(len(headers[i]), *(len(row[i]) for row in rows))
        for i in range(len(headers))
    ]

    def render(row: list[str]) -> str:
        return "| " + " | ".join(row[i].ljust(widths[i]) for i in range(len(row))) + " |"

    sep = "| " + " | ".join("-" * widths[i] for i in range(len(headers))) + " |"
    return "\n".join([render(headers), sep, *(render(row) for row in rows)])


def parse_sizes(value: str) -> list[int]:
    return [int(x.strip()) for x in value.split(",") if x.strip()]


def range_sweep_sizes(start: int, step: int, max_size: int) -> list[int]:
    sizes = list(range(start, max_size + 1, step))
    if not sizes or sizes[-1] != max_size:
        sizes.append(max_size)
    return sizes


def sweep_sizes_from_args(args: argparse.Namespace) -> list[int]:
    range_args = [args.sweep_start, args.sweep_step, args.sweep_max]
    if any(value is not None for value in range_args):
        if args.sweep_sizes is not None:
            raise SystemExit(
                "--sweep-sizes cannot be used together with "
                "--sweep-start/--sweep-step/--sweep-max"
            )
        if any(value is None for value in range_args):
            raise SystemExit(
                "--sweep-start, --sweep-step, and --sweep-max must be "
                "provided together"
            )
        return range_sweep_sizes(args.sweep_start, args.sweep_step, args.sweep_max)

    if args.sweep_sizes is None:
        return [*DEFAULT_SWEEP_SIZES]
    return parse_sizes(args.sweep_sizes)


def svg_polyline(points: list[tuple[float, float]], color: str, width: int = 3) -> str:
    pts = " ".join(f"{x:.1f},{y:.1f}" for x, y in points)
    return (
        f'<polyline points="{pts}" fill="none" stroke="{color}" '
        f'stroke-width="{width}" stroke-linejoin="round" stroke-linecap="round"/>'
    )


def compact_size_label(n: int) -> str:
    def compact(value: float, suffix: str) -> str:
        text = f"{value:.1f}".rstrip("0").rstrip(".")
        return f"{text}{suffix}"

    if n < 1_000:
        return str(n)
    if n < 1_000_000:
        if n % 1_000 == 0:
            return f"{n // 1_000}k"
        return compact(n / 1_000, "k")
    if n < 1_000_000_000:
        if n % 1_000_000 == 0:
            return f"{n // 1_000_000}M"
        return compact(n / 1_000_000, "M")
    if n % 1_000_000_000 == 0:
        return f"{n // 1_000_000_000}B"
    return compact(n / 1_000_000_000, "B")


def sanitize_path_part(value: str) -> str:
    cleaned = "".join(ch if ch.isalnum() or ch in "._-" else "_" for ch in value)
    return cleaned.strip("._-") or "run"


def sweep_size_label(sizes: list[int]) -> str:
    ordered = sorted(sizes)
    if len(ordered) == 1:
        return f"len{ordered[0]}"
    return f"len{ordered[0]}-{ordered[-1]}_points{len(ordered)}"


def default_sweep_output_base(args: argparse.Namespace,
                              program: ProgramConfig,
                              build: BuildConfig,
                              sizes: list[int]) -> Path:
    now = datetime.now()
    stamp = now.strftime("%H%M%S_%f")
    date = now.strftime("%Y-%m-%d")
    parts = [
        stamp,
        program.key,
        build.key,
        f"n{args.iterations}",
        sweep_size_label(sizes),
    ]
    if args.inf_buffer_size is not None:
        parts.append(f"buf{args.inf_buffer_size}")
    if args.inner_iterations is not None:
        parts.append(f"inner{args.inner_iterations}")
    if args.sweep_seed is not None:
        parts.append(f"seed{args.sweep_seed}")
    run_name = sanitize_path_part("_".join(parts))
    return DEFAULT_RESULTS_DIR / date / run_name / run_name


def log_axis_ticks(sizes: list[int], max_ticks: int = 10) -> list[int]:
    min_size = min(sizes)
    max_size = max(sizes)
    if min_size == max_size:
        return [min_size]

    min_pow = math.floor(math.log10(min_size))
    max_pow = math.ceil(math.log10(max_size))
    dense_ticks: list[int] = []
    for power in range(min_pow, max_pow + 1):
        for multiplier in (1, 2, 5):
            tick = multiplier * (10 ** power)
            if min_size <= tick <= max_size:
                dense_ticks.append(tick)

    dense_ticks = sorted(set([min_size, max_size, *dense_ticks]))
    if len(dense_ticks) <= max_ticks:
        return dense_ticks

    decade_ticks = [
        10 ** power
        for power in range(min_pow, max_pow + 1)
        if min_size <= 10 ** power <= max_size
    ]
    decade_ticks = sorted(set([min_size, max_size, *decade_ticks]))
    if len(decade_ticks) <= max_ticks:
        return decade_ticks

    tick_set = {min_size, max_size}
    for i in range(1, max_ticks - 1):
        target = min_pow + (i / (max_ticks - 1)) * (max_pow - min_pow)
        tick_set.add(int(round(10 ** target)))
    return sorted(tick for tick in tick_set if min_size <= tick <= max_size)


def coefficient_of_variation(values: list[float]) -> float:
    if len(values) < 2:
        return 0.0
    avg = sum(values) / len(values)
    if avg == 0.0:
        return float("inf")
    variance = sum((value - avg) ** 2 for value in values) / len(values)
    return math.sqrt(variance) / avg


def choose_x_axis_scale(sizes: list[int]) -> str:
    ordered = sorted(set(sizes))
    if len(ordered) <= 2:
        return "linear"

    diffs = [float(b - a) for a, b in zip(ordered, ordered[1:])]
    diff_cv = coefficient_of_variation(diffs)
    if diff_cv <= 0.20:
        return "linear"

    if ordered[0] > 0:
        ratios = [float(b) / float(a) for a, b in zip(ordered, ordered[1:]) if a > 0]
        ratio_cv = coefficient_of_variation(ratios)
        if ratio_cv <= 0.20:
            return "log"

    span_ratio = float(ordered[-1]) / float(max(ordered[0], 1))
    return "log" if span_ratio >= 100.0 else "linear"


def linear_axis_ticks(sizes: list[int], max_ticks: int = 8) -> list[int]:
    min_size = min(sizes)
    max_size = max(sizes)
    if min_size == max_size:
        return [min_size]

    raw_step = (max_size - min_size) / max(1, max_ticks - 1)
    magnitude = 10 ** math.floor(math.log10(raw_step))

    step = magnitude
    for multiplier in (1, 2, 2.5, 5, 10):
        candidate = multiplier * magnitude
        if (max_size - min_size) / candidate <= max_ticks - 1:
            step = candidate
            break

    tick_set = {min_size, max_size}
    tick = math.ceil(min_size / step) * step
    while tick < max_size:
        tick_set.add(int(round(tick)))
        tick += step

    return sorted(tick_set)


def axis_ticks_for_scale(sizes: list[int], scale: str) -> list[int]:
    if scale == "linear":
        return linear_axis_ticks(sizes)
    return log_axis_ticks(sizes)


def write_sweep_csv(rows: list[SweepRow], path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow([
            "list_len",
            "recursive_seconds",
            "loop_scalar_copy_seconds",
            "indir_loop_scalar_seconds",
            "indir_loop_auto_seconds",
            "indir_loop_explicit_vector_seconds",
            "loop_scalar_copy_speedup_vs_recursive",
            "indir_loop_scalar_speedup_vs_recursive",
            "indir_loop_auto_speedup_vs_recursive",
            "indir_loop_explicit_vector_speedup_vs_recursive",
        ])
        for row in rows:
            writer.writerow([
                row.list_len,
                f"{row.averages['recursive']:.9f}",
                f"{row.averages['loop_scalar_copy']:.9f}",
                f"{row.averages['indir_loop_scalar']:.9f}",
                f"{row.averages['indir_loop_auto']:.9f}",
                f"{row.averages['indir_loop_explicit_vector']:.9f}",
                f"{row.speedup_vs_recursive('loop_scalar_copy'):.6f}",
                f"{row.speedup_vs_recursive('indir_loop_scalar'):.6f}",
                f"{row.speedup_vs_recursive('indir_loop_auto'):.6f}",
                f"{row.speedup_vs_recursive('indir_loop_explicit_vector'):.6f}",
            ])


def write_hot_loop_sweep_csv(rows: list[SweepRow],
                             path: Path,
                             program: ProgramConfig,
                             build: BuildConfig) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    series = hot_loop_sweep_series(program, build)
    with path.open("w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow([
            "list_len",
            *[
                item
                for _label, _color, scalar_key, vector_key in series
                for item in (
                    scalar_key,
                    vector_key,
                    f"{vector_key}_speedup_vs_scalar",
                )
            ],
        ])
        for row in rows:
            writer.writerow([
                row.list_len,
                *[
                    item
                    for _label, _color, scalar_key, vector_key in series
                    for item in (
                        f"{row.hot_loop_averages[scalar_key]:.9f}",
                        f"{row.hot_loop_averages[vector_key]:.9f}",
                        f"{row.hot_loop_speedup(scalar_key, vector_key):.6f}",
                    )
                ],
            ])


def write_runtime_sweep_csv(rows: list[SweepRow],
                            path: Path,
                            build: BuildConfig) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    series = runtime_sweep_series(build)
    with path.open("w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow([
            "list_len",
            *[f"{key}_seconds" for _label, _color, key in series],
        ])
        for row in rows:
            writer.writerow([
                row.list_len,
                *[f"{row.averages[key]:.9f}" for _label, _color, key in series],
            ])


def write_sweep_svg(rows: list[SweepRow],
                    path: Path,
                    program: ProgramConfig,
                    build: BuildConfig,
                    inf_buffer_size: int | None) -> None:
    series = [
        (
            "Copy scalar / recursive",
            "#1f77b4",
            [row.speedup_vs_recursive("loop_scalar_copy") for row in rows],
        ),
        (
            "Indirection scalar / recursive",
            "#2ca02c",
            [row.speedup_vs_recursive("indir_loop_scalar") for row in rows],
        ),
        (
            "Indirection auto-vector / recursive",
            "#9467bd",
            [row.speedup_vs_recursive("indir_loop_auto") for row in rows],
        ),
        (
            f"Indirection {manual_simd_name(build)} / recursive",
            "#d62728",
            [row.speedup_vs_recursive("indir_loop_explicit_vector") for row in rows],
        ),
    ]
    write_speedup_svg(
        rows,
        path,
        title=f"{program.label} Speedups by Input Size ({manual_simd_name(build)})",
        y_axis_label="Speedup vs recursive",
        series=series,
        reference_lines=[
            ("Baseline 1.0x", 1.0, "#d62728", None),
        ],
        build=build,
        inf_buffer_size=inf_buffer_size,
    )


def write_hot_loop_sweep_svg(rows: list[SweepRow],
                             path: Path,
                             program: ProgramConfig,
                             build: BuildConfig,
                             inf_buffer_size: int | None) -> None:
    series = [
        (
            label,
            color,
            [row.hot_loop_speedup(scalar_key, vector_key) for row in rows],
        )
        for label, color, scalar_key, vector_key in hot_loop_sweep_series(program, build)
    ]
    theoretical_max = 4.0 if build.key == "avx2" else 2.0
    write_speedup_svg(
        rows,
        path,
        title=f"{program.label} Hot Loop Speedups by Input Size ({manual_simd_name(build)})",
        y_axis_label="Hot loop speedup vs scalar",
        series=series,
        reference_lines=[
            ("Baseline 1.0x", 1.0, "#d62728", None),
            (f"Theoretical max {theoretical_max:.1f}x", theoretical_max, "#ff7f0e", "8 6"),
        ],
        build=build,
        inf_buffer_size=inf_buffer_size,
    )


def write_runtime_sweep_svg(rows: list[SweepRow],
                            path: Path,
                            program: ProgramConfig,
                            build: BuildConfig,
                            inf_buffer_size: int | None) -> None:
    series = [
        (label, color, [1000.0 * row.averages[key] for row in rows])
        for label, color, key in runtime_sweep_series(build)
    ]
    write_series_svg(
        rows,
        path,
        title=f"{program.label} Runtimes by Input Size ({manual_simd_name(build)})",
        y_axis_label="Median runtime (ms)",
        series=series,
        reference_lines=[],
        build=build,
        inf_buffer_size=inf_buffer_size,
        y_bottom=0.0,
        y_tick_label_fn=lambda y: f"{y:.2f} ms",
    )


def write_speedup_svg(rows: list[SweepRow],
                      path: Path,
                      title: str,
                      y_axis_label: str,
                      series: list[tuple[str, str, list[float]]],
                      reference_lines: list[tuple[str, float, str, str | None]],
                      build: BuildConfig,
                      inf_buffer_size: int | None) -> None:
    write_series_svg(
        rows,
        path,
        title=title,
        y_axis_label=y_axis_label,
        series=series,
        reference_lines=reference_lines,
        build=build,
        inf_buffer_size=inf_buffer_size,
        y_bottom=0.0,
        y_tick_label_fn=lambda y: f"{y:.1f}x",
    )


def write_series_svg(rows: list[SweepRow],
                     path: Path,
                     title: str,
                     y_axis_label: str,
                     series: list[tuple[str, str, list[float]]],
                     reference_lines: list[tuple[str, float, str, str | None]],
                     build: BuildConfig,
                     inf_buffer_size: int | None,
                     y_bottom: float,
                     y_tick_label_fn) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    width = 1180
    height = 760
    sizes = [row.list_len for row in rows]
    x_scale_mode = choose_x_axis_scale(sizes)
    x_ticks = axis_ticks_for_scale(sizes, x_scale_mode)
    rotate_x_labels = len(rows) > len(x_ticks) or len(x_ticks) > 6
    margin_left = 92
    margin_right = 350
    margin_top = 58
    margin_bottom = 122 if rotate_x_labels else 84
    plot_w = width - margin_left - margin_right
    plot_h = height - margin_top - margin_bottom

    if x_scale_mode == "linear":
        min_x_value = float(min(sizes))
        max_x_value = float(max(sizes))
        if max_x_value > min_x_value:
            x_pad = 0.03 * (max_x_value - min_x_value)
            min_x_value = max(0.0, min_x_value - x_pad)
            max_x_value = max_x_value + x_pad
    else:
        min_x_value = math.log10(min(sizes))
        max_x_value = math.log10(max(sizes))
        if max_x_value > min_x_value:
            x_pad = 0.03 * (max_x_value - min_x_value)
            min_x_value -= x_pad
            max_x_value += x_pad
    max_series_y = max(max(vals) for _, _, vals in series) if series else y_bottom
    max_reference_y = (
        max((value for _label, value, _color, _dash in reference_lines), default=y_bottom)
    )
    max_y = max(max_series_y, max_reference_y)
    y_top = max(1.0, math.ceil((max_y + 0.20) * 10) / 10)

    def xscale(n: int) -> float:
        if max_x_value == min_x_value:
            return margin_left + plot_w / 2
        x_value = float(n) if x_scale_mode == "linear" else math.log10(n)
        return margin_left + ((x_value - min_x_value) / (max_x_value - min_x_value)) * plot_w

    def yscale(v: float) -> float:
        return margin_top + (1.0 - ((v - y_bottom) / (y_top - y_bottom))) * plot_h

    parts: list[str] = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">',
        '<rect width="100%" height="100%" fill="white"/>',
        '<style>text{font-family:Arial,Helvetica,sans-serif;fill:#202124} .small{font-size:13px} .axis{font-size:14px} .title{font-size:24px;font-weight:700}</style>',
        f'<text x="{margin_left}" y="34" class="title">{title}</text>',
        f'<rect x="{margin_left}" y="{margin_top}" width="{plot_w}" height="{plot_h}" fill="#fbfbfd" stroke="#c7c7cc"/>',
    ]

    y_step = 0.5 if y_top <= 8 else 1.0
    y = y_bottom
    while y <= y_top + 1e-9:
        py = yscale(y)
        stroke = "#b8b8c0" if abs(y - round(y)) < 1e-9 else "#d8d8dd"
        parts.append(
            f'<line x1="{margin_left}" y1="{py:.1f}" '
            f'x2="{margin_left + plot_w}" y2="{py:.1f}" '
            f'stroke="{stroke}" stroke-width="1"/>'
        )
        parts.append(
            f'<text x="{margin_left - 12}" y="{py + 4:.1f}" '
            f'text-anchor="end" class="small">{y_tick_label_fn(y)}</text>'
        )
        y += y_step

    for _label, value, color, dasharray in reference_lines:
        ref_y = yscale(value)
        dash_attr = f' stroke-dasharray="{dasharray}"' if dasharray is not None else ""
        parts.append(
            f'<line x1="{margin_left}" y1="{ref_y:.1f}" '
            f'x2="{margin_left + plot_w}" y2="{ref_y:.1f}" '
            f'stroke="{color}" stroke-width="2"{dash_attr}/>'
        )

    for tick in x_ticks:
        px = xscale(tick)
        parts.append(
            f'<line x1="{px:.1f}" y1="{margin_top}" '
            f'x2="{px:.1f}" y2="{margin_top + plot_h}" '
            f'stroke="#ececf1" stroke-width="1"/>'
        )
        label = compact_size_label(tick)
        label_y = margin_top + plot_h + (64 if rotate_x_labels else 24)
        if rotate_x_labels:
            parts.append(
                f'<text x="{px:.1f}" y="{label_y:.1f}" text-anchor="end" '
                f'class="small" transform="rotate(-45 {px:.1f} {label_y:.1f})">{label}</text>'
            )
        else:
            parts.append(
                f'<text x="{px:.1f}" y="{label_y:.1f}" '
                f'text-anchor="middle" class="small">{label}</text>'
            )

    parts.append(
        f'<text x="{margin_left + plot_w / 2:.1f}" y="{height - 22}" '
        f'text-anchor="middle" class="axis">Input size ({x_scale_mode} scale)</text>'
    )
    parts.append(
        f'<text x="26" y="{margin_top + plot_h / 2:.1f}" text-anchor="middle" '
        f'class="axis" transform="rotate(-90 26 {margin_top + plot_h / 2:.1f})">{y_axis_label}</text>'
    )

    for name, color, vals in series:
        pts = [(xscale(row.list_len), yscale(val)) for row, val in zip(rows, vals)]
        parts.append(svg_polyline(pts, color))
        marker_step = max(1, math.ceil(len(pts) / 40))
        for i, (px, py) in enumerate(pts):
            if len(pts) > 80 and i not in (0, len(pts) - 1) and i % marker_step != 0:
                continue
            parts.append(
                f'<circle cx="{px:.1f}" cy="{py:.1f}" r="4" '
                f'fill="{color}" stroke="white" stroke-width="1.5"/>'
            )

    legend_x = margin_left + plot_w + 34
    legend_y = margin_top + 18
    for i, (name, color, _vals) in enumerate(series):
        y = legend_y + i * 34
        parts.append(
            f'<line x1="{legend_x}" y1="{y}" x2="{legend_x + 32}" y2="{y}" '
            f'stroke="{color}" stroke-width="4" stroke-linecap="round"/>'
        )
        parts.append(f'<text x="{legend_x + 44}" y="{y + 5}" class="small">{name}</text>')

    reference_legend_start_y = legend_y + len(series) * 34
    for i, (label, _value, color, dasharray) in enumerate(reference_lines):
        ref_y = reference_legend_start_y + i * 34
        dash_attr = f' stroke-dasharray="{dasharray}"' if dasharray is not None else ""
        parts.append(
            f'<line x1="{legend_x}" y1="{ref_y}" '
            f'x2="{legend_x + 32}" y2="{ref_y}" '
            f'stroke="{color}" stroke-width="3" stroke-linecap="round"{dash_attr}/>'
        )
        parts.append(
            f'<text x="{legend_x + 44}" y="{ref_y + 5}" class="small">{label}</text>'
        )

    parts.append(f'<text x="{legend_x}" y="{height - 140}" class="small">Points: {len(rows)}</text>')
    parts.append(f'<text x="{legend_x}" y="{height - 118}" class="small">Max input: {compact_size_label(max(sizes))}</text>')
    parts.append(f'<text x="{legend_x}" y="{height - 96}" class="small">Build: {build.label}</text>')
    parts.append(f'<text x="{legend_x}" y="{height - 74}" class="small">X scale: {x_scale_mode}</text>')
    chunk_label = (
        f"{inf_buffer_size:,} bytes"
        if inf_buffer_size is not None
        else "executable default"
    )
    parts.append(f'<text x="{legend_x}" y="{height - 52}" class="small">Chunk size: {chunk_label}</text>')
    parts.append("</svg>")
    path.write_text("\n".join(parts))


def print_report(results: list[dict[str, object]],
                 program: ProgramConfig,
                 inf_buffer_size: int | None) -> None:
    labels = {result["build"].key: result["build"].label for result in results}  # type: ignore[index,union-attr]
    chunk_label = (
        f"{inf_buffer_size:,} bytes"
        if inf_buffer_size is not None
        else "executable default"
    )

    print(f"\n# {program.label} Benchmark\n")
    print(f"- Chunk size: {chunk_label}")
    for result in results:
        build: BuildConfig = result["build"]  # type: ignore[assignment]
        cpu_label = (
            result["cpu"]
            if result["cpu"] is not None
            else "not pinned"
        )
        print(
            f"- {build.label}: runs={result['runs']} sums_ok={result['sums_ok']} "
            f"failures={result['failures']} cpu={cpu_label}"
        )
    print()

    for result in results:
        build: BuildConfig = result["build"]  # type: ignore[assignment]
        avgs = result["averages"]  # type: ignore[assignment]
        hot_loop_avgs = result["hot_loop_averages"]  # type: ignore[assignment]
        rec = avgs["recursive"]
        rows = []
        for key, label, _ in VARIANTS:
            rows.append([
                variant_display_label(build, key, label),
                fmt_seconds(avgs[key]),
                fmt_speedup(rec / avgs[key]),
            ])
        print(f"## {labels[build.key]}\n")
        print(markdown_table(["Variant", "Median seconds", "Speedup vs recursive"], rows))
        print()

        rows = [
            [
                "Copy loop scalar over recursive",
                fmt_speedup(rec / avgs["loop_scalar_copy"]),
            ],
            [
                "Indirection scalar over copy scalar",
                fmt_speedup(avgs["loop_scalar_copy"] / avgs["indir_loop_scalar"]),
            ],
            [
                "Indirection scalar over recursive",
                fmt_speedup(rec / avgs["indir_loop_scalar"]),
            ],
            [
                "Indirection auto-vector over indirection scalar",
                fmt_speedup(avgs["indir_loop_scalar"] / avgs["indir_loop_auto"]),
            ],
            [
                f"Indirection {manual_simd_name(build)} vector over indirection scalar",
                fmt_speedup(avgs["indir_loop_scalar"] / avgs["indir_loop_explicit_vector"]),
            ],
            [
                f"Indirection {manual_simd_name(build)} vector over recursive",
                fmt_speedup(rec / avgs["indir_loop_explicit_vector"]),
            ],
            [
                f"Indirection {manual_simd_name(build)} vector over indirection auto-vector",
                fmt_speedup(avgs["indir_loop_auto"] / avgs["indir_loop_explicit_vector"]),
            ],
        ]
        print("## POC Comparisons\n")
        print(markdown_table(["Comparison", "Speedup"], rows))
        print()

        if program.key == "list":
            hot_rows = []
            for prefix, label in list_hot_loop_prefixes(build):
                hot_rows.append([
                    label,
                    fmt_seconds(hot_loop_avgs[f"{prefix}_seconds"]),
                    fmt_ns_per_element(hot_loop_avgs[f"{prefix}_ns_per_element"]),
                    fmt_count(hot_loop_avgs[f"{prefix}_calls"]),
                    fmt_count(hot_loop_avgs[f"{prefix}_elements"]),
                ])
            print("## Hot Loop Timings\n")
            print(
                markdown_table(
                    ["Loop", "Median seconds", "Median ns/elem", "Median calls", "Median elems"],
                    hot_rows,
                )
            )
            print()

            scalar_hot = hot_loop_avgs["indir_loop_scalar_hot_loop_seconds"]
            hot_speedup_rows = [
                [
                    "Indirection auto-vector hot loop over indirection scalar hot loop",
                    fmt_speedup(scalar_hot / hot_loop_avgs["indir_loop_auto_hot_loop_seconds"]),
                ],
                [
                    f"Indirection {manual_simd_name(build)} hot loop over indirection scalar hot loop",
                    fmt_speedup(scalar_hot / hot_loop_avgs["indir_loop_vectorized_hot_loop_seconds"]),
                ],
            ]
            print("## Hot Loop Comparisons\n")
            print(markdown_table(["Comparison", "Speedup"], hot_speedup_rows))
            print()

        elif program.key == "multi-list":
            hot_rows = []
            for prefix, label in multi_list_hot_loop_total_prefixes(build):
                hot_rows.append([
                    label,
                    fmt_seconds(hot_loop_avgs[f"{prefix}_seconds"]),
                    fmt_ns_per_element(hot_loop_avgs[f"{prefix}_ns_per_element"]),
                    fmt_count(hot_loop_avgs[f"{prefix}_calls"]),
                    fmt_count(hot_loop_avgs[f"{prefix}_elements"]),
                ])
            print("## Hot Loop Totals\n")
            print(
                markdown_table(
                    ["Loop family", "Median seconds", "Median ns/elem", "Median calls", "Median elems"],
                    hot_rows,
                )
            )
            print()

            scalar_hot = hot_loop_avgs["indir_loop_scalar_hot_loop_total_seconds"]
            hot_speedup_rows = [
                [
                    "Indirection auto-vector hot loops over indirection scalar hot loops",
                    fmt_speedup(
                        scalar_hot /
                        hot_loop_avgs["indir_loop_auto_hot_loop_total_seconds"]
                    ),
                ],
                [
                    f"Indirection {manual_simd_name(build)} hot loops over indirection scalar hot loops",
                    fmt_speedup(
                        scalar_hot /
                        hot_loop_avgs["indir_loop_vectorized_hot_loop_total_seconds"]
                    ),
                ],
            ]
            print("## Hot Loop Comparisons\n")
            print(markdown_table(["Comparison", "Speedup"], hot_speedup_rows))
            print()

            field_rows = []
            for field_ix in range(4):
                field_rows.append([
                    f"Field {field_ix}",
                    fmt_ns_per_element(
                        hot_loop_avgs[
                            f"indir_loop_scalar_hot_loop_field{field_ix}_ns_per_element"
                        ]
                    ),
                    fmt_ns_per_element(
                        hot_loop_avgs[
                            f"indir_loop_auto_hot_loop_field{field_ix}_ns_per_element"
                        ]
                    ),
                    fmt_ns_per_element(
                        hot_loop_avgs[
                            f"indir_loop_vectorized_hot_loop_field{field_ix}_ns_per_element"
                        ]
                    ),
                ])
            print("## Per-Field Hot Loop Ns/Elem\n")
            print(
                markdown_table(
                    ["Field", "Scalar", "Auto-vector", manual_simd_name(build)],
                    field_rows,
                )
            )
            print()


def run_sweep(args: argparse.Namespace,
              program: ProgramConfig,
              build: BuildConfig,
              sizes: list[int]) -> list[SweepRow]:
    rows: list[SweepRow] = []
    sweep_order = [*sizes]
    rng = random.Random(args.sweep_seed)
    rng.shuffle(sweep_order)

    if sweep_order != sizes:
        print(
            "Sweep order: " + ", ".join(str(size) for size in sweep_order),
            flush=True,
        )

    for size in sweep_order:
        size_args = argparse.Namespace(**vars(args))
        size_args.list_len = size
        exe = compile_variant(size_args, build, program)
        result = run_benchmark(size_args, exe, build, program)

        if result["failures"] != 0 or result["sums_ok"] != result["runs"]:
            raise SystemExit(
                f"sweep failed validation for {program.label}, list_len={size}: "
                f"runs={result['runs']} sums_ok={result['sums_ok']} "
                f"failures={result['failures']}"
            )

        avgs = result["averages"]  # type: ignore[assignment]
        hot_loop_avgs = result["hot_loop_averages"]  # type: ignore[assignment]
        row = SweepRow(list_len=size, averages=avgs, hot_loop_averages=hot_loop_avgs)
        rows.append(row)
        hot_loop_series = hot_loop_sweep_series(program, build)
        hot_loop_msg = ""
        if len(hot_loop_series) >= 2:
            auto_label, _auto_color, auto_scalar_key, auto_vector_key = hot_loop_series[0]
            sse_label, _sse_color, sse_scalar_key, sse_vector_key = hot_loop_series[1]
            hot_loop_msg = (
                f" hot-auto={row.hot_loop_speedup(auto_scalar_key, auto_vector_key):.3f}x"
                f" hot-{manual_simd_name(build).lower()}={row.hot_loop_speedup(sse_scalar_key, sse_vector_key):.3f}x"
            )
        print(
            f"{program.label}: size={size} "
            f"copy={row.speedup_vs_recursive('loop_scalar_copy'):.3f}x "
            f"indir-scalar={row.speedup_vs_recursive('indir_loop_scalar'):.3f}x "
            f"indir-auto={row.speedup_vs_recursive('indir_loop_auto'):.3f}x "
            f"indir-{manual_simd_name(build).lower()}={row.speedup_vs_recursive('indir_loop_explicit_vector'):.3f}x"
            f"{hot_loop_msg}",
            flush=True,
        )

    return sorted(rows, key=lambda row: row.list_len)


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Compile and benchmark a saved manual scalar-count C harness."
    )
    parser.add_argument(
        "--program",
        choices=sorted(PROGRAMS.keys()),
        default="list",
        help="Which saved C experiment to compile and benchmark.",
    )
    parser.add_argument(
        "--mode",
        choices=["benchmark", "sweep"],
        default="benchmark",
        help="Run one benchmark or sweep input sizes and emit graph files.",
    )
    parser.add_argument(
        "--source",
        type=Path,
        default=None,
        help="Override the saved C source for the selected program.",
    )
    parser.add_argument(
        "--list-len",
        type=int,
        default=None,
        help=(
            "Override the selected program's input length macro at compile time. "
            "Defaults to the value in the saved C source."
        ),
    )
    parser.add_argument(
        "--inf-buffer-size",
        type=int,
        default=None,
        help=(
            "Pass --inf-buffer-size to the generated executable. "
            "When omitted, the argument is not passed."
        ),
    )
    parser.add_argument(
        "--int-only-repeats",
        type=int,
        default=None,
        help=(
            "For --program list, compile in an int-array-only helper "
            "microbenchmark with this many repeats per executable run."
        ),
    )
    parser.add_argument(
        "--inner-iterations",
        type=int,
        default=None,
        help=(
            "For --program multi-list, override the C harness's inner timing "
            "iterations per executable run."
        ),
    )
    parser.add_argument("--iterations", "-n", type=int, default=100)
    parser.add_argument(
        "--pin-cpu",
        action=argparse.BooleanOptionalAction,
        default=True,
        help=(
            "Pin each benchmark executable run to one CPU. Enabled by default; "
            "use --no-pin-cpu to disable."
        ),
    )
    parser.add_argument(
        "--cpu",
        type=int,
        default=None,
        help=(
            "CPU id to pin benchmark executable runs to. Defaults to the first "
            "CPU available to this process."
        ),
    )
    parser.add_argument(
        "--sweep-sizes",
        default=None,
        help=(
            "Comma-separated input sizes for --mode sweep. Uses the built-in "
            "default sizes unless --sweep-start/--sweep-step/--sweep-max are used."
        ),
    )
    parser.add_argument(
        "--sweep-start",
        type=int,
        default=None,
        help=(
            "First input size for range-based --mode sweep. Must be used with "
            "--sweep-step and --sweep-max."
        ),
    )
    parser.add_argument(
        "--sweep-step",
        type=int,
        default=None,
        help=(
            "Input-size step for range-based --mode sweep. Must be used with "
            "--sweep-start and --sweep-max."
        ),
    )
    parser.add_argument(
        "--sweep-max",
        type=int,
        default=None,
        help=(
            "Maximum input size for range-based --mode sweep. The maximum is "
            "included even when the step does not land on it exactly."
        ),
    )
    parser.add_argument(
        "--sweep-seed",
        type=int,
        default=None,
        help=(
            "Seed for randomized sweep execution order. Omit for a fresh random "
            "order each run."
        ),
    )
    parser.add_argument(
        "--sweep-csv",
        type=Path,
        default=None,
        help="CSV output path for --mode sweep.",
    )
    parser.add_argument(
        "--sweep-svg",
        type=Path,
        default=None,
        help="SVG graph output path for --mode sweep.",
    )
    parser.add_argument(
        "--hot-loop-sweep-csv",
        type=Path,
        default=None,
        help="CSV output path for the hot-loop speedup sweep in --mode sweep.",
    )
    parser.add_argument(
        "--hot-loop-sweep-svg",
        type=Path,
        default=None,
        help="SVG output path for the hot-loop speedup sweep in --mode sweep.",
    )
    parser.add_argument(
        "--runtime-sweep-csv",
        type=Path,
        default=None,
        help="CSV output path for the runtime sweep in --mode sweep.",
    )
    parser.add_argument(
        "--runtime-sweep-svg",
        type=Path,
        default=None,
        help="SVG output path for the runtime sweep in --mode sweep.",
    )
    parser.add_argument("--build-dir", type=Path, default=DEFAULT_BUILD_DIR)
    parser.add_argument("--cc", default=None, help="C compiler to use, defaults to $CC or gcc")
    parser.add_argument(
        "--use-avx2",
        action="store_true",
        help="Compile and run the manual SIMD backend with AVX2 instead of SSE2.",
    )
    parser.add_argument(
        "--build",
        choices=["sse2", "avx2", "poc"],
        default="sse2",
        help="Which binary to compile and run. `poc` is an alias for `sse2`; `--use-avx2` also selects the AVX2 backend.",
    )
    parser.add_argument(
        "--build-rts",
        action="store_true",
        help="Run make -C gibbon-rts before compiling the smoke benchmark.",
    )
    parser.add_argument("--progress", type=int, default=0, help="Print progress every N runs.")
    parser.add_argument("--verbose", "-v", action="store_true")
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    program = PROGRAMS[args.program]
    if args.source is None:
        args.source = program.source
    args.source = args.source.resolve()
    args.build_dir = args.build_dir.resolve()

    if args.iterations <= 0:
        raise SystemExit("--iterations must be positive")
    if args.cpu is not None and args.cpu < 0:
        raise SystemExit("--cpu must be non-negative")
    if args.pin_cpu and not hasattr(os, "sched_setaffinity"):
        raise SystemExit("--pin-cpu requires os.sched_setaffinity; pass --no-pin-cpu to disable")
    if args.pin_cpu and args.cpu is not None and hasattr(os, "sched_getaffinity"):
        allowed_cpus = os.sched_getaffinity(0)
        if args.cpu not in allowed_cpus:
            allowed = ",".join(str(cpu) for cpu in sorted(allowed_cpus))
            raise SystemExit(f"--cpu {args.cpu} is not in this process's allowed CPU set: {allowed}")
    if args.list_len is not None and args.list_len <= 0:
        raise SystemExit("--list-len must be positive")
    if args.inf_buffer_size is not None and args.inf_buffer_size <= 0:
        raise SystemExit("--inf-buffer-size must be positive")
    if args.int_only_repeats is not None and args.int_only_repeats <= 0:
        raise SystemExit("--int-only-repeats must be positive")
    if args.inner_iterations is not None and args.inner_iterations <= 0:
        raise SystemExit("--inner-iterations must be positive")
    if args.sweep_start is not None and args.sweep_start <= 0:
        raise SystemExit("--sweep-start must be positive")
    if args.sweep_step is not None and args.sweep_step <= 0:
        raise SystemExit("--sweep-step must be positive")
    if args.sweep_max is not None and args.sweep_max <= 0:
        raise SystemExit("--sweep-max must be positive")
    if (
        args.sweep_start is not None and
        args.sweep_max is not None and
        args.sweep_start > args.sweep_max
    ):
        raise SystemExit("--sweep-start must be less than or equal to --sweep-max")
    if args.int_only_repeats is not None and program.int_only_repeats_define is None:
        raise SystemExit("--int-only-repeats is only supported with --program list")
    if args.inner_iterations is not None and program.inner_iterations_define is None:
        raise SystemExit("--inner-iterations is only supported with --program multi-list")
    if args.mode == "sweep" and args.int_only_repeats is not None:
        raise SystemExit("--int-only-repeats is not included in --mode sweep graphs")

    build_lookup = {build.key: build for build in BUILDS}
    selected_build_key = "avx2" if args.use_avx2 else args.build
    if selected_build_key == "poc":
        selected_build_key = "sse2"
    selected = [build_lookup[selected_build_key]]

    maybe_build_rts(args)

    if args.mode == "sweep":
        sizes = sweep_sizes_from_args(args)
        if not sizes:
            raise SystemExit("sweep must contain at least one positive integer")
        if any(size <= 0 for size in sizes):
            raise SystemExit("sweep sizes must all be positive")
        output_base = default_sweep_output_base(args, program, selected[0], sizes)

        csv_path = (
            args.sweep_csv
            if args.sweep_csv is not None
            else output_base.with_name(f"{output_base.name}_speedups.csv")
        )
        svg_path = (
            args.sweep_svg
            if args.sweep_svg is not None
            else output_base.with_name(f"{output_base.name}_speedups.svg")
        )
        hot_loop_csv_path = (
            args.hot_loop_sweep_csv
            if args.hot_loop_sweep_csv is not None
            else output_base.with_name(f"{output_base.name}_hot_loop_speedups.csv")
        )
        hot_loop_svg_path = (
            args.hot_loop_sweep_svg
            if args.hot_loop_sweep_svg is not None
            else output_base.with_name(f"{output_base.name}_hot_loop_speedups.svg")
        )
        runtime_csv_path = (
            args.runtime_sweep_csv
            if args.runtime_sweep_csv is not None
            else output_base.with_name(f"{output_base.name}_runtimes.csv")
        )
        runtime_svg_path = (
            args.runtime_sweep_svg
            if args.runtime_sweep_svg is not None
            else output_base.with_name(f"{output_base.name}_runtimes.svg")
        )

        rows = run_sweep(args, program, selected[0], sorted(sizes))
        write_sweep_csv(rows, csv_path.resolve())
        write_sweep_svg(rows, svg_path.resolve(), program, selected[0], args.inf_buffer_size)
        write_hot_loop_sweep_csv(rows, hot_loop_csv_path.resolve(), program, selected[0])
        write_hot_loop_sweep_svg(
            rows,
            hot_loop_svg_path.resolve(),
            program,
            selected[0],
            args.inf_buffer_size,
        )
        write_runtime_sweep_csv(rows, runtime_csv_path.resolve(), selected[0])
        write_runtime_sweep_svg(
            rows,
            runtime_svg_path.resolve(),
            program,
            selected[0],
            args.inf_buffer_size,
        )
        print(f"Wrote {csv_path.resolve()}")
        print(f"Wrote {svg_path.resolve()}")
        print(f"Wrote {hot_loop_csv_path.resolve()}")
        print(f"Wrote {hot_loop_svg_path.resolve()}")
        print(f"Wrote {runtime_csv_path.resolve()}")
        print(f"Wrote {runtime_svg_path.resolve()}")
    else:
        results = []
        for build in selected:
            exe = compile_variant(args, build, program)
            result = run_benchmark(args, exe, build, program)
            results.append(result)

        print_report(results, program, args.inf_buffer_size)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
