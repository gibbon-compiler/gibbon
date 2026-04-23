#!/usr/bin/env python3
"""Benchmark the manual scalar-count vectorization experiment suite.

This script compiles a saved generated/manual C smoke test, runs it repeatedly,
parses the timing output, and prints compact tables of averages and speedups.
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
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from statistics import mean


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

    def speedup_vs_recursive(self, key: str) -> float:
        return self.averages["recursive"] / self.averages[key]


BUILDS = [
    BuildConfig(
        key="sse2",
        label="SSE2 manual SIMD",
        flags=("-O3", "-flto", "-ftree-vectorize", "-msse2"),
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
        elif key.endswith("_seconds"):
            try:
                parsed[key] = float(value)
            except ValueError:
                pass
    return parsed


def run_benchmark(args: argparse.Namespace,
                  exe: Path,
                  build: BuildConfig,
                  program: ProgramConfig) -> dict[str, object]:
    all_variants = [*VARIANTS]
    if program.int_only_repeats_define is not None and args.int_only_repeats is not None:
        all_variants.extend(INT_ONLY_VARIANTS)
    samples: dict[str, list[float]] = {key: [] for key, _, _ in all_variants}
    sums_ok = 0
    failures = 0
    exe_cmd = [str(exe)]
    if args.inf_buffer_size is not None:
        exe_cmd.extend(["--inf-buffer-size", str(args.inf_buffer_size)])

    for i in range(args.iterations):
        proc = run_command(exe_cmd, cwd=REPO_ROOT)
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

        if args.progress and (i + 1) % args.progress == 0:
            print(
                f"{program.label} / {build.label}: "
                f"completed {i + 1}/{args.iterations}",
                flush=True,
            )

    averages = {
        key: mean(vals) if vals else float("nan")
        for key, vals in samples.items()
    }
    return {
        "build": build,
        "averages": averages,
        "runs": args.iterations,
        "sums_ok": sums_ok,
        "failures": failures,
    }


def fmt_seconds(value: float) -> str:
    if value != value:
        return "n/a"
    return f"{value:.9f}"


def fmt_speedup(value: float) -> str:
    if value != value:
        return "n/a"
    return f"{value:.3f}x"


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


def write_sweep_svg(rows: list[SweepRow],
                    path: Path,
                    program: ProgramConfig,
                    inf_buffer_size: int | None) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    width = 1180
    height = 760
    sizes = [row.list_len for row in rows]
    x_ticks = log_axis_ticks(sizes)
    rotate_x_labels = len(rows) > len(x_ticks) or len(x_ticks) > 6
    margin_left = 92
    margin_right = 350
    margin_top = 58
    margin_bottom = 122 if rotate_x_labels else 84
    plot_w = width - margin_left - margin_right
    plot_h = height - margin_top - margin_bottom

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
            "Indirection SSE2 / recursive",
            "#d62728",
            [row.speedup_vs_recursive("indir_loop_explicit_vector") for row in rows],
        ),
    ]

    min_x = math.log10(min(sizes))
    max_x = math.log10(max(sizes))
    max_y = max(max(vals) for _, _, vals in series)
    y_bottom = 0.0
    y_top = max(1.0, math.ceil((max_y + 0.20) * 10) / 10)

    def xscale(n: int) -> float:
        if max_x == min_x:
            return margin_left + plot_w / 2
        return margin_left + ((math.log10(n) - min_x) / (max_x - min_x)) * plot_w

    def yscale(v: float) -> float:
        return margin_top + (1.0 - ((v - y_bottom) / (y_top - y_bottom))) * plot_h

    title = f"{program.label} Speedups by Input Size"
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
            f'text-anchor="end" class="small">{y:.1f}x</text>'
        )
        y += y_step

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
        f'text-anchor="middle" class="axis">Input size (log scale)</text>'
    )
    parts.append(
        f'<text x="26" y="{margin_top + plot_h / 2:.1f}" text-anchor="middle" '
        f'class="axis" transform="rotate(-90 26 {margin_top + plot_h / 2:.1f})">Speedup vs recursive</text>'
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

    parts.append(f'<text x="{legend_x}" y="{height - 118}" class="small">Points: {len(rows)}</text>')
    parts.append(f'<text x="{legend_x}" y="{height - 96}" class="small">Max input: {compact_size_label(max(sizes))}</text>')
    parts.append(f'<text x="{legend_x}" y="{height - 74}" class="small">Build: SSE2 manual SIMD</text>')
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
        print(
            f"- {build.label}: runs={result['runs']} sums_ok={result['sums_ok']} "
            f"failures={result['failures']}"
        )
    print()

    for result in results:
        build: BuildConfig = result["build"]  # type: ignore[assignment]
        avgs = result["averages"]  # type: ignore[assignment]
        rec = avgs["recursive"]
        rows = []
        for key, label, _ in VARIANTS:
            rows.append([label, fmt_seconds(avgs[key]), fmt_speedup(rec / avgs[key])])
        print(f"## {labels[build.key]}\n")
        print(markdown_table(["Variant", "Avg seconds", "Speedup vs recursive"], rows))
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
                "Indirection SSE vector over indirection scalar",
                fmt_speedup(avgs["indir_loop_scalar"] / avgs["indir_loop_explicit_vector"]),
            ],
            [
                "Indirection SSE vector over recursive",
                fmt_speedup(rec / avgs["indir_loop_explicit_vector"]),
            ],
            [
                "Indirection SSE vector over indirection auto-vector",
                fmt_speedup(avgs["indir_loop_auto"] / avgs["indir_loop_explicit_vector"]),
            ],
        ]
        print("## POC Comparisons\n")
        print(markdown_table(["Comparison", "Speedup"], rows))
        print()


def run_sweep(args: argparse.Namespace,
              program: ProgramConfig,
              build: BuildConfig,
              sizes: list[int]) -> list[SweepRow]:
    rows: list[SweepRow] = []

    for size in sizes:
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
        row = SweepRow(list_len=size, averages=avgs)
        rows.append(row)
        print(
            f"{program.label}: size={size} "
            f"copy={row.speedup_vs_recursive('loop_scalar_copy'):.3f}x "
            f"indir-scalar={row.speedup_vs_recursive('indir_loop_scalar'):.3f}x "
            f"indir-auto={row.speedup_vs_recursive('indir_loop_auto'):.3f}x "
            f"indir-sse2={row.speedup_vs_recursive('indir_loop_explicit_vector'):.3f}x",
            flush=True,
        )

    return rows


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
    parser.add_argument("--build-dir", type=Path, default=DEFAULT_BUILD_DIR)
    parser.add_argument("--cc", default=None, help="C compiler to use, defaults to $CC or gcc")
    parser.add_argument(
        "--build",
        choices=["sse2", "poc"],
        default="sse2",
        help="Which binary to compile and run. `poc` is an alias for `sse2`.",
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

    if args.build in {"sse2", "poc"}:
        selected = [BUILDS[0]]

    maybe_build_rts(args)

    if args.mode == "sweep":
        sizes = sweep_sizes_from_args(args)
        if not sizes:
            raise SystemExit("sweep must contain at least one positive integer")
        if any(size <= 0 for size in sizes):
            raise SystemExit("sweep sizes must all be positive")

        csv_path = (
            args.sweep_csv
            if args.sweep_csv is not None
            else DEFAULT_RESULTS_DIR / f"{program.key}_speedups.csv"
        )
        svg_path = (
            args.sweep_svg
            if args.sweep_svg is not None
            else DEFAULT_RESULTS_DIR / f"{program.key}_speedups.svg"
        )

        rows = run_sweep(args, program, selected[0], sorted(sizes))
        write_sweep_csv(rows, csv_path.resolve())
        write_sweep_svg(rows, svg_path.resolve(), program, args.inf_buffer_size)
        print(f"Wrote {csv_path.resolve()}")
        print(f"Wrote {svg_path.resolve()}")
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
