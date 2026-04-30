#!/usr/bin/env python3
"""Benchmark the standalone simple chunked-array experiment."""

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


REPO_ROOT = Path(__file__).resolve().parents[2]
EXPERIMENT_DIR = Path(__file__).resolve().parent
DEFAULT_BUILD_DIR = Path(tempfile.gettempdir()) / "gibbon_simple_test_bench"
DEFAULT_RESULTS_DIR = Path(__file__).resolve().parent / "results"
DEFAULT_SWEEP_SIZES = [10_000, 50_000, 100_000, 250_000, 500_000, 1_000_000]

VARIANTS = [
    ("scalar", "Scalar add1", "scalar_seconds"),
    ("auto", "Auto-vectorized add1", "auto_seconds"),
    ("sse2", "Manual SSE2 add1", "sse2_seconds"),
    ("avx2", "Manual AVX2 add1", "avx2_seconds"),
]

HOT_LOOP_VARIANTS = [
    ("scalar", "Scalar hot loop", "scalar_hot_loop_seconds"),
    ("auto", "Auto-vectorized hot loop", "auto_hot_loop_seconds"),
    ("sse2", "Manual SSE2 hot loop", "sse2_hot_loop_seconds"),
    ("avx2", "Manual AVX2 hot loop", "avx2_hot_loop_seconds"),
]


@dataclass(frozen=True)
class SweepRow:
    list_len: int
    averages: dict[str, float]
    hot_loop_averages: dict[str, float]
    avx2_supported: bool

    def speedup_vs_scalar(self, key: str) -> float:
        return self.averages["scalar"] / self.averages[key]

    def hot_loop_speedup_vs_scalar(self, key: str) -> float:
        return self.hot_loop_averages["scalar"] / self.hot_loop_averages[key]


@dataclass(frozen=True)
class ProgramConfig:
    key: str
    label: str
    source: Path
    result_prefix: str


PROGRAMS = {
    "simple": ProgramConfig(
        key="simple",
        label="Simple Chunked add1",
        source=EXPERIMENT_DIR / "simple.c",
        result_prefix="simple",
    ),
    "simple2": ProgramConfig(
        key="simple2",
        label="Simple Flat add1",
        source=EXPERIMENT_DIR / "simple2.c",
        result_prefix="simple2",
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


def compile_executable(args: argparse.Namespace, program: ProgramConfig) -> Path:
    cc = args.cc or os.environ.get("CC") or "gcc"
    exe_path = args.build_dir / f"{program.result_prefix}_benchmark.exe"
    args.build_dir.mkdir(parents=True, exist_ok=True)

    cmd = [
        cc,
        "-std=gnu11",
        "-O3",
        "-flto",
        "-ftree-vectorize",
        "-march=native",
        str(args.source),
        "-lm",
        "-o",
        str(exe_path),
    ]
    proc = run_command(cmd, cwd=REPO_ROOT, verbose=args.verbose)
    if proc.returncode != 0:
        print(proc.stdout, end="")
        print(proc.stderr, end="", file=sys.stderr)
        raise SystemExit(f"compile failed with exit code {proc.returncode}")
    return exe_path


def parse_output(text: str) -> dict[str, object]:
    parsed: dict[str, object] = {}
    for line in text.splitlines():
        if "=" not in line:
            continue
        key, value = line.strip().split("=", 1)
        if key in {"sums_match", "avx2_supported"}:
            parsed[key] = value == "yes"
        elif key.endswith(("_seconds", "_ns_per_element")):
            parsed[key] = float(value)
        elif key.endswith(("_calls", "_elements")):
            parsed[key] = float(value)
        elif key.endswith("_sum") or key in {"list_len", "iterations", "expected_sum"}:
            parsed[key] = int(value)
    return parsed


def run_benchmark(args: argparse.Namespace, exe_path: Path, list_len: int) -> dict[str, object]:
    cmd = [
        str(exe_path),
        "--list-len",
        str(list_len),
        "--iterations",
        str(args.iterations),
    ]
    proc = run_command(cmd, cwd=REPO_ROOT, verbose=args.verbose)
    output = proc.stdout + proc.stderr
    if proc.returncode != 0:
        print(output, end="")
        raise SystemExit(f"benchmark failed for list_len={list_len}")

    parsed = parse_output(output)
    if parsed.get("sums_match") is not True:
        print(output, end="")
        raise SystemExit(f"sum check failed for list_len={list_len}")
    return parsed


def fmt_seconds(value: float) -> str:
    return f"{value:.9f}"


def fmt_speedup(value: float) -> str:
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
            raise SystemExit("--sweep-sizes cannot be combined with range sweep args")
        if any(value is None for value in range_args):
            raise SystemExit("--sweep-start, --sweep-step, and --sweep-max must be provided together")
        return range_sweep_sizes(args.sweep_start, args.sweep_step, args.sweep_max)

    if args.sweep_sizes is None:
        return [*DEFAULT_SWEEP_SIZES]
    return parse_sizes(args.sweep_sizes)


def compact_size_label(n: int) -> str:
    def compact(value: float, suffix: str) -> str:
        text = f"{value:.1f}".rstrip("0").rstrip(".")
        return f"{text}{suffix}"

    if n < 1_000:
        return str(n)
    if n < 1_000_000:
        return f"{n // 1_000}k" if n % 1_000 == 0 else compact(n / 1_000, "k")
    return f"{n // 1_000_000}M" if n % 1_000_000 == 0 else compact(n / 1_000_000, "M")


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
    if coefficient_of_variation(diffs) <= 0.20:
        return "linear"

    if ordered[0] > 0:
        ratios = [float(b) / float(a) for a, b in zip(ordered, ordered[1:]) if a > 0]
        if coefficient_of_variation(ratios) <= 0.20:
            return "log"

    return "log" if float(ordered[-1]) / float(max(ordered[0], 1)) >= 100.0 else "linear"


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

    ticks = {min_size, max_size}
    tick = math.ceil(min_size / step) * step
    while tick < max_size:
        ticks.add(int(round(tick)))
        tick += step
    return sorted(ticks)


def log_axis_ticks(sizes: list[int], max_ticks: int = 10) -> list[int]:
    min_size = min(sizes)
    max_size = max(sizes)
    if min_size == max_size:
        return [min_size]

    min_pow = math.floor(math.log10(min_size))
    max_pow = math.ceil(math.log10(max_size))
    ticks: list[int] = []
    for power in range(min_pow, max_pow + 1):
        for multiplier in (1, 2, 5):
            tick = multiplier * (10 ** power)
            if min_size <= tick <= max_size:
                ticks.append(tick)
    ticks = sorted(set([min_size, max_size, *ticks]))
    if len(ticks) <= max_ticks:
        return ticks
    return sorted(set([min_size, max_size, *[
        10 ** power
        for power in range(min_pow, max_pow + 1)
        if min_size <= 10 ** power <= max_size
    ]]))


def axis_ticks_for_scale(sizes: list[int], scale: str) -> list[int]:
    return linear_axis_ticks(sizes) if scale == "linear" else log_axis_ticks(sizes)


def svg_polyline(points: list[tuple[float, float]], color: str, width: int = 3) -> str:
    pts = " ".join(f"{x:.1f},{y:.1f}" for x, y in points)
    return (
        f'<polyline points="{pts}" fill="none" stroke="{color}" '
        f'stroke-width="{width}" stroke-linejoin="round" stroke-linecap="round"/>'
    )


def write_series_svg(rows: list[SweepRow],
                     path: Path,
                     title: str,
                     y_axis_label: str,
                     series: list[tuple[str, str, list[float]]],
                     reference_lines: list[tuple[str, float, str, str | None]],
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
            max_x_value += x_pad
    else:
        min_x_value = math.log10(min(sizes))
        max_x_value = math.log10(max(sizes))
        if max_x_value > min_x_value:
            x_pad = 0.03 * (max_x_value - min_x_value)
            min_x_value -= x_pad
            max_x_value += x_pad

    max_series_y = max(max(vals) for _name, _color, vals in series) if series else y_bottom
    max_reference_y = max((value for _label, value, _color, _dash in reference_lines), default=y_bottom)
    max_y = max(max_series_y, max_reference_y)
    y_top = max(1.0, math.ceil((max_y + 0.20) * 10) / 10)

    def xscale(n: int) -> float:
        if max_x_value == min_x_value:
            return margin_left + plot_w / 2
        x_value = float(n) if x_scale_mode == "linear" else math.log10(n)
        return margin_left + ((x_value - min_x_value) / (max_x_value - min_x_value)) * plot_w

    def yscale(v: float) -> float:
        return margin_top + (1.0 - ((v - y_bottom) / (y_top - y_bottom))) * plot_h

    parts = [
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
            f'<line x1="{margin_left}" y1="{py:.1f}" x2="{margin_left + plot_w}" y2="{py:.1f}" stroke="{stroke}" stroke-width="1"/>'
        )
        parts.append(
            f'<text x="{margin_left - 12}" y="{py + 4:.1f}" text-anchor="end" class="small">{y_tick_label_fn(y)}</text>'
        )
        y += y_step

    for _label, value, color, dasharray in reference_lines:
        py = yscale(value)
        dash_attr = f' stroke-dasharray="{dasharray}"' if dasharray is not None else ""
        parts.append(
            f'<line x1="{margin_left}" y1="{py:.1f}" x2="{margin_left + plot_w}" y2="{py:.1f}" stroke="{color}" stroke-width="2"{dash_attr}/>'
        )

    for tick in x_ticks:
        px = xscale(tick)
        parts.append(
            f'<line x1="{px:.1f}" y1="{margin_top}" x2="{px:.1f}" y2="{margin_top + plot_h}" stroke="#ececf1" stroke-width="1"/>'
        )
        label = compact_size_label(tick)
        label_y = margin_top + plot_h + (64 if rotate_x_labels else 24)
        if rotate_x_labels:
            parts.append(
                f'<text x="{px:.1f}" y="{label_y:.1f}" text-anchor="end" class="small" transform="rotate(-45 {px:.1f} {label_y:.1f})">{label}</text>'
            )
        else:
            parts.append(
                f'<text x="{px:.1f}" y="{label_y:.1f}" text-anchor="middle" class="small">{label}</text>'
            )

    parts.append(
        f'<text x="{margin_left + plot_w / 2:.1f}" y="{height - 22}" text-anchor="middle" class="axis">Input size ({x_scale_mode} scale)</text>'
    )
    parts.append(
        f'<text x="26" y="{margin_top + plot_h / 2:.1f}" text-anchor="middle" class="axis" transform="rotate(-90 26 {margin_top + plot_h / 2:.1f})">{y_axis_label}</text>'
    )

    for name, color, vals in series:
        points = [(xscale(row.list_len), yscale(val)) for row, val in zip(rows, vals)]
        parts.append(svg_polyline(points, color))
        marker_step = max(1, math.ceil(len(points) / 40))
        for i, (px, py) in enumerate(points):
            if len(points) > 80 and i not in (0, len(points) - 1) and i % marker_step != 0:
                continue
            parts.append(
                f'<circle cx="{px:.1f}" cy="{py:.1f}" r="4" fill="{color}" stroke="white" stroke-width="1.5"/>'
            )

    legend_x = margin_left + plot_w + 34
    legend_y = margin_top + 18
    for i, (name, color, _vals) in enumerate(series):
        y = legend_y + i * 34
        parts.append(
            f'<line x1="{legend_x}" y1="{y}" x2="{legend_x + 32}" y2="{y}" stroke="{color}" stroke-width="4" stroke-linecap="round"/>'
        )
        parts.append(f'<text x="{legend_x + 44}" y="{y + 5}" class="small">{name}</text>')

    ref_y0 = legend_y + len(series) * 34
    for i, (label, _value, color, dasharray) in enumerate(reference_lines):
        y = ref_y0 + i * 34
        dash_attr = f' stroke-dasharray="{dasharray}"' if dasharray is not None else ""
        parts.append(
            f'<line x1="{legend_x}" y1="{y}" x2="{legend_x + 32}" y2="{y}" stroke="{color}" stroke-width="3" stroke-linecap="round"{dash_attr}/>'
        )
        parts.append(f'<text x="{legend_x + 44}" y="{y + 5}" class="small">{label}</text>')

    parts.append(f'<text x="{legend_x}" y="{height - 118}" class="small">Points: {len(rows)}</text>')
    parts.append(f'<text x="{legend_x}" y="{height - 96}" class="small">Max input: {compact_size_label(max(sizes))}</text>')
    parts.append(f'<text x="{legend_x}" y="{height - 74}" class="small">Source: simple.c</text>')
    parts.append(f'<text x="{legend_x}" y="{height - 52}" class="small">Auto build: -O3 -march=native</text>')
    parts.append("</svg>")

    path.write_text("\n".join(parts))


def write_runtime_csv(rows: list[SweepRow], path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["list_len", "scalar_seconds", "auto_seconds", "sse2_seconds", "avx2_seconds"])
        for row in rows:
            writer.writerow([
                row.list_len,
                f"{row.averages['scalar']:.9f}",
                f"{row.averages['auto']:.9f}",
                f"{row.averages['sse2']:.9f}",
                f"{row.averages.get('avx2', float('nan')):.9f}",
            ])


def write_speedup_csv(rows: list[SweepRow], path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["list_len", "auto_speedup_vs_scalar", "sse2_speedup_vs_scalar", "avx2_speedup_vs_scalar"])
        for row in rows:
            writer.writerow([
                row.list_len,
                f"{row.speedup_vs_scalar('auto'):.6f}",
                f"{row.speedup_vs_scalar('sse2'):.6f}",
                f"{row.speedup_vs_scalar('avx2'):.6f}" if row.avx2_supported else "",
            ])


def write_hot_loop_speedup_csv(rows: list[SweepRow], path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["list_len", "auto_hot_loop_speedup_vs_scalar", "sse2_hot_loop_speedup_vs_scalar", "avx2_hot_loop_speedup_vs_scalar"])
        for row in rows:
            writer.writerow([
                row.list_len,
                f"{row.hot_loop_speedup_vs_scalar('auto'):.6f}",
                f"{row.hot_loop_speedup_vs_scalar('sse2'):.6f}",
                f"{row.hot_loop_speedup_vs_scalar('avx2'):.6f}" if row.avx2_supported else "",
            ])


def write_runtime_svg(rows: list[SweepRow], path: Path, program: ProgramConfig) -> None:
    series = [
        ("Scalar add1", "#7f7f7f", [1000.0 * row.averages["scalar"] for row in rows]),
        ("Auto-vectorized add1", "#9467bd", [1000.0 * row.averages["auto"] for row in rows]),
        ("Manual SSE2 add1", "#1f77b4", [1000.0 * row.averages["sse2"] for row in rows]),
    ]
    if all(row.avx2_supported for row in rows):
        series.append(("Manual AVX2 add1", "#d62728", [1000.0 * row.averages["avx2"] for row in rows]))

    write_series_svg(
        rows,
        path,
        title=f"{program.label} Runtimes by Input Size",
        y_axis_label="Avg runtime (ms)",
        series=series,
        reference_lines=[],
        y_bottom=0.0,
        y_tick_label_fn=lambda y: f"{y:.2f} ms",
    )


def write_speedup_svg(rows: list[SweepRow], path: Path, program: ProgramConfig) -> None:
    series = [
        ("Auto-vectorized / scalar", "#9467bd", [row.speedup_vs_scalar("auto") for row in rows]),
        ("Manual SSE2 / scalar", "#1f77b4", [row.speedup_vs_scalar("sse2") for row in rows]),
    ]
    if all(row.avx2_supported for row in rows):
        series.append(("Manual AVX2 / scalar", "#d62728", [row.speedup_vs_scalar("avx2") for row in rows]))

    write_series_svg(
        rows,
        path,
        title=f"{program.label} Speedups by Input Size",
        y_axis_label="Speedup vs scalar",
        series=series,
        reference_lines=[("Baseline 1.0x", 1.0, "#d62728", None)],
        y_bottom=0.0,
        y_tick_label_fn=lambda y: f"{y:.1f}x",
    )


def write_hot_loop_speedup_svg(rows: list[SweepRow], path: Path, program: ProgramConfig) -> None:
    series = [
        ("Auto-vectorized hot loop / scalar hot loop", "#9467bd",
         [row.hot_loop_speedup_vs_scalar("auto") for row in rows]),
        ("Manual SSE2 hot loop / scalar hot loop", "#1f77b4",
         [row.hot_loop_speedup_vs_scalar("sse2") for row in rows]),
    ]
    if all(row.avx2_supported for row in rows):
        series.append(
            ("Manual AVX2 hot loop / scalar hot loop", "#d62728",
             [row.hot_loop_speedup_vs_scalar("avx2") for row in rows])
        )

    write_series_svg(
        rows,
        path,
        title=f"{program.label} Hot Loop Speedups by Input Size",
        y_axis_label="Hot loop speedup vs scalar",
        series=series,
        reference_lines=[
            ("Baseline 1.0x", 1.0, "#d62728", None),
        ],
        y_bottom=0.0,
        y_tick_label_fn=lambda y: f"{y:.1f}x",
    )


def print_report(parsed: dict[str, object], program: ProgramConfig) -> None:
    avx2_supported = parsed["avx2_supported"]  # type: ignore[index]
    print(f"\n# {program.label} Benchmark\n")
    print(f"- list length: {parsed['list_len']}")
    print(f"- iterations: {parsed['iterations']}")
    print(f"- expected sum: {parsed['expected_sum']}")
    print(f"- AVX2 supported: {'yes' if avx2_supported else 'no'}")
    print()

    rows = []
    scalar = float(parsed["scalar_seconds"])
    for key, label, output_key in VARIANTS:
        if key == "avx2" and not avx2_supported:
            continue
        seconds = float(parsed[output_key])
        rows.append([label, fmt_seconds(seconds), fmt_speedup(scalar / seconds)])
    print(markdown_table(["Variant", "Avg seconds", "Speedup vs scalar"], rows))
    print()

    hot_rows = []
    scalar_hot = float(parsed["scalar_hot_loop_seconds"])
    for key, label, output_key in HOT_LOOP_VARIANTS:
        if key == "avx2" and not avx2_supported:
            continue
        hot_rows.append([
            label,
            fmt_seconds(float(parsed[output_key])),
            f"{float(parsed[f'{key}_hot_loop_ns_per_element']):.3f}",
            f"{int(round(float(parsed[f'{key}_hot_loop_calls'])))}",
            f"{int(round(float(parsed[f'{key}_hot_loop_elements'])))}",
            fmt_speedup(scalar_hot / float(parsed[output_key])),
        ])
    print(markdown_table(
        ["Hot loop", "Avg seconds", "Ns/elem", "Calls/run", "Elems/run", "Speedup vs scalar"],
        hot_rows,
    ))
    print()


def run_sweep(args: argparse.Namespace, exe_path: Path, sizes: list[int]) -> list[SweepRow]:
    rows: list[SweepRow] = []
    for size in sizes:
        parsed = run_benchmark(args, exe_path, size)
        row = SweepRow(
            list_len=size,
            averages={
                "scalar": float(parsed["scalar_seconds"]),
                "auto": float(parsed["auto_seconds"]),
                "sse2": float(parsed["sse2_seconds"]),
                "avx2": float(parsed["avx2_seconds"]) if parsed["avx2_supported"] else float("nan"),
            },
            hot_loop_averages={
                "scalar": float(parsed["scalar_hot_loop_seconds"]),
                "auto": float(parsed["auto_hot_loop_seconds"]),
                "sse2": float(parsed["sse2_hot_loop_seconds"]),
                "avx2": float(parsed["avx2_hot_loop_seconds"]) if parsed["avx2_supported"] else float("nan"),
            },
            avx2_supported=bool(parsed["avx2_supported"]),
        )
        rows.append(row)

        msg = (
            f"size={size} scalar={row.averages['scalar']:.9f}s "
            f"auto={row.speedup_vs_scalar('auto'):.3f}x "
            f"sse2={row.speedup_vs_scalar('sse2'):.3f}x"
        )
        if row.avx2_supported:
            msg += f" avx2={row.speedup_vs_scalar('avx2'):.3f}x"
        msg += (
            f" hot-auto={row.hot_loop_speedup_vs_scalar('auto'):.3f}x "
            f"hot-sse2={row.hot_loop_speedup_vs_scalar('sse2'):.3f}x"
        )
        if row.avx2_supported:
            msg += f" hot-avx2={row.hot_loop_speedup_vs_scalar('avx2'):.3f}x"
        print(msg, flush=True)

    return rows


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Benchmark the standalone simple chunked-array test.")
    parser.add_argument("--program", choices=sorted(PROGRAMS.keys()), default="simple")
    parser.add_argument("--mode", choices=["benchmark", "sweep"], default="benchmark")
    parser.add_argument("--source", type=Path, default=None)
    parser.add_argument("--list-len", type=int, default=100_000)
    parser.add_argument("--iterations", "-n", type=int, default=30)
    parser.add_argument("--sweep-sizes", default=None)
    parser.add_argument("--sweep-start", type=int, default=None)
    parser.add_argument("--sweep-step", type=int, default=None)
    parser.add_argument("--sweep-max", type=int, default=None)
    parser.add_argument("--runtime-csv", type=Path, default=None)
    parser.add_argument("--runtime-svg", type=Path, default=None)
    parser.add_argument("--speedup-csv", type=Path, default=None)
    parser.add_argument("--speedup-svg", type=Path, default=None)
    parser.add_argument("--hot-loop-speedup-csv", type=Path, default=None)
    parser.add_argument("--hot-loop-speedup-svg", type=Path, default=None)
    parser.add_argument("--build-dir", type=Path, default=DEFAULT_BUILD_DIR)
    parser.add_argument("--cc", default=None)
    parser.add_argument("--verbose", "-v", action="store_true")
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    program = PROGRAMS[args.program]
    if args.source is None:
        args.source = program.source
    args.source = args.source.resolve()
    args.build_dir = args.build_dir.resolve()

    if args.list_len <= 0:
        raise SystemExit("--list-len must be positive")
    if args.iterations <= 0:
        raise SystemExit("--iterations must be positive")
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
        raise SystemExit("--sweep-start must be <= --sweep-max")

    exe_path = compile_executable(args, program)

    if args.mode == "benchmark":
        parsed = run_benchmark(args, exe_path, args.list_len)
        print_report(parsed, program)
        return 0

    sizes = sweep_sizes_from_args(args)
    if any(size <= 0 for size in sizes):
        raise SystemExit("sweep sizes must be positive")

    runtime_csv = args.runtime_csv or (DEFAULT_RESULTS_DIR / f"{program.result_prefix}_runtimes.csv")
    runtime_svg = args.runtime_svg or (DEFAULT_RESULTS_DIR / f"{program.result_prefix}_runtimes.svg")
    speedup_csv = args.speedup_csv or (DEFAULT_RESULTS_DIR / f"{program.result_prefix}_speedups.csv")
    speedup_svg = args.speedup_svg or (DEFAULT_RESULTS_DIR / f"{program.result_prefix}_speedups.svg")
    hot_loop_speedup_csv = args.hot_loop_speedup_csv or (
        DEFAULT_RESULTS_DIR / f"{program.result_prefix}_hot_loop_speedups.csv"
    )
    hot_loop_speedup_svg = args.hot_loop_speedup_svg or (
        DEFAULT_RESULTS_DIR / f"{program.result_prefix}_hot_loop_speedups.svg"
    )

    rows = run_sweep(args, exe_path, sorted(sizes))
    write_runtime_csv(rows, runtime_csv.resolve())
    write_runtime_svg(rows, runtime_svg.resolve(), program)
    write_speedup_csv(rows, speedup_csv.resolve())
    write_speedup_svg(rows, speedup_svg.resolve(), program)
    write_hot_loop_speedup_csv(rows, hot_loop_speedup_csv.resolve())
    write_hot_loop_speedup_svg(rows, hot_loop_speedup_svg.resolve(), program)

    print(f"Wrote {runtime_csv.resolve()}")
    print(f"Wrote {runtime_svg.resolve()}")
    print(f"Wrote {speedup_csv.resolve()}")
    print(f"Wrote {speedup_svg.resolve()}")
    print(f"Wrote {hot_loop_speedup_csv.resolve()}")
    print(f"Wrote {hot_loop_speedup_svg.resolve()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
