#!/usr/bin/env python3
"""Sweep ScalarCountSmoke list sizes and plot POC speedups.

The sweep uses the scalar_count_smoke experiment driver's POC build: one binary
per list size, with the five add1List variants measured in the same executable.
"""

from __future__ import annotations

import argparse
import csv
import math
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent
BENCH = REPO_ROOT / "experiments" / "scalar_count_smoke" / "benchmark_scalar_count_smoke.py"
DEFAULT_SIZES = [10_000, 50_000, 100_000, 250_000, 500_000, 1_000_000, 2_000_000, 5_000_000]
VARIANT_LABEL_TO_KEY = {
    "Recursive add1": "recursive",
    "Loopified add1, copy dead buffers, vectorization off": "loop_scalar_copy",
    "Loopified add1, dead-buffer indirections, vectorization off": "indir_loop_scalar",
    "Loopified add1, dead-buffer indirections, auto-vectorized": "indir_loop_auto",
    "Loopified add1, dead-buffer indirections, manual SSE2 vectorized": "indir_loop_explicit_vector",
}


@dataclass(frozen=True)
class SweepRow:
    list_len: int
    recursive: float
    loop_scalar_copy: float
    indir_loop_scalar: float
    indir_loop_auto: float
    indir_loop_explicit_vector: float

    @property
    def loop_copy_over_recursive(self) -> float:
        return self.recursive / self.loop_scalar_copy

    @property
    def indirection_scalar_over_recursive(self) -> float:
        return self.recursive / self.indir_loop_scalar

    @property
    def indirection_scalar_over_copy_scalar(self) -> float:
        return self.loop_scalar_copy / self.indir_loop_scalar

    @property
    def auto_over_scalar_indirection(self) -> float:
        return self.indir_loop_scalar / self.indir_loop_auto

    @property
    def manual_over_scalar_indirection(self) -> float:
        return self.indir_loop_scalar / self.indir_loop_explicit_vector

    @property
    def manual_over_recursive(self) -> float:
        return self.recursive / self.indir_loop_explicit_vector

    @property
    def manual_over_auto_indirection(self) -> float:
        return self.indir_loop_auto / self.indir_loop_explicit_vector


def run_benchmark(list_len: int, iterations: int, progress: bool) -> SweepRow:
    cmd = [
        sys.executable,
        str(BENCH),
        "--list-len",
        str(list_len),
        "--iterations",
        str(iterations),
        "--build",
        "poc",
    ]
    if progress:
        cmd.extend(["--progress", str(max(1, iterations // 2))])

    proc = subprocess.run(
        cmd,
        cwd=REPO_ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    output = proc.stdout + proc.stderr
    if proc.returncode != 0:
        print(output, end="")
        raise SystemExit(f"benchmark failed for list_len={list_len}")

    values: dict[str, float] = {}
    for line in output.splitlines():
        if not line.startswith("| "):
            continue
        cells = [cell.strip() for cell in line.strip().strip("|").split("|")]
        if len(cells) < 3:
            continue
        key = VARIANT_LABEL_TO_KEY.get(cells[0])
        if key is None:
            continue
        try:
            values[key] = float(cells[1])
        except ValueError:
            pass

    missing = [key for key in VARIANT_LABEL_TO_KEY.values() if key not in values]
    if missing:
        print(output, end="")
        raise SystemExit(f"could not parse benchmark output for list_len={list_len}: missing {missing}")

    return SweepRow(list_len=list_len, **values)


def write_csv(rows: list[SweepRow], path: Path) -> None:
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
            "loop_copy_over_recursive",
            "indirection_scalar_over_copy_scalar",
            "indirection_scalar_over_recursive",
            "auto_over_scalar_indirection",
            "manual_over_scalar_indirection",
            "manual_over_recursive",
            "manual_over_auto_indirection",
        ])
        for row in rows:
            writer.writerow([
                row.list_len,
                f"{row.recursive:.9f}",
                f"{row.loop_scalar_copy:.9f}",
                f"{row.indir_loop_scalar:.9f}",
                f"{row.indir_loop_auto:.9f}",
                f"{row.indir_loop_explicit_vector:.9f}",
                f"{row.loop_copy_over_recursive:.6f}",
                f"{row.indirection_scalar_over_copy_scalar:.6f}",
                f"{row.indirection_scalar_over_recursive:.6f}",
                f"{row.auto_over_scalar_indirection:.6f}",
                f"{row.manual_over_scalar_indirection:.6f}",
                f"{row.manual_over_recursive:.6f}",
                f"{row.manual_over_auto_indirection:.6f}",
            ])


def svg_polyline(points: list[tuple[float, float]], color: str, width: int = 3) -> str:
    pts = " ".join(f"{x:.1f},{y:.1f}" for x, y in points)
    return f'<polyline points="{pts}" fill="none" stroke="{color}" stroke-width="{width}" stroke-linejoin="round" stroke-linecap="round"/>'


def write_svg(rows: list[SweepRow], path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    width = 1100
    height = 680
    margin_left = 92
    margin_right = 280
    margin_top = 52
    margin_bottom = 76
    plot_w = width - margin_left - margin_right
    plot_h = height - margin_top - margin_bottom

    series = [
        ("Manual SSE indirection / recursive", "#1f77b4", [r.manual_over_recursive for r in rows]),
        ("Scalar indirection / recursive", "#2ca02c", [r.indirection_scalar_over_recursive for r in rows]),
        ("Manual SSE / scalar indirection", "#d62728", [r.manual_over_scalar_indirection for r in rows]),
        ("Auto-vector / scalar indirection", "#9467bd", [r.auto_over_scalar_indirection for r in rows]),
    ]

    min_x = math.log10(min(r.list_len for r in rows))
    max_x = math.log10(max(r.list_len for r in rows))
    max_y = max(max(vals) for _, _, vals in series)
    y_top = math.ceil((max_y + 0.15) * 10) / 10
    y_bottom = 0.9

    def xscale(n: int) -> float:
        if max_x == min_x:
            return margin_left + plot_w / 2
        return margin_left + ((math.log10(n) - min_x) / (max_x - min_x)) * plot_w

    def yscale(v: float) -> float:
        return margin_top + (1.0 - ((v - y_bottom) / (y_top - y_bottom))) * plot_h

    parts: list[str] = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">',
        '<rect width="100%" height="100%" fill="white"/>',
        '<style>text{font-family:Arial,Helvetica,sans-serif;fill:#202124} .small{font-size:13px} .axis{font-size:14px} .title{font-size:24px;font-weight:700}</style>',
        f'<text x="{margin_left}" y="30" class="title">ScalarCountSmoke POC Speedups by List Size</text>',
        f'<rect x="{margin_left}" y="{margin_top}" width="{plot_w}" height="{plot_h}" fill="#fbfbfd" stroke="#c7c7cc"/>',
    ]

    for i in range(0, int(math.floor(y_top * 10)) + 1):
        y = i / 10
        if y < y_bottom or y > y_top:
            continue
        py = yscale(y)
        stroke = "#d8d8dd" if abs(y - round(y)) > 1e-9 else "#b8b8c0"
        parts.append(f'<line x1="{margin_left}" y1="{py:.1f}" x2="{margin_left + plot_w}" y2="{py:.1f}" stroke="{stroke}" stroke-width="1"/>')
        if abs((y * 10) % 5) < 1e-9:
            parts.append(f'<text x="{margin_left - 12}" y="{py + 4:.1f}" text-anchor="end" class="small">{y:.1f}x</text>')

    for row in rows:
        px = xscale(row.list_len)
        parts.append(f'<line x1="{px:.1f}" y1="{margin_top}" x2="{px:.1f}" y2="{margin_top + plot_h}" stroke="#ececf1" stroke-width="1"/>')
        label = f"{row.list_len // 1000}k" if row.list_len < 1_000_000 else f"{row.list_len // 1_000_000}M"
        parts.append(f'<text x="{px:.1f}" y="{margin_top + plot_h + 24}" text-anchor="middle" class="small">{label}</text>')

    parts.append(f'<text x="{margin_left + plot_w / 2:.1f}" y="{height - 22}" text-anchor="middle" class="axis">Input list length (log scale)</text>')
    parts.append(f'<text x="26" y="{margin_top + plot_h / 2:.1f}" text-anchor="middle" class="axis" transform="rotate(-90 26 {margin_top + plot_h / 2:.1f})">Speedup</text>')

    for name, color, vals in series:
        pts = [(xscale(row.list_len), yscale(val)) for row, val in zip(rows, vals)]
        parts.append(svg_polyline(pts, color))
        for px, py in pts:
            parts.append(f'<circle cx="{px:.1f}" cy="{py:.1f}" r="4" fill="{color}" stroke="white" stroke-width="1.5"/>')

    legend_x = margin_left + plot_w + 34
    legend_y = margin_top + 12
    for i, (name, color, _vals) in enumerate(series):
        y = legend_y + i * 34
        parts.append(f'<line x1="{legend_x}" y1="{y}" x2="{legend_x + 32}" y2="{y}" stroke="{color}" stroke-width="4" stroke-linecap="round"/>')
        parts.append(f'<text x="{legend_x + 44}" y="{y + 5}" class="small">{name}</text>')

    parts.append(f'<text x="{legend_x}" y="{height - 88}" class="small">Chunk size: 65,500 bytes</text>')
    parts.append(f'<text x="{legend_x}" y="{height - 66}" class="small">Build: same-binary POC</text>')
    parts.append("</svg>")
    path.write_text("\n".join(parts))


def parse_sizes(value: str) -> list[int]:
    return [int(x.strip()) for x in value.split(",") if x.strip()]


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description="Sweep and plot ScalarCountSmoke POC speedups.")
    parser.add_argument("--sizes", default=",".join(str(x) for x in DEFAULT_SIZES))
    parser.add_argument("--iterations", type=int, default=20)
    parser.add_argument("--csv", type=Path, default=REPO_ROOT / "scalar_count_smoke_sweep.csv")
    parser.add_argument("--svg", type=Path, default=REPO_ROOT / "scalar_count_smoke_sweep.svg")
    parser.add_argument("--progress", action="store_true")
    args = parser.parse_args(argv)

    sizes = parse_sizes(args.sizes)
    if not sizes:
        raise SystemExit("--sizes must contain at least one positive integer")
    if any(size <= 0 for size in sizes):
        raise SystemExit("--sizes must all be positive")
    if args.iterations <= 0:
        raise SystemExit("--iterations must be positive")

    rows: list[SweepRow] = []
    for size in sizes:
        print(f"Running list_len={size} iterations={args.iterations}", flush=True)
        row = run_benchmark(size, args.iterations, args.progress)
        rows.append(row)
        print(
            f"  manual/recursive={row.manual_over_recursive:.3f}x "
            f"manual/scalar-indirection={row.manual_over_scalar_indirection:.3f}x",
            flush=True,
        )

    write_csv(rows, args.csv.resolve())
    write_svg(rows, args.svg.resolve())
    print(f"Wrote {args.csv.resolve()}")
    print(f"Wrote {args.svg.resolve()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
