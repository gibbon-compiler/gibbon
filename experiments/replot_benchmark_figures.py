#!/usr/bin/env python3
"""Rebuild benchmark figures from saved CSV result files with matplotlib."""

from __future__ import annotations

import argparse
import csv
import math
import sys
import textwrap
from dataclasses import dataclass
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
RESULT_ROOTS = [
    REPO_ROOT / "experiments" / "simple_test" / "results",
    REPO_ROOT / "experiments" / "scalar_count_smoke" / "results",
]


@dataclass(frozen=True)
class PlotRow:
    list_len: int


@dataclass(frozen=True)
class PlotStyle:
    kind: str
    title_suffix: str
    y_axis_label: str
    y_tick_unit: str
    reference_lines: list[tuple[str, float, str, str | None]]


COLORS = [
    "#4c78a8",
    "#f58518",
    "#54a24b",
    "#b279a2",
    "#e45756",
    "#72b7b2",
    "#9d755d",
    "#bab0ac",
]


def parse_float(value: str) -> float:
    value = value.strip()
    if not value:
        return float("nan")
    try:
        return float(value)
    except ValueError:
        return float("nan")


def read_csv(path: Path) -> tuple[list[str], list[dict[str, str]]]:
    with path.open(newline="") as f:
        reader = csv.DictReader(f)
        rows = list(reader)
        return list(reader.fieldnames or []), rows


def prettify_column(name: str) -> str:
    cleaned = name
    replacements = [
        ("_speedup_vs_recursive", " / recursive"),
        ("_speedup_vs_scalar", " / scalar"),
        ("_hot_loop_speedup_vs_scalar", " hot loop / scalar hot loop"),
        ("_seconds", ""),
        ("recursive", "recursive"),
        ("loop_scalar_copy", "copy scalar"),
        ("indir_loop_scalar", "indirection scalar"),
        ("indir_loop_auto", "indirection auto-vector"),
        ("indir_loop_explicit_vector", "indirection manual SIMD"),
        ("auto", "auto-vectorized"),
        ("sse2", "manual SSE2"),
        ("avx2", "manual AVX2"),
        ("scalar", "scalar"),
    ]
    for old, new in replacements:
        cleaned = cleaned.replace(old, new)
    return " ".join(part for part in cleaned.replace("_", " ").split()).capitalize()


def title_from_path(path: Path, style: PlotStyle) -> str:
    run_name = path.parent.name
    if run_name in ("results", "2026-04-30", "2026-05-01", "2026-05-02"):
        run_name = path.stem
    run_name = run_name.replace("_", " ")
    return f"{run_name} {style.title_suffix}"


def style_for_csv(path: Path) -> PlotStyle | None:
    name = path.name
    if "hot_loop_speedups" in name:
        return PlotStyle(
            kind="hot_loop_speedup",
            title_suffix="Hot Loop Speedups",
            y_axis_label="Hot loop speedup",
            y_tick_unit="x",
            reference_lines=[("Baseline 1.0x", 1.0, "#d62728", None)],
        )
    if "speedups" in name:
        return PlotStyle(
            kind="speedup",
            title_suffix="Speedups",
            y_axis_label="Speedup",
            y_tick_unit="x",
            reference_lines=[("Baseline 1.0x", 1.0, "#d62728", None)],
        )
    if "runtimes" in name:
        return PlotStyle(
            kind="runtime",
            title_suffix="Runtimes",
            y_axis_label="Median runtime (ms)",
            y_tick_unit="ms",
            reference_lines=[],
        )
    return None


def y_tick_formatter(unit: str):
    if unit == "ms":
        return lambda y: f"{y:.2f} ms"
    if unit == "x":
        return lambda y: f"{y:.1f}x"
    return lambda y: f"{y:.2f}"


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

    ratios = [float(b) / float(a) for a, b in zip(ordered, ordered[1:]) if a > 0]
    if ratios and coefficient_of_variation(ratios) <= 0.20:
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

    tick_set = {min_size, max_size}
    tick = math.ceil(min_size / step) * step
    while tick < max_size:
        tick_set.add(int(round(tick)))
        tick += step
    return sorted(tick_set)


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


def series_from_csv(headers: list[str],
                    rows: list[dict[str, str]],
                    style: PlotStyle) -> list[tuple[str, str, list[float]]]:
    if style.kind == "runtime":
        data_columns = [
            header for header in headers
            if header != "list_len" and header.endswith("_seconds")
        ]
    else:
        data_columns = [
            header for header in headers
            if header != "list_len" and "speedup" in header
        ]
    series: list[tuple[str, str, list[float]]] = []
    for i, column in enumerate(data_columns):
        vals = [parse_float(row.get(column, "")) for row in rows]
        if style.kind == "runtime":
            vals = [1000.0 * value if math.isfinite(value) else value for value in vals]
        if not any(math.isfinite(value) for value in vals):
            continue
        series.append((prettify_column(column), COLORS[i % len(COLORS)], vals))
    return series


def configure_matplotlib():
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        from matplotlib.ticker import FuncFormatter, MaxNLocator
    except ModuleNotFoundError as exc:
        raise SystemExit(
            "matplotlib is required for replotting. Activate a virtualenv with "
            "matplotlib installed, for example:\n"
            "  source experiments/.plot_venv/bin/activate"
        ) from exc

    plt.rcParams.update({
        "figure.facecolor": "white",
        "axes.facecolor": "white",
        "axes.edgecolor": "#333333",
        "axes.labelsize": 18,
        "axes.titlesize": 20,
        "axes.titleweight": "bold",
        "xtick.labelsize": 15,
        "ytick.labelsize": 15,
        "legend.fontsize": 13,
        "font.family": "DejaVu Sans",
        "lines.linewidth": 2.6,
        "savefig.bbox": "tight",
        "savefig.facecolor": "white",
    })
    return plt, FuncFormatter, MaxNLocator


def replot_csv(path: Path, *, plt, FuncFormatter, MaxNLocator, formats: list[str], dpi: int) -> list[Path]:
    style = style_for_csv(path)
    if style is None:
        return []

    headers, raw_rows = read_csv(path)
    if "list_len" not in headers or not raw_rows:
        return []

    rows = [PlotRow(int(row["list_len"])) for row in raw_rows]
    series = series_from_csv(headers, raw_rows, style)
    if not series:
        return []

    sizes = [row.list_len for row in rows]
    x_scale = choose_x_axis_scale(sizes)
    fig, ax = plt.subplots(figsize=(12.5, 7.8), dpi=dpi, constrained_layout=True)

    for label, color, values in series:
        xs: list[int] = []
        ys: list[float] = []
        for size, value in zip(sizes, values):
            if math.isfinite(value):
                xs.append(size)
                ys.append(value)
            else:
                if len(xs) >= 2:
                    ax.plot(xs, ys, label=label, color=color, marker="o", markersize=4.5, markevery=max(1, len(xs) // 40))
                xs = []
                ys = []
        if len(xs) >= 2:
            ax.plot(xs, ys, label=label, color=color, marker="o", markersize=4.5, markevery=max(1, len(xs) // 40))
        elif len(xs) == 1:
            ax.scatter(xs, ys, label=label, color=color, s=42)

    for label, value, color, dasharray in style.reference_lines:
        if not math.isfinite(value):
            continue
        linestyle = "--" if dasharray is not None else "-"
        ax.axhline(value, color=color, linestyle=linestyle, linewidth=1.9, alpha=0.85, label=label)

    ax.set_title(textwrap.fill(title_from_path(path, style), width=78), pad=18)
    ax.set_xlabel(f"Input size ({x_scale} scale)", labelpad=14)
    ax.set_ylabel(style.y_axis_label, labelpad=14)
    ax.set_xscale(x_scale)
    ax.set_xticks(axis_ticks_for_scale(sizes, x_scale))
    ax.set_xticklabels([compact_size_label(tick) for tick in axis_ticks_for_scale(sizes, x_scale)])
    ax.yaxis.set_major_locator(MaxNLocator(nbins=8))
    if style.y_tick_unit == "x":
        ax.yaxis.set_major_formatter(FuncFormatter(lambda value, _pos: f"{value:.1f}x"))
    ax.grid(True, which="major", color="#d9d9d9", linewidth=0.9, alpha=0.85)
    ax.grid(True, which="minor", color="#ededed", linewidth=0.5, alpha=0.65)
    ax.margins(x=0.025, y=0.08)
    ax.legend(loc="center left", bbox_to_anchor=(1.02, 0.5), frameon=False)
    for label in ax.get_xticklabels():
        label.set_rotation(35)
        label.set_ha("right")

    written: list[Path] = []
    for fmt in formats:
        output_path = path.with_suffix(f".{fmt}")
        fig.savefig(output_path, dpi=dpi if fmt == "png" else None, format=fmt)
        written.append(output_path)
    plt.close(fig)
    return written


def discover_csvs(roots: list[Path]) -> list[Path]:
    paths: list[Path] = []
    for root in roots:
        if root.exists():
            paths.extend(root.rglob("*.csv"))
    return sorted(path for path in paths if style_for_csv(path) is not None)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "paths",
        nargs="*",
        type=Path,
        help="CSV files or result directories to replot. Defaults to all experiment result CSVs.",
    )
    parser.add_argument(
        "--formats",
        default="svg,png,pdf",
        help="Comma-separated output formats. Default: svg,png,pdf.",
    )
    parser.add_argument(
        "--dpi",
        type=int,
        default=1200,
        help="Raster output DPI. Default: 1200.",
    )
    return parser.parse_args()


def expand_paths(paths: list[Path]) -> list[Path]:
    if not paths:
        return discover_csvs(RESULT_ROOTS)

    csvs: list[Path] = []
    for path in paths:
        path = path.resolve()
        if path.is_dir():
            csvs.extend(discover_csvs([path]))
        elif path.is_file() and style_for_csv(path) is not None:
            csvs.append(path)
    return sorted(set(csvs))


def main() -> int:
    args = parse_args()
    if args.dpi <= 0:
        raise SystemExit("--dpi must be positive")
    formats = [fmt.strip().lower() for fmt in args.formats.split(",") if fmt.strip()]
    if not formats:
        raise SystemExit("--formats must include at least one format")
    supported_formats = {"svg", "png", "pdf"}
    unknown_formats = sorted(set(formats) - supported_formats)
    if unknown_formats:
        raise SystemExit(f"unsupported output format(s): {', '.join(unknown_formats)}")

    plt, FuncFormatter, MaxNLocator = configure_matplotlib()
    csv_paths = expand_paths(args.paths)
    if not csv_paths:
        print("No benchmark CSV files found to replot.")
        return 0

    written: list[Path] = []
    skipped: list[Path] = []
    for csv_path in csv_paths:
        outputs = replot_csv(
            csv_path,
            plt=plt,
            FuncFormatter=FuncFormatter,
            MaxNLocator=MaxNLocator,
            formats=formats,
            dpi=args.dpi,
        )
        if not outputs:
            skipped.append(csv_path)
        else:
            written.extend(outputs)
            for output in outputs:
                print(f"Wrote {output}")

    print(f"Replotted {len(csv_paths) - len(skipped)} CSV-backed figure(s); wrote {len(written)} file(s).")
    if skipped:
        print(f"Skipped {len(skipped)} CSV file(s) with no plottable data.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
