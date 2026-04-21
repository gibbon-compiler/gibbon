#!/usr/bin/env python3
"""Benchmark the manual ScalarCountSmoke vectorization experiment.

This script compiles the generated/manual C smoke test into AVX2-off and
AVX2-on variants, runs each variant repeatedly, parses the timing output, and
prints compact tables of averages and speedups.

It intentionally does not regenerate ScalarCountSmoke.c. The file is a manual
experiment and must already contain the benchmark harness.
"""

from __future__ import annotations

import argparse
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from statistics import mean


REPO_ROOT = Path(__file__).resolve().parent
DEFAULT_SOURCE = (
    REPO_ROOT
    / "gibbon-compiler"
    / "examples"
    / "soa_examples"
    / "programs"
    / "SOA"
    / "ScalarCountSmoke.c"
)
DEFAULT_BUILD_DIR = Path(tempfile.gettempdir()) / "gibbon_scalar_count_smoke_bench"


VARIANTS = [
    ("recursive", "Recursive scalar", "recursive_add1_seconds"),
    ("loop_scalar_copy", "Loop scalar, copies dcon/float", "loop_scalar_add1_seconds"),
    (
        "loop_explicit_vector_copy",
        "Loop explicit vector, copies dcon/float",
        "loop_vectorized_add1_seconds",
    ),
    ("indir_loop_scalar", "Indirection loop scalar", "indir_loop_scalar_add1_seconds"),
    ("indir_loop_auto", "Indirection auto-vector loop", "indir_loop_auto_add1_seconds"),
    (
        "indir_loop_explicit_vector",
        "Indirection explicit vector",
        "indir_loop_vectorized_add1_seconds",
    ),
]


@dataclass(frozen=True)
class BuildConfig:
    key: str
    label: str
    flags: tuple[str, ...]
    exe_name: str


BUILDS = [
    BuildConfig(
        key="avx2_off",
        label="AVX2 Off",
        flags=("-O3", "-flto", "-ftree-vectorize", "-mno-avx2", "-DMANUAL_DISABLE_AVX2"),
        exe_name="ScalarCountSmoke_avx2_off.exe",
    ),
    BuildConfig(
        key="avx2_on",
        label="AVX2 On",
        flags=("-O3", "-flto", "-ftree-vectorize", "-mavx2"),
        exe_name="ScalarCountSmoke_avx2_on.exe",
    ),
]


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


def cpu_supports_avx2() -> bool:
    machine = platform.machine().lower()
    if machine not in {"x86_64", "amd64", "i386", "i686"}:
        return False

    cpuinfo = Path("/proc/cpuinfo")
    if cpuinfo.exists():
        try:
            return "avx2" in cpuinfo.read_text(errors="ignore").lower()
        except OSError:
            pass

    lscpu = shutil.which("lscpu")
    if lscpu:
        proc = run_command([lscpu], cwd=REPO_ROOT)
        return "avx2" in (proc.stdout + proc.stderr).lower()

    return False


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


def compile_variant(args: argparse.Namespace, build: BuildConfig) -> Path:
    cc = args.cc or os.environ.get("CC") or "gcc"
    out = args.build_dir / build.exe_name
    rts_build = REPO_ROOT / "gibbon-rts" / "build"
    uthash = REPO_ROOT / "deps" / "uthash"

    require_file(args.source, "ScalarCountSmoke C source")
    require_file(rts_build / "gibbon_rts.h", "RTS header")
    require_file(rts_build / "libgibbon_rts.a", "C RTS archive")
    require_file(rts_build / "libgibbon_rts_ng.so", "Rust RTS shared library")
    require_file(uthash / "uthash.h", "uthash header")

    args.build_dir.mkdir(parents=True, exist_ok=True)

    cmd = [
        cc,
        "-std=gnu11",
        *build.flags,
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


def run_benchmark(args: argparse.Namespace, exe: Path, build: BuildConfig) -> dict[str, object]:
    samples: dict[str, list[float]] = {key: [] for key, _, _ in VARIANTS}
    sums_ok = 0
    failures = 0

    for i in range(args.iterations):
        proc = run_command([str(exe)], cwd=REPO_ROOT)
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

        for key, _, output_key in VARIANTS:
            value = parsed.get(output_key)
            if isinstance(value, float):
                samples[key].append(value)

        if args.progress and (i + 1) % args.progress == 0:
            print(f"{build.label}: completed {i + 1}/{args.iterations}", flush=True)

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


def print_report(results: list[dict[str, object]]) -> None:
    by_key = {result["build"].key: result for result in results}  # type: ignore[index,union-attr]
    labels = {result["build"].key: result["build"].label for result in results}  # type: ignore[index,union-attr]

    print("\n# ScalarCountSmoke Benchmark\n")
    for result in results:
        build: BuildConfig = result["build"]  # type: ignore[assignment]
        print(
            f"- {build.label}: runs={result['runs']} sums_ok={result['sums_ok']} "
            f"failures={result['failures']}"
        )
    print()

    if "avx2_off" in by_key and "avx2_on" in by_key:
        off_avgs = by_key["avx2_off"]["averages"]  # type: ignore[index]
        on_avgs = by_key["avx2_on"]["averages"]  # type: ignore[index]
        rows = []
        for key, label, _ in VARIANTS:
            off = off_avgs[key]
            on = on_avgs[key]
            rows.append([
                label,
                fmt_seconds(off),
                fmt_seconds(on),
                fmt_speedup(off / on),
            ])
        print("## Average Seconds\n")
        print(markdown_table(["Variant", "AVX2 Off", "AVX2 On", "On vs Off"], rows))
        print()

        rows = []
        off_rec = off_avgs["recursive"]
        on_rec = on_avgs["recursive"]
        for key, label, _ in VARIANTS:
            rows.append([
                label,
                fmt_speedup(off_rec / off_avgs[key]),
                fmt_speedup(on_rec / on_avgs[key]),
            ])
        print("## Speedup vs Recursive\n")
        print(markdown_table(["Variant", "AVX2 Off", "AVX2 On"], rows))
        print()

        rows = [
            [
                "Auto-vector over scalar indirection",
                fmt_speedup(off_avgs["indir_loop_scalar"] / off_avgs["indir_loop_auto"]),
                fmt_speedup(on_avgs["indir_loop_scalar"] / on_avgs["indir_loop_auto"]),
            ],
            [
                "Explicit vector over scalar indirection",
                fmt_speedup(off_avgs["indir_loop_scalar"] / off_avgs["indir_loop_explicit_vector"]),
                fmt_speedup(on_avgs["indir_loop_scalar"] / on_avgs["indir_loop_explicit_vector"]),
            ],
            [
                "Explicit vector over auto-vector indirection",
                fmt_speedup(off_avgs["indir_loop_auto"] / off_avgs["indir_loop_explicit_vector"]),
                fmt_speedup(on_avgs["indir_loop_auto"] / on_avgs["indir_loop_explicit_vector"]),
            ],
        ]
        print("## Indirection-Only Comparisons\n")
        print(markdown_table(["Comparison", "AVX2 Off", "AVX2 On"], rows))
        print()

        best_key = min(VARIANTS, key=lambda item: on_avgs[item[0]])[0]
        best_label = next(label for key, label, _ in VARIANTS if key == best_key)
        print(
            f"Best AVX2-on variant: {best_label} "
            f"({fmt_seconds(on_avgs[best_key])}, "
            f"{fmt_speedup(on_rec / on_avgs[best_key])} vs recursive)."
        )
    else:
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


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Compile and benchmark the manual ScalarCountSmoke C harness."
    )
    parser.add_argument("--source", type=Path, default=DEFAULT_SOURCE)
    parser.add_argument("--iterations", "-n", type=int, default=100)
    parser.add_argument("--build-dir", type=Path, default=DEFAULT_BUILD_DIR)
    parser.add_argument("--cc", default=None, help="C compiler to use, defaults to $CC or gcc")
    parser.add_argument(
        "--build",
        choices=["both", "avx2-off", "avx2-on"],
        default="both",
        help="Which binaries to compile and run.",
    )
    parser.add_argument(
        "--force-avx2",
        action="store_true",
        help="Run the AVX2-on binary even if this machine does not advertise AVX2.",
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
    args.source = args.source.resolve()
    args.build_dir = args.build_dir.resolve()

    if args.iterations <= 0:
        raise SystemExit("--iterations must be positive")

    selected = BUILDS
    if args.build == "avx2-off":
        selected = [BUILDS[0]]
    elif args.build == "avx2-on":
        selected = [BUILDS[1]]

    if any(build.key == "avx2_on" for build in selected):
        if not args.force_avx2 and not cpu_supports_avx2():
            raise SystemExit(
                "This machine does not appear to support AVX2. "
                "Use --build avx2-off, or pass --force-avx2 if you know it is safe."
            )

    maybe_build_rts(args)

    results = []
    for build in selected:
        exe = compile_variant(args, build)
        result = run_benchmark(args, exe, build)
        results.append(result)

    print_report(results)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
