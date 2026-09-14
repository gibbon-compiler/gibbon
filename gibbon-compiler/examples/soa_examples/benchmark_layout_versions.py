#!/usr/bin/env python3
"""Run side-by-side Gibbon AoS/SoA layout optimization comparisons.

This is a thin parent script around the sibling `gibbon_benchmark.py` in this
same directory.  It runs the benchmark configurations needed to compare the
built-in layout/optimization variants and combines their JSON outputs into one
Markdown report:

AoS:
  1. immutable cursors, recursive
  2. mutable cursors, recursive
  3. mutable cursors, loopified

SoA:
  1. immutable cursors, recursive
  2. mutable cursors, recursive
  3. mutable cursors, loopified
  4. mutable cursors, loopified + selective buffer sharing
  5. mutable cursors, loopified + selective buffer sharing + SIMD vectorization
  6. as (5), but the generated C is compiled with -msse4.1

Instruction set:
  Version 6 differs from version 5 ONLY in the ISA passed to the C compiler.
  This axis is kept separate from --opt-vectorization on purpose: -msse4.1
  applies to the whole translation unit -- including the scalar tail loop and
  GCC's own auto-vectorizer -- so folding it into the vectorization flag would
  make the vectorized/scalar delta impossible to attribute.  Comparing 5 vs 6
  isolates the effect of granting the C compiler SSE4.1.

Int width:
  Integer width is declared by each source program (Int8/Int16/Int32/Int64;
  bare Int means Int64).  There is no whole-program width mode: the removed
  --32-bit/--int32 option is rejected.
"""

from __future__ import annotations

import argparse
import json
import queue
import shutil
import re
import subprocess
import tempfile
import sys
import textwrap
import threading
import time
import math
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple


# This script lives in gibbon-compiler/examples/soa_examples/ alongside the
# gibbon_benchmark.py it drives.  BENCH_DIR is therefore simply its own
# directory, and REPO_ROOT is three levels up
# (soa_examples -> examples -> gibbon-compiler -> repo root).
BENCH_DIR = Path(__file__).resolve().parent
REPO_ROOT = BENCH_DIR.parents[2]
BENCH_SCRIPT = BENCH_DIR / "gibbon_benchmark.py"


@dataclass(frozen=True)
class Version:
    key: str
    title: str
    run_key: str
    json_variant: str
    description: str


@dataclass(frozen=True)
class RunConfig:
    key: str
    args: Tuple[str, ...]
    versions: Tuple[Version, ...]
    # True when every flag in `args` only affects passes marked OPT:MayVectorize
    # -- i.e. map passes.  A program with no map pass produces byte-identical
    # code in such a configuration (verified: DecisionTree.hs, 12 folds, is
    # identical across all six vectorizer configs), so building and running it
    # there measures nothing and is skipped.  See skip_mapless_programs().
    map_only: bool = False


VERSIONS: Tuple[Version, ...] = (
    Version("aos_imm_recursive", "AoS imm recursive", "recursive", "aos_imm",
            "AoS, immutable/non-mutable cursors, recursive traversal"),
    Version("aos_mut_recursive", "AoS mut recursive", "recursive", "aos",
            "AoS, mutable cursors, recursive traversal"),
    Version("aos_mut_loopified", "AoS mut loopified", "loopified", "aos",
            "AoS, mutable cursors, OPT:MayVectorize loopification"),
    Version("soa_imm_recursive", "SoA imm recursive", "recursive", "soa_imm",
            "SoA, immutable/non-mutable cursors, recursive traversal"),
    Version("soa_mut_recursive", "SoA mut recursive", "recursive", "soa",
            "SoA, mutable cursors, recursive traversal"),
    Version("soa_mut_loopified", "SoA mut loopified", "loopified", "soa",
            "SoA, mutable cursors, scalar-counted loopification"),
    Version("soa_mut_loopified_selective", "SoA mut loop+share", "selective", "soa",
            "SoA, mutable cursors, loopification plus selective buffer sharing"),
    # --- the vectorizer 2x2 -------------------------------------------------
    # There are TWO vectorizers in play: GCC's auto-vectorizer (on by default at
    # -O3) and Gibbon's explicit SIMD pass.  Turning OFF --opt-vectorization
    # does NOT give a scalar baseline, because GCC still vectorizes the loop.
    # These four configs vary both independently so the contribution of each can
    # actually be attributed.  All four sit on top of loopification + sharing.
    Version("ls_scalar", "loop+share scalar", "ls_scalar", "soa",
            "Loopified + shared, BOTH vectorizers off (--no-gcc-vectorize (compiler-aware loop+SLP disable), no --opt-vectorization). "
            "The only true scalar baseline in the matrix"),
    Version("ls_gccvec", "loop+share GCCvec", "ls_gccvec", "soa",
            "Loopified + shared, GCC auto-vectorizer only (this is what the old 'selective' column was)"),
    Version("ls_gibvec", "loop+share Gibbonvec", "ls_gibvec", "soa",
            "Loopified + shared, Gibbon's SIMD pass only (GCC auto-vectorizer disabled; explicit "
            "intrinsics are unaffected by --no-gcc-vectorize (compiler-aware loop+SLP disable))"),
    Version("ls_both", "loop+share both vec", "ls_both", "soa",
            "Loopified + shared, both vectorizers (this is what the old 'vectorized' column was)"),
    Version("ls_gibvec_sse41", "loop+share Gibbonvec (SSE4.1)", "ls_gibvec_sse41", "soa",
            "Gibbon SIMD only at --simd-isa=sse4.1: -msse4.1 for the C compiler AND "
            "Gibbon's own _mm_mullo_epi32 W32 multiply. Only run at --simd-isa=sse2, "
            "since every wider ISA already has SSE4.1"),
    Version("ls_both_sse41", "loop+share both vec (SSE4.1)", "ls_both_sse41", "soa",
            "Both vectorizers at --simd-isa=sse4.1. Only run at --simd-isa=sse2"),
)


# Columns that mean anything for a FOLD pass.  Loopification, selective buffer
# sharing and SIMD vectorization only fire on OPT:MayVectorize (map) passes, so
# the remaining configurations compile a fold to byte-identical code -- verified
# by diffing the generated C.  Showing them would imply an optimization applied
# where none did, and the differences are pure measurement artifact.
FOLD_VERSIONS: Tuple[Version, ...] = tuple(v for v in VERSIONS if v.run_key == "recursive")


def versions_for_kind(kind: str) -> Tuple[Version, ...]:
    return FOLD_VERSIONS if kind == "fold" else VERSIONS


# ---------------------------------------------------------------------------
# Report modes
# ---------------------------------------------------------------------------
# The vectorizer 2x2 and the SSE4.1 axis exist to ATTRIBUTE a speedup between
# GCC's auto-vectorizer, Gibbon's SIMD pass and the SSE4.1 ISA permission.  That
# attribution is the point of the arithmetic-intensity experiment and noise in
# an application sweep, where the six configurations differ by ~9% end to end
# and mostly reflect code layout.  So the full sweep runs and reports ONE
# vectorized configuration, and the detailed matrix is enabled by
# --verify-intensity-codegen along with the intensity table.
#
# ls_both is the representative: both vectorizers, every vectorization
# capability the driver's ISA offers switched on.  It was ls_both_sse41, on the
# strength of being "the fastest of the six" at 0.2773s against 0.2800s -- but
# at the driver's avx2 default that configuration compiled to the same bytes as
# ls_both, so the two numbers were the same compile measured twice and the gap
# was noise.  THAT COMPARISON, AND EVERY NUMBER RECORDED FOR ls_both_sse41 OR
# ls_gibvec_sse41 AT AN ISA OTHER THAN sse2, NEEDS RE-MEASURING.
HEADLINE_VECTOR_RUN_KEY = "ls_both"
DETAIL_ONLY_RUN_KEYS = frozenset(
    {"ls_scalar", "ls_gccvec", "ls_gibvec", "ls_gibvec_sse41", "ls_both_sse41"}
)


def detailed_mode(args: argparse.Namespace) -> bool:
    """True when the full vectorizer matrix and the intensity table are wanted.

    Driven by --intensity-report, NOT by --verify-intensity-codegen.  Those were
    briefly the same flag, which was a mistake: "verify" reads as a safety check
    you would leave in any command, so a full application sweep silently ran and
    reported all nine configurations.  Verification is now free of side effects
    and safe to pass anywhere; only --intensity-report changes what is measured.
    """
    return bool(getattr(args, "intensity_report", False))


LOOP_SHARE: Tuple[str, ...] = (
    "--opt-loopification", "--auto-loopification",
    "--store-scalar-field-counts", "--opt-selective-buffer-sharing",
)


RUN_CONFIGS: Tuple[RunConfig, ...] = (
    RunConfig(
        "recursive",
        ("--benchmark-immutable",),
        tuple(v for v in VERSIONS if v.run_key == "recursive"),
    ),
    RunConfig(
        "loopified",
        ("--opt-loopification", "--auto-loopification", "--store-scalar-field-counts"),
        tuple(v for v in VERSIONS if v.run_key == "loopified"),
        map_only=True,
    ),
    RunConfig(
        "selective",
        ("--opt-loopification", "--auto-loopification", "--store-scalar-field-counts",
         "--opt-selective-buffer-sharing"),
        tuple(v for v in VERSIONS if v.run_key == "selective"),
        map_only=True,
    ),
    # The vectorizer 2x2.  Ratios these enable:
    #   ls_gccvec / ls_scalar  -> what GCC's auto-vectorizer is worth
    #   ls_gibvec / ls_scalar  -> what Gibbon's vectorizer is worth ON ITS OWN
    #   ls_both   / ls_gccvec  -> what Gibbon adds on top of GCC
    #   ls_both   / ls_gibvec  -> what GCC adds on top of Gibbon
    RunConfig("ls_scalar", LOOP_SHARE + ("--no-gcc-vectorize",),
              tuple(v for v in VERSIONS if v.run_key == "ls_scalar"), map_only=True),
    RunConfig("ls_gccvec", LOOP_SHARE,
              tuple(v for v in VERSIONS if v.run_key == "ls_gccvec"), map_only=True),
    RunConfig("ls_gibvec", LOOP_SHARE + ("--opt-vectorization", "--no-gcc-vectorize"),
              tuple(v for v in VERSIONS if v.run_key == "ls_gibvec"), map_only=True),
    RunConfig("ls_both", LOOP_SHARE + ("--opt-vectorization",),
              tuple(v for v in VERSIONS if v.run_key == "ls_both"), map_only=True),
    # SSE4.1 is kept on its own axis: -msse4.1 applies to the whole translation
    # unit, so folding it into --opt-vectorization would make the delta
    # un-attributable.
    #
    # The axis only means something when the rest of the run is at sse2.  Every
    # wider ISA already HAS SSE4.1 -- -mavx2 and -march=native both define
    # __SSE4_1__ and Gibbon's own sse4.1 tier is below avx2 -- so at the
    # driver's avx2 default these two compiled identically to their non-SSE4.1
    # twins, and the difference reported between them was noise.
    # `sse41_axis_is_real` gates them; see `apply_report_mode`.
    RunConfig("ls_gibvec_sse41",
              LOOP_SHARE + ("--opt-vectorization", "--no-gcc-vectorize", "--sse4.1"),
              tuple(v for v in VERSIONS if v.run_key == "ls_gibvec_sse41"), map_only=True),
    RunConfig("ls_both_sse41", LOOP_SHARE + ("--opt-vectorization", "--sse4.1"),
              tuple(v for v in VERSIONS if v.run_key == "ls_both_sse41"), map_only=True),
)

SSE41_RUN_KEYS = frozenset({"ls_gibvec_sse41", "ls_both_sse41"})


def sse41_axis_is_real(simd_isa: str) -> bool:
    """Does asking for SSE4.1 change anything at this ISA?

    Only at sse2.  Everything wider already includes SSE4.1, so the axis would
    compare a configuration against an identical one.
    """
    return simd_isa == "sse2"


def short_status_line(line: str, limit: int = 86) -> str:
    line = " ".join(line.strip().split())
    if len(line) <= limit:
        return line
    return line[: max(0, limit - 3)] + "..."


def render_status(config_idx: int, config_count: int, config: RunConfig,
                  elapsed: float, line_count: int, latest: str) -> str:
    bar_width = 24
    # The child benchmark script does the real work; this bar shows wrapper-level
    # progress while the live message reports fine-grained child progress.
    filled = int(bar_width * (config_idx - 1) / max(config_count, 1))
    if filled < bar_width and line_count > 0:
        filled = min(bar_width, filled + 1)
    bar = "#" * filled + "-" * (bar_width - filled)
    return (f"\r[{bar}] {config_idx}/{config_count} {config.key} "
            f"elapsed={elapsed:6.1f}s lines={line_count:5d} "
            f"{short_status_line(latest)}")


def run_child_with_progress(cmd: Sequence[str], cwd: Path, run_dir: Path,
                            config: RunConfig, config_idx: int,
                            config_count: int, verbose: bool) -> int:
    stdout_path = run_dir / "stdout.txt"
    stderr_path = run_dir / "stderr.txt"
    start = time.time()
    latest = "starting"
    line_count = 0
    q: "queue.Queue[Optional[str]]" = queue.Queue()

    proc = subprocess.Popen(
        cmd,
        cwd=cwd,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        bufsize=1,
    )

    def reader() -> None:
        assert proc.stdout is not None
        try:
            for line in proc.stdout:
                q.put(line)
        finally:
            q.put(None)

    thread = threading.Thread(target=reader, daemon=True)
    thread.start()

    def print_status(force_newline: bool = False) -> None:
        if verbose:
            return
        msg = render_status(
            config_idx,
            config_count,
            config,
            time.time() - start,
            line_count,
            latest,
        )
        sys.stdout.write(msg)
        if force_newline:
            sys.stdout.write("\n")
        sys.stdout.flush()

    with stdout_path.open("w", encoding="utf-8") as stdout_log, \
         stderr_path.open("w", encoding="utf-8") as stderr_log:
        stderr_log.write("stderr was merged into stdout for live progress streaming.\n")
        print_status()
        reader_done = False
        while not reader_done:
            try:
                item = q.get(timeout=0.2)
            except queue.Empty:
                print_status()
                continue
            if item is None:
                reader_done = True
                break
            stdout_log.write(item)
            stdout_log.flush()
            line_count += 1
            stripped = item.rstrip("\n")
            if stripped:
                latest = stripped
            if verbose:
                sys.stdout.write(f"[{config.key}] {item}")
                sys.stdout.flush()
            else:
                print_status()

    returncode = proc.wait()
    thread.join(timeout=1.0)
    if verbose:
        print(f"[{config.key}] finished exit={returncode} elapsed={time.time() - start:.1f}s")
    else:
        latest = f"finished exit={returncode}"
        print_status(force_newline=True)
    return returncode


def md_escape(text: str) -> str:
    return text.replace("|", "\\|")


def highlight_color(speedup: Optional[float]) -> str:
    """Color the best cell by the size of the win over the row baseline."""
    if speedup is None:
        return "#d73a49"
    if speedup <= 1.05:
        return "#d73a49"  # red: essentially a tie, 0-5% faster
    if speedup <= 1.25:
        return "#0969da"  # blue: moderate, 5-25% faster
    return "#1a7f37"      # green: large, >25% faster


def highlight(text: str, enabled: bool, speedup: Optional[float] = None,
              colorize: bool = False) -> str:
    if not enabled or text in {"--", "FAIL", "missing", "fail", "n/a"}:
        return text
    if not colorize:
        return f"**{text}**"
    color = highlight_color(speedup)
    return f'<span style="color: {color}; font-weight: 700;">{text}</span>'


MAP_ENTRY_BORDERS = {
    "soa_mut_loopified": "2px dotted #0969da",
    "soa_mut_loopified_selective": "2px solid #8250df",
    "soa_mut_loopified_selective_vectorized": "2px solid #1a7f37",
}


# Result namespace for the source-typed model.  The old tree used "int32"/"int64"
# to namespace a whole-program width mode that no longer exists; a fresh name
# guarantees a stale old-mode executable or results file can never be reused as
# if it belonged to this schema.
RESULT_NAMESPACE = "srcwidth"


def version_title(version: Version, _unused: bool = False) -> str:
    return version.title


def version_description(version: Version, _unused: bool = False) -> str:
    return version.description


def map_entry_cell(version: Version, text: str, kind: Optional[str], colorize: bool) -> str:
    if (not colorize or kind != "map" or version.key not in MAP_ENTRY_BORDERS
            or text in {"--", "FAIL", "missing", "fail", "n/a"}):
        return text
    border = MAP_ENTRY_BORDERS[version.key]
    return (
        f'<span style="border: {border}; border-radius: 999px; '
        'padding: 0.05rem 0.35rem; font-weight: 700; display: inline-block; '
        'white-space: nowrap;">'
        f'{text}</span>'
    )


def min_keys(values: Dict[str, Optional[float]]) -> set:
    present = {k: v for k, v in values.items() if isinstance(v, (int, float))}
    if not present:
        return set()
    best = min(present.values())
    return {k for k, v in present.items() if v == best}


def max_keys(values: Dict[str, Optional[float]]) -> set:
    present = {k: v for k, v in values.items() if isinstance(v, (int, float))}
    if not present:
        return set()
    best = max(present.values())
    return {k for k, v in present.items() if v == best}



_T_CRIT_975 = {
    1: 12.706, 2: 4.303, 3: 3.182, 4: 2.776, 5: 2.571,
    6: 2.447, 7: 2.365, 8: 2.306, 9: 2.262, 10: 2.228,
    11: 2.201, 12: 2.179, 13: 2.160, 14: 2.145, 15: 2.131,
    16: 2.120, 17: 2.110, 18: 2.101, 19: 2.093, 20: 2.086,
    21: 2.080, 22: 2.074, 23: 2.069, 24: 2.064, 25: 2.060,
    26: 2.056, 27: 2.052, 28: 2.048, 29: 2.045, 30: 2.042,
}


def t_crit_975(n: Optional[int]) -> Optional[float]:
    if not isinstance(n, int) or n < 2:
        return None
    df = n - 1
    return _T_CRIT_975.get(df, 1.96)


def ci95_from_stderr(mean: float, stderr: Optional[float], n: Optional[int]) -> Optional[float]:
    if not isinstance(stderr, (int, float)):
        return None
    tcrit = t_crit_975(n)
    return None if tcrit is None else tcrit * float(stderr)


def fmt_ci(value: Optional[float]) -> str:
    if value is None:
        return "--"
    if value < 1e-3:
        return f"{value:.6f}"
    return f"{value:.4f}"


def pass_summary(variant: Optional[Dict], pass_name: str) -> Optional[Dict[str, Optional[float]]]:
    if not variant or not variant.get("run_success"):
        return None
    pdata = (variant.get("passes") or {}).get(pass_name)
    if not pdata:
        return None
    med = pdata.get("median_time")
    if not isinstance(med, (int, float)):
        return None
    mean = pdata.get("mean_time", med)
    if not isinstance(mean, (int, float)):
        mean = med
    n = pdata.get("n")
    ci = pdata.get("ci95_abs")
    if ci is None:
        ci = ci95_from_stderr(float(mean), pdata.get("stderr"), n)
    return {
        "median": float(med),
        "mean": float(mean),
        "ci95_abs": float(ci) if isinstance(ci, (int, float)) else None,
        "n": n if isinstance(n, int) else None,
    }


def total_pass_summary(variant: Optional[Dict]) -> Optional[Dict[str, Optional[float]]]:
    if not variant or not variant.get("run_success"):
        return None
    summaries = []
    for pname in (variant.get("passes") or {}):
        sm = pass_summary(variant, pname)
        if sm is not None:
            summaries.append(sm)
    if not summaries:
        return None
    median = sum(sm["median"] or 0.0 for sm in summaries)
    mean = sum((sm["mean"] if sm["mean"] is not None else sm["median"]) or 0.0 for sm in summaries)
    # Approximate CI for the sum of per-pass means by adding independent
    # standard errors in quadrature.  This is conservative enough for the
    # report while preserving backwards compatibility with existing JSON.
    n_vals = [sm.get("n") for sm in summaries if isinstance(sm.get("n"), int)]
    n_min = min(n_vals) if n_vals else None
    stderr_sq = 0.0
    have_stderr = False
    for sm in summaries:
        ci = sm.get("ci95_abs")
        n = sm.get("n")
        tcrit = t_crit_975(n)
        if isinstance(ci, (int, float)) and tcrit:
            stderr_sq += (float(ci) / tcrit) ** 2
            have_stderr = True
    total_ci = None
    if have_stderr:
        tcrit_total = t_crit_975(n_min) or 1.96
        total_ci = tcrit_total * math.sqrt(stderr_sq)
    return {"median": median, "mean": mean, "ci95_abs": total_ci, "n": n_min}


def fmt_runtime_cell(summary: Optional[Dict[str, Optional[float]]], colorize: bool) -> str:
    if summary is None:
        return "--"
    med = fmt_time(summary.get("median"))
    mean = fmt_time(summary.get("mean"))
    ci = fmt_ci(summary.get("ci95_abs"))
    n = summary.get("n")
    n_s = f", n={n}" if isinstance(n, int) else ""
    if colorize:
        return f"med {med}<br><small>mean {mean} ±{ci}{n_s}</small>"
    return f"med {med}; mean {mean} ±{ci}{n_s}"


def runtime_stat_value(summary: Optional[Dict[str, Optional[float]]], stat: str) -> str:
    if summary is None:
        return "--"
    if stat == "median":
        return fmt_time(summary.get("median"))
    if stat == "mean":
        return fmt_time(summary.get("mean"))
    if stat == "error":
        return f"±{fmt_ci(summary.get('ci95_abs'))}"
    raise ValueError(f"unknown runtime stat row: {stat}")


def runtime_stat_rows(row_prefix: Sequence[str],
                      summaries: Dict[str, Optional[Dict[str, Optional[float]]]],
                      best_keys: set,
                      speedups: Dict[str, Optional[float]],
                      colorize_best: bool,
                      kind: Optional[str] = None,
                      versions: Optional[Sequence["Version"]] = None) -> List[List[str]]:
    rows: List[List[str]] = []
    for idx, stat in enumerate(["median", "mean", "error"]):
        prefix = list(row_prefix) if idx == 0 else [""] * len(row_prefix)
        prefix.append(stat)
        highlight_best = stat == "median"
        rows.append(
            prefix +
            [map_entry_cell(
                v,
                highlight(runtime_stat_value(summaries[v.key], stat), highlight_best and v.key in best_keys,
                          speedups.get(v.key), colorize_best),
                kind,
                colorize_best,
             )
             for v in (versions if versions is not None else VERSIONS)]
        )
    return rows


def fmt_time(value: Optional[float]) -> str:
    if value is None:
        return "--"
    if value < 1e-3:
        return f"{value:.6f}"
    return f"{value:.4f}"


def fmt_total_cell(variant: Optional[Dict], colorize: bool = False) -> str:
    if variant is None:
        return "--"
    if not variant.get("run_success"):
        return "FAIL"
    return fmt_runtime_cell(total_pass_summary(variant), colorize)


def fmt_speedup(base: Optional[float], value: Optional[float]) -> str:
    if base is None or value is None or value <= 0:
        return "--"
    return f"{base / value:.3f}x"


def total_pass_time(variant: Optional[Dict]) -> Optional[float]:
    if not variant or not variant.get("run_success"):
        return None
    passes = variant.get("passes") or {}
    if not passes:
        return None
    total = 0.0
    saw_time = False
    for pdata in passes.values():
        med = pdata.get("median_time")
        if isinstance(med, (int, float)):
            total += float(med)
            saw_time = True
    return total if saw_time else None


def pass_time(variant: Optional[Dict], pass_name: str) -> Optional[float]:
    if not variant or not variant.get("run_success"):
        return None
    pdata = (variant.get("passes") or {}).get(pass_name)
    med = pdata.get("median_time") if pdata else None
    return float(med) if isinstance(med, (int, float)) else None


def load_json(path: Path) -> List[Dict]:
    with path.open("r", encoding="utf-8") as f:
        data = json.load(f)
    if not isinstance(data, list):
        raise ValueError(f"Expected a list in {path}")
    return data


PROGRAMS_DIR = BENCH_DIR / "programs"

# printsym (quote "Running pass Name (map[, key=N]...): ")
_PASS_ANNOT_RE = re.compile(
    r'printsym\s*\(\s*quote\s*"Running pass\s+[^("]+?\s*'
    r'\(\s*([^,)]+?)\s*(?:,\s*\w+\s*=\s*\d+)*\s*\)\s*:',
    re.IGNORECASE,
)


def programs_with_map_passes(programs_dir: Path = PROGRAMS_DIR) -> Set[str]:
    """File names that declare at least one `map` pass, by source scan.

    Static, so it works on a first run with no results to consult.  A file is
    kept if EITHER layout declares a map pass; the AoS and SoA sources of a
    program are the same program and must be benchmarked as a pair.
    """
    found: Set[str] = set()
    for layout in ("SOA", "AOS"):
        d = programs_dir / layout
        if not d.is_dir():
            continue
        for src in d.glob("*.hs"):
            try:
                text = src.read_text(encoding="utf-8", errors="ignore")
            except OSError:
                continue
            for m in _PASS_ANNOT_RE.finditer(text):
                if "map" in m.group(1).strip().lower():
                    found.add(src.name)
                    break
    return found


def programs_for_config(config: RunConfig, args: argparse.Namespace) -> Optional[List[str]]:
    """The `--programs` list to hand the child benchmark for this configuration.

    Returns None to mean "no restriction" (the child's own default set).

    Loopification, selective buffer sharing and SIMD vectorization only fire on
    passes annotated OPT:MayVectorize -- i.e. map passes.  A fold-only program
    compiled with those flags produces byte-identical code, so the run measures
    nothing but code layout and allocator state.  Half the suite is fold-only,
    so skipping those builds is most of the wall-clock cost of a full run.
    """
    requested = list(args.programs) if args.programs else None
    if not config.map_only or args.no_skip_mapless:
        return requested

    with_maps = programs_with_map_passes()
    if not with_maps:
        # Scan found nothing -- unannotated sources, or a moved programs/ dir.
        # Fall back to running everything rather than silently benchmarking none.
        return requested

    base = requested if requested is not None else default_program_set()
    if base is None:
        # Could not determine the child's default set; do not guess a list, as
        # that would silently ADD programs the default set deliberately omits.
        return requested
    return [prog for prog in base if prog in with_maps]


def default_program_set() -> Optional[List[str]]:
    """The child benchmark's default program list, or None if unavailable.

    Read from gibbon_benchmark.DEFAULT_PROGRAMS rather than by globbing
    programs/: the default set is a curated subset (it excludes OctTree.hs in
    favour of the OctTree_* splits, and the MapIntensity* microbenchmarks), so
    globbing would quietly enlarge a full-suite run.
    """
    try:
        import gibbon_benchmark
        progs = list(gibbon_benchmark.DEFAULT_PROGRAMS)
        return progs or None
    except Exception:
        return None


def write_empty_results(json_path: Path) -> None:
    """Write an empty result set for a configuration that was skipped entirely."""
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text("[]", encoding="utf-8")


def run_benchmark(config: RunConfig, args: argparse.Namespace) -> Path:
    # Deliberately NOT "int64": the old tree namespaced results by a
    # whole-program width mode that no longer exists, and reusing that name
    # would let a stale old-mode executable be picked up as if it represented
    # the source-typed model.  "srcwidth" marks the new schema.
    run_dir = args.output_dir / RESULT_NAMESPACE / config.key
    json_path = run_dir / "results.json"
    report_path = run_dir / "benchmark_report.txt"
    bench_output_dir = run_dir / "benchmark_output"
    run_dir.mkdir(parents=True, exist_ok=True)

    cmd = [
        sys.executable,
        str(BENCH_SCRIPT.name),
        "--iterations", str(args.iterations),
        "--warmup-runs", str(args.warmup_runs),
        "--warmup-iterations", str(args.warmup_iterations),
        "--cooldown-seconds", str(args.cooldown_seconds),
        "--output-dir", str(bench_output_dir),
        "--json", str(json_path),
        "--report", str(report_path),
    ]
    if args.cc:
        cmd += ["--cc", args.cc]
    if args.clean:
        cmd.append("--clean")
    if args.dump_raw:
        cmd.append("--dump-raw")
    selected = programs_for_config(config, args)
    if selected is not None and not selected:
        print(f"\n[{config.key}] skipped: no program in this run declares a map pass, "
              f"and this configuration only affects map passes.")
        write_empty_results(json_path)
        return json_path
    if selected:
        cmd.append("--programs")
        cmd.extend(selected)
    cmd.extend(config.args)

    print(f"\n[{config.key}] {' '.join(cmd)}")
    returncode = run_child_with_progress(
        cmd, BENCH_DIR, run_dir, config, args._config_index,
        len(RUN_CONFIGS), args.verbose,
    )

    if returncode != 0:
        raise RuntimeError(
            f"benchmark config '{config.key}' failed with exit code {returncode}; "
            f"see {run_dir / 'stdout.txt'} and {run_dir / 'stderr.txt'}"
        )
    if not json_path.exists():
        raise RuntimeError(f"benchmark config '{config.key}' did not write {json_path}")
    return json_path


def collect_results(json_paths: Dict[str, Path]) -> Dict[str, Dict[str, Optional[Dict]]]:
    combined: Dict[str, Dict[str, Optional[Dict]]] = {}
    for config in RUN_CONFIGS:
        rows_by_program = {row["program"]: row for row in load_json(json_paths[config.key])}
        for program, row in rows_by_program.items():
            combined.setdefault(program, {})
            for version in config.versions:
                combined[program][version.key] = row.get(version.json_variant)
    return combined


def natural_key(name: str) -> List:
    """Sort key that orders embedded numbers numerically.

    Plain alphabetical sorting puts mapPar16 between mapPar1 and mapPar2, which
    scrambles a sweep whose whole point is that the parameter increases down the
    column.  This groups by family and orders numerically inside it.
    """
    return [int(tok) if tok.isdigit() else tok.lower()
            for tok in re.split(r"(\d+)", name)]


def collect_pass_names(version_rows: Dict[str, Optional[Dict]]) -> List[str]:
    names = set()
    for variant in version_rows.values():
        if variant and variant.get("run_success"):
            names.update((variant.get("passes") or {}).keys())
    return sorted(names, key=natural_key)


def pass_kind(version_rows: Dict[str, Optional[Dict]], pass_name: str) -> str:
    for variant in version_rows.values():
        if not variant:
            continue
        pdata = (variant.get("passes") or {}).get(pass_name)
        if pdata and pdata.get("pass_type"):
            return str(pdata["pass_type"])
    return "unknown"


def speedup_value(base: Optional[float], value: Optional[float]) -> Optional[float]:
    if base is None or value is None or value <= 0:
        return None
    return base / value


def table(headers: Sequence[str], rows: Sequence[Sequence[str]]) -> str:
    header = "| " + " | ".join(md_escape(h) for h in headers) + " |"
    sep = "| " + " | ".join("---" for _ in headers) + " |"
    body = ["| " + " | ".join(md_escape(cell) for cell in row) + " |" for row in rows]
    return "\n".join([header, sep] + body)


# ---------------------------------------------------------------------------
# Arithmetic intensity of a map pass
# ---------------------------------------------------------------------------
# `mul/el` is MEASURED, not declared: the multiply count is read out of the
# scalar build the benchmark already produced, by disassembling each pass's
# innermost multiply-carrying loop.  Declared intensity is not trustworthy --
# GCC has repeatedly reduced it away (constant multipliers -> shift+add;
# `sum_k (i + c_k) * m` -> one multiply), silently, leaving a benchmark that
# still ran and still reported a flat curve.  See check_intensity_codegen.py.
#
# `ILP` cannot be recovered from the assembly, so it comes from an `ilp=N`
# annotation in the pass's printsym line.  Passes without one render as "--".

_MUL_CACHE: Dict[Path, Dict[str, Optional[int]]] = {}


def multiplies_per_pass(c_file: Path, pass_names: Sequence[str]) -> Dict[str, Optional[int]]:
    """Multiplies per element in each pass's innermost loop, from the scalar build.

    Returns None for a pass whose name is not a C function in the emitted code
    (inlined, renamed, or simply a pass with no multiply at all).  Never raises:
    a missing compiler or an unreadable file degrades to "unknown", because this
    is reporting detail, not a correctness gate -- that is what
    check_intensity_codegen.py is for.
    """
    key = c_file.resolve()
    if key in _MUL_CACHE:
        return {p: _MUL_CACHE[key].get(p) for p in pass_names}

    counts: Dict[str, Optional[int]] = {}
    try:
        import check_intensity_codegen as cic
        with tempfile.TemporaryDirectory(prefix="gibbon-mulcount-") as td:
            s_file = Path(td) / "scalar.s"
            cic.emit_asm(c_file, s_file, sse41=False, verbose=False)
            asm = s_file.read_text().split("\n")
            for pname in pass_names:
                try:
                    body = cic.function_body(asm, pname)
                except cic.CheckError:
                    counts[pname] = None
                    continue
                chunk = cic.innermost_mul_loop(body)
                counts[pname] = cic.count(chunk, "imul") if chunk is not None else 0
    except Exception:
        counts = {p: None for p in pass_names}

    _MUL_CACHE[key] = counts
    return counts


def scalar_c_file(args: argparse.Namespace, program: str) -> Optional[Path]:
    """The SoA C file emitted for the `ls_scalar` configuration, if it exists."""
    stem = Path(program).stem
    candidate = (args.output_dir / RESULT_NAMESPACE / "ls_scalar" /
                 "benchmark_output" / f"{stem}.soa.c")
    return candidate if candidate.exists() else None


def pass_ilp(version_rows: Dict[str, Optional[Dict]], pass_name: str) -> Optional[int]:
    for variant in version_rows.values():
        if not variant:
            continue
        pdata = (variant.get("passes") or {}).get(pass_name)
        if pdata and pdata.get("ilp") is not None:
            return int(pdata["ilp"])
    return None


def selected_cc(requested=None) -> str:
    """The C compiler the child benchmark will use; mirrors gibbon_benchmark."""
    try:
        import gibbon_benchmark
        return gibbon_benchmark.resolve_cc(requested)
    except Exception:
        return requested or "gcc"


def selected_cc_version(requested=None) -> str:
    try:
        import gibbon_benchmark
        return gibbon_benchmark.cc_version(selected_cc(requested))
    except Exception:
        return "unknown"


def render_report(combined: Dict[str, Dict[str, Optional[Dict]]],
                  json_paths: Dict[str, Path],
                  args: argparse.Namespace,
                  colorize_best: bool) -> str:
    version_by_key = {v.key: v for v in VERSIONS}
    # Programs declaring at least one map pass.  Decides which summary table a
    # program lands in; an empty set (unannotated sources, or --no-skip-mapless)
    # makes every program count as map-bearing, so the tables degrade to the
    # single wide form rather than mis-sorting anything.
    map_bearing = set() if args.no_skip_mapless else programs_with_map_passes()

    lines: List[str] = []
    lines.append("# Gibbon AoS/SoA Layout Optimization Comparison")
    lines.append("")
    lines.append(f"Timed iterations per executable run: {args.iterations}")
    lines.append(f"Warmup: {args.warmup_runs} run(s) x --iterate {args.warmup_iterations}")
    lines.append(f"Cooldown between variants: {args.cooldown_seconds:g}s")
    lines.append("Int width: declared by each source program (bare Int = Int64)")
    lines.append(f"Programs: {' '.join(args.programs) if args.programs else 'default benchmark set'}")
    lines.append(f"Output directory root: {args.output_dir}")
    lines.append(f"Output namespace: {RESULT_NAMESPACE}")
    lines.append(f"C compiler: {selected_cc()}  ({selected_cc_version()})")
    if detailed_mode(args):
        lines.append("Report mode: **arithmetic intensity** (`--intensity-report`) -- full "
                     "vectorizer matrix, plus the per-map intensity table.")
    else:
        lines.append(f"Report mode: **application sweep** (default) -- one vectorized "
                     f"configuration (`{HEADLINE_VECTOR_RUN_KEY}`). Pass `--intensity-report` "
                     f"for the full vectorizer matrix and the per-map intensity table.")
    lines.append("")
    lines.append("## Benchmark Runs")
    for config in RUN_CONFIGS:
        lines.append(f"- {config.key}: {json_paths[config.key]}")
    lines.append("")
    lines.append("## Compared Versions")
    for version in VERSIONS:
        lines.append(f"- {version_title(version)}: {version_description(version)}")
    lines.append("")
    if colorize_best:
        lines.append("Best entries are colored by speedup over the row baseline: red = 0-5%, blue = 5-25%, green = >25%.")
        lines.append("For map pass entries only, SoA mut loopified uses a dotted blue border, SoA mut loop+share uses a solid purple border, and SoA mut loop+share+vec uses a solid green border.")
    else:
        lines.append("Bold entries mark the lowest runtime or highest speedup in that row.")
    lines.append("")

    # The whole-program summary tables are split the same way the per-program
    # sections are.  A program with no map pass is never built in the
    # loopification/sharing/vectorization configurations, so carrying those nine
    # columns on its row would be nine dead cells implying an optimization that
    # was neither applied nor attempted.
    def program_is_map_bearing(program: str) -> bool:
        return (not map_bearing) or (program in map_bearing)

    map_programs = [p for p in sorted(combined) if program_is_map_bearing(p)]
    fold_programs = [p for p in sorted(combined) if not program_is_map_bearing(p)]

    failures: List[str] = []

    def summary_tables(programs: Sequence[str], cols: Sequence["Version"]):
        """(runtime rows, speedup rows, status rows) over `programs` x `cols`."""
        rows: List[List[str]] = []
        speed_rows: List[List[str]] = []
        status_rows: List[List[str]] = []
        for program in programs:
            version_rows = combined[program]
            summaries = {v.key: total_pass_summary(version_rows.get(v.key)) for v in cols}
            totals = {v.key: (summaries[v.key] or {}).get("median") for v in cols}
            base = totals.get("aos_imm_recursive") or totals.get("aos_mut_recursive")
            total_best = min_keys(totals)
            speedups = {v.key: speedup_value(base, totals[v.key]) for v in cols}
            speed_best = max_keys(speedups)
            rows.extend(runtime_stat_rows([program], summaries, total_best, speedups,
                                          colorize_best, versions=cols))
            speed_rows.append(
                [program] +
                [highlight(fmt_speedup(base, totals[v.key]), v.key in speed_best,
                           speedups.get(v.key), colorize_best)
                 for v in cols]
            )
            status_cells: List[str] = []
            for v in cols:
                variant = version_rows.get(v.key)
                if variant is None:
                    status_cells.append("missing")
                elif variant.get("run_success"):
                    status_cells.append("ok")
                else:
                    status_cells.append("fail")
                    failures.append(
                        f"- {program}, {version_title(v)}: "
                        f"{variant.get('error') or 'run failed'}"
                    )
            status_rows.append([program] + status_cells)
        return rows, speed_rows, status_rows

    def hdr(cols: Sequence["Version"], first: str = "Program") -> List[str]:
        return [first] + [version_title(v) for v in cols]

    map_rows, map_speed, map_status = summary_tables(map_programs, VERSIONS)
    fold_rows, fold_speed, fold_status = summary_tables(fold_programs, FOLD_VERSIONS)

    split_note = (
        "Programs are split by whether they declare any map pass. Loopification, "
        "selective buffer sharing and vectorization fire only on `OPT:MayVectorize` "
        "(map) passes, so fold-only programs are neither built nor reported in those "
        "configurations -- see `--no-skip-mapless` to run them anyway."
    )

    lines.append("## Total Timed Pass Runtime")
    lines.append("")
    lines.append("Seconds. Each benchmark expands into median, mean, and error sub-rows. Error is the two-sided 95% confidence interval for the mean.")
    lines.append("")
    lines.append(split_note)
    if map_rows:
        lines.append("")
        lines.append("### Programs with map passes")
        lines.append("")
        lines.append(table(["Program", "Statistic"] +
                           [version_title(v) for v in VERSIONS], map_rows))
    if fold_rows:
        lines.append("")
        lines.append("### Fold-only programs")
        lines.append("")
        lines.append(table(["Program", "Statistic"] +
                           [version_title(v) for v in FOLD_VERSIONS], fold_rows))
    lines.append("")
    lines.append("## Speedup Vs AoS Recursive Baseline")
    lines.append("")
    lines.append("Uses AoS immutable recursive when available, otherwise AoS mutable recursive.")
    if map_speed:
        lines.append("")
        lines.append("### Programs with map passes")
        lines.append("")
        lines.append(table(hdr(VERSIONS), map_speed))
    if fold_speed:
        lines.append("")
        lines.append("### Fold-only programs")
        lines.append("")
        lines.append(table(hdr(FOLD_VERSIONS), fold_speed))
    lines.append("")
    lines.append("## Run Status")
    lines.append("")
    lines.append("`missing` means the configuration ran but produced no row, which is worth")
    lines.append("investigating. Configurations that were deliberately skipped are not shown")
    lines.append("as columns at all.")
    if map_status:
        lines.append("")
        lines.append("### Programs with map passes")
        lines.append("")
        lines.append(table(hdr(VERSIONS), map_status))
    if fold_status:
        lines.append("")
        lines.append("### Fold-only programs")
        lines.append("")
        lines.append(table(hdr(FOLD_VERSIONS), fold_status))
    lines.append("")
    if failures:
        lines.append("## Failure Details")
        lines.append("")
        lines.extend(failures)
        lines.append("")

    lines.append("## Per-Program Pass Timings")
    lines.append("")
    lines.append("Map passes and fold passes are reported in separate sections. They are not")
    lines.append("comparable: only map passes are eligible for loopification, selective buffer")
    lines.append("sharing and SIMD vectorization, so only map passes carry the vectorizer")
    lines.append("columns and the arithmetic-intensity table.")

    for program in sorted(combined):
        version_rows = combined[program]
        pass_names = collect_pass_names(version_rows)
        if not pass_names:
            lines.append("")
            lines.append(f"{program}: no successful pass timings")
            continue
        lines.append("")
        lines.append(f"### {program}")

        by_kind: Dict[str, List[str]] = {}
        for pname in pass_names:
            by_kind.setdefault(pass_kind(version_rows, pname), []).append(pname)

        def render_group(kind_key: str, heading: str) -> None:
            group = by_kind.get(kind_key) or []
            if not group:
                return
            cols = versions_for_kind(kind_key)
            runtime_hdr = ["Pass", "Kind", "Statistic"] + [version_title(v) for v in cols]
            speed_hdr = ["Pass", "Kind"] + [version_title(v) for v in cols]
            pass_rows: List[List[str]] = []
            pass_speed_rows: List[List[str]] = []
            for pname in group:
                pass_summaries = {v.key: pass_summary(version_rows.get(v.key), pname) for v in cols}
                times = {v.key: (pass_summaries[v.key] or {}).get("median") for v in cols}
                best_times = min_keys(times)
                base_time = times.get("aos_imm_recursive") or times.get("aos_mut_recursive")
                speedups = {v.key: speedup_value(base_time, times[v.key]) for v in cols}
                best_speedups = max_keys(speedups)
                kind = pass_kind(version_rows, pname)
                pass_rows.extend(runtime_stat_rows([pname, kind], pass_summaries, best_times,
                                                   speedups, colorize_best, kind=kind, versions=cols))
                pass_speed_rows.append(
                    [pname, kind] +
                    [map_entry_cell(
                        v,
                        highlight(fmt_speedup(base_time, times[v.key]), v.key in best_speedups,
                                  speedups.get(v.key), colorize_best),
                        kind,
                        colorize_best,
                     )
                     for v in cols]
                )
            lines.append("")
            lines.append(f"#### {heading} -- timings")
            if kind_key == "fold":
                lines.append("")
                lines.append("Layout and traversal columns only. Loopification, selective buffer")
                lines.append("sharing and vectorization fire exclusively on `OPT:MayVectorize` (map)")
                lines.append("passes, so they are neither run nor reported for folds.")
            lines.append("")
            lines.append(table(runtime_hdr, pass_rows))
            lines.append("")
            lines.append(f"#### {heading} -- speedup vs AoS recursive baseline")
            lines.append("")
            lines.append("Uses AoS immutable recursive when available, otherwise AoS mutable recursive.")
            lines.append("")
            lines.append(table(speed_hdr, pass_speed_rows))

        render_group("map", "Map passes")
        if detailed_mode(args):
            lines.extend(render_intensity_table(program, version_rows,
                                                by_kind.get("map") or [], args))
        render_group("fold", "Fold passes")
        render_group("unknown", "Unclassified passes")

    return "\n".join(lines) + "\n"


def render_intensity_table(program: str,
                           version_rows: Dict[str, Optional[Dict]],
                           map_passes: Sequence[str],
                           args: argparse.Namespace) -> List[str]:
    """(pass, mul/el, ILP, scalar, SSE4.1, speedup) for every map pass.

    This is the table that answers "what did vectorization buy me", which the
    AoS-baseline tables above deliberately do not: they divide by AoS recursive,
    whose cost ALSO grows with arithmetic intensity, so their ratio shrinks as
    intensity rises even while vectorization is helping more. Here both columns
    sit on identical loopified + buffer-shared code and differ only in the
    vectorizer, so the ratio is attributable.
    """
    out: List[str] = []
    if not map_passes:
        return out

    c_file = scalar_c_file(args, program)
    muls = multiplies_per_pass(c_file, map_passes) if c_file else {p: None for p in map_passes}

    rows: List[List[str]] = []
    any_data = False
    for pname in map_passes:
        sc = (pass_summary(version_rows.get("ls_scalar"), pname) or {}).get("median")
        v41 = (pass_summary(version_rows.get("ls_gibvec_sse41"), pname) or {}).get("median")
        n_mul = muls.get(pname)
        ilp = pass_ilp(version_rows, pname)
        if sc is not None and v41 is not None:
            any_data = True
        rows.append([
            pname,
            "--" if n_mul is None else str(n_mul),
            "--" if ilp is None else str(ilp),
            "--" if sc is None else f"{sc:.4f}",
            "--" if v41 is None else f"{v41:.4f}",
            "--" if (sc is None or v41 is None or v41 <= 0) else f"{sc / v41:.2f}x",
        ])
    if not any_data:
        return out

    out.append("")
    out.append(f"#### Map passes -- vectorization vs loop+share scalar")
    out.append("")
    out.append("Seconds (median). Both columns are loopified + buffer-shared SoA and differ")
    out.append("ONLY in the vectorizer, so the speedup is attributable to it -- unlike the")
    out.append("AoS-baseline tables above, whose denominator also grows with intensity.")
    out.append("")
    out.append("- `mul/el` -- multiplies per element, **measured** by disassembling the")
    out.append("  scalar build's innermost loop, not read from the source. Declared")
    out.append("  intensity is not trustworthy: GCC has silently reduced it away more than")
    out.append("  once. `--` means the pass name is not a function in the emitted C.")
    out.append("- `ILP` -- independent dependence chains, from an `ilp=N` pass annotation.")
    out.append("  `--` where the program does not declare one.")
    out.append("- `scalar` -- `ls_scalar`: both vectorizers off (the only true scalar baseline).")
    out.append("- `SSE4.1` -- `ls_gibvec_sse41`: Gibbon SIMD only, `-msse4.1`, GCC autovec off.")
    out.append("")
    out.append(table(["Pass", "mul/el", "ILP", "scalar (s)", "SSE4.1 (s)", "speedup"], rows))
    return out


def write_report(combined: Dict[str, Dict[str, Optional[Dict]]],
                 json_paths: Dict[str, Path],
                 args: argparse.Namespace) -> None:
    args.results_file.parent.mkdir(parents=True, exist_ok=True)
    requested_is_md = args.results_file.suffix.lower() == ".md"
    report = render_report(combined, json_paths, args, colorize_best=requested_is_md)
    args.results_file.write_text(report, encoding="utf-8")
    print(f"\nWrote combined Markdown comparison: {args.results_file}")

    # Keep the Markdown companion fresh even when a run is explicitly pointed at
    # the old .txt filename.  The companion gets colorized best-cell highlights,
    # while the requested .txt report stays plain text/Markdown.
    if not requested_is_md:
        md_path = args.results_file.with_suffix(".md")
        md_path.parent.mkdir(parents=True, exist_ok=True)
        md_report = render_report(combined, json_paths, args, colorize_best=True)
        md_path.write_text(md_report, encoding="utf-8")
        print(f"Wrote Markdown companion: {md_path}")


def parse_args(argv: Optional[Sequence[str]] = None) -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description="Run AoS/SoA recursive, loopified, selective-sharing, and vectorized benchmark comparisons.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=textwrap.dedent(
            """\
            This script lives in gibbon-compiler/examples/soa_examples/, next to the
            gibbon_benchmark.py it drives.  It can be run from anywhere; output paths
            default to the repo root regardless of the working directory.

            Examples (from soa_examples/):
              ./benchmark_layout_versions.py --clean --iterations 20 --programs List.hs MonoTree.hs
              ./benchmark_layout_versions.py --iterations 20 --results-file layout_comparison.md

            Integer width is a property of each source program (Int8/Int16/
            Int32/Int64; bare Int means Int64).  To compare widths, write
            explicit-width source variants and run them as separate programs --
            there is no whole-program width switch.

            Results land under <output-dir>/srcwidth/, a new namespace, so
            executables and results produced by the removed --int32 mode can
            never be reused here.
            """
        ),
    )
    ap.add_argument("--programs", nargs="+",
                    help="Subset of benchmark source files, e.g. List.hs MonoTree.hs.")
    ap.add_argument("--iterations", type=int, default=20,
                    help="Timed iterations passed to gibbon_benchmark.py. Default: 20.")
    ap.add_argument("--warmup-runs", type=int, default=1,
                    help="Untimed warmup runs before each measured variant. Default: 1.")
    ap.add_argument("--warmup-iterations", type=int, default=1,
                    help="--iterate value for each warmup run. Default: 1.")
    ap.add_argument("--cooldown-seconds", type=float, default=3.0,
                    help="Sleep between variant runs in the child benchmark. Default: 3.0.")
    ap.add_argument("--clean", action="store_true",
                    help="Force recompilation in each benchmark run.")
    ap.add_argument("--dump-raw", action="store_true",
                    help="Ask gibbon_benchmark.py to save raw executable stdout.")
    # Tombstone only: recognized so it can be rejected, suppressed from --help,
    # and never turned into configuration.  See the note on RESULT_NAMESPACE.
    ap.add_argument("--32-bit", "--int32", dest="removed_int32_mode",
                    action="store_true", help=argparse.SUPPRESS)

    ap.add_argument("--verbose", "-v", action="store_true",
                    help="Stream child benchmark output in real time instead of the compact status bar.")
    ap.add_argument("--cc", default=None,
                    help="C compiler Gibbon shells out to. Default: gcc-16 if present, else gcc. "
                         "Pinned deliberately -- GCC 15 fails to register-promote the SoA "
                         "traversal's cursors across loop iterations, inflating SoA fold times by "
                         "~2.7x (List.hs/sumList: 143.7ms on GCC 15 vs 48.1ms on GCC 16, where SoA "
                         "is actually FASTER than AoS). The compiler and its version are recorded "
                         "in the report header so a silent toolchain change cannot go unnoticed.")
    ap.add_argument("--no-skip-mapless", action="store_true",
                    help="Benchmark every program in every configuration, including fold-only "
                         "programs in the loopification/sharing/vectorization configurations. "
                         "Those flags only fire on passes marked OPT:MayVectorize, so a fold-only "
                         "program compiles to byte-identical code in all of them and the extra "
                         "runs measure only code layout and allocator state -- which is why they "
                         "are skipped by default. Pass this to restore the old behaviour, e.g. to "
                         "quantify the representation cost that --store-scalar-field-counts "
                         "imposes on folds.")
    ap.add_argument("--intensity-report", action="store_true",
                    help="Arithmetic-intensity mode: run the FULL vectorizer matrix -- both "
                         "vectorizers varied independently plus the SSE4.1 axis -- and add the "
                         "per-map `(pass, mul/el, ILP, scalar, SSE4.1, speedup)` table. Implies "
                         "--verify-intensity-codegen. Without it the sweep runs and reports one "
                         f"vectorized configuration ({HEADLINE_VECTOR_RUN_KEY}: both vectorizers, "
                         "-msse4.1), because attributing a speedup between the two vectorizers is "
                         "only meaningful for the intensity experiment and is noise on application "
                         "traversals -- the six configurations differ by ~9%% there, mostly code "
                         "layout.")
    ap.add_argument("--verify-intensity-codegen", action="store_true",
                    help="Before benchmarking, run check_intensity_codegen.py "
                         "and abort if it "
                         "fails. The arithmetic-intensity programs only measure intensity if the "
                         "arithmetic they declare survives into the generated code, and it has "
                         "repeatedly not: GCC strength-reduced constant multipliers to shift+add, "
                         "and reassociated a sum of products into a single multiply. Both "
                         "collapses were silent -- the sweep still produced numbers, and the "
                         "numbers were meaningless. Use this whenever you intend to cite the "
                         "MapIntensity results.")
    # Defaults are anchored to the repo root rather than the current working
    # directory, so results land in the same place whether this is invoked from
    # the repo root or from soa_examples/.  Relative paths given on the command
    # line still resolve against the CWD, as usual.
    ap.add_argument("--output-dir", type=Path,
                    default=REPO_ROOT / "layout_version_benchmark_output",
                    help="Directory for the per-configuration benchmark outputs. "
                         "Default: <repo-root>/layout_version_benchmark_output.")
    ap.add_argument("--results-file", type=Path,
                    default=REPO_ROOT / "layout_version_comparison.md",
                    help="Combined side-by-side Markdown report to write. "
                         "Default: <repo-root>/layout_version_comparison.md.")
    return ap.parse_args(argv)


def apply_report_mode(args: argparse.Namespace) -> None:
    """Narrow RUN_CONFIGS/VERSIONS to the headline set unless in detailed mode.

    Rebinding the module globals keeps every downstream consumer -- the runner,
    collect_results, and the renderer -- consistent with a single decision, so a
    configuration cannot be run but not reported, or vice versa.
    """
    global RUN_CONFIGS, VERSIONS
    if not sse41_axis_is_real(getattr(args, "simd_isa", "avx2")):
        RUN_CONFIGS = tuple(c for c in RUN_CONFIGS if c.key not in SSE41_RUN_KEYS)
        VERSIONS = tuple(v for v in VERSIONS if v.run_key not in SSE41_RUN_KEYS)
    if detailed_mode(args):
        return
    RUN_CONFIGS = tuple(c for c in RUN_CONFIGS if c.key not in DETAIL_ONLY_RUN_KEYS)
    # With the matrix collapsed to one column, the headline no longer contrasts
    # with anything; name it for what it is in this report.
    VERSIONS = tuple(
        replace(v, title="SoA mut loop+share+vec",
                description="SoA, mutable cursors, loopification plus selective buffer sharing "
                            "plus SIMD vectorization (both vectorizers)")
        if v.run_key == HEADLINE_VECTOR_RUN_KEY else v
        for v in VERSIONS if v.run_key not in DETAIL_ONLY_RUN_KEYS
    )


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = parse_args(argv)

    # Reject the removed whole-program width mode before any output directory is
    # created or any child compile is launched.
    if getattr(args, "removed_int32_mode", False):
        print("error: --32-bit/--int32 has been removed; use explicit Int32 source "
              "types.\n"
              "       Integer width is declared by the source program (Int8/Int16/"
              "Int32/Int64;\n"
              "       bare Int means Int64).  To compare widths, write explicit-width\n"
              "       source variants and run them as separate programs.",
              file=sys.stderr)
        return 2
    if args.intensity_report:
        # A detailed intensity report you have not verified is precisely the
        # trap check_intensity_codegen.py exists to catch.
        args.verify_intensity_codegen = True
    apply_report_mode(args)
    if not BENCH_SCRIPT.exists():
        print(f"Missing benchmark script: {BENCH_SCRIPT}", file=sys.stderr)
        return 2

    args.output_dir = args.output_dir.resolve()
    args.results_file = args.results_file.resolve()

    if args.verify_intensity_codegen:
        checker = BENCH_DIR / "check_intensity_codegen.py"
        if not checker.exists():
            print(f"error: {checker} not found", file=sys.stderr)
            return 2
        for layout in ("SOA", "AOS"):
            print(f"Verifying intensity codegen ({layout}) ...")
            cmd = [sys.executable, str(checker), "--layout", layout]
            rc = subprocess.run(cmd).returncode
            if rc != 0:
                print("\nAborting: the intensity benchmarks are not emitting the arithmetic "
                      "they declare, so any speedup curve from them would be meaningless.",
                      file=sys.stderr)
                return rc

    json_paths: Dict[str, Path] = {}
    try:
        for idx, config in enumerate(RUN_CONFIGS, start=1):
            args._config_index = idx
            json_paths[config.key] = run_benchmark(config, args)
        combined = collect_results(json_paths)
        write_report(combined, json_paths, args)
    except Exception as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
