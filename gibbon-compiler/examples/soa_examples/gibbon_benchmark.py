#!/usr/bin/env python3
"""
Gibbon Compiler Benchmark Suite v3.0
=====================================
Benchmarks AoS vs SoA gibbon programs and produces publication-quality
LaTeX tables and matplotlib figures.

Field-usage analysis:
  Gibbon's SoA mode is hypothesised to win on passes that access fewer
  fields of the ADT (i.e. more "dead" fields are skipped).
  Two source annotations drive this analysis:

    (a) ADT field count — one comment per source file, near the type def:
          -- @BENCH adt_fields=5

    (b) Per-pass field usage — extend the existing printsym line:
          _ = printsym (quote "Running pass SumArea (fold, uses=2): ")
          _ = printsym (quote "Running pass scaleLayout (map, uses=5): ")

  From these the script computes:
    dead_fields = adt_fields - uses
    dead_ratio  = dead_fields / adt_fields   (0 = all used, 1 = none used)

  A scatter-plot of dead_ratio vs speedup is produced to visualise the
  correlation between "deadness" and SoA benefit.

Fold/map detection (dual strategy):
  PRIMARY:  exe output line "Running pass Foo (fold, uses=2):"
  FALLBACK: source-file printsym scan (also captures uses= and adt_fields)

Usage:
  ./gibbon_benchmark.py                          run all programs
  ./gibbon_benchmark.py --programs DomTree.hs    run one program
  ./gibbon_benchmark.py --clean                  force recompile
  ./gibbon_benchmark.py --generate-paper         LaTeX + figures
  ./gibbon_benchmark.py --iterations 50 --generate-paper
"""

import os, re, sys, json, time, shutil, argparse, statistics, subprocess
import multiprocessing
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Dict, List, Optional, Tuple

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import numpy as np

# ---------------------------------------------------------------------------
# Default program list
# ---------------------------------------------------------------------------
DEFAULT_PROGRAMS = [
    "Compiler.hs", "DBQuery.hs", "DecisionTree.hs", "DomTree.hs",
    "KDTree.hs", "LinearListReduction.hs", "List.hs", "MonoTree.hs",
    "ObjectGraph.hs", "OctTree.hs", "PiecewiseFunctions.hs",
    "TernaryTree.hs", "Trie.hs",
]

# ---------------------------------------------------------------------------
# Result container
# ---------------------------------------------------------------------------
class BenchmarkResult:
    def __init__(self, program: str, variant: str):
        self.program                  = program
        self.variant                  = variant
        self.passes: Dict             = {}
        self.output: Optional[str]    = None
        self.compile_time             = 0.0
        self.compile_success          = False
        self.run_success              = False
        self.error_message: Optional[str] = None

# ---------------------------------------------------------------------------
# Source-file annotation scanner
# ---------------------------------------------------------------------------

def _name_variants(name: str) -> List[str]:
    """Return all variants of a pass name to index under."""
    strip_pass = re.sub(r'[Pp]ass$', '', name).strip()
    variants: set = set()
    for base in (name, strip_pass):
        b = base.strip()
        if not b:
            continue
        variants.add(b)
        variants.add(b.lower())
        variants.add(b.replace(' ', ''))
        variants.add(b.replace(' ', '').lower())
        variants.add(b.title().replace(' ', ''))
        variants.add(b.replace(' ', '') + 'Pass')
        variants.add(b.replace(' ', '').lower() + 'pass')
    return [v for v in variants if v]


def build_source_classification(programs_dir: Path) -> Dict[str, Dict]:
    """
    Scan AoS/*.hs and SoA/*.hs for:
      -- @BENCH adt_fields=N
      printsym (quote "Running pass Name (type[, uses=N]): ")

    Returns:
      {
        prog_filename: {
          "adt_fields": int | None,
          "pass_types": {name_variant: "fold"|"map"|"unknown"},
          "pass_uses":  {name_variant: int},   # fields used by each pass
        }
      }
    """
    result: Dict[str, Dict] = {}

    # Match:  -- @BENCH adt_fields=N
    adt_re   = re.compile(r'--\s*@BENCH\s+adt_fields\s*=\s*(\d+)', re.IGNORECASE)

    # Match:  printsym (quote "Running pass Name (fold[, uses=N]): ")
    # Group 1 = name, Group 2 = type keyword, Group 3 = uses value (optional)
    pass_re  = re.compile(
        r'printsym\s*\(\s*quote\s*"Running pass\s+([^("]+?)\s*'
        r'\(\s*([^,)]+?)\s*(?:,\s*uses\s*=\s*(\d+))?\s*\)\s*:',
        re.IGNORECASE,
    )

    print(f"\n{'='*70}")
    print("Scanning source files for field-usage annotations ...")
    print(f"{'='*70}")

    for vdir in ("AOS", "SOA"):
        vpath = programs_dir / vdir
        if not vpath.exists():
            continue
        for src in sorted(vpath.glob("*.hs")):
            prog = src.name
            if prog not in result:
                result[prog] = {
                    "adt_fields": None,
                    "pass_types": {},
                    "pass_uses":  {},
                }
            try:
                content = src.read_text(encoding="utf-8", errors="ignore")
            except Exception as e:
                print(f"  ✗ {src.name}: {e}")
                continue

            # ADT fields
            m = adt_re.search(content)
            if m and result[prog]["adt_fields"] is None:
                result[prog]["adt_fields"] = int(m.group(1))
                if vdir == "AOS":
                    print(f"  ✓ {prog}: adt_fields={m.group(1)}")

            # Per-pass annotations
            found = 0
            for pm in pass_re.finditer(content):
                raw_name  = pm.group(1).strip()
                raw_type  = pm.group(2).strip().lower()
                raw_uses  = pm.group(3)            # may be None
                ptype = ("fold"    if "fold" in raw_type
                         else ("map" if "map"  in raw_type else "unknown"))
                uses  = int(raw_uses) if raw_uses is not None else None

                for variant in _name_variants(raw_name):
                    result[prog]["pass_types"][variant] = ptype
                    if uses is not None:
                        result[prog]["pass_uses"][variant] = uses

                found += 1
                if vdir == "AOS":
                    uses_str = f", uses={uses}" if uses is not None else " (no uses annotation)"
                    print(f"  ✓ {prog}: '{raw_name}' → {ptype}{uses_str}")

            if found == 0 and vdir == "AOS":
                print(f"  ⚠  {prog}: no pass annotations found")

    # Summary
    with_adt   = sum(1 for v in result.values() if v["adt_fields"] is not None)
    with_passes = sum(1 for v in result.values() if v["pass_types"])
    with_uses  = sum(1 for v in result.values()
                     if any(u is not None for u in v["pass_uses"].values()))
    print(f"\n  {with_adt} programs have adt_fields annotation")
    print(f"  {with_passes} programs have pass type annotations")
    print(f"  {with_uses} programs have uses= field-usage annotations")
    print(f"{'='*70}\n")
    return result


def lookup_pass_type(exe_pass_name: str, src_data: Dict) -> str:
    for v in _name_variants(exe_pass_name):
        if v in src_data.get("pass_types", {}):
            return src_data["pass_types"][v]
    return "unknown"


def lookup_pass_uses(exe_pass_name: str, src_data: Dict) -> Optional[int]:
    for v in _name_variants(exe_pass_name):
        if v in src_data.get("pass_uses", {}):
            return src_data["pass_uses"][v]
    return None

# ---------------------------------------------------------------------------
# Output parsing  — extract type and uses from exe output line
# ---------------------------------------------------------------------------
def parse_passes(raw: str) -> Dict:
    """
    Parse gibbon stdout.

    Handles lines like:
      Running pass SumArea (fold, uses=2):    → type=fold, uses=2
      Running pass SumArea (fold):            → type=fold, uses=None (fill from source)
      Running pass SumArea:                   → type=unknown, uses=None

    Returns {pass_name: stats_dict} where stats_dict includes:
      median_time, iter_times, stdev, mean_time, min_time, max_time,
      pass_type ("fold"|"map"|"unknown"),
      uses (int|None)
    """
    passes: Dict        = {}
    current: Optional[str] = None
    cur_type            = "unknown"
    cur_uses: Optional[int] = None
    times: List[float]  = []

    # Group 1=name, Group 2=type keyword (opt), Group 3=uses value (opt)
    pass_re = re.compile(
        r'Running\s+pass\s+([^(:\n]+?)\s*'
        r'(?:\(\s*([^,)]+?)\s*(?:,\s*uses\s*=\s*(\d+))?\s*\))?\s*:',
        re.IGNORECASE,
    )
    iter_re = re.compile(r'itertime:\s*([\d.eE+\-]+)')

    for line in raw.splitlines():
        s = line.strip()
        m = pass_re.match(s)
        if m:
            if current is not None and times:
                passes[current] = _stats(times, cur_type, cur_uses)
            current  = m.group(1).strip()
            hint     = (m.group(2) or "").strip().lower()
            uses_str = m.group(3)
            cur_type = ("fold"    if "fold" in hint
                        else ("map" if "map"  in hint else "unknown"))
            cur_uses = int(uses_str) if uses_str else None
            times    = []
            continue

        m2 = iter_re.match(s)
        if m2 and current is not None:
            try:
                times.append(float(m2.group(1)))
            except ValueError:
                pass
            continue

        if s == "End" and current is not None and times:
            passes[current] = _stats(times, cur_type, cur_uses)
            current  = None
            times    = []

    if current is not None and times:
        passes[current] = _stats(times, cur_type, cur_uses)

    return passes


def _stats(times: List[float], pass_type: str = "unknown",
           uses: Optional[int] = None) -> Dict:
    return {
        "iter_times":  times,
        "median_time": statistics.median(times),
        "mean_time":   statistics.mean(times),
        "min_time":    min(times),
        "max_time":    max(times),
        "stdev":       statistics.stdev(times) if len(times) > 1 else 0.0,
        "pass_type":   pass_type,
        "uses":        uses,   # fields used (None if not annotated)
    }


def apply_source_classification(result: BenchmarkResult,
                                 src_data: Dict) -> None:
    """
    For each pass, fill in any missing pass_type and uses from source scan.
    Also attach adt_fields to the result object.
    """
    adt = src_data.get("adt_fields")
    result.adt_fields = adt

    for pname, pdata in result.passes.items():
        if pdata.get("pass_type", "unknown") == "unknown":
            pdata["pass_type"] = lookup_pass_type(pname, src_data)
        if pdata.get("uses") is None:
            pdata["uses"] = lookup_pass_uses(pname, src_data)
        # Compute derived fields
        if adt is not None and pdata.get("uses") is not None:
            pdata["dead_fields"] = adt - pdata["uses"]
            pdata["dead_ratio"]  = pdata["dead_fields"] / adt
        else:
            pdata["dead_fields"] = None
            pdata["dead_ratio"]  = None

# ---------------------------------------------------------------------------
# GC / allocator noise filter
# ---------------------------------------------------------------------------
_GC_RE = re.compile(
    r"itertime:|ITER TIMES:|ITERS:|SIZE:|BATCHTIME:|SELFTIMED:|"
    r"Running pass|Running program|^End$|INFO_TABLE:|Initialized footer at|"
    r"GibOldgenChunkFooter|GibRegionInfo|refcount:.*outset:|"
    r"Total allocated bytes:|Total copied bytes:|ALLOC_TOTAL:|GC_TOTAL:",
    re.IGNORECASE,
)

def clean_output(raw: str) -> Optional[str]:
    lines = []
    for line in raw.splitlines():
        s = line.strip()
        if not s or _GC_RE.search(s):
            continue
        if re.search(r"0x[0-9a-fA-F]+", s):
            if any(kw in s.lower() for kw in
                   ("footer", "chunk", "region", "refcount", "outset")):
                continue
        lines.append(s)
    txt = "\n".join(lines)
    return txt if txt else None


def outputs_match(a: BenchmarkResult, b: BenchmarkResult) -> bool:
    return bool(a.output and b.output
                and a.output.strip() == b.output.strip())

# ---------------------------------------------------------------------------
# Smart recompilation check
# ---------------------------------------------------------------------------
def needs_recompilation(source: Path, exe: Path, c_file: Path) -> bool:
    if not exe.exists() or not c_file.exists():
        return True
    return source.stat().st_mtime > exe.stat().st_mtime

# ---------------------------------------------------------------------------
# Compile one variant  (called from thread pool)
# ---------------------------------------------------------------------------
def compile_one(source: Path, variant: str, out_dir: Path,
                force: bool) -> Tuple[bool, float, Optional[str]]:
    stem   = source.stem
    c_file = out_dir / f"{stem}.{variant}.c"
    exe    = out_dir / f"{stem}.{variant}.exe"
    out_dir.mkdir(parents=True, exist_ok=True)

    if not force and not needs_recompilation(source, exe, c_file):
        print(f"  [{variant.upper()}] {stem}: up-to-date, skipping")
        return True, 0.0, None

    cmd = [
        "gibbon", "--use-mutable-cursors", "--packed", "--to-exe",
        "--cfile",   str(c_file),
        "--exefile", str(exe),
        str(source),
    ]
    print(f"  [{variant.upper()}] {stem}: compiling ...", end=" ", flush=True)
    t0 = time.time()
    try:
        r = subprocess.run(cmd, capture_output=True, text=True)
        elapsed = time.time() - t0
        if r.returncode == 0:
            print(f"ok ({elapsed:.1f}s)")
            return True, elapsed, None
        print(f"FAILED ({elapsed:.1f}s)")
        return False, elapsed, r.stderr.strip()
    except FileNotFoundError:
        elapsed = time.time() - t0
        print("FAILED (gibbon not in PATH)")
        return False, elapsed, "gibbon not found"

# ---------------------------------------------------------------------------
# Parallel compilation dispatcher
# ---------------------------------------------------------------------------
def compile_parallel(tasks: List[Tuple]) -> Dict:
    if not tasks:
        return {}
    #workers = max(1, multiprocessing.cpu_count())
    # Vidush: Explicitly making this serial for now since parallel compilation is causing issues in Gibbon
    workers = 1
    print(f"\nCompiling {len(tasks)} file(s) using {workers} thread(s) ...")
    results: Dict = {}
    with ThreadPoolExecutor(max_workers=workers) as pool:
        fmap = {
            pool.submit(compile_one, src, var, od, force): (prog, var)
            for prog, var, src, od, force in tasks
        }
        for fut in as_completed(fmap):
            prog, var = fmap[fut]
            try:
                results[(prog, var)] = fut.result()
            except Exception as e:
                results[(prog, var)] = (False, 0.0, str(e))
    return results

# ---------------------------------------------------------------------------
# Run one executable  (always single-threaded)
# ---------------------------------------------------------------------------
def run_exe(exe: Path, iterations: int) -> Tuple[bool, float, Optional[str]]:
    if not exe.exists():
        return False, 0.0, None
    env = {**os.environ, "GIBBON_ITERS": str(iterations)}
    t0  = time.time()
    try:
        r = subprocess.run([str(exe)], capture_output=True, text=True, env=env)
        elapsed = time.time() - t0
        return (r.returncode == 0, elapsed,
                r.stdout if r.returncode == 0 else r.stderr)
    except Exception as e:
        return False, time.time() - t0, str(e)

# ---------------------------------------------------------------------------
# Benchmark one program
# ---------------------------------------------------------------------------
def benchmark_program(prog: str, programs_dir: Path, out_dir: Path,
                      iterations: int, force: bool,
                      source_cls_all: Dict
                      ) -> Tuple[Optional[BenchmarkResult], Optional[BenchmarkResult]]:
    print(f"\n{'='*70}\nBenchmarking: {prog}\n{'='*70}")

    tasks = []
    for var in ("aos", "soa"):
        src = programs_dir / var.upper() / prog
        if src.exists():
            tasks.append((prog, var, src, out_dir, force))
        else:
            print(f"  Warning: {src} not found")

    compile_results = compile_parallel(tasks)
    results: Dict[str, BenchmarkResult] = {}
    src_data = source_cls_all.get(prog, {"adt_fields": None,
                                          "pass_types": {}, "pass_uses": {}})

    for var in ("aos", "soa"):
        res = BenchmarkResult(prog, var)
        res.adt_fields = src_data.get("adt_fields")
        key = (prog, var)

        if key not in compile_results:
            res.compile_success = False
            res.error_message   = "source not found"
            results[var]        = res
            continue

        ok, ct, err = compile_results[key]
        res.compile_time = ct
        if not ok:
            res.compile_success = False
            res.error_message   = err or "compile failed"
            results[var]        = res
            continue

        res.compile_success = True
        stem = prog.replace(".hs", "")
        exe  = out_dir / f"{stem}.{var}.exe"

        print(f"  [{var.upper()}] running ...", end=" ", flush=True)
        ok2, rt, stdout = run_exe(exe, iterations)
        if not ok2:
            print("FAILED")
            res.run_success   = False
            res.error_message = "execution failed"
        else:
            print(f"done ({rt:.1f}s)")
            res.run_success = True
            if stdout:
                res.output  = clean_output(stdout)
                res.passes  = parse_passes(stdout)
                apply_source_classification(res, src_data)

        results[var] = res

    aos, soa = results.get("aos"), results.get("soa")
    if aos and soa and aos.run_success and soa.run_success:
        m = outputs_match(aos, soa)
        print(f"\n  Output check: {'✓ MATCH' if m else '✗ MISMATCH'}")
        if aos.passes:
            classified = [(p, d) for p, d in aos.passes.items()
                          if d["pass_type"] != "unknown"]
            with_uses  = [(p, d) for p, d in aos.passes.items()
                          if d.get("uses") is not None]
            folds = sum(1 for _, d in classified if d["pass_type"] == "fold")
            maps  = sum(1 for _, d in classified if d["pass_type"] == "map")
            unk   = len(aos.passes) - len(classified)
            adt_s = (f", adt_fields={aos.adt_fields}"
                     if aos.adt_fields is not None else "")
            print(f"  Passes: {folds} fold, {maps} map, {unk} unknown"
                  f"{adt_s}, {len(with_uses)} have uses= annotation")
    return aos, soa

# ---------------------------------------------------------------------------
# Time formatting
# ---------------------------------------------------------------------------
def fmt(seconds: float) -> str:
    if seconds == 0.0:
        return "0"
    a = abs(seconds)
    if a >= 100.0:  return f"{seconds:.1f}"
    if a >= 10.0:   return f"{seconds:.2f}"
    if a >= 1.0:    return f"{seconds:.3f}"
    if a >= 0.001:  return f"{seconds:.4f}"
    return f"{seconds:.2e}"

# ---------------------------------------------------------------------------
# LaTeX tables
# ---------------------------------------------------------------------------
def write_latex_tables(all_results: List[Tuple], out_file: Path):
    with open(out_file, "w") as f:
        f.write("% Gibbon Benchmark Suite v3.0 – auto-generated\n")
        f.write("% Requires: \\usepackage{booktabs} in preamble\n\n")
        _table_summary(f, all_results)
        _table_per_program(f, all_results)
    print(f"  ✓ LaTeX tables → {out_file}")


def _spd_cell(spd: float, bold_threshold: float = 1.1) -> str:
    s = f"{spd:.2f}" + r"$\times$"
    return r"\textbf{" + s + "}" if spd > bold_threshold else s


def _table_summary(f, all_results):
    """
    Table 1: one row per program.
    Program | ADT fields | Fold AoS | Fold SoA | Fold Speedup | Map AoS | Map SoA | Map Speedup
    """
    f.write("% -- Table 1: Summary by pass type --\n")
    f.write("\\begin{table}[t]\n\\centering\n")
    f.write(
        "\\caption{End-to-end execution time (s, median per iteration) "
        "and speedup split by pass type. "
        "ADT = total fields in the data type. "
        "Speedup ${>}1{\\times}$ means SoA is faster; "
        "\\textbf{bold} marks ${>}1.1{\\times}$.}\n"
    )
    f.write("\\label{tab:summary}\n\\small\n")
    f.write("\\begin{tabular}{l c r r r r r r}\n\\toprule\n")
    f.write(
        "\\textbf{Program} & \\textbf{ADT}"
        " & \\multicolumn{3}{c}{\\textbf{Fold passes}}"
        " & \\multicolumn{3}{c}{\\textbf{Map passes}} \\\\\n"
    )
    f.write("\\cmidrule(lr){3-5}\\cmidrule(lr){6-8}\n")
    f.write(
        " & fields"
        " & AoS (s) & SoA (s) & Speedup"
        " & AoS (s) & SoA (s) & Speedup \\\\\n"
    )
    f.write("\\midrule\n")

    for aos, soa in all_results:
        if not (aos and soa and aos.run_success and soa.run_success):
            continue
        prog     = aos.program.replace(".hs", "").replace("_", "\\_")
        adt      = getattr(aos, "adt_fields", None)
        adt_str  = str(adt) if adt is not None else "--"

        af = sum(p["median_time"] for p in aos.passes.values()
                 if p["pass_type"] == "fold")
        sf = sum(p["median_time"] for p in soa.passes.values()
                 if p["pass_type"] == "fold")
        am = sum(p["median_time"] for p in aos.passes.values()
                 if p["pass_type"] == "map")
        sm = sum(p["median_time"] for p in soa.passes.values()
                 if p["pass_type"] == "map")

        fspd_s = _spd_cell(af / sf) if af > 0 and sf > 0 else "--"
        mspd_s = _spd_cell(am / sm) if am > 0 and sm > 0 else "--"

        f.write(
            f"{prog} & {adt_str}"
            f" & {fmt(af) if af > 0 else '--'}"
            f" & {fmt(sf) if sf > 0 else '--'}"
            f" & {fspd_s}"
            f" & {fmt(am) if am > 0 else '--'}"
            f" & {fmt(sm) if sm > 0 else '--'}"
            f" & {mspd_s} \\\\\n"
        )

    f.write("\\bottomrule\n\\end{tabular}\n\\end{table}\n\n\n")


def _table_per_program(f, all_results):
    """
    One table per program.
    Pass | T | Uses/ADT | Dead% | AoS (s) | SoA (s) | Speedup
    """
    for aos, soa in all_results:
        if not (aos and soa and aos.run_success and soa.run_success):
            continue

        prog_hs  = aos.program
        prog     = prog_hs.replace(".hs", "")
        pdisplay = prog.replace("_", "\\_")
        adt      = getattr(aos, "adt_fields", None)
        passes   = sorted(set(list(aos.passes) + list(soa.passes)))
        if not passes:
            continue

        adt_note = f", ADT has {adt} fields" if adt is not None else ""
        f.write(f"% -- Table: {prog} --\n")
        f.write("\\begin{table}[t]\n\\centering\n")
        f.write(
            f"\\caption{{Per-pass performance for \\texttt{{{pdisplay}}}"
            f"{adt_note}. "
            "Times are median per iteration (s). "
            "T: F=fold, M=map. "
            "Uses: fields accessed / total ADT fields. "
            "Dead\\%: fraction of unused fields. "
            "Speedup ${>}1{\\times}$ means SoA is faster.}}\n"
        )
        f.write(f"\\label{{tab:{prog}}}\n\\small\n")

        # Decide whether to show Uses and Dead% columns
        has_uses = any(
            aos.passes.get(p, {}).get("uses") is not None or
            soa.passes.get(p, {}).get("uses") is not None
            for p in passes
        )
        if has_uses and adt is not None:
            f.write("\\begin{tabular}{l c c r r r r}\n\\toprule\n")
            f.write(
                "\\textbf{Pass} & \\textbf{T}"
                " & \\textbf{Uses} & \\textbf{Dead\\%}"
                " & \\textbf{AoS (s)} & \\textbf{SoA (s)} & \\textbf{Speedup} \\\\\n"
            )
        else:
            f.write("\\begin{tabular}{l c r r r}\n\\toprule\n")
            f.write(
                "\\textbf{Pass} & \\textbf{T}"
                " & \\textbf{AoS (s)} & \\textbf{SoA (s)} & \\textbf{Speedup} \\\\\n"
            )
        f.write("\\midrule\n")

        speedups = []
        for pname in passes:
            ad   = aos.passes.get(pname, {})
            sd   = soa.passes.get(pname, {})
            at_s = ad.get("median_time", 0.0)
            st_s = sd.get("median_time", 0.0)
            if at_s == 0.0 and st_s == 0.0:
                continue

            ptype = ad.get("pass_type") or sd.get("pass_type") or "unknown"
            tchar = "F" if ptype == "fold" else ("M" if ptype == "map" else "?")
            spd   = at_s / st_s if st_s > 0 else 0.0
            at_f  = fmt(at_s) if at_s > 0 else "--"
            st_f  = fmt(st_s) if st_s > 0 else "--"
            pdisp = pname.replace("_", "\\_")

            if spd > 1.1:
                at_f_r, st_f_r = at_f, f"\\textbf{{{st_f}}}"
            elif 0 < spd < 0.9:
                at_f_r, st_f_r = f"\\textbf{{{at_f}}}", st_f
            else:
                at_f_r, st_f_r = at_f, st_f

            spd_s = _spd_cell(spd) if spd > 0 else "--"

            if has_uses and adt is not None:
                uses = ad.get("uses") or sd.get("uses")
                dead_r = ad.get("dead_ratio") or sd.get("dead_ratio")
                uses_s  = f"{uses}/{adt}" if uses is not None else "--"
                dead_s  = f"{dead_r*100:.0f}\\%" if dead_r is not None else "--"
                f.write(f"{pdisp} & {tchar} & {uses_s} & {dead_s}"
                        f" & {at_f_r} & {st_f_r} & {spd_s} \\\\\n")
            else:
                f.write(f"{pdisp} & {tchar}"
                        f" & {at_f_r} & {st_f_r} & {spd_s} \\\\\n")

            if spd > 0:
                speedups.append(spd)

        at_tot = sum(p["median_time"] for p in aos.passes.values())
        st_tot = sum(p["median_time"] for p in soa.passes.values())
        sp_tot = at_tot / st_tot if st_tot > 0 else 0.0
        f.write("\\midrule\n")
        f.write(f"\\textbf{{Total}} & "
                + ("& & " if has_uses and adt is not None else "")
                + f"& {fmt(at_tot)} & {fmt(st_tot)} & {_spd_cell(sp_tot)} \\\\\n")
        if speedups:
            gm = statistics.geometric_mean(speedups)
            f.write("\\textbf{Geomean} & "
                    + ("& & " if has_uses and adt is not None else "")
                    + f"& & & {_spd_cell(gm)} \\\\\n")

        f.write("\\bottomrule\n\\end{tabular}\n\\end{table}\n\n\n")


def compile_latex_preview(tex_file: Path, out_dir: Path):
    out_dir.mkdir(parents=True, exist_ok=True)
    wrapper = (
        "\\documentclass{article}\n"
        "\\usepackage{booktabs}\n"
        "\\usepackage[margin=0.5in,a3paper]{geometry}\n"
        "\\begin{document}\\pagestyle{empty}\n"
        f"\\input{{{tex_file.name}}}\n"
        "\\end{document}\n"
    )
    tmp = out_dir / "table_preview.tex"
    tmp.write_text(wrapper)
    if tex_file.parent.resolve() != out_dir.resolve():
        shutil.copy(tex_file, out_dir / tex_file.name)
    try:
        subprocess.run(
            ["pdflatex", "-interaction=nonstopmode",
             "-output-directory", str(out_dir), str(tmp)],
            capture_output=True, timeout=60,
        )
        pdf = out_dir / "table_preview.pdf"
        print(f"  {'✓ Table PDF → ' + str(pdf) if pdf.exists() else 'Note: pdflatex produced no PDF'}")
    except FileNotFoundError:
        print("  Note: pdflatex not found – skipping PDF preview")
    except Exception as e:
        print(f"  Note: PDF preview skipped ({e})")

# ---------------------------------------------------------------------------
# Text + JSON reports
# ---------------------------------------------------------------------------
def write_text_report(all_results: List[Tuple], out_file: Path):
    lines = ["=" * 72, "GIBBON BENCHMARK REPORT v3.0",
             "=" * 72, f"Generated: {time.strftime('%Y-%m-%d %H:%M:%S')}", ""]
    for aos, soa in all_results:
        if not aos or not soa:
            continue
        adt   = getattr(aos, "adt_fields", None)
        lines.append(f"\nProgram: {aos.program}"
                     + (f"  [ADT fields: {adt}]" if adt else ""))
        lines.append("-" * 40)
        for tag, res in (("AOS", aos), ("SOA", soa)):
            if not res.run_success:
                lines.append(f"  {tag}: FAILED – {res.error_message}")
                continue
            total = sum(p["median_time"] for p in res.passes.values())
            lines.append(f"  {tag}: {total:.4f}s total")
            for pname, pd in res.passes.items():
                t    = pd["pass_type"][0].upper() if pd["pass_type"] != "unknown" else "?"
                uses = pd.get("uses")
                dr   = pd.get("dead_ratio")
                ann  = ""
                if uses is not None and adt:
                    ann = f"  uses={uses}/{adt}  dead={dr*100:.0f}%"
                lines.append(f"    [{t}] {pname}: {pd['median_time']:.4f}s"
                              f" ±{pd['stdev']:.4f}{ann}")
        if aos.run_success and soa.run_success:
            at = sum(p["median_time"] for p in aos.passes.values())
            st = sum(p["median_time"] for p in soa.passes.values())
            lines.append(f"  Speedup: {at/st:.3f}×" if st > 0 else "  Speedup: N/A")
            lines.append(f"  Output match: {'YES' if outputs_match(aos, soa) else 'NO'}")
    out_file.write_text("\n".join(lines))
    print(f"  ✓ Text report → {out_file}")


def write_json_results(all_results: List[Tuple], out_file: Path):
    data = []
    for aos, soa in all_results:
        if not aos or not soa:
            continue
        def ser(r: BenchmarkResult) -> Dict:
            return {
                "compile_success": r.compile_success,
                "run_success":     r.run_success,
                "error":           r.error_message,
                "adt_fields":      getattr(r, "adt_fields", None),
                "passes": {k: {kk: vv for kk, vv in v.items()
                               if kk != "iter_times"}
                           for k, v in r.passes.items()},
            }
        data.append({"program": aos.program, "aos": ser(aos), "soa": ser(soa),
                     "output_match": outputs_match(aos, soa)})
    out_file.write_text(json.dumps(data, indent=2))
    print(f"  ✓ JSON → {out_file}")

# ---------------------------------------------------------------------------
# Figures
# ---------------------------------------------------------------------------
_HATCHES = ["", "/", "\\", "|", "-", "+", "x", "o", "O", ".", "*"]

def _pub_rc():
    plt.rcParams.update({
        "font.size": 9, "font.family": "serif",
        "axes.labelsize": 9, "axes.titlesize": 10,
        "xtick.labelsize": 8, "ytick.labelsize": 8,
        "legend.fontsize": 8,
        "axes.grid": True, "grid.alpha": 0.3,
        "savefig.dpi": 300, "savefig.bbox": "tight",
    })

def _save(fig, stem: Path):
    fig.savefig(stem.with_suffix(".pdf"))
    fig.savefig(stem.with_suffix(".png"))
    plt.close(fig)


# ── Figure A: overall speedup — fold vs map ──────────────────────────────────
def _fig_speedup_fold_map(good: List, out: Path):
    programs, fold_s, map_s = [], [], []
    for aos, soa in good:
        af = sum(p["median_time"] for p in aos.passes.values() if p["pass_type"] == "fold")
        sf = sum(p["median_time"] for p in soa.passes.values() if p["pass_type"] == "fold")
        am = sum(p["median_time"] for p in aos.passes.values() if p["pass_type"] == "map")
        sm = sum(p["median_time"] for p in soa.passes.values() if p["pass_type"] == "map")
        programs.append(aos.program.replace(".hs", ""))
        fold_s.append(af / sf if sf > 0 else 0.0)
        map_s.append(am / sm if sm > 0 else 0.0)

    y, h = np.arange(len(programs)), 0.35
    fig, ax = plt.subplots(figsize=(10, max(5, len(programs) * 0.45)))
    ax.barh(y - h/2, fold_s, h, label="Fold passes",
            color="#3498db", alpha=0.85, edgecolor="black", linewidth=0.5)
    ax.barh(y + h/2, map_s, h, label="Map passes",
            color="#e67e22", alpha=0.85, edgecolor="black", linewidth=0.5)
    ax.set_yticks(y); ax.set_yticklabels(programs, fontsize=8)
    ax.set_xlabel("Speedup (AoS / SoA)  —  >1 means SoA is faster")
    ax.set_title("End-to-End Speedup: Fold vs Map Passes")
    ax.axvline(1.0, color="black", linestyle="--", linewidth=1, alpha=0.6)
    ax.legend()
    fig.tight_layout()
    _save(fig, out)
    print(f"  speedup_comparison.*")


# ── Figure B: per-program — all passes, error bars, geomean ──────────────────
def _fig_per_program(good: List, out_dir: Path):
    dest = out_dir / "per_program"
    dest.mkdir(parents=True, exist_ok=True)

    for aos, soa in good:
        prog   = aos.program.replace(".hs", "")
        passes = sorted(set(list(aos.passes) + list(soa.passes)))

        labels, a_m, s_m, a_e, s_e, spds, bar_colors = [], [], [], [], [], [], []

        for pname in passes:
            ad   = aos.passes.get(pname, {})
            sd   = soa.passes.get(pname, {})
            am_s = ad.get("median_time", 0.0)
            sm_s = sd.get("median_time", 0.0)
            if am_s == 0.0 and sm_s == 0.0:
                continue
            a_its = ad.get("iter_times", [])
            s_its = sd.get("iter_times", [])

            ptype = ad.get("pass_type") or sd.get("pass_type") or "unknown"
            labels.append(pname.replace("_", " "))
            a_m.append(am_s); s_m.append(sm_s)
            a_e.append(statistics.stdev(a_its) if len(a_its) > 1 else 0.0)
            s_e.append(statistics.stdev(s_its) if len(s_its) > 1 else 0.0)
            if sm_s > 0:
                spds.append(am_s / sm_s)
            bar_colors.append(
                "#3498db" if ptype == "fold" else
                "#e67e22" if ptype == "map"  else "#95a5a6"
            )

        if not labels:
            continue

        # Geomean
        if spds:
            gm_a = statistics.geometric_mean([v for v in a_m if v > 0])
            gm_s = statistics.geometric_mean([v for v in s_m if v > 0])
            labels.append("Geomean")
            a_m.append(gm_a); s_m.append(gm_s)
            a_e.append(0.0);  s_e.append(0.0)
            bar_colors.append("#2c3e50")

        x, w = np.arange(len(labels)), 0.35
        fig, ax = plt.subplots(figsize=(max(10, len(labels) * 0.9), 6))

        # Use type-based colours for AoS bars; slightly lighter for SoA
        b1 = ax.bar(x - w/2, a_m, w, yerr=a_e, label="AOS",
                    color=bar_colors, alpha=0.85, edgecolor="black",
                    linewidth=0.5, capsize=3, error_kw={"elinewidth": 1.2})
        b2 = ax.bar(x + w/2, s_m, w, yerr=s_e, label="SOA",
                    color=bar_colors, alpha=0.50, edgecolor="black",
                    linewidth=0.5, capsize=3, error_kw={"elinewidth": 1.2},
                    hatch="///")

        # Highlight geomean
        if labels[-1] == "Geomean":
            gi = len(labels) - 1
            for bar in (b1[gi], b2[gi]):
                bar.set_facecolor("#2c3e50"); bar.set_alpha(0.9 if bar in b1 else 0.6)
                bar.set_linewidth(2)
            for bar, val in ((b1[gi], a_m[gi]), (b2[gi], s_m[gi])):
                ax.text(bar.get_x() + bar.get_width() / 2, val,
                        f"{val:.3f}s", ha="center", va="bottom",
                        fontsize=7, fontweight="bold")

        ax.set_xticks(x)
        ax.set_xticklabels(labels, rotation=45, ha="right", fontsize=8)
        ax.set_xlabel("Compiler Pass  (bar colour: blue=fold, orange=map, grey=unknown)")
        ax.set_ylabel("Median Time per Iteration (s)")
        ax.set_title(f"{prog} — AoS (solid) vs SoA (hatched), all passes\n"
                     "(error bars = std dev,  rightmost bar = geomean)")

        # Custom legend
        legend_items = [
            mpatches.Patch(facecolor="#3498db", label="Fold pass – AoS"),
            mpatches.Patch(facecolor="#3498db", alpha=0.5, hatch="///", label="Fold pass – SoA"),
            mpatches.Patch(facecolor="#e67e22", label="Map pass – AoS"),
            mpatches.Patch(facecolor="#e67e22", alpha=0.5, hatch="///", label="Map pass – SoA"),
        ]
        ax.legend(handles=legend_items, fontsize=7, loc="best")
        fig.tight_layout()
        _save(fig, dest / prog)
        print(f"  per_program/{prog}.*  ({len(labels)} bars incl. geomean)")


# ── Figure C: dead-field ratio vs speedup scatter ────────────────────────────
def _fig_dead_vs_speedup(good: List, out: Path):
    """
    Scatter plot: x = dead_ratio (fraction of unused ADT fields),
                  y = speedup (AoS / SoA).
    One point per (program, pass) pair that has both uses= and speedup data.
    Fold passes in blue, map passes in orange.
    A horizontal dashed line at y=1 marks break-even.
    """
    fold_x, fold_y, fold_labels = [], [], []
    map_x,  map_y,  map_labels  = [], [], []
    unk_x,  unk_y,  unk_labels  = [], [], []

    for aos, soa in good:
        prog = aos.program.replace(".hs", "")
        for pname, ad in aos.passes.items():
            sd = soa.passes.get(pname, {})
            at = ad.get("median_time", 0.0)
            st = sd.get("median_time", 0.0)
            if at == 0.0 or st == 0.0:
                continue
            dr = ad.get("dead_ratio")
            if dr is None:
                continue
            spd   = at / st
            label = f"{prog}\n{pname}"
            ptype = ad.get("pass_type", "unknown")
            if ptype == "fold":
                fold_x.append(dr); fold_y.append(spd); fold_labels.append(label)
            elif ptype == "map":
                map_x.append(dr);  map_y.append(spd);  map_labels.append(label)
            else:
                unk_x.append(dr);  unk_y.append(spd);  unk_labels.append(label)

    total = len(fold_x) + len(map_x) + len(unk_x)
    if total == 0:
        print("  Skipping dead-field scatter: no uses= annotations found")
        return

    fig, ax = plt.subplots(figsize=(9, 6))

    for xs, ys, labels, col, marker, name in (
        (fold_x, fold_y, fold_labels, "#3498db", "o", "Fold"),
        (map_x,  map_y,  map_labels,  "#e67e22", "s", "Map"),
        (unk_x,  unk_y,  unk_labels,  "#95a5a6", "^", "Unknown"),
    ):
        if xs:
            ax.scatter(xs, ys, c=col, marker=marker, s=70, alpha=0.85,
                       edgecolors="black", linewidths=0.4, label=name, zorder=3)
            for x, y, lbl in zip(xs, ys, labels):
                ax.annotate(lbl, (x, y),
                            textcoords="offset points", xytext=(5, 4),
                            fontsize=5.5, color="#333333")

    ax.axhline(1.0, color="black", linestyle="--", linewidth=1,
               alpha=0.6, label="Break-even (1×)")

    # Trend line across all points
    all_x = fold_x + map_x + unk_x
    all_y = fold_y + map_y + unk_y
    if len(all_x) >= 3:
        z   = np.polyfit(all_x, all_y, 1)
        px  = np.linspace(min(all_x), max(all_x), 100)
        ax.plot(px, np.polyval(z, px), "k--", linewidth=1.2, alpha=0.4,
                label=f"Trend  (slope={z[0]:+.2f})")

    ax.set_xlabel("Dead-field ratio  (unused fields / total ADT fields)\n"
                  "0 = all fields used,  1 = no fields used")
    ax.set_ylabel("Speedup  (AoS time / SoA time)\n>1 means SoA is faster")
    ax.set_title("Does higher dead-field ratio predict SoA speedup?")
    ax.legend(fontsize=8)
    fig.tight_layout()
    _save(fig, out)
    print(f"  dead_vs_speedup.*  ({total} data points)")


# ── Figure D: per-program heatmap ────────────────────────────────────────────
def _fig_heatmaps(good: List, out_dir: Path):
    dest = out_dir / "heatmaps"
    dest.mkdir(parents=True, exist_ok=True)

    for aos, soa in good:
        prog   = aos.program.replace(".hs", "")
        passes = sorted(set(list(aos.passes) + list(soa.passes)))
        spds, labs, types = [], [], []
        for pname in passes:
            at = aos.passes.get(pname, {}).get("median_time", 0.0)
            st = soa.passes.get(pname, {}).get("median_time", 0.0)
            if at > 0 and st > 0:
                spds.append(at / st)
                labs.append(pname.replace("_", " "))
                pt = (aos.passes.get(pname) or soa.passes.get(pname) or {}).get("pass_type", "unknown")
                types.append({"fold": "F", "map": "M"}.get(pt, "?"))

        if not spds:
            continue

        arr = np.array([spds])
        fig, ax = plt.subplots(figsize=(max(8, len(spds) * 1.0), 3.2))
        im = ax.imshow(arr, cmap="RdYlGn", aspect="auto",
                       vmin=0.7, vmax=1.3, interpolation="nearest")
        ax.set_xticks(np.arange(len(labs)))
        ax.set_xticklabels(
            [f"{l}\n[{t}]" for l, t in zip(labs, types)],
            rotation=45, ha="right", fontsize=8)
        ax.set_yticks([0]); ax.set_yticklabels([prog])
        plt.colorbar(im, ax=ax, orientation="horizontal", pad=0.45,
                     label="Speedup (AoS/SoA)  —  green = SoA faster")
        for i, (s, t) in enumerate(zip(spds, types)):
            ax.text(i, 0, f"{s:.2f}\n[{t}]",
                    ha="center", va="center", fontsize=7, fontweight="bold")
        ax.set_title(f"{prog}: per-pass speedup heatmap  (F=fold M=map ?=unknown)")
        fig.tight_layout()
        _save(fig, dest / f"{prog}_heatmap")

    print(f"  heatmaps/  (one per program)")


# ── Figure E: stacked breakdown ──────────────────────────────────────────────
def _fig_breakdown(good: List, out: Path):
    all_passes: set = set()
    for aos, soa in good:
        all_passes.update(aos.passes); all_passes.update(soa.passes)
    passes = sorted(all_passes)
    progs  = [r.program.replace(".hs", "") for r, _ in good]

    a_data = {p: [] for p in passes}
    s_data = {p: [] for p in passes}
    for aos, soa in good:
        for p in passes:
            a_data[p].append(aos.passes.get(p, {}).get("median_time", 0.0))
            s_data[p].append(soa.passes.get(p, {}).get("median_time", 0.0))

    colors = plt.cm.tab20(np.linspace(0, 1, max(len(passes), 1)))
    x, w   = np.arange(len(progs)), 0.6
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(18, max(7, len(progs) * 0.55)))
    handles = []
    bot_a   = np.zeros(len(progs))
    bot_s   = np.zeros(len(progs))
    for i, p in enumerate(passes):
        lbl   = p.replace("_", " ")
        hatch = _HATCHES[i % len(_HATCHES)]
        bh = ax1.barh(x, a_data[p], w, left=bot_a, color=colors[i],
                      edgecolor="black", linewidth=0.3, hatch=hatch, label=lbl)
        ax2.barh(x, s_data[p], w, left=bot_s, color=colors[i],
                 edgecolor="black", linewidth=0.3, hatch=hatch)
        bot_a += np.array(a_data[p])
        bot_s += np.array(s_data[p])
        handles.append(bh)

    for ax, title in ((ax1, "AOS"), (ax2, "SOA")):
        ax.set_yticks(x); ax.set_yticklabels(progs, fontsize=8)
        ax.set_xlabel("Median time per iteration (s)")
        ax.set_title(f"{title}: Complete Pass Breakdown")

    fig.legend(handles, [p.replace("_", " ") for p in passes],
               loc="lower center", ncol=min(6, len(passes)),
               bbox_to_anchor=(0.5, -0.04), fontsize=7, frameon=True)
    fig.suptitle("All Programs — Complete Pass Breakdown",
                 fontsize=11, y=0.998)
    fig.tight_layout(rect=[0, 0.07, 1, 0.97])
    _save(fig, out)
    print(f"  pass_breakdown_all.*")


def generate_all_figures(all_results: List[Tuple], out_dir: Path):
    _pub_rc()
    out_dir.mkdir(parents=True, exist_ok=True)
    good = [(a, s) for a, s in all_results
            if a and s and a.run_success and s.run_success]
    if not good:
        print("  No successful results to plot.")
        return
    print("\nGenerating figures ...")
    _fig_speedup_fold_map(good, out_dir / "speedup_comparison")
    _fig_per_program(good, out_dir)
    _fig_dead_vs_speedup(good, out_dir / "dead_vs_speedup")
    _fig_heatmaps(good, out_dir)
    _fig_breakdown(good, out_dir / "pass_breakdown_all")
    print(f"\n  All figures written to {out_dir}/")

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser(description="Gibbon Benchmark Suite v3.0")
    ap.add_argument("--programs-dir",   type=Path, default=Path("programs"))
    ap.add_argument("--output-dir",     type=Path, default=Path("benchmark_output"))
    ap.add_argument("--iterations",     type=int,  default=20)
    ap.add_argument("--programs",       nargs="+")
    ap.add_argument("--clean",          action="store_true")
    ap.add_argument("--generate-paper", action="store_true")
    ap.add_argument("--latex-table",    type=Path, default=Path("performance_table.tex"))
    ap.add_argument("--figures-dir",    type=Path, default=Path("figures"))
    ap.add_argument("--report",         type=Path, default=Path("benchmark_report.txt"))
    ap.add_argument("--json",           type=Path, default=Path("benchmark_results.json"))
    args = ap.parse_args()

    programs_to_run = args.programs or DEFAULT_PROGRAMS

    print("\n" + "=" * 72)
    print("GIBBON BENCHMARK SUITE v3.0")
    print("=" * 72)
    print(f"  Programs dir : {args.programs_dir}")
    print(f"  Output dir   : {args.output_dir}")
    print(f"  Iterations   : {args.iterations}")
    print(f"  Programs     : {len(programs_to_run)}")
    print(f"  Force recomp : {'YES' if args.clean else 'no (smart)'}")
    print(f"  Paper mode   : {'YES' if args.generate_paper else 'no'}")
    print(f"  CPU cores    : {multiprocessing.cpu_count()}")
    print("=" * 72)

    args.output_dir.mkdir(parents=True, exist_ok=True)
    source_cls_all = build_source_classification(args.programs_dir)

    all_results: List[Tuple] = []
    for prog in programs_to_run:
        aos, soa = benchmark_program(
            prog, args.programs_dir, args.output_dir,
            args.iterations, args.clean, source_cls_all,
        )
        all_results.append((aos, soa))

    ok    = sum(1 for a, s in all_results if a and s and a.run_success and s.run_success)
    match = sum(1 for a, s in all_results
                if a and s and a.run_success and s.run_success and outputs_match(a, s))

    print(f"\n\n{'='*72}")
    print(f"DONE  –  {ok}/{len(all_results)} succeeded  |  {match}/{ok} output matches")
    print(f"{'='*72}")

    print("\nWriting reports ...")
    write_text_report(all_results, args.report)
    write_json_results(all_results, args.json)

    if args.generate_paper:
        print(f"\n{'='*72}")
        print("Generating conference paper materials ...")
        print(f"{'='*72}")
        write_latex_tables(all_results, args.latex_table)
        compile_latex_preview(args.latex_table, args.figures_dir)
        generate_all_figures(all_results, args.figures_dir)
        print(f"\n  LaTeX  : {args.latex_table}")
        print(f"  Figs   : {args.figures_dir}/")


if __name__ == "__main__":
    main()
