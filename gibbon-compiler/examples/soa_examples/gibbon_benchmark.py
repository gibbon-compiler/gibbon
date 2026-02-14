#!/usr/bin/env python3
"""
Gibbon Compiler Benchmark Suite v3.1
=====================================
Benchmarks AoS vs SoA gibbon programs and produces publication-quality
LaTeX tables and matplotlib figures.

Field-usage analysis:
  Gibbon's SoA mode is hypothesised to win on passes that access fewer
  fields of the ADT (more "dead" fields skipped, fewer cache streams).
  Two source annotations drive the analysis:

    (a) ADT field count — one comment per source file, near the type def:
          -- @BENCH adt_fields=5

    (b) Per-pass field usage — extend the existing printsym line:
          _ = printsym (quote "Running pass SumArea (fold, uses=2): ")

  From these the script computes:
    dead_fields = adt_fields - uses
    dead_ratio  = dead_fields / adt_fields   (0 = all used, 1 = none used)

Buffer analysis (automatic — no extra annotation needed):
  The script parses each Haskell source file to find the main ADT definition
  and counts memory buffers under each memory layout:

    AoS: always 1 buffer (all data packed together).

    SoA: 1 buffer for constructor tags (recursive children stored here too)
         + 1 buffer per NON-recursive field slot across all constructors
       e.g.  data Tree = Node Int Tree Tree | Leaf Int
             → tags:1  Node.Int:1  Leaf.Int:1
             → soa_total_buffers = 3
             (Tree recursive fields go in the tags buffer, no extra buffer)

       e.g.  data IR = Instr Int*7 IR | BlockEnd IR | End
             → tags:1  Instr.Int×7:7
             → soa_total_buffers = 8

  Per-pass buffer access:
    dead_fields = adt_fields - uses         (adt_fields and uses both include recursive)
    dead_ratio  = dead_fields / adt_fields

    soa_total_buffers is known from the ADT definition (1 + non-recursive slots)
    and shown in the summary table.  Per-pass SoA buffer usage is NOT computed:
    uses= counts total fields (recursive + non-recursive) and the recursive/
    non-recursive split within a pass is not available without further annotation.

  Optional annotation to name the target ADT explicitly (overrides heuristic):
    -- @BENCH adt_type=MyTypeName

Fold/map detection (dual strategy):
  PRIMARY:  exe output line "Running pass Foo (fold, uses=2):"
  FALLBACK: source-file printsym scan (also captures uses= and adt_fields)

Usage:
  ./gibbon_benchmark.py                              run all programs
  ./gibbon_benchmark.py --programs DomTree.hs        run one program
  ./gibbon_benchmark.py --clean                      force recompile
  ./gibbon_benchmark.py --generate-paper             LaTeX + figures
  ./gibbon_benchmark.py --iterations 50 --generate-paper
  ./gibbon_benchmark.py --iterations 1               match cold manual run
  ./gibbon_benchmark.py --dump-raw                   save raw exe output
"""

import os, re, sys, json, time, shutil, argparse, statistics, subprocess, textwrap, datetime
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
        self.adt_fields: Optional[int]    = None
        self.adt_info:   Optional[Dict]   = None   # from parse_adt_buffers

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


# ---------------------------------------------------------------------------
# ADT buffer analysis
# ---------------------------------------------------------------------------

def _split_alts(text: str) -> List[str]:
    """
    Split a Haskell constructor body by '|' at parenthesis depth 0.
    Handles:  'C1 Int Bool | C2 (Maybe Int) Tree | C3'
    """
    parts: List[str] = []
    depth   = 0
    current: List[str] = []
    for ch in text:
        if ch == '(':
            depth += 1
            current.append(ch)
        elif ch == ')':
            depth -= 1
            current.append(ch)
        elif ch == '|' and depth == 0:
            parts.append(''.join(current).strip())
            current = []
        else:
            current.append(ch)
    if current:
        parts.append(''.join(current).strip())
    return [p for p in parts if p]


def _tokenize_fields(text: str) -> List[str]:
    """
    Extract field type tokens from a constructor definition, respecting
    parenthesised groups.
      'Node Int (Maybe Float) Tree'  →  ['Node', 'Int', '(Maybe Float)', 'Tree']
    """
    tokens: List[str] = []
    i, n = 0, len(text)
    while i < n:
        if text[i].isspace():
            i += 1
        elif text[i] == '(':
            depth = 1; j = i + 1
            while j < n and depth > 0:
                if   text[j] == '(': depth += 1
                elif text[j] == ')': depth -= 1
                j += 1
            tokens.append(text[i:j])
            i = j
        else:
            j = i
            while j < n and not text[j].isspace() and text[j] != '(':
                j += 1
            tokens.append(text[i:j])
            i = j
    return tokens


def parse_adt_buffers(content: str) -> Optional[Dict]:
    """
    Parse all Haskell data declarations in *content* and compute buffer layout.

    SoA buffer counting rules:
      • 1 buffer for all constructor tags AND all recursive (self-referential)
        fields — recursive children are stored inline in the tag buffer,
        they do NOT get a separate buffer.
      • 1 buffer per NON-recursive field slot across ALL constructors

      Examples:
        data Tree = Node Int Tree Tree | Leaf Int
          → 1(tags) + 1(Node.Int) + 1(Leaf.Int) = 3 SoA buffers

        data IR = Instr Int Int Int Int Int Int Int IR
                | BlockEnd IR
                | End
          → 1(tags) + 7(Instr Ints) = 8 SoA buffers
            (IR recursive fields go into the tags buffer)

    AoS is always 1 buffer.

    The target ADT is selected by:
      1. The optional source annotation:  -- @BENCH adt_type=TypeName
      2. Otherwise the data type with the most total field slots.

    Returns:
      {
        "type_name": str,
        "aos_buffers": 1,
        "soa_total_buffers": int,
        "constructors": [
          {
            "name": str,
            "field_count": int,
            "field_types": [str, ...],
            "recursive_count": int,   # how many fields are the ADT itself
          }
        ]
      }
    or None if no data declarations found.
    """
    # Optional explicit type-name hint
    hint_m = re.search(
        r'--\s*@BENCH\s+adt_type\s*=\s*([A-Za-z][A-Za-z0-9_\']*)',
        content,
    )
    type_hint = hint_m.group(1) if hint_m else None

    # Strip line comments so we don't confuse the parser
    no_comments = re.sub(r'--[^\n]*', ' ', content)
    # Also strip block strings / pragmas that could fool us
    no_comments = re.sub(r'\{-.*?-\}', ' ', no_comments, flags=re.DOTALL)

    # Find all data declaration start positions
    data_re = re.compile(r'\bdata\s+([A-Z][A-Za-z0-9_\']*)\b')
    starts  = list(data_re.finditer(no_comments))
    if not starts:
        return None

    # Top-level keyword OR lowercase-at-col-0 function def boundaries
    # Stops at: data/type/newtype/class/instance/module/import/where
    #           OR  lowercase identifier at column 0 (= a function def/sig)
    boundary_re = re.compile(
        r'\n(?:data|type|newtype|class|instance|module|import|where\b'
        r'|[a-z][A-Za-z0-9_\']*\s*(?:::|=|\s*[A-Za-z0-9_\(\[]))'
    )

    parsed_adts: List[Dict] = []
    for i, m in enumerate(starts):
        type_name = m.group(1)

        # Extract the body up to the next top-level declaration
        search_from = m.start()
        bnd = boundary_re.search(no_comments, search_from + 1)
        body = no_comments[m.end(): bnd.start() if bnd else len(no_comments)]

        # Skip past optional type variables to the '='
        eq_m = re.search(r'=', body)
        if not eq_m:
            continue
        alts_text = body[eq_m.end():]

        # Strip any trailing 'deriving (...)' clause
        deriving_m = re.search(r'\bderiving\b', alts_text, re.IGNORECASE)
        if deriving_m:
            alts_text = alts_text[:deriving_m.start()]

        # Split into individual constructor alternatives
        alts = _split_alts(alts_text)
        ctor_list: List[Dict] = []
        for alt in alts:
            tokens = _tokenize_fields(alt)
            if not tokens:
                continue
            ctor_name = tokens[0]
            if not ctor_name[0].isupper():
                continue   # malformed, skip
            # Tokens after constructor name are field types
            fields    = tokens[1:]
            # Recursive fields = same type as the ADT being defined.
            # They are stored inline in the constructor-tag buffer and do NOT
            # get their own SoA buffer.
            recursive    = [t for t in fields if type_name in t]
            nonrecursive = [t for t in fields if type_name not in t]
            ctor_list.append({
                "name":              ctor_name,
                "field_count":       len(fields),
                "field_types":       fields,
                "recursive_count":   len(recursive),
                "nonrec_count":      len(nonrecursive),
                "nonrec_types":      nonrecursive,
            })

        if not ctor_list:
            continue

        total_fields     = sum(c["field_count"]   for c in ctor_list)
        nonrec_fields    = sum(c["nonrec_count"]  for c in ctor_list)
        # SoA layout:
        #   1 buffer  — constructor tags  (recursive child pointers stored here)
        #   1 buffer  — per non-recursive field slot across ALL constructors
        # e.g. IR = Instr Int*7 IR | BlockEnd IR | End
        #      → 1(tags) + 7(Instr's Ints) = 8  ✓
        # e.g. Tree = Node Int Tree Tree | Leaf Int
        #      → 1(tags) + 1(Node.Int) + 1(Leaf.Int) = 3  ✓
        parsed_adts.append({
            "type_name":           type_name,
            "constructors":        ctor_list,
            "total_field_slots":   total_fields,   # used for heuristic only
            "nonrec_field_slots":  nonrec_fields,  # drives soa_total_buffers
            "aos_buffers":         1,
            "soa_total_buffers":   1 + nonrec_fields,
        })

    if not parsed_adts:
        return None

    # Select target ADT
    if type_hint:
        match = [a for a in parsed_adts if a["type_name"] == type_hint]
        if match:
            return match[0]

    # Heuristic: pick the type with the most field slots (likely the main ADT)
    return max(parsed_adts, key=lambda a: a["total_field_slots"])


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
    # adt_info is populated once (from AOS source) by parse_adt_buffers()

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
                    "adt_info":   None,   # from parse_adt_buffers
                    "pass_types": {},
                    "pass_uses":  {},
                }
            try:
                content = src.read_text(encoding="utf-8", errors="ignore")
            except Exception as e:
                print(f"  ✗ {src.name}: {e}")
                continue

            # ADT fields annotation
            m = adt_re.search(content)
            if m and result[prog]["adt_fields"] is None:
                result[prog]["adt_fields"] = int(m.group(1))
                if vdir == "AOS":
                    print(f"  ✓ {prog}: adt_fields={m.group(1)}")

            # Parse ADT structure for buffer counting (once, from AOS)
            if vdir == "AOS" and result[prog]["adt_info"] is None:
                adt_info = parse_adt_buffers(content)
                if adt_info:
                    result[prog]["adt_info"] = adt_info
                    print(f"  ✓ {prog}: ADT '{adt_info['type_name']}' "
                          f"→ AoS=1 buf, SoA={adt_info['soa_total_buffers']} bufs "
                          f"({adt_info['nonrec_field_slots']} non-recursive field slots, "
                          f"{adt_info['total_field_slots'] - adt_info['nonrec_field_slots']} recursive, "
                          f"{len(adt_info['constructors'])} constructor(s))")
                else:
                    print(f"  ⚠  {prog}: could not parse ADT definition for buffer count")

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
    with_buffers = sum(1 for v in result.values() if v["adt_info"] is not None)
    with_passes = sum(1 for v in result.values() if v["pass_types"])
    with_uses  = sum(1 for v in result.values()
                     if any(u is not None for u in v["pass_uses"].values()))
    print(f"\n  {with_adt} programs have adt_fields annotation")
    print(f"  {with_buffers} programs have parseable ADT definitions (buffer counts)")
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

    Pass header line examples:
      Running pass SumArea (fold, uses=2):    → type=fold, uses=2
      Running pass SumArea (fold):            → type=fold, uses=None
      Running pass SumArea:                   → type=unknown, uses=None

    Timing is read from the ITER TIMES line that Gibbon emits after each pass:
      ITER TIMES: [0.052013, 0.052099, ...]

    Individual itertime: lines are ignored (they are the raw loop output that
    Gibbon also collects into ITER TIMES; using the sorted list directly is
    cleaner and avoids any partial-iteration noise).

    Returns {pass_name: stats_dict}.
    """
    passes: Dict            = {}
    current: Optional[str]  = None
    cur_type                = "unknown"
    cur_uses: Optional[int] = None
    cur_times: List[float]  = []

    # Match:  Running pass Name (fold[, uses=N]):
    pass_re = re.compile(
        r'Running\s+pass\s+([^(:\n]+?)\s*'
        r'(?:\(\s*([^,)]+?)\s*(?:,\s*uses\s*=\s*(\d+))?\s*\))?\s*:',
        re.IGNORECASE,
    )
    # Match:  ITER TIMES: [0.052013, 0.052099, ...]
    iter_times_re = re.compile(
        r'ITER\s+TIMES\s*:\s*\[([^\]]+)\]',
        re.IGNORECASE,
    )

    def _commit():
        if current is not None and cur_times:
            passes[current] = _stats(cur_times, cur_type, cur_uses)

    for line in raw.splitlines():
        s = line.strip()

        # ── New pass header ──────────────────────────────────────────────────
        m = pass_re.match(s)
        if m:
            _commit()
            current  = m.group(1).strip()
            hint     = (m.group(2) or "").strip().lower()
            uses_str = m.group(3)
            cur_type = ("fold" if "fold" in hint
                        else ("map" if "map" in hint else "unknown"))
            cur_uses  = int(uses_str) if uses_str else None
            cur_times = []
            continue

        # ── ITER TIMES list (authoritative timing source) ────────────────────
        m2 = iter_times_re.search(s)
        if m2 and current is not None:
            raw_nums = m2.group(1)
            parsed = []
            for tok in raw_nums.split(','):
                tok = tok.strip()
                if tok:
                    try:
                        parsed.append(float(tok))
                    except ValueError:
                        pass
            if parsed:
                cur_times = parsed   # replace any partial itertime accumulation
            continue

        # ── End marker ───────────────────────────────────────────────────────
        if s == "End":
            _commit()
            current   = None
            cur_times = []

    _commit()   # in case output ended without a final "End"
    return passes


def _stats(times: List[float], pass_type: str = "unknown",
           uses: Optional[int] = None) -> Dict:
    """
    Compute summary statistics from the ITER TIMES list.

    stderr = standard error of the mean = stdev / sqrt(n)
    This is what's shown as ± in the tables.
    """
    n      = len(times)
    med    = statistics.median(times)
    mean   = statistics.mean(times)
    mn     = min(times)
    mx     = max(times)
    sd     = statistics.stdev(times) if n > 1 else 0.0
    stderr = sd / (n ** 0.5) if n > 1 else 0.0
    return {
        "iter_times":  times,
        "median_time": med,
        "mean_time":   mean,
        "min_time":    mn,
        "max_time":    mx,
        "stdev":       sd,
        "stderr":      stderr,   # ± shown in tables
        "n":           n,
        "pass_type":   pass_type,
        "uses":        uses,
    }


def apply_source_classification(result: BenchmarkResult,
                                 src_data: Dict) -> None:
    """
    For each pass, fill in any missing pass_type and uses from source scan.
    Attaches adt_fields and adt_info to the result object.
    Computes derived fields: dead_ratio.

    Semantics:
      adt_fields  = TOTAL fields in the ADT including recursive ones.
                    This is what @BENCH adt_fields=N counts.
      uses        = TOTAL fields the pass accesses (recursive + non-recursive).
                    This is what uses=N in printsym counts.
      dead_ratio  = (adt_fields - uses) / adt_fields
                    Consistent: both counts include recursive fields.

    NOTE: per-pass SoA buffer usage cannot be computed here because uses= counts
    total fields accessed (recursive + non-recursive) and we would need the
    non-recursive-only count to know how many distinct SoA buffers are touched.
    soa_total_buffers is still valid at the ADT level (computed from the
    parsed non-recursive field slots) and shown in the summary table.
    """
    adt = src_data.get("adt_fields")          # total incl. recursive
    result.adt_fields  = adt
    result.adt_info    = src_data.get("adt_info")
    result.nonrec_fields = (result.adt_info["nonrec_field_slots"]
                            if result.adt_info else None)

    for pname, pdata in result.passes.items():
        if pdata.get("pass_type", "unknown") == "unknown":
            pdata["pass_type"] = lookup_pass_type(pname, src_data)
        if pdata.get("uses") is None:
            pdata["uses"] = lookup_pass_uses(pname, src_data)

        uses = pdata.get("uses")

        # Dead-field metrics: denominator is adt_fields (total, incl. recursive)
        # because uses= also counts total fields accessed (incl. recursive).
        if adt is not None and uses is not None:
            pdata["dead_fields"] = adt - uses
            pdata["dead_ratio"]  = pdata["dead_fields"] / adt if adt > 0 else 0.0
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
# ---------------------------------------------------------------------------
# Compiler mtime cache (checked once per script run)
# ---------------------------------------------------------------------------
_GIBBON_COMPILER_CACHE: Optional[Tuple[Path, float]] = None  # (path, mtime)

def get_gibbon_compiler_info() -> Optional[Tuple[Path, float]]:
    """
    Returns (compiler_path, mtime) for the gibbon executable.
    Cached globally so we only look it up once per run.
    Returns None if gibbon is not in PATH.
    """
    global _GIBBON_COMPILER_CACHE
    if _GIBBON_COMPILER_CACHE is not None:
        return _GIBBON_COMPILER_CACHE
    
    gibbon_path = shutil.which("gibbon")
    if gibbon_path is None:
        return None
    
    p = Path(gibbon_path).resolve()
    if not p.exists():
        return None
    
    mtime = p.stat().st_mtime
    _GIBBON_COMPILER_CACHE = (p, mtime)
    return _GIBBON_COMPILER_CACHE


def needs_recompilation(source: Path, exe: Path, c_file: Path
                        ) -> Tuple[bool, str]:
    """
    Returns (needs_recompile: bool, reason: str).
    reason is printed so the user knows why we skipped or recompiled.
    
    Checks:
      1. exe or c_file missing → recompile
      2. source newer than exe → recompile
      3. gibbon compiler newer than exe → recompile (common sense: if the
         compiler was updated, old exes are stale)
    """
    if not exe.exists():
        return True, "exe missing"
    if not c_file.exists():
        return True, "c file missing"
    
    exe_t = exe.stat().st_mtime
    src_t = source.stat().st_mtime
    
    if src_t > exe_t:
        src_dt  = datetime.datetime.fromtimestamp(src_t).strftime("%Y-%m-%d %H:%M:%S")
        exe_dt  = datetime.datetime.fromtimestamp(exe_t).strftime("%Y-%m-%d %H:%M:%S")
        return True, f"source ({src_dt}) newer than exe ({exe_dt})"
    
    # Check if the compiler itself is newer than the exe
    compiler_info = get_gibbon_compiler_info()
    if compiler_info is not None:
        compiler_path, compiler_t = compiler_info
        if compiler_t > exe_t:
            comp_dt = datetime.datetime.fromtimestamp(compiler_t).strftime("%Y-%m-%d %H:%M:%S")
            exe_dt  = datetime.datetime.fromtimestamp(exe_t).strftime("%Y-%m-%d %H:%M:%S")
            return True, f"compiler ({compiler_path}, {comp_dt}) newer than exe ({exe_dt})"
    
    exe_dt = datetime.datetime.fromtimestamp(exe_t).strftime("%Y-%m-%d %H:%M:%S")
    return False, f"exe up-to-date (compiled {exe_dt})"

# ---------------------------------------------------------------------------
# Compile one variant  (called from thread pool)
# ---------------------------------------------------------------------------
def compile_one(source: Path, variant: str, out_dir: Path,
                force: bool, use_mutable_cursors: bool = True
                ) -> Tuple[bool, float, Optional[str]]:
    stem   = source.stem
    c_file = out_dir / f"{stem}.{variant}.c"
    exe    = out_dir / f"{stem}.{variant}.exe"
    out_dir.mkdir(parents=True, exist_ok=True)

    recompile, reason = needs_recompilation(source, exe, c_file)
    if not force and not recompile:
        print(f"  [{variant.upper()}] {stem}: skipping  ({reason})")
        print(f"           exe: {exe}")
        print(f"           src: {source}")
        return True, 0.0, None

    if force:
        reason = "forced recompile"

    cmd = ["gibbon"]
    if use_mutable_cursors:
        cmd.append("--use-mutable-cursors")
    cmd.extend([
        "--packed", "--to-exe",
        "--no-ran",
        "--cfile",   str(c_file),
        "--exefile", str(exe),
        str(source),
    ])
    
    flags_str = "mut-cursors" if use_mutable_cursors else "imm-cursors"
    print(f"  [{variant.upper()} {flags_str}] {stem}: compiling  ({reason})")
    print(f"           src: {source}  →  {exe}")
    t0 = time.time()
    try:
        r = subprocess.run(cmd, capture_output=True, text=True)
        elapsed = time.time() - t0
        if r.returncode == 0:
            print(f"           ok ({elapsed:.1f}s)")
            return True, elapsed, None
        print(f"           FAILED ({elapsed:.1f}s)")
        return False, elapsed, r.stderr.strip()
    except FileNotFoundError:
        elapsed = time.time() - t0
        print("           FAILED (gibbon not in PATH)")
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
            pool.submit(compile_one, src, var, od, force, use_mut): (prog, var)
            for prog, var, src, od, force, use_mut in tasks
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
def run_exe(exe: Path, iterations: int,
            dump_dir: Optional[Path] = None) -> Tuple[bool, float, Optional[str], int]:
    """
    Run executable and return (success, elapsed_time, stdout_or_stderr, returncode).
    returncode is used to detect OOM (e.g., 137 = killed by OOM, 139 = segfault).
    """
    if not exe.exists():
        return False, 0.0, None, -1
    exe_mtime = datetime.datetime.fromtimestamp(exe.stat().st_mtime).strftime(
        "%Y-%m-%d %H:%M:%S"
    )
    print(f"           running: {exe}")
    print(f"           exe mtime: {exe_mtime}  |  --iterate {iterations}")
    # Gibbon exes accept --iterate N on the command line, NOT via GIBBON_ITERS
    cmd = [str(exe), "--iterate", str(iterations)]
    t0  = time.time()
    try:
        r = subprocess.run(cmd, capture_output=True, text=True)
        elapsed = time.time() - t0
        if r.returncode == 0:
            if dump_dir is not None:
                dump_dir.mkdir(parents=True, exist_ok=True)
                dump_file = dump_dir / f"{exe.stem}.stdout.txt"
                dump_file.write_text(r.stdout)
            return True, elapsed, r.stdout, 0
        # Failed - return stderr and the actual exit code for OOM detection
        return False, elapsed, r.stderr, r.returncode
    except Exception as e:
        return False, time.time() - t0, str(e), -1

# ---------------------------------------------------------------------------
# Benchmark one program
# ---------------------------------------------------------------------------
def benchmark_program(prog: str, programs_dir: Path, out_dir: Path,
                      iterations: int, force: bool,
                      source_cls_all: Dict,
                      dump_raw: bool = False,
                      benchmark_immutable: bool = False,
                      ) -> Tuple[Optional[BenchmarkResult], Optional[BenchmarkResult]]:
    """
    Benchmark one program. Returns (aos_result, soa_result) for backwards compatibility.
    If benchmark_immutable=True, also compiles/runs immutable cursor variants but only
    returns the mutable cursor results. Use benchmark_program_all_variants() to get all 4.
    """
    print(f"\n{'='*70}\nBenchmarking: {prog}\n{'='*70}")

    # Determine which variants to compile
    if benchmark_immutable:
        variants = [
            ("aos", True),       # AOS with mutable cursors
            ("aos_imm", False),  # AOS without mutable cursors
            ("soa", True),       # SoA with mutable cursors
            ("soa_imm", False),  # SoA without mutable cursors
        ]
    else:
        variants = [
            ("aos", True),
            ("soa", True),
        ]

    tasks = []
    for var, use_mut in variants:
        # Source is always in AOS/ or SOA/ directory, not aos_imm/soa_imm
        src_dir = "AOS" if var.startswith("aos") else "SOA"
        src = programs_dir / src_dir / prog
        if src.exists():
            tasks.append((prog, var, src, out_dir, force, use_mut))
        else:
            print(f"  Warning: {src} not found")

    compile_results = compile_parallel(tasks)
    results: Dict[str, BenchmarkResult] = {}
    src_data = source_cls_all.get(prog, {"adt_fields": None, "adt_info": None,
                                          "pass_types": {}, "pass_uses": {}})

    dump_dir = (out_dir / "raw_output") if dump_raw else None

    for var, use_mut in variants:
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

        print(f"  [{var.upper()}] running ...")
        ok2, rt, stdout_or_stderr, returncode = run_exe(exe, iterations, dump_dir)
        if not ok2:
            # Detect OOM from both exit code and stderr content
            # Common OOM exit codes: 137 (killed by OOM), 139 (segfault), -11 (SIGSEGV)
            oom_exit_codes = {137, 139, -11, 134}  # 134 = SIGABRT from stack overflow
            stderr_text = (stdout_or_stderr or "").lower()
            
            is_oom = (returncode in oom_exit_codes) or any(keyword in stderr_text for keyword in [
                "stack overflow", "out of memory", "cannot allocate",
                "segmentation fault", "stack space overflow",
                "memory exhausted", "bad_alloc", "killed"
            ])
            
            # Debug output - show what we got
            print(f"           exit code: {returncode}")
            if stdout_or_stderr:
                stderr_preview = stdout_or_stderr[:200].replace('\n', ' ')
                print(f"           stderr: {stderr_preview}...")
            
            if is_oom:
                print(f"           FAILED (out of memory)")
                res.error_message = "out of memory"
            else:
                print(f"           FAILED (exit non-zero)")
                res.error_message = "execution failed"
            res.run_success = False
        else:
            res.run_success = True
            if stdout_or_stderr:
                res.output  = clean_output(stdout_or_stderr)
                res.passes  = parse_passes(stdout_or_stderr)
                apply_source_classification(res, src_data)

                # ── Print per-pass timing digest ──────────────────────────
                total_t = sum(p["median_time"] for p in res.passes.values())
                print(f"           wall={rt:.2f}s  passes={len(res.passes)}"
                      f"  total_itertime={total_t:.4f}s")
                for pname, pd in res.passes.items():
                    its = pd.get("iter_times", [])
                    med = pd["median_time"]
                    se  = pd.get("stderr", 0.0)
                    mn  = pd["min_time"]
                    mx  = pd["max_time"]
                    n   = pd.get("n", len(its))
                    t   = pd["pass_type"][0].upper() if pd["pass_type"] != "unknown" else "?"
                    print(f"           [{t}] {pname}: "
                          f"median={med:.4f} ±{se:.5f}s  "
                          f"min={mn:.4f}s  max={mx:.4f}s  n={n}")

        results[var] = res

    # For backwards compatibility, return (aos, soa) with mutable cursors
    # Also store all results globally if benchmarking immutable variants
    aos, soa = results.get("aos"), results.get("soa")
    
    # Global storage for extended results (used by new comparison table)
    if benchmark_immutable and hasattr(benchmark_program, '_all_variants_results'):
        benchmark_program._all_variants_results.append({
            'program': prog,
            'aos': results.get("aos"),
            'aos_imm': results.get("aos_imm"),
            'soa': results.get("soa"),
            'soa_imm': results.get("soa_imm"),
        })
    
    if aos and soa and aos.run_success and soa.run_success:
        m = outputs_match(aos, soa)
        print(f"\n  Output check (mutable cursors): {'✓ MATCH' if m else '✗ MISMATCH'}")
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
            buf_s = ""
            if aos.adt_info:
                buf_s = (f", AoS=1 buf, SoA={aos.adt_info['soa_total_buffers']} bufs")
            print(f"  Passes: {folds} fold, {maps} map, {unk} unknown"
                  f"{adt_s}{buf_s}, {len(with_uses)} have uses= annotation")
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


def fmt_pm(median: float, stderr: float) -> str:
    """Format as 'median ± stderr' using consistent decimal places."""
    if stderr == 0.0:
        return fmt(median)
    # Use one extra decimal place of precision for stderr vs median
    a = abs(median)
    if a >= 10.0:   dp = 2
    elif a >= 1.0:  dp = 3
    elif a >= 0.001: dp = 4
    else:           dp = 2
    # stderr shown with one more sig fig
    err_dp = min(dp + 1, 6)
    return f"{median:.{dp}f}$\\pm${stderr:.{err_dp}f}"

# ---------------------------------------------------------------------------
# LaTeX tables
# ---------------------------------------------------------------------------
def _table_cursor_comparison(f, all_variants_results):
    """
    Generates Table 2: Cursor mode comparison showing all 4 variants:
    AOS-mut, AOS-imm, SoA-mut, SoA-imm for each program.
    """
    f.write("\n\n")
    f.write("% ============================================================================\n")
    f.write("% Table 2: Mutable vs Immutable Cursor Comparison\n")
    f.write("% ============================================================================\n\n")
    f.write("\\begin{table}[htbp]\n\\centering\n")
    f.write("\\caption{Mutable vs immutable cursor comparison. "
            "Times are median per iteration (s). "
            "Speedups shown are AoS-mut/SoA-mut, AoS-imm/AoS-mut, and AoS-imm/SoA-mut. "
            "${>}1{\\times}$ means the denominator is faster. "
            "\\textbf{Bold} marks the fastest time across all four variants.}\n")
    f.write("\\label{tab:cursor_comparison}\n\\small\n")
    f.write("\\begin{tabular}{l r r r r r r r}\n\\toprule\n")
    f.write(
        "\\textbf{Program}"
        " & \\textbf{AoS-mut} & \\textbf{AoS-imm}"
        " & \\textbf{SoA-mut} & \\textbf{SoA-imm}"
        " & \\textbf{AoS-mut/SoA-mut}"
        " & \\textbf{AoS-imm/AoS-mut}"
        " & \\textbf{AoS-imm/SoA-mut} \\\\\n"
    )
    f.write("\\midrule\n")

    for entry in all_variants_results:
        prog = entry['program'].replace(".hs", "").replace("_", "\\_")
        aos_mut = entry.get('aos')
        aos_imm = entry.get('aos_imm')
        soa_mut = entry.get('soa')
        soa_imm = entry.get('soa_imm')

        # Calculate total times (sum of all passes)
        # Calculate total times (sum of all passes)
        def get_total_or_oom(res):
            """Returns (time, is_oom) tuple."""
            if res is None:
                return None, False
            if res.run_success:
                return sum(p["median_time"] for p in res.passes.values()), False
            # Failed - check if it was OOM
            is_oom = (res.error_message == "out of memory")
            return None, is_oom

        aost_mut, aost_mut_oom = get_total_or_oom(aos_mut)
        aost_imm, aost_imm_oom = get_total_or_oom(aos_imm)
        soat_mut, soat_mut_oom = get_total_or_oom(soa_mut)
        soat_imm, soat_imm_oom = get_total_or_oom(soa_imm)

        # Format times and bold the overall fastest across all four variants.
        def fmt_cell(t, is_oom):
            """Format a single time cell, showing OOM if applicable."""
            if is_oom:
                return "\\textit{OOM}"
            if t is None:
                return "--"
            return fmt(t)

        cells = {
            "aos_mut": [fmt_cell(aost_mut, aost_mut_oom), aost_mut, aost_mut_oom],
            "aos_imm": [fmt_cell(aost_imm, aost_imm_oom), aost_imm, aost_imm_oom],
            "soa_mut": [fmt_cell(soat_mut, soat_mut_oom), soat_mut, soat_mut_oom],
            "soa_imm": [fmt_cell(soat_imm, soat_imm_oom), soat_imm, soat_imm_oom],
        }
        valid_times = [v[1] for v in cells.values() if v[1] is not None and not v[2]]
        if valid_times:
            min_t = min(valid_times)
            for k, v in cells.items():
                if v[1] is not None and not v[2] and v[1] == min_t:
                    v[0] = f"\\textbf{{{v[0]}}}"

        aos_mut_f = cells["aos_mut"][0]
        aos_imm_f = cells["aos_imm"][0]
        soa_mut_f = cells["soa_mut"][0]
        soa_imm_f = cells["soa_imm"][0]

        # Calculate speedups
        def speedup(a, s):
            if a is not None and s is not None and s > 0:
                return a / s
            return None

        spd_mut = speedup(aost_mut, soat_mut)
        spd_aos_imm_over_aos_mut = speedup(aost_imm, aost_mut)
        spd_imm = speedup(aost_imm, soat_mut)

        spd_mut_s = _spd_cell(spd_mut) if spd_mut else "--"
        spd_aos_imm_over_aos_mut_s = _spd_cell(spd_aos_imm_over_aos_mut) if spd_aos_imm_over_aos_mut else "--"
        spd_imm_s = _spd_cell(spd_imm) if spd_imm else "--"

        f.write(f"{prog}"
                f" & {aos_mut_f} & {aos_imm_f}"
                f" & {soa_mut_f} & {soa_imm_f}"
                f" & {spd_mut_s}"
                f" & {spd_aos_imm_over_aos_mut_s}"
                f" & {spd_imm_s} \\\\\n")

    f.write("\\bottomrule\n\\end{tabular}\n\\end{table}\n\n")


def write_latex_tables(all_results: List[Tuple], out_file: Path,
                       all_variants_results: Optional[List[Dict]] = None):
    with open(out_file, "w") as f:
        f.write("% Gibbon Benchmark Suite v3.1 – auto-generated\n")
        f.write("% Requires: \\usepackage{booktabs} in preamble\n\n")
        _table_summary(f, all_results)
        if all_variants_results:
            _table_cursor_comparison(f, all_variants_results)
        _table_per_program(f, all_results, all_variants_results)
    print(f"  ✓ LaTeX tables → {out_file}")
    if all_variants_results:
        print(f"    (includes Table 2: cursor mode comparison with {len(all_variants_results)} programs)")
        print(f"    (per-program tables show 4 variants: mut + imm cursors)")


def _spd_cell(spd: float, bold_threshold: float = 1.1) -> str:
    s = f"{spd:.2f}" + r"$\times$"
    return r"\textbf{" + s + "}" if spd > bold_threshold else s


def _table_summary(f, all_results):
    """
    Table 1: one row per program.
    Program | ADT fields | SoA bufs | Fold AoS | Fold SoA | Fold Speedup | Map AoS | Map SoA | Map Speedup
    """
    f.write("% -- Table 1: Summary by pass type --\n")
    f.write("\\begin{table}[t]\n\\centering\n")
    f.write(
        "\\caption{End-to-end execution time (s, median per iteration) "
        "and speedup split by pass type. "
        "ADT fields = non-recursive fields annotated with {\\tt @BENCH adt\\_fields}; "
        "SoA bufs = $1 + $ non-recursive field slots across all constructors "
        "(recursive children are stored in the tag buffer). "
        "Speedup ${>}1{\\times}$ means SoA is faster; "
        "\\textbf{bold} marks ${>}1.1{\\times}$.}\n"
    )
    f.write("\\label{tab:summary}\n\\small\n")
    f.write("\\begin{tabular}{l c c r r r r r r}\n\\toprule\n")
    f.write(
        "\\textbf{Program} & \\textbf{ADT} & \\textbf{SoA}"
        " & \\multicolumn{3}{c}{\\textbf{Fold passes}}"
        " & \\multicolumn{3}{c}{\\textbf{Map passes}} \\\\\n"
    )
    f.write("\\cmidrule(lr){4-6}\\cmidrule(lr){7-9}\n")
    f.write(
        " & fields & bufs"
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
        adt_info = getattr(aos, "adt_info", None)
        bufs_str = str(adt_info["soa_total_buffers"]) if adt_info else "--"

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
            f"{prog} & {adt_str} & {bufs_str}"
            f" & {fmt(af) if af > 0 else '--'}"
            f" & {fmt(sf) if sf > 0 else '--'}"
            f" & {fspd_s}"
            f" & {fmt(am) if am > 0 else '--'}"
            f" & {fmt(sm) if sm > 0 else '--'}"
            f" & {mspd_s} \\\\\n"
        )

    f.write("\\bottomrule\n\\end{tabular}\n\\end{table}\n\n\n")


def _table_per_program(f, all_results, all_variants_results=None):
    """
    One table per program showing per-pass performance.
    
    If all_variants_results is None (default):
        Shows 2 variants: AoS-mut, SoA-mut
    If all_variants_results is provided:
        Shows 4 variants: AoS-mut, AoS-imm, SoA-mut, SoA-imm
    """
    # Build a mapping from program name to variant results
    variants_map = {}
    if all_variants_results:
        for entry in all_variants_results:
            variants_map[entry['program']] = entry
    
    for aos, soa in all_results:
        if not (aos and soa):
            continue

        prog_hs  = aos.program
        prog     = prog_hs.replace(".hs", "")
        pdisplay = prog.replace("_", "\\_")
        
        # Get all 4 variants if available
        aos_imm = None
        soa_imm = None
        if prog_hs in variants_map:
            aos_imm = variants_map[prog_hs].get('aos_imm')
            soa_imm = variants_map[prog_hs].get('soa_imm')
        
        show_4_variants = (aos_imm is not None or soa_imm is not None)
        
        # Skip if mutable cursors didn't run successfully
        if not (aos.run_success and soa.run_success):
            continue
        
        adt      = getattr(aos, "adt_fields", None)
        adt_info = getattr(aos, "adt_info", None)
        soa_total_bufs = adt_info["soa_total_buffers"] if adt_info else None
        passes   = sorted(set(list(aos.passes) + list(soa.passes)))
        if not passes:
            continue

        type_name = adt_info["type_name"] if adt_info else None
        adt_note  = ""
        if adt is not None:
            adt_note += f", ADT has {adt} fields"
        if soa_total_bufs is not None:
            adt_note += f", SoA uses {soa_total_bufs} buffers"

        f.write(f"% -- Table: {prog} --\n")
        f.write("\\begin{table}[t]\n\\centering\n")
        
        cursor_note = " (mutable + immutable cursors)" if show_4_variants else ""
        f.write(
            f"\\caption{{Per-pass performance for \\texttt{{{pdisplay}}}"
            f"{adt_note}{cursor_note}. "
            "Times are median per iteration (s); $\\pm$ shows standard error of the mean "
            "across --iterate runs. "
            "T: F=fold, M=map. "
            "Uses: fields accessed / total (recursive + non-recursive). "
            "Dead\\%: fraction of fields not accessed by this pass. "
            "Speedup ${>}1{\\times}$ means SoA is faster. "
            "OOM = out of memory.}}\n"
        )
        f.write(f"\\label{{tab:{prog}}}\n\\small\n")

        # Decide which optional columns to show
        has_uses = any(
            aos.passes.get(p, {}).get("uses") is not None or
            soa.passes.get(p, {}).get("uses") is not None
            for p in passes
        )

        # Table header depends on whether we show 2 or 4 variants
        if show_4_variants:
            if has_uses and adt is not None:
                f.write("\\begin{tabular}{l c c r r r r r r r r}\n\\toprule\n")
                f.write(
                    "\\textbf{Pass} & \\textbf{T}"
                    " & \\textbf{Uses} & \\textbf{Dead\\%}"
                    " & \\textbf{AoS-mut} & \\textbf{AoS-imm}"
                    " & \\textbf{SoA-mut} & \\textbf{SoA-imm}"
                    " & \\textbf{AoS-mut/SoA-mut}"
                    " & \\textbf{AoS-imm/AoS-mut}"
                    " & \\textbf{AoS-imm/SoA-mut} \\\\\n"
                )
            else:
                f.write("\\begin{tabular}{l c r r r r r r r}\n\\toprule\n")
                f.write(
                    "\\textbf{Pass} & \\textbf{T}"
                    " & \\textbf{AoS-mut} & \\textbf{AoS-imm}"
                    " & \\textbf{SoA-mut} & \\textbf{SoA-imm}"
                    " & \\textbf{AoS-mut/SoA-mut}"
                    " & \\textbf{AoS-imm/AoS-mut}"
                    " & \\textbf{AoS-imm/SoA-mut} \\\\\n"
                )
        else:
            # Original 2-variant table
            if has_uses and adt is not None:
                f.write("\\begin{tabular}{l c c r r r r}\n\\toprule\n")
                f.write(
                    "\\textbf{Pass} & \\textbf{T}"
                    " & \\textbf{Uses} & \\textbf{Dead\\%}"
                    " & \\textbf{AoS med$\\pm$err} & \\textbf{SoA med$\\pm$err} & \\textbf{Speedup} \\\\\n"
                )
            else:
                f.write("\\begin{tabular}{l c r r r}\n\\toprule\n")
                f.write(
                    "\\textbf{Pass} & \\textbf{T}"
                    " & \\textbf{AoS med$\\pm$err} & \\textbf{SoA med$\\pm$err} & \\textbf{Speedup} \\\\\n"
                )
        f.write("\\midrule\n")

        speedups_mut = []
        speedups_aos_imm_over_aos_mut = []
        speedups_imm = []
        
        for pname in passes:
            ad   = aos.passes.get(pname, {})
            sd   = soa.passes.get(pname, {})
            
            ptype = ad.get("pass_type") or sd.get("pass_type") or "unknown"
            tchar = "F" if ptype == "fold" else ("M" if ptype == "map" else "?")
            pdisp = pname.replace("_", "\\_")

            uses   = ad.get("uses") or sd.get("uses")
            dead_r = ad.get("dead_ratio") or sd.get("dead_ratio")

            if show_4_variants:
                # Get data for all 4 variants
                def get_time_info(res, pname):
                    """Get (display, median_time, is_oom) for a pass."""
                    if res is None:
                        return "--", None, False
                    if not res.run_success:
                        if res.error_message == "out of memory":
                            return "\\textit{OOM}", None, True
                        return "--", None, False
                    pd = res.passes.get(pname, {})
                    med = pd.get("median_time", 0.0)
                    err = pd.get("stderr", 0.0)
                    if med == 0.0:
                        return "--", None, False
                    return fmt_pm(med, err), med, False
                
                aost_mut, aost_mut_v, aost_mut_oom = get_time_info(aos, pname)
                aost_imm, aost_imm_v, aost_imm_oom = get_time_info(aos_imm, pname)
                soat_mut, soat_mut_v, soat_mut_oom = get_time_info(soa, pname)
                soat_imm, soat_imm_v, soat_imm_oom = get_time_info(soa_imm, pname)

                # Bold only the fastest available time across all 4 variants.
                cells = {
                    "aos_mut": [aost_mut, aost_mut_v, aost_mut_oom],
                    "aos_imm": [aost_imm, aost_imm_v, aost_imm_oom],
                    "soa_mut": [soat_mut, soat_mut_v, soat_mut_oom],
                    "soa_imm": [soat_imm, soat_imm_v, soat_imm_oom],
                }
                valid_times = [v[1] for v in cells.values() if v[1] is not None and not v[2]]
                if valid_times:
                    min_t = min(valid_times)
                    for _, v in cells.items():
                        if v[1] is not None and not v[2] and v[1] == min_t:
                            v[0] = f"\\textbf{{{v[0]}}}"

                aost_mut = cells["aos_mut"][0]
                aost_imm = cells["aos_imm"][0]
                soat_mut = cells["soa_mut"][0]
                soat_imm = cells["soa_imm"][0]
                
                # Calculate speedups
                def calc_spd(a_res, s_res, pname):
                    if a_res and s_res and a_res.run_success and s_res.run_success:
                        at = a_res.passes.get(pname, {}).get("median_time", 0.0)
                        st = s_res.passes.get(pname, {}).get("median_time", 0.0)
                        if at > 0 and st > 0:
                            return at / st
                    return None
                
                spd_mut = calc_spd(aos, soa, pname)
                spd_aos_imm_over_aos_mut = calc_spd(aos_imm, aos, pname)
                spd_imm = calc_spd(aos_imm, soa, pname)
                
                spd_mut_s = _spd_cell(spd_mut) if spd_mut else "--"
                spd_aos_imm_over_aos_mut_s = _spd_cell(spd_aos_imm_over_aos_mut) if spd_aos_imm_over_aos_mut else "--"
                spd_imm_s = _spd_cell(spd_imm) if spd_imm else "--"
                
                if spd_mut:
                    speedups_mut.append(spd_mut)
                if spd_aos_imm_over_aos_mut:
                    speedups_aos_imm_over_aos_mut.append(spd_aos_imm_over_aos_mut)
                if spd_imm:
                    speedups_imm.append(spd_imm)
                
                # Write row
                if has_uses and adt is not None:
                    uses_s = f"{uses}/{adt}" if uses is not None else "--"
                    dead_s = f"{dead_r*100:.0f}\\%" if dead_r is not None else "--"
                    f.write(f"{pdisp} & {tchar} & {uses_s} & {dead_s}"
                            f" & {aost_mut} & {aost_imm}"
                            f" & {soat_mut} & {soat_imm}"
                            f" & {spd_mut_s}"
                            f" & {spd_aos_imm_over_aos_mut_s}"
                            f" & {spd_imm_s} \\\\\n")
                else:
                    f.write(f"{pdisp} & {tchar}"
                            f" & {aost_mut} & {aost_imm}"
                            f" & {soat_mut} & {soat_imm}"
                            f" & {spd_mut_s}"
                            f" & {spd_aos_imm_over_aos_mut_s}"
                            f" & {spd_imm_s} \\\\\n")
            
            else:
                # Original 2-variant logic
                at_s = ad.get("median_time", 0.0)
                st_s = sd.get("median_time", 0.0)
                if at_s == 0.0 and st_s == 0.0:
                    continue

                spd   = at_s / st_s if st_s > 0 else 0.0

                # median ± stderr cells
                a_err = ad.get("stderr", 0.0)
                s_err = sd.get("stderr", 0.0)
                at_f  = fmt_pm(at_s, a_err) if at_s > 0 else "--"
                st_f  = fmt_pm(st_s, s_err) if st_s > 0 else "--"

                # Bold the faster side's cell
                if spd > 1.1:
                    at_f_r, st_f_r = at_f, f"\\textbf{{{st_f}}}"
                elif 0 < spd < 0.9:
                    at_f_r, st_f_r = f"\\textbf{{{at_f}}}", st_f
                else:
                    at_f_r, st_f_r = at_f, st_f

                spd_s = _spd_cell(spd) if spd > 0 else "--"

                if has_uses and adt is not None:
                    uses_s = f"{uses}/{adt}" if uses is not None else "--"
                    dead_s = f"{dead_r*100:.0f}\\%" if dead_r is not None else "--"
                    f.write(f"{pdisp} & {tchar} & {uses_s} & {dead_s}"
                            f" & {at_f_r} & {st_f_r} & {spd_s} \\\\\n")
                else:
                    f.write(f"{pdisp} & {tchar}"
                            f" & {at_f_r} & {st_f_r} & {spd_s} \\\\\n")

                if spd > 0:
                    speedups_mut.append(spd)

        # Totals row
        def get_total(res):
            if res and res.run_success:
                return sum(p["median_time"] for p in res.passes.values())
            return None
        
        aost_mut_tot = get_total(aos)
        aost_imm_tot = get_total(aos_imm) if aos_imm else None
        soat_mut_tot = get_total(soa)
        soat_imm_tot = get_total(soa_imm) if soa_imm else None
        
        def fmt_total(t):
            return fmt(t) if t is not None else "--"
        
        sp_mut_tot = aost_mut_tot / soat_mut_tot if (aost_mut_tot and soat_mut_tot) else None
        sp_aos_imm_over_aos_mut_tot = aost_imm_tot / aost_mut_tot if (aost_imm_tot and aost_mut_tot) else None
        sp_imm_tot = aost_imm_tot / soat_mut_tot if (aost_imm_tot and soat_mut_tot) else None
        
        if show_4_variants:
            total_cells = {
                "aos_mut": [fmt_total(aost_mut_tot), aost_mut_tot],
                "aos_imm": [fmt_total(aost_imm_tot), aost_imm_tot],
                "soa_mut": [fmt_total(soat_mut_tot), soat_mut_tot],
                "soa_imm": [fmt_total(soat_imm_tot), soat_imm_tot],
            }
            total_valid = [v[1] for v in total_cells.values() if v[1] is not None]
            if total_valid:
                min_tot = min(total_valid)
                for _, v in total_cells.items():
                    if v[1] is not None and v[1] == min_tot:
                        v[0] = f"\\textbf{{{v[0]}}}"

            extra_cols = "& & " if (has_uses and adt is not None) else ""
            f.write("\\midrule\n")
            f.write(f"\\textbf{{Total}} & {extra_cols}"
                    f"& {total_cells['aos_mut'][0]} & {total_cells['aos_imm'][0]}"
                    f" & {total_cells['soa_mut'][0]} & {total_cells['soa_imm'][0]}"
                    f" & {_spd_cell(sp_mut_tot) if sp_mut_tot else '--'}"
                    f" & {_spd_cell(sp_aos_imm_over_aos_mut_tot) if sp_aos_imm_over_aos_mut_tot else '--'}"
                    f" & {_spd_cell(sp_imm_tot) if sp_imm_tot else '--'} \\\\\n")
            if speedups_mut:
                gm_mut = statistics.geometric_mean(speedups_mut)
                gm_aos_imm_over_aos_mut = (
                    statistics.geometric_mean(speedups_aos_imm_over_aos_mut)
                    if speedups_aos_imm_over_aos_mut else None
                )
                gm_imm = statistics.geometric_mean(speedups_imm) if speedups_imm else None
                f.write(f"\\textbf{{Geomean}} & {extra_cols}"
                        f"& & & & & {_spd_cell(gm_mut)}"
                        f" & {_spd_cell(gm_aos_imm_over_aos_mut) if gm_aos_imm_over_aos_mut else '--'}"
                        f" & {_spd_cell(gm_imm) if gm_imm else '--'} \\\\\n")
        else:
            extra_cols = "& & " if (has_uses and adt is not None) else ""
            f.write("\\midrule\n")
            f.write(f"\\textbf{{Total}} & {extra_cols}"
                    f"& {fmt(aost_mut_tot)} & {fmt(soat_mut_tot)} & {_spd_cell(sp_mut_tot)} \\\\\n")
            if speedups_mut:
                gm = statistics.geometric_mean(speedups_mut)
                f.write(f"\\textbf{{Geomean}} & {extra_cols}"
                        f"& & & {_spd_cell(gm)} \\\\\n")

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
    lines = ["=" * 72, "GIBBON BENCHMARK REPORT v3.1",
             "=" * 72, f"Generated: {time.strftime('%Y-%m-%d %H:%M:%S')}", ""]
    for aos, soa in all_results:
        if not aos or not soa:
            continue
        adt      = getattr(aos, "adt_fields", None)
        adt_info = getattr(aos, "adt_info", None)
        buf_hdr  = ""
        if adt_info:
            buf_hdr = (f"  [AoS=1 buf, SoA={adt_info['soa_total_buffers']} bufs"
                       f" | {adt_info['type_name']}]")
        lines.append(f"\nProgram: {aos.program}"
                     + (f"  [ADT fields: {adt}]" if adt else "")
                     + buf_hdr)
        lines.append("-" * 40)
        for tag, res in (("AOS", aos), ("SOA", soa)):
            if not res.run_success:
                lines.append(f"  {tag}: FAILED – {res.error_message}")
                continue
            total = sum(p["median_time"] for p in res.passes.values())
            lines.append(f"  {tag}: {total:.4f}s total")
            for pname, pd in res.passes.items():
                t     = pd["pass_type"][0].upper() if pd["pass_type"] != "unknown" else "?"
                uses  = pd.get("uses")
                dr    = pd.get("dead_ratio")
                n_it  = pd.get("n", len(pd.get("iter_times", [])))
                med   = pd["median_time"]
                se    = pd.get("stderr", 0.0)
                ann   = ""
                if uses is not None and adt:
                    ann += f"  uses={uses}/{adt}  dead={dr*100:.0f}%"
                lines.append(f"    [{t}] {pname}: {med:.4f} ±{se:.5f}s  (n={n_it}){ann}")
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
            adt_info = getattr(r, "adt_info", None)
            return {
                "compile_success":  r.compile_success,
                "run_success":      r.run_success,
                "error":            r.error_message,
                "adt_fields":       getattr(r, "adt_fields", None),
                "adt_type":         adt_info["type_name"] if adt_info else None,
                "aos_buffers":      1,
                "soa_total_buffers": adt_info["soa_total_buffers"] if adt_info else None,
                "nonrec_field_slots": adt_info["nonrec_field_slots"] if adt_info else None,
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


# ── Figure E: per-program heatmap ────────────────────────────────────────────
def _fig_heatmaps(good: List, out_dir: Path):
    dest = out_dir / "heatmaps"
    dest.mkdir(parents=True, exist_ok=True)

    for aos, soa in good:
        prog     = aos.program.replace(".hs", "")
        adt_info = getattr(aos, "adt_info", None)
        soa_tot  = adt_info["soa_total_buffers"] if adt_info else None
        passes   = sorted(set(list(aos.passes) + list(soa.passes)))
        spds, labs, types = [], [], []

        for pname in passes:
            at = aos.passes.get(pname, {}).get("median_time", 0.0)
            st = soa.passes.get(pname, {}).get("median_time", 0.0)
            if at > 0 and st > 0:
                spds.append(at / st)
                pt = (aos.passes.get(pname) or soa.passes.get(pname) or {}).get("pass_type", "unknown")
                types.append({"fold": "F", "map": "M"}.get(pt, "?"))
                labs.append(pname.replace("_", " "))

        if not spds:
            continue

        arr = np.array([spds])
        fig, ax = plt.subplots(figsize=(max(8, len(spds) * 1.2), 3.5))
        im = ax.imshow(arr, cmap="RdYlGn", aspect="auto",
                       vmin=0.7, vmax=1.3, interpolation="nearest")
        ax.set_xticks(np.arange(len(labs)))

        tick_labels = [f"{l}\n[{t}]" for l, t in zip(labs, types)]
        ax.set_xticklabels(tick_labels, rotation=45, ha="right", fontsize=7)
        ax.set_yticks([0]); ax.set_yticklabels([prog])
        plt.colorbar(im, ax=ax, orientation="horizontal", pad=0.55,
                     label="Speedup (AoS/SoA)  —  green = SoA faster")
        for i, (s, t) in enumerate(zip(spds, types)):
            ax.text(i, 0, f"{s:.2f}\n[{t}]",
                    ha="center", va="center", fontsize=7, fontweight="bold")
        bufs_hdr = (f"  |  SoA={soa_tot} buffers total" if soa_tot else "")
        ax.set_title(f"{prog}: per-pass speedup heatmap  "
                     f"(F=fold M=map ?=unknown{bufs_hdr})")
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
    ap = argparse.ArgumentParser(
        description="Gibbon Benchmark Suite v3.1",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=textwrap.dedent("""\
          Diagnosing timing discrepancies vs manual runs:
            1. Run with --dump-raw to save every exe's full stdout to
               benchmark_output/raw_output/*.stdout.txt  then inspect ITER TIMES lines.
            2. Run with --iterations 1 to match a cold single-run manual test.
               (More iterations can inflate median due to GC/cache warm-up effects.)
            3. Run with --clean to force recompilation and rule out stale exes.
               Every run prints the exact exe path and its mtime for verification.
        """),
    )
    ap.add_argument("--programs-dir",   type=Path, default=Path("programs"))
    ap.add_argument("--output-dir",     type=Path, default=Path("benchmark_output"))
    ap.add_argument("--iterations",     type=int,  default=20,
                    help="Number of timed iterations passed as --iterate N to each exe. "
                         "Use --iterations 1 to match a cold single-run manual test. "
                         "(default: 20)")
    ap.add_argument("--programs",       nargs="+")
    ap.add_argument("--clean",          action="store_true",
                    help="Force recompile every program regardless of mtime")
    ap.add_argument("--generate-paper", action="store_true")
    ap.add_argument("--latex-table",    type=Path, default=Path("performance_table.tex"))
    ap.add_argument("--figures-dir",    type=Path, default=Path("figures"))
    ap.add_argument("--report",         type=Path, default=Path("benchmark_report.txt"))
    ap.add_argument("--json",           type=Path, default=Path("benchmark_results.json"))
    ap.add_argument("--dump-raw",       action="store_true",
                    help="Save full exe stdout to benchmark_output/raw_output/. "
                         "Each file is <stem>.<variant>.stdout.txt and contains "
                         "the ITER TIMES list for every pass for manual inspection.")
    ap.add_argument("--benchmark-immutable", "--benchmark-imm", action="store_true",
                    help="Also compile and benchmark immutable cursor variants "
                         "(aos_imm, soa_imm) in addition to mutable cursor variants. "
                         "Generates Table 2 showing 4-way comparison.")
    args = ap.parse_args()

    programs_to_run = args.programs or DEFAULT_PROGRAMS

    print("\n" + "=" * 72)
    print("GIBBON BENCHMARK SUITE v3.1")
    print("=" * 72)
    print(f"  Programs dir : {args.programs_dir}")
    print(f"  Output dir   : {args.output_dir}")
    print(f"  Iterations   : {args.iterations}  "
          f"(passed as --iterate N; use --iterations 1 to match cold manual runs)")
    print(f"  Programs     : {len(programs_to_run)}")
    print(f"  Force recomp : {'YES  (--clean)' if args.clean else 'no  (smart mtime check)'}")
    print(f"  Paper mode   : {'YES' if args.generate_paper else 'no'}")
    print(f"  Dump raw     : {'YES → benchmark_output/raw_output/' if args.dump_raw else 'no'}")
    print(f"  Immutable    : {'YES  (4 variants: aos, aos_imm, soa, soa_imm)' if args.benchmark_immutable else 'no  (2 variants: aos, soa)'}")
    print(f"  CPU cores    : {multiprocessing.cpu_count()}")
    
    # Show which gibbon compiler will be used and its mtime
    compiler_info = get_gibbon_compiler_info()
    if compiler_info:
        compiler_path, compiler_t = compiler_info
        compiler_dt = datetime.datetime.fromtimestamp(compiler_t).strftime("%Y-%m-%d %H:%M:%S")
        print(f"  Compiler     : {compiler_path}")
        print(f"  Compiler mtime: {compiler_dt}  (exes older than this will be rebuilt)")
    else:
        print(f"  Compiler     : gibbon NOT FOUND in PATH")
    print("=" * 72)

    args.output_dir.mkdir(parents=True, exist_ok=True)
    source_cls_all = build_source_classification(args.programs_dir)

    # Initialize global storage for extended results (used by cursor comparison table)
    if args.benchmark_immutable:
        benchmark_program._all_variants_results = []

    all_results: List[Tuple] = []
    for prog in programs_to_run:
        aos, soa = benchmark_program(
            prog, args.programs_dir, args.output_dir,
            args.iterations, args.clean, source_cls_all,
            dump_raw=args.dump_raw,
            benchmark_immutable=args.benchmark_immutable,
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
        # Get extended results if they were collected
        extended_results = (getattr(benchmark_program, '_all_variants_results', None)
                           if args.benchmark_immutable else None)
        write_latex_tables(all_results, args.latex_table, extended_results)
        compile_latex_preview(args.latex_table, args.figures_dir)
        generate_all_figures(all_results, args.figures_dir)
        print(f"\n  LaTeX  : {args.latex_table}")
        print(f"  Figs   : {args.figures_dir}/")


if __name__ == "__main__":
    main()
