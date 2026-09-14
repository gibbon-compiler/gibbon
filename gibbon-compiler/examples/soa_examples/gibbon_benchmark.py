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

    SoA: 1 buffer for constructor tags
         + 1 buffer per scalar field
         + 0 buffers for self-recursive fields
         + 1 buffer for non-self packed fields annotated Linear
         + recursively counted buffers for non-self packed fields annotated Factored

       e.g.  data Tree = Node Int Tree Tree | Leaf Int
             with Tree annotated Linear
             → tags:1  Node.Int:1  Leaf.Int:1
             → soa_total_buffers = 3
             (self-recursive Tree fields add no extra buffers)

       e.g.  data ListA = ConsA Int ListA | NilA
             data List  = Cons Int ListA List | Nil
             with ListA annotated Linear, List annotated Factored
             → tags:1  Cons.Int:1  Cons.ListA:1
             → soa_total_buffers = 3
             (the self-recursive List field adds no new buffer)

  Per-pass buffer access:
    dead_fields = adt_fields - uses         (adt_fields and uses both include recursive)
    dead_ratio  = dead_fields / adt_fields

    soa_total_buffers is known from the parsed ADT definition and SoA layout
    annotations and shown in the summary table. Per-pass SoA buffer usage is
    NOT computed: uses= counts total fields (recursive + non-recursive) and
    the field-layout split within a pass is not available without further
    annotation.

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

import os, re, sys, json, time, shutil, argparse, statistics, subprocess, textwrap, datetime, math, signal
import hashlib
import platform
try:
    import resource
except ImportError:
    resource = None
import multiprocessing
import fnmatch
import difflib
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Dict, List, Optional, Tuple

HAS_PLOT_LIBS = True
try:
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    import matplotlib.patches as mpatches
    import numpy as np
except ModuleNotFoundError:
    HAS_PLOT_LIBS = False

REPO_ROOT = Path(__file__).resolve().parents[3]

# ---------------------------------------------------------------------------
# Default program list
# ---------------------------------------------------------------------------
DEFAULT_PROGRAMS = [
    "Compiler.hs", "DBQuery.hs", "DecisionTree.hs", "DecisionTreeClassify.hs",
    "DomTree.hs",
    "KDTree.hs", "LinearListReduction.hs", "reduceNestedList.hs",
    "List.hs", "MonoTree.hs",
    "ObjectGraph.hs",
    "OctTree_sumMass.hs", "OctTree_sumEnergy.hs",
    "OctTree_countActive.hs", "OctTree_countParticles.hs",
    "OctTree_barnesHutPotential.hs", "OctTree_fmmPotential.hs",
    "OctTree_scaleEnergy.hs", "OctTree_clearFlags.hs",
    # PiecewiseFunctions ships as one executable per timed pass (see
    # PROGRAM_MERGE_GROUPS); the tables fold these eight back into a single
    # "PiecewiseFunctions" row/table.
    "PiecewiseFunctions_norm2Estimate.hs",
    "PiecewiseFunctions_truncateTolViolations.hs",
    "PiecewiseFunctions_compressMass.hs",
    "PiecewiseFunctions_autorefineMaxLevel.hs",
    "PiecewiseFunctions_pmapCutHistogram.hs",
    "PiecewiseFunctions_lbDeuxLoadProxy.hs",
    "PiecewiseFunctions_addConstPW.hs",
    "PiecewiseFunctions_diffPW.hs",
    "TernaryTree.hs", "Trie.hs", "ColorOctree.hs"
]

# The four-width add1Tree correctness-generation family. Deliberately NOT
# part of DEFAULT_PROGRAMS -- these are opt-in via --add1tree-widths (the
# same "narrow opt-in flag" pattern as --benchmark-ghc/--benchmark-mlton
# below), not unconditionally included in every default run. This family
# performs no timing; the constant and its collection/table plumbing exist
# so a future full-mode invocation can request all four programs and emit
# the width table without special manual post-processing.
ADD1TREE_WIDTH_PROGRAMS = [
    "Add1TreeInt8.hs", "Add1TreeInt16.hs", "Add1TreeInt32.hs", "Add1TreeInt64.hs",
]

class ProgramSelectionError(ValueError):
    """Raised by resolve_program_selection for an unusable --programs /
    --exclude-programs combination (an unknown name, or an exclusion set
    that leaves nothing to run)."""


def normalize_program_name(name: str) -> str:
    """Canonicalize a program name to its `Foo.hs` basename, so the command
    line accepts `Trie`, `Trie.hs` and `programs/AOS/Trie.hs` alike."""
    stem = Path(name).name
    return stem if stem.endswith(".hs") else stem + ".hs"


def resolve_program_selection(selected: Optional[List[str]],
                              excluded: Optional[List[str]],
                              default_programs: Optional[List[str]] = None,
                              programs_dir: Optional[Path] = None) -> List[str]:
    """The program list a run actually benchmarks.

    --programs picks the candidate set (default: DEFAULT_PROGRAMS);
    --exclude-programs then subtracts from whatever that set is, which is
    what lets a full evaluation skip a benchmark that is broken, too slow,
    or otherwise not wanted for this campaign without having to retype the
    other 21 names. Both accept the loose spellings normalize_program_name
    handles.

    Each exclusion is a shell-style glob matched case-insensitively against
    the whole candidate name (fnmatch: `*`, `?`, `[...]`), so a family comes
    out in one entry rather than name by name. Note that the octree family
    is spelled two ways -- OctTree_*.hs is Oct+Tree, ColorOctree.hs is
    Color+Octree -- so `OctTree*` leaves ColorOctree.hs behind; all nine
    take either two patterns (`OctTree* ColorOctree.hs`) or one that spans
    both spellings (`*oct*ree*`). Matching is anchored to the full name, not
    a substring search, which is what keeps a literal `List.hs` from also
    taking LinearListReduction.hs and reduceNestedList.hs; a literal name
    has no wildcards and so still matches only itself.

    An exclusion that matches NOTHING in the candidate set is an ERROR, not
    a silent no-op: a typo (or a pattern the shell already expanded) would
    otherwise leave the unwanted benchmark in a multi-hour run, and the
    mistake would only surface in the results. Excluding everything is
    likewise an error rather than a no-op run.

    A --programs entry naming a program with NO source file is likewise an
    error, when `programs_dir` is supplied so existence can be checked. It was
    not, and that cost a real multi-hour run: `--programs Add1Tree8.hs` (the
    actual name is Add1TreeInt8.hs) was accepted, every configuration failed
    "source not found", and the run produced a report of nothing but failures
    and a PDF with no per-program tables at all -- the mistake only visible
    after the fact. An unmatched --exclude-programs pattern was already an
    error for exactly this reason; a misspelled --programs entry is the same
    mistake and now fails the same way, with near-miss suggestions."""
    candidates = [normalize_program_name(p)
                  for p in (selected if selected
                            else (default_programs if default_programs is not None
                                  else DEFAULT_PROGRAMS))]
    if selected and programs_dir is not None:
        missing = [c for c in candidates
                   if not _program_source_exists(programs_dir, c)]
        if missing:
            known = _known_program_names(programs_dir)
            hints = []
            for m in missing:
                close = difflib.get_close_matches(m, known, n=3, cutoff=0.6)
                hints.append("%s%s" % (repr(m),
                                       " (did you mean %s?)"
                                       % " or ".join(repr(c) for c in close)
                                       if close else ""))
            raise ProgramSelectionError(
                "--programs names %s, which has no source under %s/AOS or "
                "%s/SOA. Nothing would be benchmarked for it."
                % (" and ".join(hints), programs_dir, programs_dir))
    patterns = [normalize_program_name(p) for p in (excluded or [])]
    dropset: set = set()
    unmatched: List[str] = []
    for pat in patterns:
        # fnmatch.fnmatch() would normcase via the platform, which is a
        # no-op on POSIX -- lowercase both sides explicitly instead.
        hits = [c for c in candidates
                if fnmatch.fnmatchcase(c.lower(), pat.lower())]
        if not hits:
            unmatched.append(pat)
        dropset.update(hits)
    if unmatched:
        raise ProgramSelectionError(
            "--exclude-programs entry %s matched no program in the list for "
            "this run (%s). Available: %s"
            % (" and ".join(repr(p) for p in unmatched),
               "from --programs" if selected else "DEFAULT_PROGRAMS",
               ", ".join(candidates)))
    kept = [p for p in candidates if p not in dropset]
    if not kept:
        raise ProgramSelectionError(
            "--exclude-programs excluded every program in the run; nothing left "
            "to benchmark.")
    return kept


def _program_source_exists(programs_dir: Path, program: str) -> bool:
    """Does this program have a source in EITHER layout?

    Either is enough: a program present only as AoS or only as SoA is a
    partial-coverage case the tables already render, whereas a name present in
    neither cannot produce a single measurement.
    """
    d = Path(programs_dir)
    return (d / "AOS" / program).exists() or (d / "SOA" / program).exists()


def _known_program_names(programs_dir: Path) -> List[str]:
    """Every program name that could legitimately be asked for, for
    near-miss suggestions on a misspelled --programs entry."""
    d = Path(programs_dir)
    names = set(DEFAULT_PROGRAMS) | set(PLDI_EXTRA_PROGRAMS)
    for layout in ("AOS", "SOA"):
        sub = d / layout
        if sub.is_dir():
            names.update(f.name for f in sub.glob("*.hs"))
    return sorted(names)


# Per-program compile overrides for benchmarks that need non-default flags.
#
# No override may weaken the campaign-wide --no-ran policy for a curated
# program: `--no-ran` is a correctness/provenance requirement, not a
# per-program tuning knob, and reduceNestedList.hs in particular is
# independently driver-QUALIFIED under --no-ran (see
# benchmark_qualification.md), so no entry here should ever need to disable
# it. `_validate_no_ran_overrides` below runs at every benchmark invocation
# and raises loudly if any entry here (or in any override table) ever
# weakens `use_no_ran` for a curated/default program -- see that function's
# docstring.
PROGRAM_COMPILE_OVERRIDES: Dict[str, Dict[str, Dict]] = {}


# Programs measured with random-access nodes ENABLED, by explicit exception to
# the campaign-wide --no-ran policy.
#
# The policy exists because a result compiled with RAN silently enabled is not
# admissible evidence for the timing campaign.  The operative word is
# SILENTLY: an exception is admissible when it is named, justified, and
# reported as such, which is what this table and 'ran_caption_note' provide.
# Everything not listed here still gets --no-ran, and
# '_validate_no_ran_overrides' still rejects any attempt to disable it by
# other means.
#
# Each value states why the exception is sound FOR THAT PROGRAM. Adding an
# entry requires re-qualifying the program under RAN against its oracle --
# the existing qualification was established under --no-ran and does not
# carry over on its own.
RAN_ENABLED_PROGRAMS: Dict[str, str] = {
    "DecisionTreeClassify.hs":
        "classify follows a single root-to-leaf path. Without random-access "
        "nodes, descending to a right child must first walk the entire left "
        "subtree, so the benchmark measured subtree-skipping rather than "
        "classification: _traverse_DTree was 90.7% of cycles under AoS and "
        "93.7% under SoA, and the AoS/SoA ratio it reported (1.52x) was an "
        "artifact of that walk -- with RAN the two layouts are within 1.03x. "
        "Re-qualified under RAN: AoS and SoA, each with and without RAN, all "
        "four produce the oracle's '#(1907500 -210000) at the driver's own "
        "--size-param 0.",
}


def program_uses_no_ran(program: str, use_ran: bool = False) -> bool:
    """Should this program be compiled with --no-ran?

    Yes for everything except the explicitly re-qualified exceptions in
    'RAN_ENABLED_PROGRAMS', and no for any run that asked for RAN globally.
    """
    if use_ran:
        return False
    return normalize_program_name(program) not in RAN_ENABLED_PROGRAMS


def ran_caption_note(program: str) -> str:
    """The sentence a table must carry when a program was measured with RAN.

    The --no-ran policy permits an exception only if the result is labelled
    RAN-enabled wherever it is reported; this is that label.
    """
    if normalize_program_name(program) not in RAN_ENABLED_PROGRAMS:
        return ""
    return ("\\textbf{Measured with random-access nodes enabled} "
            "(no \\texttt{--no-ran}), unlike every other benchmark in this "
            "campaign: without them this program measures subtree-skipping "
            "rather than the traversal it names. See "
            "\\texttt{RAN\\_ENABLED\\_PROGRAMS} for the justification and "
            "its re-qualification against the oracle. ")


def _validate_no_ran_overrides(overrides: Dict[str, Dict[str, Dict]] = PROGRAM_COMPILE_OVERRIDES) -> None:
    """Fail loudly if ANY program/variant entry in a compile-override
    table tries to weaken the campaign-wide `--no-ran` policy.

    `--no-ran` is a correctness/provenance requirement, not a per-program
    tuning knob: RAN bugs and RAN performance are explicitly deferred (see
    BUGS.md), so a curated/default benchmark result compiled with RAN
    silently enabled is not admissible evidence for the timing campaign,
    no matter how it got there. This validator is the single place that
    enforces that -- called from `benchmark_program`/`main` before any
    override is consulted, so a future override entry that sets
    `use_no_ran: False` (or omits the key while trying to disable it some
    other way) is rejected at the source, not discovered later by staring
    at a suspiciously large speedup.
    """
    violations = []
    for prog, variants in overrides.items():
        for variant, opts in variants.items():
            if opts.get("use_no_ran") is False and prog not in RAN_ENABLED_PROGRAMS:
                violations.append("%s[%s]: use_no_ran=False" % (prog, variant))
    if violations:
        raise RuntimeError(
            "VW-36 policy violation: a PROGRAM_COMPILE_OVERRIDES entry weakens "
            "the campaign-wide --no-ran requirement for a curated/default "
            "program. RAN bugs and RAN performance are deferred; no override "
            "may silently disable --no-ran. Offending entries:\n  " +
            "\n  ".join(violations) +
            "\nIf a program genuinely needs a RAN-enabled measurement, use "
            "--use-ran explicitly for that single invocation and label the "
            "result as RAN-enabled in every table/report -- never bake it "
            "into the default campaign path. A program that genuinely needs "
            "RAN for every run belongs in RAN_ENABLED_PROGRAMS, which "
            "requires re-qualifying it under RAN and makes every table say "
            "so; it is not the same thing as an unannounced override.")


# Defense in depth: validate at import time too, so the violation is caught
# by merely loading this module (e.g. from a test or a REPL), not only by
# reaching benchmark_program()'s own call.
_validate_no_ran_overrides()

# ---------------------------------------------------------------------------
# Benchmark-driver C arithmetic mode policy
#
# The driver's own default is `unsafe` (native C operators, no
# `-fwrapv`) -- distinct from Gibbon the COMPILER's own default, which stays
# `portable` (see Gibbon.Common.defaultConfig). Every Gibbon compile the
# driver issues must pass `--c-arithmetic=<mode>` EXPLICITLY; the driver must
# never rely on Gibbon's own default, so a curated benchmark's arithmetic
# mode is always the one this file's caller asked for, not whatever Gibbon
# ships with next.
# ---------------------------------------------------------------------------
C_ARITH_MODES = ("portable", "wrapv", "unsafe")
DEFAULT_C_ARITH_MODE = "unsafe"

# SIMD instruction set every configuration in a comparison is compiled for --
# BOTH Gibbon's own vectorizer (which picks its register width from it) and the
# C compiler's auto-vectorizer (which gets the matching -m flag).
#
# avx2 rather than sse2 because that is what this machine is: pinning it to the
# baseline would report numbers for hardware nobody is running.  It is pinned
# EXPLICITLY, and identically for every configuration, because Gibbon's own
# default depends on whether --opt-vectorization was given -- so leaving it
# implicit would compile the Gibbon-vectorized column for a 256-bit target and
# everything it is compared against for the x86-64 baseline.
#
# Note `native` is deliberately NOT the default: on a machine with AVX-512 it
# would let the C compiler's auto-vectorizer go wider than Gibbon's vectorizer
# can (there is no 512-bit helper set), which is the same asymmetry again.
DEFAULT_SIMD_ISA = "avx2"
SIMD_ISA_CHOICES = ("sse2", "sse4.1", "avx2", "native")


# Routine per-item chatter (paths, mtimes, per-compile status) is suppressed
# while the pinned progress display is showing, because a two-line bar is not
# readable next to a fast-scrolling log. Warnings, failures and qualification
# problems are NOT routed through this -- they use plain print() and scroll
# above the bar as usual, so nothing diagnostic is ever hidden.
#
# --verbose restores the full output and turns the bar off, which is the mode
# to use when investigating one specific compile.
_VERBOSE = True
_PROGRESS = None


def set_verbosity(verbose: bool) -> None:
    global _VERBOSE
    _VERBOSE = bool(verbose)


def vprint(*args, **kwargs) -> None:
    """print() for routine progress chatter; silent unless --verbose."""
    if _VERBOSE:
        print(*args, **kwargs)


def set_progress(display) -> None:
    global _PROGRESS
    _PROGRESS = display


def progress():
    """The active display, or a no-op stand-in."""
    if _PROGRESS is not None:
        return _PROGRESS
    import bench_progress
    return bench_progress.NullProgress()


def _parse_cpu_list(text: str) -> List[int]:
    """Parse a Linux CPU list such as "0-15" or "0,2,4-7"."""
    out: List[int] = []
    for part in (text or "").strip().split(","):
        part = part.strip()
        if not part:
            continue
        if "-" in part:
            lo, _, hi = part.partition("-")
            try:
                out.extend(range(int(lo), int(hi) + 1))
            except ValueError:
                continue
        else:
            try:
                out.append(int(part))
            except ValueError:
                continue
    return out


def reserve_pin_cpu(pin_cpu: Optional[int]) -> bool:
    """Keep the DRIVER off the core reserved for measurement.

    Pinning the benchmark to a core does not reserve it: the driver, its
    compile subprocesses and the progress ticker are all still schedulable
    there, so the measurement competes with the tool measuring it. Restricting
    this process to every core EXCEPT the pinned one fixes that, and children
    inherit the restriction -- so compiles stay off it too.

    The timed run itself is launched through `taskset -c <pin>`, which
    explicitly widens that child's affinity back to the reserved core.
    Verified: a plain child inherits the exclusion, while a taskset child
    lands on CPU <pin> alone.

    Returns True if the reservation was applied.
    """
    if pin_cpu is None or not hasattr(os, "sched_setaffinity"):
        return False
    try:
        allowed = set(os.sched_getaffinity(0))
    except OSError:
        return False
    rest = allowed - {pin_cpu}
    if not rest:
        # A single-CPU machine (or an already-restricted cpuset): reserving
        # would leave the driver nowhere to run.
        return False
    try:
        os.sched_setaffinity(0, rest)
        return True
    except OSError:
        return False


def default_pin_cpu() -> Optional[int]:
    """A performance core to pin timed runs to, or None if pinning is
    impossible.

    Timed runs are pinned because an unpinned number is not comparable
    run-to-run on a HYBRID machine. On this project's i7-12700K the kernel
    may schedule a run on a P-core or on a much slower E-core, or migrate it
    mid-measurement, and `perf` reports the two core types as separate
    `cpu_core/` and `cpu_atom/` counter sets -- a run that straddles both
    yields counts that belong to neither.

    Intel hybrid parts publish the P-core list at
    /sys/devices/cpu_core/cpus; a non-hybrid machine has no such file and
    every core is equivalent, so CPU 0 is fine there. CPU 0 is avoided when
    there is a choice because it typically carries the bulk of interrupt
    handling.
    """
    if not shutil.which("taskset"):
        return None
    try:
        cpus = _parse_cpu_list(Path("/sys/devices/cpu_core/cpus").read_text())
    except OSError:
        cpus = []
    if not cpus:
        return 0
    # Skip CPU 0 AND its SMT siblings. On this project's 12700K, CPU 1 is the
    # second hyperthread of CPU 0's physical core, so pinning there would
    # share execution resources with the core that handles most interrupts --
    # the noise this pinning exists to remove.
    avoid = set()
    try:
        avoid = set(_parse_cpu_list(
            Path("/sys/devices/system/cpu/cpu0/topology/thread_siblings_list").read_text()))
    except OSError:
        avoid = {0}
    avoid.add(0)
    for c in cpus:
        if c not in avoid:
            return c
    return cpus[0]

# The SIMD target the CURRENT report was compiled for, named in table captions
# so a reader can tell which hardware the numbers describe -- and, more to the
# point, that every column describes the SAME hardware.  Run-scoped rather than
# threaded through each table writer: one report is one ISA by construction,
# since the driver passes a single --simd-isa to every compile.
_REPORT_SIMD_ISA = DEFAULT_SIMD_ISA


def set_report_simd_isa(isa: str) -> None:
    """Record the ISA this report's tables were compiled for."""
    global _REPORT_SIMD_ISA
    _REPORT_SIMD_ISA = isa


# Whether every compile in THIS run passes --reclaim-iterate-regions.
#
# Gibbon's `iterate` loop rewinds to its output region's first chunk and
# re-grows it each iteration, stranding the previous iteration's chunk chain:
# memory grows by one whole output value per iteration (929 MB/iteration for a
# 100M-element list, i.e. an OOM kill at --iterate 101).  The compiler flag is
# opt-in, so this is too.
#
# Run-scoped rather than threaded through every config dict, and consumed
# inside `build_gibbon_command` -- the single point every compile passes
# through.  Threading it through the ~20 config dictionaries instead would let
# one of them silently miss the flag, which is exactly the failure this must
# not have: a campaign where some columns reclaim and others do not is not
# comparable.
RECLAIM_ITERATE_REGIONS = False


def set_reclaim_iterate_regions(enabled: bool) -> None:
    """Turn region reclamation on for every compile in this run."""
    global RECLAIM_ITERATE_REGIONS
    RECLAIM_ITERATE_REGIONS = bool(enabled)


def reclaim_caption_note() -> str:
    """One clause for table captions when reclamation is on.

    Worth naming in the report: it changes runtime memory behaviour and, at
    large outputs, the measured times too -- the un-fixed loop makes the kernel
    supply fresh zeroed pages for memory it leaked, and that cost disappears.
    """
    if not RECLAIM_ITERATE_REGIONS:
        return ""
    return ("Every configuration was compiled with "
            "\\texttt{--reclaim-iterate-regions}, so the per-iteration region "
            "chunks are freed rather than stranded; peak memory is flat in the "
            "iteration count instead of linear. ")


def no_gcc_vec_caption_note() -> str:
    """One sentence for the two integer-width table captions.

    Both tables compile EVERY column with the C compiler's auto-vectorizer
    off, so the only vectorization they can show is Gibbon's own.  Saying so
    matters because the alternative reading -- that these are ordinary builds
    -- would make the absolute times look unaccountably slow next to the
    per-program tables, which do leave the C vectorizer on."""
    return ("Every column is compiled with the C compiler's auto-vectorizer "
            "disabled (\\texttt{--no-gcc-vectorize}, which suppresses "
            "basic-block/SLP vectorization as well as loop vectorization), so "
            "the SIMD column isolates Gibbon's own vectorizer rather than the "
            "backend's; absolute times are correspondingly higher than a "
            "default build. ")


def simd_isa_caption_note() -> str:
    """One sentence for a table caption, naming the shared SIMD target.

    This exists because the comparison is only meaningful if every column was
    compiled for the same instruction set, and that fact is invisible in the
    numbers themselves.
    """
    detail = {
        "sse2": "128-bit SSE2, the x86-64 baseline (no \\texttt{-m} flag)",
        "avx2": "256-bit AVX2 (\\texttt{-mavx2})",
        "native": "\\texttt{-march=native} (256-bit registers for Gibbon's own vectorizer)",
    }.get(_REPORT_SIMD_ISA, _REPORT_SIMD_ISA)
    return ("Every configuration was compiled for the same SIMD target, " + detail
            + "; Gibbon's vectorizer and the C compiler's auto-vectorizer both "
              "target it, so the columns are like-for-like. ")


def _validate_c_arith_mode(mode: str) -> str:
    """Reject anything but the three Gibbon-recognized modes before it ever
    reaches an argv list. Defense in depth against a typo or a future caller
    passing an arbitrary string straight through to `--c-arithmetic=`."""
    if mode not in C_ARITH_MODES:
        raise ValueError(
            f"invalid --c-arithmetic mode {mode!r}; must be one of "
            f"{', '.join(C_ARITH_MODES)}")
    return mode


def check_arithmetic_mode_consistency(records: List[Dict]) -> Optional[str]:
    """Given a list of serialized result records (each with an `arith_mode`
    key), return an error string if more than one distinct mode is present,
    else None. A single report must never silently mix artifacts compiled
    under different arithmetic-mode policies -- reports from different
    arithmetic modes must not be silently merged or compared as if they used
    the same configuration."""
    modes = {r.get("arith_mode") for r in records if r and r.get("arith_mode") is not None}
    if len(modes) > 1:
        return ("incompatible arithmetic modes in one report: " +
                ", ".join(sorted(modes)))
    return None


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
        self.exec_wall_time           = 0.0   # full executable runtime for this run (seconds)
        self.exec_time_per_iter       = 0.0   # full executable runtime normalized by --iterations
        self.compile_success          = False
        self.run_success              = False
        # Exit status of the run, kept so a stack-exhaustion crash can be
        # told apart from any other run failure.
        self.run_returncode: Optional[int] = None
        # When this variant's timed run finished, so a single measurement
        # can be attributed to a moment rather than only to the campaign.
        self.run_finished_at: Optional[str] = None
        self.error_message: Optional[str] = None
        self.adt_fields: Optional[int]    = None
        self.adt_info:   Optional[Dict]   = None   # from parse_adt_buffers
        self.papi_file: Optional[str]     = None
        self.papi_counters: List[str]     = []
        self.papi_regions_total: int      = 0
        self.papi_regions_used: int       = 0
        # The one place a numeric sink may ask "is this trustworthy?".
        # Populated by `qualify_variant` for every variant of every program
        # in full benchmark mode -- see `bench_provenance.verified_result`.
        self.qualification: Optional["prov.QualificationStatus"] = None
        # Per-artifact arithmetic-mode/no-RAN provenance, set from the
        # actual compile options used for THIS result -- not a
        # global assumption, so a mixed-mode report is mechanically detectable
        # (see `check_arithmetic_mode_consistency`).
        self.arith_mode: Optional[str] = None
        self.use_no_ran: Optional[bool] = None

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


def _strip_wrapping_parens(text: str) -> str:
    s = text.strip()
    while s.startswith("(") and s.endswith(")"):
        depth = 0
        wraps = True
        for i, ch in enumerate(s):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and i != len(s) - 1:
                    wraps = False
                    break
        if not wraps or depth != 0:
            break
        s = s[1:-1].strip()
    return s


def _extract_type_ctor(type_expr: str) -> Optional[str]:
    """
    Extract the outer type constructor from a simple Haskell type expression.
    Examples:
      Int -> Int
      ListA -> ListA
      (Maybe Int) -> Maybe
    """
    s = _strip_wrapping_parens(type_expr)
    m = re.match(r'([A-Z][A-Za-z0-9_\']*)\b', s)
    return m.group(1) if m else None


def _parse_type_annots(content: str) -> Dict[str, str]:
    """
    Parse type layout annotations of the form:
      {-# ANN type Foo "Linear" #-}
      {-# ANN type Foo "Factored" #-}
    """
    ann_re = re.compile(
        r'\{-#\s*ANN\s+type\s+([A-Z][A-Za-z0-9_\']*)\s+"(Linear|Factored)"\s*#-\}',
        re.IGNORECASE,
    )
    layouts: Dict[str, str] = {}
    for m in ann_re.finditer(content):
        layouts[m.group(1)] = m.group(2).lower()
    return layouts


def parse_adt_buffers(content: str, search_root: Optional[Path] = None) -> Optional[Dict]:
    """
    Parse all Haskell data declarations in *content* and compute buffer layout.

    SoA buffer counting rules:
      • 1 buffer for all constructor tags.
      • 1 buffer per primitive/scalar field slot.
      • 0 extra buffers for self-recursive fields.
      • 1 buffer per NON-self packed field slot whose type is annotated "Linear".
      • For NON-self packed field slots whose type is annotated "Factored",
        count that nested type recursively using the same rules.

      Examples:
        data Tree = Node Int Tree Tree | Leaf Int
        {-# ANN type Tree "Linear" #-}
          → 1(tags) + 1(Node.Int) + 1(Leaf.Int) = 3 SoA buffers

        data ListA = ConsA Int ListA | NilA
        data List = Cons Int ListA List | Nil
        {-# ANN type ListA "Linear" #-}
        {-# ANN type List "Factored" #-}
          → 1(tags) + 1(Int slot) + 1(linear ListA field) = 3 SoA buffers
            (the self-recursive List field adds no new buffer)

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
    or None if no data declarations found (including imported modules if a
    search_root is provided).
    """
    type_layouts = _parse_type_annots(content)

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
    if not starts and search_root is not None:
        import_re = re.compile(r'^\s*import\s+([A-Z][A-Za-z0-9_\.]*)', re.MULTILINE)
        for imp in import_re.findall(content):
            mod_path = search_root / (imp.replace('.', '/') + ".hs")
            if not mod_path.exists():
                continue
            try:
                imported = mod_path.read_text(encoding="utf-8", errors="ignore")
            except Exception:
                continue
            found = parse_adt_buffers(imported, None)
            if found:
                return found
        return None
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
            # Tokens after constructor name are field types.
            fields = tokens[1:]
            field_ctors = [_extract_type_ctor(t) for t in fields]
            recursive = [t for t in field_ctors if t == type_name]
            ctor_list.append({
                "name":              ctor_name,
                "field_count":       len(fields),
                "field_types":       fields,
                "field_ctors":       field_ctors,
                "recursive_count":   len(recursive),
            })

        if not ctor_list:
            continue

        parsed_adts.append({
            "type_name":           type_name,
            "constructors":        ctor_list,
            "aos_buffers":         1,
        })

    if not parsed_adts:
        return None

    all_type_names = {a["type_name"] for a in parsed_adts}

    adt_map = {a["type_name"]: a for a in parsed_adts}
    memo_total_buffers: Dict[str, int] = {}

    def _buffer_cost(owner_type: str, field_ctor: Optional[str]) -> int:
        # Scalars / primitive slots always get one buffer.
        if field_ctor is None:
            return 1
        # Self-recursive fields do not allocate an additional buffer.
        if field_ctor == owner_type:
            return 0
        # User-defined packed fields: linear => one buffer, factored => recurse.
        is_user_adt = (field_ctor in adt_map) or (field_ctor in type_layouts)
        if is_user_adt:
            field_layout = type_layouts.get(field_ctor, "linear")
            if field_layout == "factored":
                return _buffers_for_type(field_ctor)
            return 1
        # Primitive / scalar slots.
        return 1

    def _buffers_for_type(type_name: str) -> int:
        if type_name in memo_total_buffers:
            return memo_total_buffers[type_name]
        adt = adt_map.get(type_name)
        if adt is None:
            return 1
        total = 1  # constructor/tag buffer
        for ctor in adt["constructors"]:
            for fctor in ctor["field_ctors"]:
                total += _buffer_cost(type_name, fctor)
        memo_total_buffers[type_name] = total
        return total

    # Compute SoA layout stats after all type names are known, so nested ADT
    # fields can be counted recursively when their layout is Factored.
    for adt in parsed_adts:
        type_name = adt["type_name"]
        adt_layout = type_layouts.get(type_name, "linear")
        total_fields = 0
        scalar_fields = 0
        linear_packed_fields = 0
        factored_packed_fields = 0
        recursive_fields = 0
        direct_field_entries = 0

        for ctor in adt["constructors"]:
            ctor_entry_count = 0
            ctor_recursive_count = 0
            for fctor in ctor["field_ctors"]:
                total_fields += 1
                if fctor == type_name:
                    recursive_fields += 1
                    ctor_recursive_count += 1
                    continue
                direct_field_entries += 1
                ctor_entry_count += 1
                is_user_adt = (fctor in adt_map) or (fctor in type_layouts)
                if is_user_adt:
                    field_layout = type_layouts.get(fctor, "linear")
                    if field_layout == "factored":
                        factored_packed_fields += 1
                    else:
                        linear_packed_fields += 1
                else:
                    scalar_fields += 1
            ctor["buffer_field_count"] = ctor_entry_count
            ctor["inline_field_count"] = 0
            ctor["recursive_count"] = ctor_recursive_count

        soa_total_buffers = _buffers_for_type(type_name)
        expanded_nested_buffers = max(0, (soa_total_buffers - 1) - direct_field_entries)

        adt["layout"] = adt_layout
        adt["total_field_slots"] = total_fields
        adt["buffer_field_slots"] = soa_total_buffers - 1
        adt["direct_field_entry_slots"] = direct_field_entries
        adt["expanded_nested_buffer_slots"] = expanded_nested_buffers
        adt["scalar_field_slots"] = scalar_fields
        adt["linear_packed_field_slots"] = linear_packed_fields
        adt["factored_packed_field_slots"] = factored_packed_fields
        adt["recursive_field_slots"] = recursive_fields
        # Back-compat for existing report/JSON consumers.
        adt["nonrec_field_slots"] = direct_field_entries
        adt["inline_field_slots"] = 0
        adt["primitive_field_slots"] = scalar_fields
        adt["factored_field_slots"] = factored_packed_fields
        adt["soa_total_buffers"] = soa_total_buffers

    # Select target ADT
    if type_hint:
        match = [a for a in parsed_adts if a["type_name"] == type_hint]
        if match:
            return match[0]

    # Heuristic: pick the type with the most field slots (likely the main ADT)
    return max(parsed_adts, key=lambda a: a["total_field_slots"])


ATTR_RE = re.compile(r'(\w+)\s*=\s*(\d+)')


def parse_pass_attrs(blob: Optional[str]) -> Dict[str, int]:
    """Parse the trailing ``, key=N, key=N`` list of a pass annotation.

    Both the source scan and the exe-output scan feed this the same text, so a
    new key only has to be understood here.  Unknown keys are kept in the dict
    and simply ignored by callers that do not care about them.
    """
    if not blob:
        return {}
    return {k.lower(): int(v) for k, v in ATTR_RE.findall(blob)}


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

    # Match:  printsym (quote "Running pass Name (fold[, key=N]...): ")
    # Group 1 = name, Group 2 = type keyword, Group 3 = the trailing
    # comma-separated key=value list (optional), parsed by parse_pass_attrs().
    # Recognised keys: uses=N (field-usage count) and ilp=N (independent
    # dependence chains in the pass body -- see the intensity table in the
    # layout-version report).  Unknown keys are ignored, so the annotation can
    # grow without breaking older programs.
    pass_re  = re.compile(
        r'printsym\s*\(\s*quote\s*"Running pass\s+([^("]+?)\s*'
        r'\(\s*([^,)]+?)\s*((?:,\s*\w+\s*=\s*\d+)*)\s*\)\s*:',
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
                    "adt_fields_annot": None,
                    "adt_info":   None,   # from parse_adt_buffers
                    "adt_info_source": None,
                    "pass_types": {},
                    "pass_uses":  {},
                    "pass_shared": {},
                    "pass_ilp":   {},
                }
            try:
                content = src.read_text(encoding="utf-8", errors="ignore")
            except Exception as e:
                print(f"  ✗ {src.name}: {e}")
                continue

            # ADT fields annotation
            m = adt_re.search(content)
            if m and result[prog]["adt_fields_annot"] is None:
                result[prog]["adt_fields_annot"] = int(m.group(1))

            # Parse ADT structure. Prefer SOA source because Factored/Linear
            # annotations determine how many SoA buffers a packed field needs.
            adt_info = parse_adt_buffers(content, search_root=src.parent)
            if adt_info and (vdir == "SOA" or result[prog]["adt_info"] is None):
                result[prog]["adt_info"] = adt_info
                result[prog]["adt_info_source"] = vdir

            # Per-pass annotations
            found = 0
            for pm in pass_re.finditer(content):
                raw_name  = pm.group(1).strip()
                raw_type  = pm.group(2).strip().lower()
                attrs     = parse_pass_attrs(pm.group(3))
                ptype = ("fold"    if "fold" in raw_type
                         else ("map" if "map"  in raw_type else "unknown"))
                uses  = attrs.get("uses")
                ilp   = attrs.get("ilp")
                shared = attrs.get("shared")

                for variant in _name_variants(raw_name):
                    result[prog]["pass_types"][variant] = ptype
                    if uses is not None:
                        result[prog]["pass_uses"][variant] = uses
                    if ilp is not None:
                        result[prog].setdefault("pass_ilp", {})[variant] = ilp
                    if shared is not None:
                        result[prog].setdefault("pass_shared", {})[variant] = shared

                found += 1
                if vdir == "AOS":
                    uses_str = f", uses={uses}" if uses is not None else " (no uses annotation)"
                    vprint(f"  ✓ {prog}: '{raw_name}' → {ptype}{uses_str}")

            if found == 0 and vdir == "AOS":
                print(f"  ⚠  {prog}: no pass annotations found")

    for prog in sorted(result.keys()):
        entry = result[prog]
        ann = entry.get("adt_fields_annot")
        adt_info = entry.get("adt_info")
        if ann is not None:
            vprint(f"  ✓ {prog}: @BENCH adt_fields={ann}")
        if adt_info:
            parsed_fields = adt_info["total_field_slots"]
            entry["adt_fields"] = parsed_fields
            src_variant = entry.get("adt_info_source") or "AOS"
            print(
                f"  ✓ {prog}: ADT '{adt_info['type_name']}' from {src_variant} "
                f"(layout={adt_info.get('layout', 'linear')}) "
                f"→ AoS=1 buf, SoA={adt_info['soa_total_buffers']} bufs "
                f"({adt_info['direct_field_entry_slots']} non-self field entries, "
                f"{adt_info['expanded_nested_buffer_slots']} recursively expanded nested buffers, "
                f"{adt_info['recursive_field_slots']} self-recursive field slots skipped, "
                f"{len(adt_info['constructors'])} constructor(s))"
            )
            if ann is not None and ann != parsed_fields:
                print(
                    f"  ⚠  {prog}: @BENCH adt_fields={ann} disagrees with parsed "
                    f"ADT field count {parsed_fields}; using parsed value"
                )
        else:
            entry["adt_fields"] = ann
            print(f"  ⚠  {prog}: could not parse ADT definition for buffer count")

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


def lookup_pass_ilp(exe_pass_name: str, src_data: Dict) -> Optional[int]:
    """Independent dependence chains in a pass body, from an ``ilp=N``
    annotation.  Only the arithmetic-intensity programs declare it; everything
    else returns None and renders as ``--``."""
    for v in _name_variants(exe_pass_name):
        if v in src_data.get("pass_ilp", {}):
            return src_data["pass_ilp"][v]
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
    cur_ilp:  Optional[int] = None
    # `shared=N`: for a MAP pass, how many scalar fields the pass leaves
    # unmodified. A map copies every field to the output region, so "used"
    # is vacuously all of them and says nothing; what distinguishes maps is
    # which fields are merely COPIED, since those are what selective buffer
    # sharing can share instead of rewriting.
    cur_shared: Optional[int] = None
    cur_times: List[float]  = []

    # Match:  Running pass Name (fold[, key=N]...):
    pass_re = re.compile(
        r'Running\s+pass\s+([^(:\n]+?)\s*'
        r'(?:\(\s*([^,)]+?)\s*((?:,\s*\w+\s*=\s*\d+)*)\s*\))?\s*:',
        re.IGNORECASE,
    )
    # Match:  ITER TIMES: [0.052013, 0.052099, ...]
    iter_times_re = re.compile(
        r'ITER\s+TIMES\s*:\s*\[([^\]]+)\]',
        re.IGNORECASE,
    )

    def _commit():
        if current is not None and cur_times:
            passes[current] = _stats(cur_times, cur_type, cur_uses, cur_ilp,
                                     cur_shared)

    for line in raw.splitlines():
        s = line.strip()

        # ── New pass header ──────────────────────────────────────────────────
        m = pass_re.match(s)
        if m:
            _commit()
            current  = m.group(1).strip()
            hint     = (m.group(2) or "").strip().lower()
            attrs    = parse_pass_attrs(m.group(3))
            cur_type = ("fold" if "fold" in hint
                        else ("map" if "map" in hint else "unknown"))
            cur_uses = attrs.get("uses")
            cur_ilp  = attrs.get("ilp")
            cur_shared = attrs.get("shared")
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



_T_CRIT_975 = {
    1: 12.706, 2: 4.303, 3: 3.182, 4: 2.776, 5: 2.571,
    6: 2.447, 7: 2.365, 8: 2.306, 9: 2.262, 10: 2.228,
    11: 2.201, 12: 2.179, 13: 2.160, 14: 2.145, 15: 2.131,
    16: 2.120, 17: 2.110, 18: 2.101, 19: 2.093, 20: 2.086,
    21: 2.080, 22: 2.074, 23: 2.069, 24: 2.064, 25: 2.060,
    26: 2.056, 27: 2.052, 28: 2.048, 29: 2.045, 30: 2.042,
}


def _t_crit_975(n: int) -> Optional[float]:
    """Two-sided 95% Student-t critical value for n samples."""
    if n < 2:
        return None
    df = n - 1
    if df in _T_CRIT_975:
        return _T_CRIT_975[df]
    # Normal approximation is fine once df is moderately large.
    return 1.96


def _ci95_from_stderr(mean: float, stderr: float, n: int) -> Tuple[Optional[float], Optional[float], Optional[float], Optional[float]]:
    tcrit = _t_crit_975(n)
    if tcrit is None:
        return None, None, None, None
    half = tcrit * stderr
    pct = (100.0 * half / mean) if mean != 0 else None
    return half, mean - half, mean + half, pct


def fmt_ci95(ci: Optional[float]) -> str:
    if ci is None:
        return "--"
    if ci < 1e-3:
        return f"{ci:.6f}s"
    return f"{ci:.5f}s"


def _stats(times: List[float], pass_type: str = "unknown",
           uses: Optional[int] = None, ilp: Optional[int] = None,
           shared: Optional[int] = None) -> Dict:
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
    ci95, ci95_low, ci95_high, ci95_pct = _ci95_from_stderr(mean, stderr, n)
    return {
        "iter_times":  times,
        "median_time": med,
        "mean_time":   mean,
        "min_time":    mn,
        "max_time":    mx,
        "stdev":       sd,
        "stderr":      stderr,
        "ci95_abs":    ci95,
        "ci95_low":    ci95_low,
        "ci95_high":   ci95_high,
        "ci95_pct":    ci95_pct,
        "n":           n,
        "pass_type":   pass_type,
        "ilp":         ilp,
        "uses":        uses,
        "shared":      shared,
    }


_PAPI_AVAIL_COUNTERS_CACHE: Optional[List[str]] = None
_PAPI_SELECTED_EVENTS: List[str] = []
_PAPI_COUNTER_ORDER: List[str] = []


def _to_int_maybe(val) -> Optional[int]:
    try:
        return int(str(val))
    except Exception:
        return None


def _counter_stats(values: List[float]) -> Dict:
    n = len(values)
    med = statistics.median(values)
    mean = statistics.mean(values)
    mn = min(values)
    mx = max(values)
    sd = statistics.stdev(values) if n > 1 else 0.0
    stderr = sd / (n ** 0.5) if n > 1 else 0.0
    ci95, ci95_low, ci95_high, ci95_pct = _ci95_from_stderr(mean, stderr, n)
    return {
        "median": med,
        "mean": mean,
        "min": mn,
        "max": mx,
        "stdev": sd,
        "stderr": stderr,
        "ci95_abs": ci95,
        "ci95_low": ci95_low,
        "ci95_high": ci95_high,
        "ci95_pct": ci95_pct,
        "n": n,
    }


def _discover_papi_avail_counters() -> List[str]:
    """
    Best-effort fallback when JSON event_definitions is absent.
    Returns names like PAPI_TOT_CYC parsed from `papi_avail`.
    """
    global _PAPI_AVAIL_COUNTERS_CACHE
    if _PAPI_AVAIL_COUNTERS_CACHE is not None:
        return _PAPI_AVAIL_COUNTERS_CACHE
    try:
        r = subprocess.run(["papi_avail"], capture_output=True, text=True, timeout=5)
        if r.returncode != 0:
            _PAPI_AVAIL_COUNTERS_CACHE = []
            return _PAPI_AVAIL_COUNTERS_CACHE
        found = sorted(set(re.findall(r"\bPAPI_[A-Z0-9_]+\b", r.stdout)))
        _PAPI_AVAIL_COUNTERS_CACHE = found
        return found
    except Exception:
        _PAPI_AVAIL_COUNTERS_CACHE = []
        return []


def select_preferred_papi_events() -> List[str]:
    """
    Pick the counters we care about, using papi_avail when possible:
      - total cycles
      - L1/L2/L3 cache misses
    """
    avail = set(_discover_papi_avail_counters())

    # If papi_avail failed, still provide sensible defaults.
    use_avail = len(avail) > 0

    def pick(cands: List[str]) -> Optional[str]:
        if use_avail:
            for c in cands:
                if c in avail:
                    return c
            return None
        return cands[0] if cands else None

    selected: List[str] = []
    for grp in [
        ["PAPI_TOT_CYC"],
        ["PAPI_L1_TCM", "PAPI_L1_DCM", "PAPI_L1_ICM"],
        ["PAPI_L2_TCM", "PAPI_L2_DCM", "PAPI_L2_ICM"],
        ["PAPI_L3_TCM", "PAPI_L3_DCM", "PAPI_L3_ICM"],
    ]:
        ev = pick(grp)
        if ev and ev not in selected:
            selected.append(ev)
    return selected


def select_preferred_papi_native_metrics() -> List[str]:
    """
    Logical native metrics emitted by --enable-papi-native output lines.
    """
    return [
        "CPU_CYCLES",
        "INSTRUCTIONS",
        "L1D_LOAD_MISSES",
        "L1I_LOAD_MISSES",
        "L2D_MISSES",
        "L2I_MISSES",
        "LLC_LOAD_MISSES",
    ]


def attach_papi_native_to_passes(result: BenchmarkResult, raw_stdout: str) -> None:
    """
    Parse native PAPI lines from executable stdout and attach per-pass summaries.
    Supports both:
      1) per-iteration immediate prints
      2) bulk-per-pass prints after the loop (current compiler behavior)
    Expected line format:
      PAPI_NATIVE <METRIC>[<EVENT_NAME>]=<VALUE>
    """
    # Same annotation grammar as parse_passes(); see parse_pass_attrs().  This
    # only needs the pass NAME, but it must still tolerate the full trailing
    # key=value list or it silently stops matching annotated passes.
    pass_re = re.compile(
        r'Running\s+pass\s+([^(:\n]+?)\s*'
        r'(?:\(\s*([^,)]+?)\s*((?:,\s*\w+\s*=\s*\d+)*)\s*\))?\s*:',
        re.IGNORECASE,
    )
    native_re = re.compile(
        r'^PAPI_NATIVE\s+([A-Za-z0-9_]+)\[([^\]]+)\]=(-?\d+(?:\.\d+)?)$'
    )

    current: Optional[str] = None
    metric_values_by_pass: Dict[str, Dict[str, List[float]]] = {}
    metric_event_name: Dict[str, str] = {}

    # Collect by pass block (Running pass ... End) so ordering inside a pass
    # does not matter (e.g. native metrics printed after the full loop).
    for line in raw_stdout.splitlines():
        s = line.strip()
        m = pass_re.match(s)
        if m:
            current = m.group(1).strip()
            metric_values_by_pass.setdefault(current, {})
            continue
        if s == "End":
            current = None
            continue
        m2 = native_re.match(s)
        if m2 and current is not None:
            metric = m2.group(1)
            event_name = m2.group(2)
            try:
                value = float(m2.group(3))
            except ValueError:
                continue
            metric_event_name.setdefault(metric, event_name)
            metric_values_by_pass.setdefault(current, {}).setdefault(metric, []).append(value)

    if not metric_values_by_pass:
        return

    metric_order = _PAPI_COUNTER_ORDER or sorted(metric_event_name.keys())
    result.papi_counters = [m for m in metric_order if any(m in by_m for by_m in metric_values_by_pass.values())]

    for pname, pdata in result.passes.items():
        by_metric = metric_values_by_pass.get(pname, {})
        if not by_metric:
            continue
        pdata.setdefault("papi_counters", {})
        sample_count = max((len(vs) for vs in by_metric.values()), default=0)
        pdata["papi_sample_count"] = sample_count
        pdata["papi_native_events"] = {}
        for metric, vals in by_metric.items():
            if vals:
                pdata["papi_counters"][metric] = _counter_stats(vals)
                pdata["papi_native_events"][metric] = metric_event_name.get(metric, "")
        expected_n = pdata.get("n")
        if isinstance(expected_n, int) and expected_n > 0 and sample_count not in (0, expected_n):
            print(f"           Native PAPI warning: pass '{pname}' has {sample_count} samples, expected {expected_n}")


def _papi_json_files(search_root: Path) -> List[Path]:
    files: List[Path] = []
    files.extend(search_root.glob("papi_hl_output/rank_*.json"))
    files.extend(search_root.glob("papi_hl_output-*/rank_*.json"))
    return files


def _snapshot_papi_json_files(search_root: Path) -> Dict[str, float]:
    snap: Dict[str, float] = {}
    for fp in _papi_json_files(search_root):
        try:
            snap[str(fp.resolve())] = fp.stat().st_mtime
        except OSError:
            pass
    return snap


def _pick_latest_papi_json(search_root: Path, before: Dict[str, float],
                           started_at: float) -> Optional[Path]:
    changed: List[Tuple[float, Path]] = []
    for fp in _papi_json_files(search_root):
        try:
            mtime = fp.stat().st_mtime
        except OSError:
            continue
        key = str(fp.resolve())
        prev = before.get(key)
        if prev is None or mtime > prev + 1e-9:
            changed.append((mtime, fp))

    # Fallback: newest file updated around this run window.
    if not changed:
        for fp in _papi_json_files(search_root):
            try:
                mtime = fp.stat().st_mtime
            except OSError:
                continue
            if mtime >= started_at - 2.0:
                changed.append((mtime, fp))

    if not changed:
        return None
    changed.sort(key=lambda x: x[0])
    return changed[-1][1]


def _load_papi_regions(papi_json: Path) -> Tuple[List[str], List[Dict]]:
    """
    Parse PAPI high-level output JSON.
    Returns (counter_names, regions_sorted_chronologically).
    """
    with open(papi_json, "r", encoding="utf-8") as f:
        blob = json.load(f)

    # Prefer counters that are explicitly reported by PAPI.
    counters = sorted([
        c for c in (blob.get("event_definitions") or {}).keys()
        if str(c).startswith("PAPI_")
    ])

    regions: List[Dict] = []
    threads = blob.get("threads") or {}
    if isinstance(threads, dict):
        for tid, tdata in threads.items():
            if not isinstance(tdata, dict):
                continue
            regs = tdata.get("regions") or {}
            if not isinstance(regs, dict):
                continue
            for rid, rdata in regs.items():
                if not isinstance(rdata, dict):
                    continue
                rec = dict(rdata)
                rec["_thread_id"] = tid
                rec["_region_id"] = rid
                regions.append(rec)

    # If event_definitions isn't populated, infer counters from region payloads.
    if not counters:
        inferred = set()
        for reg in regions:
            for k in reg.keys():
                if isinstance(k, str) and k.startswith("PAPI_"):
                    inferred.add(k)
        counters = sorted(inferred)

    # Final fallback: probe system PAPI event names.
    if not counters:
        avail = set(_discover_papi_avail_counters())
        inferred = set()
        for reg in regions:
            for k in reg.keys():
                if isinstance(k, str) and k in avail:
                    inferred.add(k)
        counters = sorted(inferred)

    # Respect selected events when the runner has explicitly set PAPI_EVENTS.
    if _PAPI_SELECTED_EVENTS:
        selected = set(_PAPI_SELECTED_EVENTS)
        counters = [c for c in _PAPI_SELECTED_EVENTS if c in selected and c in counters]

    def _region_key(reg: Dict) -> Tuple[int, int, int]:
        tid = _to_int_maybe(reg.get("_thread_id"))
        name_num = _to_int_maybe(reg.get("name"))
        rid = _to_int_maybe(reg.get("_region_id"))
        return (
            tid if tid is not None else 0,
            name_num if name_num is not None else (rid if rid is not None else 10**18),
            rid if rid is not None else 10**18,
        )

    regions.sort(key=_region_key)
    return counters, regions


def attach_papi_to_passes(result: BenchmarkResult, iterations: int,
                          search_root: Path, before_snapshot: Dict[str, float],
                          run_started_at: float) -> None:
    """
    Attach PAPI counter summaries to each pass in chronological chunks:
      first `iterations` regions -> pass 1,
      next `iterations` regions -> pass 2, ...
    """
    papi_json = _pick_latest_papi_json(search_root, before_snapshot, run_started_at)
    if papi_json is None:
        return

    try:
        counters, regions = _load_papi_regions(papi_json)
    except Exception as e:
        print(f"           PAPI parse warning: {papi_json} ({e})")
        return

    result.papi_file = str(papi_json)
    result.papi_counters = counters
    result.papi_regions_total = len(regions)

    if not counters or not regions or not result.passes:
        return

    samples_per_pass = max(1, iterations)
    pass_names = list(result.passes.keys())  # preserve source/runtime order
    expected_regions = len(pass_names) * samples_per_pass
    used_regions = min(len(regions), expected_regions)
    result.papi_regions_used = used_regions

    for i, pname in enumerate(pass_names):
        start = i * samples_per_pass
        end = start + samples_per_pass
        chunk = regions[start:end]
        if not chunk:
            break
        pdata = result.passes.get(pname, {})
        pdata["papi_sample_count"] = len(chunk)
        pdata["papi_counters"] = {}
        for counter in counters:
            vals: List[float] = []
            for reg in chunk:
                raw = reg.get(counter)
                if raw is None:
                    continue
                try:
                    vals.append(float(raw))
                except (TypeError, ValueError):
                    continue
            if vals:
                pdata["papi_counters"][counter] = _counter_stats(vals)

    if len(regions) < expected_regions:
        print(f"           PAPI warning: expected {expected_regions} region entries "
              f"({len(pass_names)} passes x {samples_per_pass}) but found {len(regions)}")


def apply_source_classification(result: BenchmarkResult,
                                 src_data: Dict) -> None:
    """
    For each pass, fill in any missing pass_type and uses from source scan.
    Attaches adt_fields and adt_info to the result object.
    Computes derived fields: dead_ratio.

    Semantics:
      adt_fields  = TOTAL fields in the selected benchmark ADT, including
                    recursive ones. Prefer the parsed ADT definition; fall
                    back to @BENCH adt_fields=N only if parsing fails.
      uses        = TOTAL fields the pass accesses (recursive + non-recursive).
                    This is what uses=N in printsym counts.
      dead_ratio  = (adt_fields - uses) / adt_fields
                    Consistent: both counts include recursive fields.

    NOTE: per-pass SoA buffer usage cannot be computed here because uses= counts
    total fields accessed (recursive + non-recursive) and we would need field-
    layout information per pass to know how many distinct SoA buffers are
    touched. soa_total_buffers is still valid at the ADT level and is derived
    from the parsed SoA layout annotations.
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
        if pdata.get("ilp") is None:
            pdata["ilp"] = lookup_pass_ilp(pname, src_data)
        if pdata.get("shared") is None:
            pdata["shared"] = (src_data.get("pass_shared") or {}).get(pname)

        uses = pdata.get("uses")

        # Shareable-field metric, for MAP passes only.
        #
        # A map copies every field into the output region, so "fields used" is
        # vacuously all of them and distinguishes nothing. What separates one
        # map from another is how many scalar fields it leaves UNMODIFIED,
        # because those are exactly the buffers selective buffer sharing can
        # share rather than rewrite.
        #
        # The denominator is scalar_field_slots, NOT adt_fields: a recursive
        # child field is structurally rebuilt and is not a buffer that could
        # be shared, so counting it would understate the ratio against a
        # denominator no configuration can ever reach.
        shared = pdata.get("shared")
        slots = (result.adt_info or {}).get("scalar_field_slots")
        pdata["shared_slots"] = slots
        if shared is not None and slots:
            pdata["shared_ratio"] = shared / slots
        else:
            pdata["shared_ratio"] = None

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
_LEGACY_UNANCHORED_GC_RE_REMOVED = re.compile(
    r"itertime:|ITER TIMES:|ITERS:|SIZE:|BATCHTIME:|SELFTIMED:|"
    r"PAPI_NATIVE\s+|"
    r"Running pass|Running program|^End$|INFO_TABLE:|Initialized footer at|"
    r"GibOldgenChunkFooter|GibRegionInfo|refcount:.*outset:|"
    r"Total allocated bytes:|Total copied bytes:|ALLOC_TOTAL:|GC_TOTAL:",
    re.IGNORECASE,
)

def clean_output(raw: str) -> Optional[str]:
    """Semantic (program) output only.

    Delegates to bench_provenance.semantic_output, whose rules match a WHOLE
    line.  The previous implementation used an unanchored substring search, so
    a program value line containing "SIZE:", "SELFTIMED:", "ITER TIMES:" or
    "Running pass" was discarded in full and the driver compared empty text."""
    lines = []
    for line in prov.semantic_lines(raw):
        s = line.strip()
        if not s:
            continue
        # Normalize SML tuple output "#(" to Gibbon-style "'#(".
        if s.startswith("#("):
            s = "'" + s
        # Normalize SML negative literals (~123) to -123.
        s = re.sub(r'~(\d)', r'-\1', s)
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


def outputs_match_all(results: List[Optional[BenchmarkResult]]) -> bool:
    """
    Return True iff all provided results:
      1) exist
      2) ran successfully
      3) have non-empty cleaned output
      4) have identical cleaned output text
    """
    rs = [r for r in results if r is not None]
    if not rs:
        return False
    if any(not r.run_success for r in rs):
        return False
    outs: List[str] = []
    for r in rs:
        if not r.output:
            return False
        outs.append(r.output.strip())
    return len(set(outs)) == 1


def analyze_outputs_by_variant(named_results: Dict[str, Optional[BenchmarkResult]]) -> Dict:
    """
    Analyze outputs across variants while excluding runtime failures from matching.
    Returns:
      {
        "comparable_count": int,   # successful variants with non-empty output
        "is_match": Optional[bool],# None if <2 comparable variants
        "groups": List[Tuple[List[str], str]],  # (variants, output_text)
        "failed": List[Tuple[str, str]],        # (variant, error_message)
      }
    """
    comparable: List[Tuple[str, str]] = []
    failed: List[Tuple[str, str]] = []
    for vname, res in named_results.items():
        if res is None:
            continue
        if not res.run_success:
            failed.append((vname, res.error_message or "execution failed"))
            continue
        if res.output:
            comparable.append((vname, res.output.strip()))

    out_map: Dict[str, List[str]] = {}
    for vname, out in comparable:
        out_map.setdefault(out, []).append(vname)

    groups = [(sorted(vs), out) for out, vs in out_map.items()]
    groups.sort(key=lambda x: ",".join(x[0]))

    comparable_count = len(comparable)
    if comparable_count < 2:
        is_match = None
    else:
        is_match = (len(out_map) == 1)

    return {
        "comparable_count": comparable_count,
        "is_match": is_match,
        "groups": groups,
        "failed": sorted(failed, key=lambda x: x[0]),
    }

# ---------------------------------------------------------------------------
# Smart recompilation check
# ---------------------------------------------------------------------------
# ---------------------------------------------------------------------------
# Compiler mtime cache (checked once per script run)
# ---------------------------------------------------------------------------
_COMPILER_CACHE: Dict[str, Tuple[Path, float]] = {}
import bench_provenance as prov

_GIBBON_EXE_CACHE: Optional[Path] = None

_GIBBON_RESOLUTION: Optional["prov.CompilerResolution"] = None

def resolve_gibbon() -> "prov.CompilerResolution":
    """THE Gibbon compiler for this run: $GIBBON_EXE, then `cabal list-bin`,
    then $PATH.  The same absolute path is used for argv[0], the build
    fingerprint, the status block and the recorded provenance -- previously the
    driver resolved here but executed the bare string "gibbon", so a
    GIBBON_EXE override could be reported while a different binary ran."""
    global _GIBBON_RESOLUTION
    if _GIBBON_RESOLUTION is None:
        _GIBBON_RESOLUTION = prov.resolve_gibbon_exe(REPO_ROOT)
    return _GIBBON_RESOLUTION


def get_gibbon_exe() -> Optional[Path]:
    """Absolute path of the resolved Gibbon compiler (see resolve_gibbon)."""
    return resolve_gibbon().path


def postprocess_sml_for_bench(sml_path: Path) -> None:
    """
    Patch gibbon-generated SML so benchmark output matches parser expectations.
    - Use printsym for Running pass/End/NEWLINE
    - Wrap pass computations with iterate to emit ITER TIMES
    - Prefix tuple output with "'#(" (matches Gibbon)
    - Use runtime sizeParam for build sizes to avoid compile-time precompute
    """
    if not sml_path.exists():
        return
    if sml_path.name == "GibbonCompat.sml":
        return
    text = sml_path.read_text()

    if sml_path.name == "Compiler.sml":
        text = text.replace("Int.toString(x__6)", "showBool(x__6)")

    # Ensure GibbonCompat is in scope for printsym/iterate/salt.
    if not text.lstrip().startswith("open GibbonCompat;"):
        text = "open GibbonCompat;\n\n" + text
    helper_block = """
open IntInf;

fun clampInf x =
  let
    val maxVal = IntInf.fromInt Int.maxInt
    val minVal = IntInf.fromInt Int.minInt
    val clamped =
      if x > maxVal then maxVal
      else if x < minVal then minVal
      else x
  in
    IntInf.toInt clamped
  end;

fun safeAdd (a, b) = clampInf (IntInf.+ (IntInf.fromInt a, IntInf.fromInt b));
fun safeSub (a, b) = clampInf (IntInf.- (IntInf.fromInt a, IntInf.fromInt b));
fun safeMul (a, b) = clampInf (IntInf.* (IntInf.fromInt a, IntInf.fromInt b));
fun safeDiv (a, b) = if b = 0 then 0 else clampInf (IntInf.div (IntInf.fromInt a, IntInf.fromInt b));

fun safeSumList xs =
  case xs of
    [] => 0
  | x::xs2 => safeAdd (x, safeSumList xs2);

fun sum8 a b c d e f g h = safeSumList [a, b, c, d, e, f, g, h];

fun safePassInt (f: unit -> int) = (f ()) handle Overflow => 0;
"""
    if "safePassInt" not in text:
        text = helper_block + "\n" + text
    safe_pass_def = "fun safePassInt (f: unit -> int) = (f ()) handle Overflow => 0;\n\n"
    if "safePassInt" not in text:
        text = text.replace("open GibbonCompat;\n\n", "open GibbonCompat;\n\n" + safe_pass_def, 1)

    # Replace prints for markers.
    text = re.sub(r'print "NEWLINE"', 'printsym "NEWLINE"', text)
    text = re.sub(r'print "(Running pass[^\"]*)"', r'printsym "\1"', text)
    text = re.sub(r'print "(Running program[^\"]*)"', r'printsym "\1"', text)
    text = re.sub(r'print "End"', 'printsym "End"', text)
    # Fix SML case pattern arrow emitted by gibbon for tuple print.
    text = re.sub(r'of\s*\(([^)]*)\)\s*->', r'of (\1) =>', text)


    # Normalize any previous salt injection to use full sizeParam.
    text = re.sub(r'\(\(GibbonCompat\.getSizeParam\(\)\s+mod\s+2\)\s+\+\s+(\d+)\)',
                  r'((GibbonCompat.getSizeParam()) + \1)', text)

    lines = text.splitlines()
    out = []
    in_main = False
    expect_pass_result = False
    replaced_size_param = False
    for i, line in enumerate(lines):
        if "val _ = (case" in line:
            in_main = True

        if in_main and "Running pass" in line:
            expect_pass_result = True

        # Replace the first sizeParam literal in main with runtime sizeParam.
        if in_main and (not replaced_size_param):
            m = re.match(r'(\s*let val\s+(fltPrm_\w+)\s*=\s*)1(\s*in\s*)', line)
            if m:
                lookahead = "\n".join(lines[i:i + 5])
                if re.search(r'\b' + re.escape(m.group(2)) + r'\b\s*\+\s*\d+', lookahead):
                    out.append(m.group(1) + "(GibbonCompat.getSizeParam())" + m.group(3))
                    replaced_size_param = True
                    continue

        # Inject runtime sizeParam into any literal top-level build in main.
        if in_main:
            m = re.search(r'(let val \w+ = \(build\w+\s+)(\d+)([^)]*\) in)', line)
            if m:
                new_line = (m.group(1) +
                            f"((GibbonCompat.getSizeParam()) + {m.group(2)})" +
                            m.group(3))
                out.append(new_line)
                continue

        # Wrap pass result with iterate.
        if in_main and expect_pass_result:
            m = re.match(r'(\s*let val\s+(\w+)\s*=\s*\()(.+)(\)\s*in\s*)', line)
            if m and "iterate" not in line:
                var = m.group(2)
                expr = m.group(3).strip()
                # Skip wrapping print/printsym wildcards; wait for actual pass result.
                if var.startswith("wildcard") or "printsym" in expr or "print " in expr:
                    # Let other normalizations run on this line.
                    pass
                else:
                    iter_expr = expr
                    if "safePassInt" not in iter_expr:
                        iter_expr = f"safePassInt (fn () => {iter_expr})"
                    out.append(m.group(1) + f"iterate (fn () => {iter_expr})" + m.group(4))
                    expect_pass_result = False
                    continue
                # fall through to append original line

        # Compiler: print bool for hasCycle in tuple output.
        if in_main and sml_path.name == "Compiler.sml":
            line = re.sub(r'print\(Int\.toString\(x__6\)\)', 'print(showBool(x__6))', line)

        # Ensure tuple-print let blocks end properly.
        line = re.sub(r'print "\)" in \(\)\);', 'print ")" in () end);', line)
        line = re.sub(r'print "\)" in \(\)\)$', 'print ")" in () end)', line)

        # Make feature vector size depend on sizeParam in main.
        if in_main:
            line = re.sub(
                r'mkFeatureVec\s+(\d+)',
                lambda m: f"mkFeatureVec ((GibbonCompat.getSizeParam()) + {m.group(1)})",
                line,
            )
            line = re.sub(
                r'classifyBatch\(([^,]*),\s*(\d+)\s*,',
                lambda m: f"classifyBatch({m.group(1)}, ((GibbonCompat.getSizeParam()) + {m.group(2)}),",
                line,
            )

        out.append(line)

    sml_path.write_text("\n".join(out) + "\n")

def ensure_mlton_sml(aos_hs: Path, mlton_sml: Path, force: bool = False) -> Tuple[bool, Optional[str]]:
    """
    Ensure MLton SML exists.
    Regenerate via gibbon if:
      1) AOS source is newer than MLTON SML, or
      2) --clean (force) is set, or
      3) MLTON SML is missing.
    Otherwise leave MLTON SML untouched.
    """
    gibbon_exe = get_gibbon_exe()
    if gibbon_exe is None:
        return False, "gibbon executable not found (set GIBBON_EXE or build gibbon)"

    need_regen = force or (not mlton_sml.exists())
    if (not need_regen) and aos_hs.exists():
        need_regen = aos_hs.stat().st_mtime > mlton_sml.stat().st_mtime
    if (not need_regen) and mlton_sml.exists():
        try:
            need_regen = gibbon_exe.stat().st_mtime > mlton_sml.stat().st_mtime
        except Exception:
            pass

    if need_regen:
        aos_sml = aos_hs.with_suffix(".sml")
        env = os.environ.copy()
        env.setdefault("GIBBONDIR", str(REPO_ROOT))
        soa_root = REPO_ROOT / "gibbon-compiler" / "examples" / "soa_examples"
        try:
            rel = aos_hs.resolve().relative_to(soa_root.resolve())
        except Exception:
            rel = aos_hs
        r = subprocess.run([str(gibbon_exe), "--hs", "--mpl", str(rel)],
                           cwd=str(soa_root),
                           capture_output=True, text=True, env=env)
        if r.returncode != 0:
            # If we already have an MLTON file, keep it and warn.
            if mlton_sml.exists():
                return True, f"gibbon --mpl failed; keeping existing {mlton_sml}"
            return False, r.stderr.strip() or "gibbon --mpl failed"

        mlton_sml.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(aos_sml, mlton_sml)
        postprocess_sml_for_bench(mlton_sml)

    return True, None

# ---------------------------------------------------------------------------
# C compiler selection
# ---------------------------------------------------------------------------
# Pinned deliberately.  GCC 15 fails to register-promote the SoA traversal's
# cursors across loop iterations, which made SoA folds run at IPC ~1.5 against
# AoS's ~4 and cost a spurious 2.7x on List.hs/sumList.  A silent toolchain
# upgrade can change SoA results by multiples, so the compiler is chosen
# explicitly and its version is recorded in every report rather than being
# whatever `gcc` happens to resolve to.
#
# A prior version of this comment additionally claimed that GCC 16 promotes
# those cursors well enough that "SoA comes out slightly FASTER than AoS".
# That claim was measured before List.hs's fields were migrated to explicit
# per-field GibInt32 codegen (under the old whole-program `--int32` macro
# trick, where the RTS's own GibInt was also 32-bit). Under the current
# explicit-width codegen it does not hold: with GCC 16.2.0, --no-ran,
# --use-mutable-cursors, List.hs's SoA sumList/sumListAcc measures SLOWER
# than AoS, by roughly 3.8x, not faster.
#
# Root cause (isolated by recompiling the current generated List.soa.c with
# ONLY the sumList/sumListAcc accumulator/return type widened from GibInt32 to
# GibInt (int64), everything else byte-identical): GCC 16's -O3 -flto inliner
# produces a materially worse loop for this specific shape -- a self-recursive
# tail-position function taking Gibbon's SoA `GibCursor x[2]` array-by-
# reference parameters (aliased/restrict-qualified sub-cursors threaded
# through the whole recursive chain) -- when the accumulator is 32-bit than
# when it is 64-bit; widening it alone restores AoS-competitive timing with no
# other change. Simplified reproducers (a plain malloc'd linked-list fold, and
# the same fold using the real branchy gib_add_i32/gib_u2s_i32 deterministic-
# wraparound helper) do NOT reproduce the gap, so this is specific to the
# interaction between GCC 16's LTO loop/tail-call heuristics and Gibbon's
# cursor-array calling convention at narrow width -- a GCC 16 code-generation-
# quality characteristic of that combination, not a Gibbon compiler defect,
# and not something to "fix" by widening List.hs's types (List.hs's Int32
# policy stays as-is; RAN performance/bugs are separately deferred).
PREFERRED_CC = "gcc-16"
SELECTED_CC: Optional[str] = None   # set by --cc; None means auto-detect


def resolve_cc(requested: Optional[str] = None) -> str:
    """Pick the C compiler Gibbon should shell out to."""
    requested = requested or SELECTED_CC
    if requested:
        return requested
    if shutil.which(PREFERRED_CC):
        return PREFERRED_CC
    return "gcc"


def cc_version(cc: str) -> str:
    """First line of `<cc> --version`, or a marker if it cannot be run."""
    try:
        out = subprocess.run([cc, "--version"], capture_output=True, text=True, timeout=20)
        first = (out.stdout or out.stderr).strip().split("\n")
        return first[0] if first and first[0] else "unknown"
    except Exception:
        return "unavailable"


def get_compiler_info(name: str = "gibbon") -> Optional[Tuple[Path, float]]:
    """
    Returns (compiler_path, mtime) for the specified compiler executable.
    Cached globally so we only look it up once per run.
    Returns None if compiler is not in PATH.
    """
    if name in _COMPILER_CACHE:
        return _COMPILER_CACHE[name]
    
    path = shutil.which(name)
    if path is None:
        return None
    
    p = Path(path).resolve()
    if not p.exists():
        return None
    
    mtime = p.stat().st_mtime
    _COMPILER_CACHE[name] = (p, mtime)
    return _COMPILER_CACHE[name]


# `needs_recompilation` was removed: it decided freshness from mtimes plus
# the compile-command string, which reused a stale executable whenever a
# source, imported module, compiler, RTS input or artifact changed with an
# unchanged or older timestamp. The content-addressed replacement is
# bench_provenance.decide_recompile; there is deliberately no second path.

# ---------------------------------------------------------------------------
# Variant-specific optimization policy
# ---------------------------------------------------------------------------
def is_soa_gibbon_variant(variant: str) -> bool:
    return variant.startswith("soa")

def effective_optimization_flags(variant: str,
                                 store_scalar_field_counts: bool,
                                 enable_loopification: bool,
                                 enable_loop_fusion: bool,
                                 enable_selective_buffer_sharing: bool,
                                 enable_vectorization: bool,
                                 auto_loopification: bool = True,
                                 defer_scalar_counts: bool = False) -> Dict[str, bool]:
    """Return the flags that should actually be passed for this variant.

    AoS flat layouts can use only flat map loopification.  Scalar-count
    footers, selective buffer sharing, and loop fusion are fully factored SoA
    mechanisms, so the harness deliberately does not pass those flags to AoS
    variants even when the user enabled them globally.

    `auto_loopification` is independent of layout (unlike the SoA-only flags
    above): it only controls whether `--auto-loopification` accompanies
    `--opt-loopification`, not whether loopification itself is attempted.
    Defaults to True so every existing caller keeps getting today's paired
    behavior; callers that know every relevant function is already annotated
    `OPT:MayVectorize` may pass False to rely on the annotation alone.
    """
    is_soa = is_soa_gibbon_variant(variant)
    counts = store_scalar_field_counts and is_soa
    return {
        "store_scalar_field_counts": counts,
        "enable_loopification": enable_loopification,
        "auto_loopification": auto_loopification,
        "enable_loop_fusion": enable_loop_fusion and is_soa,
        "enable_selective_buffer_sharing": enable_selective_buffer_sharing and is_soa,
        "enable_vectorization": enable_vectorization and is_soa,
        # Deferred delivery of the counts the footers already record; without
        # the footers there is nothing to defer, and the compiler rejects the
        # pair outright rather than treating it as a no-op.
        "defer_scalar_counts": defer_scalar_counts and counts,
    }

# ---------------------------------------------------------------------------
# Pure command construction
# ---------------------------------------------------------------------------
def build_gibbon_command(source: Path, variant: str, c_file: Path, exe: Path,
                         cc: str,
                         gibbon_exe: Optional[str] = None,
                         use_mutable_cursors: bool = True,
                         enable_papi: bool = False,
                         enable_papi_native: bool = False,
                         store_scalar_field_counts: bool = False,
                         defer_scalar_counts: bool = False,
                         enable_loopification: bool = False,
                         enable_loop_fusion: bool = False,
                         enable_selective_buffer_sharing: bool = False,
                         enable_vectorization: bool = False,
                         use_sse41: bool = False,
                         use_no_gcc_vec: bool = False,
                         use_no_ran: bool = True,
                         c_arith_mode: str = DEFAULT_C_ARITH_MODE,
                         use_no_gcc_tail_calls: bool = False,
                         auto_loopification: bool = True,
                         simd_isa: str = DEFAULT_SIMD_ISA,
                         reclaim_iterate_regions: Optional[bool] = None) -> List[str]:
    """Build the Gibbon compile command.

    Pure: no filesystem access, no subprocess, no compiler lookup.  `cc` is
    passed in rather than resolved here so tests can construct and assert on a
    command without a compiler installed.

    NOTE ON WIDTH: this function takes no width parameter, and must not grow
    one.  Integer width is declared by the source program (`Int8`/`Int16`/
    `Int32`/`Int64`; bare `Int` means `Int64`), and a mixed-width program has no
    single width a benchmark flag could select.  The removed `--int32`
    whole-program mode used to be appended here.

    `--sse4.1` and `--no-gcc-vectorize` are deliberately independent of
    `--opt-vectorization`: the first grants an ISA permission to the C
    compiler, the second suppresses the C compiler's own auto-vectorizer, and
    only the third turns on Gibbon's SIMD pass.

    `simd_isa` is ALWAYS passed explicitly, to EVERY configuration, and this is
    load-bearing for the comparison rather than a convenience.  Gibbon defaults
    `--simd-isa` to avx2 when `--opt-vectorization` is given and to sse2
    otherwise, so leaving it implicit compiles the Gibbon-vectorized column for
    a 256-bit target while every column it is compared against gets the x86-64
    baseline -- where the C compiler's own auto-vectorizer can only reach SSE2.
    Measured: the same non-vectorized program contains 0 `ymm` references
    without the flag and 528 with it.  That difference lands entirely in
    Gibbon's favour, so the flag is pinned for all configurations.

    `c_arith_mode` is ALWAYS passed explicitly as `--c-arithmetic=<mode>` --
    never omitted to fall back on Gibbon's own compiler default (`portable`).
    The driver's own default is `unsafe`; see `DEFAULT_C_ARITH_MODE`. This
    never adds `-fwrapv` or any other C flag itself -- that is Gibbon's job
    for `wrapv` mode.

    `auto_loopification=False` suppresses `--auto-loopification` while still
    passing `--opt-loopification` when `enable_loopification` is set -- for a
    caller that knows every relevant function is already annotated
    `OPT:MayVectorize`, so structural inference isn't needed. Defaults to
    True, preserving every existing caller's paired behavior unchanged.
    """
    _validate_c_arith_mode(c_arith_mode)
    # argv[0] must BE the resolved compiler, not the name "gibbon": otherwise
    # the binary we fingerprint and report is not the binary PATH executes.
    cmd = [str(gibbon_exe) if gibbon_exe else "gibbon", "--cc", cc,
           f"--c-arithmetic={c_arith_mode}"]
    if use_mutable_cursors:
        cmd.append("--use-mutable-cursors")
    if enable_papi_native:
        cmd.append("--enable-papi-native")
    if enable_papi:
        cmd.append("--enable-papi")
    if use_no_ran:
        cmd.append("--no-ran")
    if use_sse41:
        cmd.append("--sse4.1")
    cmd.append(f"--simd-isa={simd_isa}")
    if use_no_gcc_vec:
        cmd.append("--no-gcc-vectorize")
    if use_no_gcc_tail_calls:
        cmd.append("--no-gcc-tail-calls")
    # None means "whatever this run selected", which is how every caller gets
    # it without passing it; tests pass an explicit bool.  Resolved here at
    # CALL time, not as a default argument, because Python binds defaults once
    # at definition time and would freeze the value before main() sets it.
    if (RECLAIM_ITERATE_REGIONS if reclaim_iterate_regions is None
            else reclaim_iterate_regions):
        cmd.append("--reclaim-iterate-regions")
    effective_opts = effective_optimization_flags(
        variant,
        store_scalar_field_counts,
        enable_loopification,
        enable_loop_fusion,
        enable_selective_buffer_sharing,
        enable_vectorization,
        auto_loopification,
        defer_scalar_counts,
    )
    if effective_opts["store_scalar_field_counts"]:
        cmd.append("--store-scalar-field-counts")
    if effective_opts["defer_scalar_counts"]:
        cmd.append("--defer-scalar-counts")
    if effective_opts["enable_loopification"]:
        cmd.append("--opt-loopification")
        if effective_opts["auto_loopification"]:
            cmd.append("--auto-loopification")
    if effective_opts["enable_loop_fusion"]:
        cmd.append("--opt-loop-fusion")
    if effective_opts["enable_selective_buffer_sharing"]:
        cmd.append("--opt-selective-buffer-sharing")
    if effective_opts["enable_vectorization"]:
        cmd.append("--opt-vectorization")
    cmd.extend([
        "--packed", "--to-exe",
        "--cfile",   str(c_file),
        "--exefile", str(exe),
        str(source),
    ])
    return cmd


# ---------------------------------------------------------------------------
# Compile one variant  (called from thread pool)
# ---------------------------------------------------------------------------
def compile_one(source: Path, variant: str, out_dir: Path,
                force: bool, use_mutable_cursors: bool = True,
                enable_papi: bool = False,
                enable_papi_native: bool = False,
                store_scalar_field_counts: bool = False,
                enable_loopification: bool = False,
                enable_loop_fusion: bool = False,
                enable_selective_buffer_sharing: bool = False,
                enable_vectorization: bool = False,
                use_sse41: bool = False,
                use_no_gcc_vec: bool = False,
                use_no_ran: bool = True,
                c_arith_mode: str = DEFAULT_C_ARITH_MODE,
                use_no_gcc_tail_calls: bool = False,
                auto_loopification: bool = True,
                simd_isa: str = DEFAULT_SIMD_ISA,
                # Keep new parameters LAST: the parallel compile path calls
                # this positionally, so an insert anywhere else silently
                # shifts every argument after it.
                defer_scalar_counts: bool = False,
                ) -> Tuple[bool, float, Optional[str]]:
    _validate_c_arith_mode(c_arith_mode)
    source = source.resolve()
    out_dir = out_dir.resolve()
    stem   = source.stem
    exe    = out_dir / f"{stem}.{variant}.exe"
    buildinfo_file = out_dir / f"{stem}.{variant}.buildinfo.json"
    out_dir.mkdir(parents=True, exist_ok=True)

    compiler = "gibbon"
    if variant == "ghc":
        compiler = "ghc"
    elif variant == "mlton":
        compiler = "mlton"

    c_file = (out_dir / f"{stem}.{variant}.c") if compiler == "gibbon" else None

    if compiler == "ghc":
        cmd = [
            "ghc",
            "-O2",
            "-rtsopts",
            "-fno-full-laziness",
            "-fno-cse",
            "-fno-strictness",
            "-XNoImplicitPrelude",
            "-XPackageImports",
            "-i" + str(Path(__file__).resolve().parent / "programs" / "GHC"),
            f"-i{source.parent}",
            "-o", str(exe),
            str(source),
        ]
    elif compiler == "mlton":
        # MLton expects a single .sml or .mlb entry. Include GibbonCompat.
        compat = source.parent / "GibbonCompat.sml"
        mlb_file = out_dir / f"{stem}.{variant}.mlb"
        parts = ["local", "  $(SML_LIB)/basis/basis.mlb"]
        if compat.exists():
            parts.append(f"  {compat}")
        parts.append(f"  {source}")
        parts.append("in")
        parts.append("end")
        mlb_file.write_text("\n".join(parts) + "\n")
        # Use 64-bit ints to avoid overflow in larger synthetic benchmarks.
        cmd = ["mlton", "-default-type", "int64", "-output", str(exe), str(mlb_file)]
    else:
        _res = resolve_gibbon()
        if _res.path is None:
            print(f"           FAILED (gibbon executable could not be resolved)")
            return False, 0.0, "gibbon executable not found (set GIBBON_EXE or build it)"
        cmd = build_gibbon_command(
            source, variant, c_file, exe, resolve_cc(),
            gibbon_exe=str(_res.path),
            use_mutable_cursors=use_mutable_cursors,
            enable_papi=enable_papi,
            enable_papi_native=enable_papi_native,
            store_scalar_field_counts=store_scalar_field_counts,
            defer_scalar_counts=defer_scalar_counts,
            enable_loopification=enable_loopification,
            enable_loop_fusion=enable_loop_fusion,
            enable_selective_buffer_sharing=enable_selective_buffer_sharing,
            enable_vectorization=enable_vectorization,
            use_sse41=use_sse41,
            use_no_gcc_vec=use_no_gcc_vec,
            use_no_gcc_tail_calls=use_no_gcc_tail_calls,
            auto_loopification=auto_loopification,
            use_no_ran=use_no_ran,
            c_arith_mode=c_arith_mode,
            simd_isa=simd_isa,
        )
    cmd_sig = " ".join(cmd)

    # Content-addressed freshness.  mtimes are NOT consulted: a source, an
    # imported module, the compiler, the RTS, the generated C or the executable
    # can all change with an unchanged or older timestamp.
    _fp = prov.build_fingerprint(
        source, cmd,
        resolve_gibbon() if compiler == "gibbon"
            else prov.CompilerResolution(None, compiler, None),
        prov.cc_identity(resolve_cc()) if compiler == "gibbon" else {"cc": compiler},
        REPO_ROOT,
        driver_path=Path(__file__).resolve(),
        extra_roots=[source.parent],
    )
    recompile, reason = prov.decide_recompile(buildinfo_file, _fp, c_file, exe)
    if not force and not recompile:
        progress().item(f"{stem} · {variant}", "cached")
        vprint(f"  [{variant.upper()}] {stem}: skipping  ({reason})")
        vprint(f"           exe: {exe}")
        vprint(f"           src: {source}")
        return True, 0.0, None

    if force:
        reason = "forced recompile"
    
    flags_str = "mut-cursors" if use_mutable_cursors else "imm-cursors"
    flags_str += f",arith={c_arith_mode},simd-isa={simd_isa}"
    if enable_papi_native:
        flags_str += ",papi-native"
    if enable_papi:
        flags_str += ",papi"
    effective_label_opts = effective_optimization_flags(
        variant,
        store_scalar_field_counts,
        enable_loopification,
        enable_loop_fusion,
        enable_selective_buffer_sharing,
        enable_vectorization,
        auto_loopification,
    )
    if effective_label_opts["enable_loopification"]:
        flags_str += ",loopify"
        if not effective_label_opts["auto_loopification"]:
            flags_str += "(annotation-only)"
    if effective_label_opts["store_scalar_field_counts"]:
        flags_str += ",scalar-counts"
    if effective_label_opts["enable_selective_buffer_sharing"]:
        flags_str += ",selective-sharing"
    if effective_label_opts["enable_loop_fusion"]:
        flags_str += ",loop-fusion"
    if effective_label_opts["enable_vectorization"]:
        flags_str += ",vectorization"
    if use_sse41:
        flags_str += ",sse4.1"
    if use_no_gcc_vec:
        flags_str += ",no-gcc-vec"
    if use_no_gcc_tail_calls:
        flags_str += ",no-gcc-tail-calls"
    progress().item(f"{stem} · {variant}", "compiling")
    vprint(f"  [{variant.upper()} {flags_str}] {stem}: compiling  ({reason})")
    vprint(f"           src: {source}  →  {exe}")
    t0 = time.time()
    try:
        env = os.environ.copy()
        if compiler == "gibbon":
            env.setdefault("GIBBONDIR", str(REPO_ROOT))
        r = subprocess.run(cmd, capture_output=True, text=True, cwd=str(REPO_ROOT), env=env)
        elapsed = time.time() - t0
        if r.returncode == 0:
            # Written atomically, and ONLY after a successful build, so a crash
            # can never leave metadata that half-describes an executable.
            prov.write_buildinfo_atomic(
                buildinfo_file, _fp, c_file, exe, REPO_ROOT,
                extra={"compile_cmd": cmd,
                       "compile_cmd_signature": cmd_sig,
                       "source": str(source),
                       "c_file": str(c_file) if c_file else None,
                       "exe": str(exe),
                       "c_arithmetic": c_arith_mode if compiler == "gibbon" else None,
                       "use_no_ran": use_no_ran if compiler == "gibbon" else None})
            vprint(f"           ok ({elapsed:.1f}s)")
            return True, elapsed, None
        print(f"           FAILED ({elapsed:.1f}s)")
        return False, elapsed, r.stderr.strip()
    except FileNotFoundError:
        elapsed = time.time() - t0
        print(f"           FAILED ({compiler} not in PATH)")
        return False, elapsed, f"{compiler} not found"

# ---------------------------------------------------------------------------
# Parallel compilation dispatcher
# ---------------------------------------------------------------------------
def compile_parallel(tasks: List[Tuple]) -> Dict:
    if not tasks:
        return {}
    #workers = max(1, multiprocessing.cpu_count())
    # Vidush: Explicitly making this serial for now since parallel compilation is causing issues in Gibbon
    workers = 1
    # Name the sources. A bare count ("Compiling 2 file(s)") tells you nothing
    # about which benchmark is slow, which is the question being asked when a
    # campaign appears to sit still.
    _by_prog: Dict[str, List[str]] = {}
    for _t in tasks:
        _by_prog.setdefault(_t[0], []).append(_t[1])
    _named = "; ".join(f"{prog} [{', '.join(vs)}]" for prog, vs in _by_prog.items())
    print(f"\n▸ compiling {_named}  ({len(tasks)} file(s), {workers} thread(s))")
    results: Dict = {}
    with ThreadPoolExecutor(max_workers=workers) as pool:
        fmap = {
            pool.submit(compile_one, src, var, od, force, use_mut, enable_papi,
                        enable_papi_native, store_scalar_field_counts,
                        enable_loopification, enable_loop_fusion,
                        enable_selective_buffer_sharing, enable_vectorization,
                        use_sse41, use_no_gcc_vec, use_no_ran, c_arith_mode,
                        defer_scalar_counts=defer_counts): (prog, var)
            for prog, var, src, od, force, use_mut, enable_papi, enable_papi_native,
                store_scalar_field_counts, enable_loopification, enable_loop_fusion,
                enable_selective_buffer_sharing, enable_vectorization, use_sse41, use_no_gcc_vec,
                use_no_ran, c_arith_mode, defer_counts in tasks
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
def _disable_child_core_dumps() -> None:
    if resource is not None:
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


def run_exe(exe: Path, iterations: int,
            timeout: int = 600,
            dump_dir: Optional[Path] = None,
            env_override: Optional[Dict[str, str]] = None,
            use_iterate_flag: bool = True,
            size_param: int = 0,
            record_argv: Optional[List[List[str]]] = None,
            pin_cpu: Optional[int] = None,
            ) -> Tuple[bool, float, Optional[str], Optional[str], int]:
    """
    Run executable and return (success, elapsed, stdout, stderr, returncode).
    """
    if not exe.exists():
        return False, 0.0, None, "executable not found", -1
    exe_mtime = datetime.datetime.fromtimestamp(exe.stat().st_mtime).strftime(
        "%Y-%m-%d %H:%M:%S"
    )
    progress().item(exe.stem,
                    f"running x{iterations}" if use_iterate_flag and iterations > 1
                    else "running")
    vprint(f"           running: {exe}")
    if use_iterate_flag:
        run_mode = f"--iterate {iterations}"
    else:
        run_mode = "single-run (no --iterate)"
    vprint(f"           exe mtime: {exe_mtime}  |  {run_mode}")

    cmd = [str(exe)]
    # For GHC, pass RTS options to increase heap size. This should prevent OOM crashes.
    if ".ghc." in exe.name:
        cmd.extend(["+RTS", "-H4G", "-RTS"])
    # A deterministic size-param prevents the compiler from precomputing the
    # workload.  The historical default is 0 and is PRESERVED; --size-param on
    # the driver overrides it, and the effective value is always recorded.
    cmd.extend(["--size-param", str(size_param)])
    if use_iterate_flag:
        cmd.extend(["--iterate", str(iterations)])
    if record_argv is not None:
        # The PROGRAM's own argv, without the launcher prefix below: callers
        # and tests assert on the arguments the benchmark received, and
        # pinning is a property of how it was launched, not of what it ran.
        record_argv.append(list(cmd))
    # Pin AFTER recording argv. Prepending `taskset` keeps the measurement on
    # one core for its whole life, so it cannot migrate between a P-core and a
    # much slower E-core mid-run.
    if pin_cpu is not None and shutil.which("taskset"):
        cmd = ["taskset", "-c", str(pin_cpu)] + cmd
        vprint(f"           pinned to CPU {pin_cpu}")

    t0  = time.time()
    env = os.environ.copy()
    if env_override:
        env.update(env_override)
    popen_kwargs = {
        "stdout": subprocess.PIPE,
        "stderr": subprocess.PIPE,
        "text": True,
        "env": env,
    }
    if os.name == "posix":
        popen_kwargs["preexec_fn"] = _disable_child_core_dumps
        # A new session (== a new process group, this process as its
        # leader) so a timeout can kill the WHOLE group, not just this one
        # direct child -- Gibbon's own compiled executables never fork, so
        # this makes no difference for them today, but `subprocess.run`'s
        # plain timeout path only ever signals the direct child, which is a
        # latent leak for any exe that does spawn a subprocess of its own
        # -- see test_vw38_driver_boundary.py for the regression coverage.
        popen_kwargs["start_new_session"] = True
    proc = subprocess.Popen(cmd, **popen_kwargs)
    try:
        stdout, stderr = proc.communicate(timeout=timeout)
        elapsed = time.time() - t0
        if dump_dir is not None:
            dump_dir.mkdir(parents=True, exist_ok=True)
            (dump_dir / f"{exe.stem}.stdout.txt").write_text(stdout or "")
            (dump_dir / f"{exe.stem}.stderr.txt").write_text(stderr or "")

        success = (proc.returncode == 0)
        return success, elapsed, stdout, stderr, proc.returncode
    except subprocess.TimeoutExpired:
        if os.name == "posix":
            try:
                os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
            except ProcessLookupError:
                pass
        else:
            proc.kill()
        proc.communicate()
        return False, timeout, None, "timeout expired", -1
    except Exception as e:
        return False, time.time() - t0, None, str(e), -1


def benchmark_build_pass(program: str, variant: str, use_mutable_cursors: bool,
                         programs_dir: Path, out_dir: Path, iterations: int, force: bool,
                         store_scalar_field_counts: bool = False,
                         defer_scalar_counts: bool = False,
                         enable_loopification: bool = False,
                         enable_loop_fusion: bool = False,
                         enable_selective_buffer_sharing: bool = False,
                         enable_vectorization: bool = False,
                         use_sse41: bool = False,
                         use_no_gcc_vec: bool = False,
                         use_no_ran: bool = True,
                         c_arith_mode: str = DEFAULT_C_ARITH_MODE,
                         dump_raw: bool = False,
                        pin_cpu: Optional[int] = None) -> Tuple[Optional[Dict], Optional[str]]:
    """
    Benchmark build-only executable by launching it repeatedly (no --iterate).
    Returns (_stats dict tagged as pass_type='build', error_message).
    """
    if not (variant.startswith("aos") or variant.startswith("soa")):
        return None, None

    build_src_dir = "AOS_BUILD" if variant.startswith("aos") else "SOA_BUILD"
    src_dir = "AOS" if variant.startswith("aos") else "SOA"
    build_src = programs_dir / build_src_dir / program
    if not build_src.exists():
        return None, f"build-only source not found: {build_src}"

    # Build-only files may import sibling modules (e.g. OctTreeBase). Ensure
    # missing imports are available in *_BUILD by copying from AOS/SOA.
    def _ensure_build_imports(entry_src: Path, build_root: Path, variant_root: Path,
                              seen: Optional[set] = None) -> None:
        if seen is None:
            seen = set()
        if entry_src in seen or not entry_src.exists():
            return
        seen.add(entry_src)

        try:
            txt = entry_src.read_text(encoding="utf-8", errors="ignore")
        except Exception:
            return

        imp_re = re.compile(
            r'^\s*import\s+(?:qualified\s+)?([A-Z][A-Za-z0-9_\.]*)',
            re.MULTILINE
        )
        for mod in imp_re.findall(txt):
            rel = Path(*mod.split(".")).with_suffix(".hs")
            # Skip external libraries; keep only local module dependencies.
            if rel.parts and rel.parts[0] in ("Gibbon", "Prelude"):
                continue
            dst = build_root / rel
            if dst.exists():
                _ensure_build_imports(dst, build_root, variant_root, seen)
                continue
            src = variant_root / rel
            if src.exists():
                dst.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(src, dst)
                _ensure_build_imports(dst, build_root, variant_root, seen)

    _ensure_build_imports(
        build_src,
        programs_dir / build_src_dir,
        programs_dir / src_dir,
    )

    build_out_dir = out_dir / "build_only"
    ok, _ct, err = compile_one(
        build_src, variant, build_out_dir, force,
        use_mutable_cursors=use_mutable_cursors,
        enable_papi=False,
        enable_papi_native=False,
        store_scalar_field_counts=store_scalar_field_counts,
        defer_scalar_counts=defer_scalar_counts,
        enable_loopification=enable_loopification,
        enable_loop_fusion=enable_loop_fusion,
        enable_selective_buffer_sharing=enable_selective_buffer_sharing,
        enable_vectorization=enable_vectorization,
        use_sse41=use_sse41,
        use_no_gcc_vec=use_no_gcc_vec,
        use_no_ran=use_no_ran,
        c_arith_mode=c_arith_mode,
    )
    if not ok:
        return None, err or "build-only compile failed"

    exe = build_out_dir / f"{build_src.stem}.{variant}.exe"
    dump_dir = (out_dir / "raw_output") if dump_raw else None

    run_times: List[float] = []
    for i in range(iterations):
        vprint(f"           [build] run {i + 1}/{iterations}")
        ok2, rt, _stdout, stderr, returncode = run_exe(
            exe, 1, dump_dir=dump_dir, use_iterate_flag=False, pin_cpu=pin_cpu
        )
        if not ok2:
            err_txt = stderr or f"build-only execution failed (exit {returncode})"
            return None, err_txt
        run_times.append(rt)

    if not run_times:
        return None, "no build-only runtimes collected"

    return _stats(run_times, pass_type="build", uses=None), None


# ---------------------------------------------------------------------------
# Benchmark one program
# ---------------------------------------------------------------------------
def benchmark_program(prog: str, programs_dir: Path, out_dir: Path,
                      iterations: int, force: bool,
                      source_cls_all: Dict,
                      dump_raw: bool = False,
                      include_build_pass: bool = False,
                      benchmark_immutable: bool = False,
                      benchmark_baseline_gibbon: bool = False,
                      enable_papi: bool = False,
                      enable_papi_native: bool = False,
                      store_scalar_field_counts: bool = False,
                      defer_scalar_counts: bool = False,
                      enable_loopification: bool = False,
                      enable_loop_fusion: bool = False,
                      enable_selective_buffer_sharing: bool = False,
                      enable_vectorization: bool = False,
                      use_sse41: bool = False,
                      use_no_gcc_vec: bool = False,
                      use_ran: bool = False,
                      pin_cpu: Optional[int] = None,
                      benchmark_ghc: bool = False,
                      benchmark_mlton: bool = False,
                      warmup_runs: int = 1,
                      warmup_iterations: int = 1,
                      cooldown_seconds: float = 3.0,
                      allow_unverified_output: bool = False,
                      c_arith_mode: str = DEFAULT_C_ARITH_MODE,
                      ) -> Tuple[Optional[BenchmarkResult], Optional[BenchmarkResult]]:
    """
    Benchmark one program. Returns (aos_result, soa_result) for backwards compatibility.
    Calls `_validate_no_ran_overrides()` first -- an override that weakens
    --no-ran must never reach the compile step, even if a future edit
    reintroduces one.
    If benchmark_immutable=True, also compiles/runs immutable cursor variants but only
    returns the mutable cursor results. Use benchmark_program_all_variants() to get all 4.
    """
    _validate_no_ran_overrides()
    _validate_c_arith_mode(c_arith_mode)
    print(f"\n{'='*70}\nBenchmarking: {prog}\n{'='*70}")

    # Determine which variants to compile
    variants = []
    if benchmark_immutable:
        variants.extend([("aos", True), ("aos_imm", False),
                         ("soa", True), ("soa_imm", False)])
    elif benchmark_baseline_gibbon:
        variants.extend([("aos", True), ("aos_imm", False), ("soa", True)])
    else:
        variants.extend([("aos", True), ("soa", True)])

    if benchmark_ghc:
        variants.append(("ghc", False))
    if benchmark_mlton:
        variants.append(("mlton", False))

    tasks = []
    variant_compile_opts: Dict[str, Dict[str, bool]] = {}
    variant_src: Dict[str, Path] = {}
    for var, use_mut in variants:
        # By default benchmark Gibbon variants with --no-ran.  --use-ran omits
        # that flag without adding GHC/MLton comparison variants.  Keep the old
        # --benchmark-ghc behavior for compatibility: when GHC is requested, the
        # Gibbon comparison variants are also compiled with RAN enabled.
        is_gibbon_variant = var.startswith("aos") or var.startswith("soa")
        use_no_ran = not ((use_ran or benchmark_ghc) and is_gibbon_variant)
        if is_gibbon_variant and not program_uses_no_ran(prog, use_ran):
            use_no_ran = False
        override = PROGRAM_COMPILE_OVERRIDES.get(prog, {}).get(var, {})
        use_mut_eff = override.get("use_mutable_cursors", use_mut)
        use_no_ran_eff = override.get("use_no_ran", use_no_ran)
        variant_compile_opts[var] = {
            "use_mutable_cursors": use_mut_eff,
            "store_scalar_field_counts": store_scalar_field_counts,
            "defer_scalar_counts": defer_scalar_counts,
            "enable_loopification": enable_loopification,
            "enable_loop_fusion": enable_loop_fusion,
            "enable_selective_buffer_sharing": enable_selective_buffer_sharing,
            "enable_vectorization": enable_vectorization,
            "use_sse41": use_sse41,
            "use_no_gcc_vec": use_no_gcc_vec,
            "use_no_ran": use_no_ran_eff,
            "c_arith_mode": c_arith_mode,
        }
        if var == "ghc":
            src_dir = "GHC"
            src = programs_dir / src_dir / prog
        elif var == "mlton":
            src_dir = "MLTON"
            # MLton programs live in MLTON/*.sml
            src = programs_dir / src_dir / prog.replace(".hs", ".sml")
            # Generate/update SML from HiCal and postprocess into MLTON.
            aos_hs = programs_dir / "AOS" / prog
            ok, err = ensure_mlton_sml(aos_hs, src, force=force)
            if not ok:
                print(f"  Warning: MLton SML generation failed for {prog}: {err}")
        else:
            # Source is always in AOS/ or SOA/ directory, not aos_imm/soa_imm
            src_dir = "AOS" if var.startswith("aos") else "SOA"
            src = programs_dir / src_dir / prog
        variant_src[var] = src
        if src.exists():
            tasks.append((prog, var, src, out_dir, force, use_mut_eff, enable_papi,
                          enable_papi_native, store_scalar_field_counts,
                          enable_loopification, enable_loop_fusion,
                          enable_selective_buffer_sharing, enable_vectorization,
                          use_sse41, use_no_gcc_vec, use_no_ran_eff, c_arith_mode,
                          defer_scalar_counts))
        else:
            print(f"  Warning: {src} not found")

    compile_results = compile_parallel(tasks)
    results: Dict[str, BenchmarkResult] = {}
    src_data = source_cls_all.get(prog, {"adt_fields": None, "adt_info": None,
                                          "pass_types": {}, "pass_uses": {}})

    dump_dir = (out_dir / "raw_output") if dump_raw else None

    for idx, (var, use_mut) in enumerate(variants):
        res = BenchmarkResult(prog, var)
        res.adt_fields = src_data.get("adt_fields")
        key = (prog, var)
        compile_opts = variant_compile_opts.get(var, {
            "use_mutable_cursors": use_mut,
            "store_scalar_field_counts": store_scalar_field_counts,
            "defer_scalar_counts": defer_scalar_counts,
            "enable_loopification": enable_loopification,
            "enable_loop_fusion": enable_loop_fusion,
            "enable_selective_buffer_sharing": enable_selective_buffer_sharing,
            "enable_vectorization": enable_vectorization,
            "use_sse41": use_sse41,
            "use_no_gcc_vec": use_no_gcc_vec,
            "use_no_ran": True,
            "c_arith_mode": c_arith_mode,
        })
        res.arith_mode = compile_opts.get("c_arith_mode")
        res.use_no_ran = compile_opts.get("use_no_ran")

        variant_source = variant_src.get(var)
        if key not in compile_results:
            res.compile_success = False
            res.error_message   = "source not found"
            res.qualification = qualify_variant(
                prog, var, variant_source, False, res.error_message, False, None, None,
                allow_unverified=allow_unverified_output)
            results[var]        = res
            continue

        ok, ct, err = compile_results[key]
        res.compile_time = ct
        if not ok:
            res.compile_success = False
            res.error_message   = err or "compile failed"
            res.qualification = qualify_variant(
                prog, var, variant_source, False, res.error_message, False, None, None,
                allow_unverified=allow_unverified_output)
            results[var]        = res
            continue

        res.compile_success = True
        stem = prog.replace(".hs", "")
        exe  = out_dir / f"{stem}.{var}.exe"

        progress().item(f"{prog.replace('.hs','')} · {var}", "running")
        # Compiling and running are the two phases whose cost differs by
        # orders of magnitude, so the transition is announced rather than
        # left to be inferred from a stalled display.
        # Mirror the actual loop below: warmup is `warmup_runs` separate runs
        # of `warmup_iterations` each, THEN the timed run. Stating it wrongly
        # would misrepresent where the time goes, which is the whole reason
        # for printing it.
        _wr, _wi = max(0, warmup_runs), max(1, warmup_iterations)
        _plan = f"{iterations} timed iteration(s)"
        if _wr:
            _plan = f"{_wr} warmup run(s) x {_wi} iters, then " + _plan
        print(f"\u25b8 running   {prog} [{var}]  ({_plan})")
        papi_env = ({"PAPI_EVENTS": ",".join(_PAPI_SELECTED_EVENTS)}
                    if (enable_papi and _PAPI_SELECTED_EVENTS) else None)

        warmup_failed = False
        warmup_runs_eff = max(0, warmup_runs)
        warmup_iters_eff = max(1, warmup_iterations)
        for w in range(warmup_runs_eff):
            vprint(f"           warmup {w + 1}/{warmup_runs_eff}  (--iterate {warmup_iters_eff})")
            progress().item(f"{prog.replace('.hs','')} · {var}",
                            f"warmup x{warmup_iters_eff}")
            ok_w, _rt_w, _stdout_w, stderr_w, rc_w = run_exe(
                exe, warmup_iters_eff, dump_dir=None, env_override=papi_env,
                pin_cpu=pin_cpu
            )
            if not ok_w:
                res.compile_success = True
                res.run_success = False
                res.error_message = stderr_w or f"warmup failed (exit {rc_w})"
                res.qualification = qualify_variant(
                    prog, var, variant_source, True, None, False, res.error_message, None,
                    allow_unverified=allow_unverified_output)
                print(f"           FAILED during warmup (exit {rc_w})")
                warmup_failed = True
                break
        if warmup_failed:
            results[var] = res
            continue

        papi_before = _snapshot_papi_json_files(Path.cwd()) if enable_papi else {}
        run_started_at = time.time()
        ok2, rt, stdout, stderr, returncode = run_exe(
            exe, iterations, dump_dir=dump_dir, env_override=papi_env,
            pin_cpu=pin_cpu
        )
        # Full executable end-to-end time for this run.
        res.exec_wall_time = rt
        res.exec_time_per_iter = (rt / iterations) if iterations > 0 else rt
        if not ok2:
            # Detect OOM from both exit code and stderr content
            # Common OOM exit codes: 137 (killed by OOM), 139 (segfault), -11 (SIGSEGV)
            oom_exit_codes = {137, 139, -11, 134}  # 134 = SIGABRT from stack overflow
            err_text = (stderr or stdout or "").lower()
            
            is_oom = (returncode in oom_exit_codes) or any(keyword in err_text for keyword in [
                "stack overflow", "out of memory", "cannot allocate",
                "segmentation fault", "stack space overflow",
                "memory exhausted", "heap exhausted", "bad_alloc", "killed"
            ])
            
            # Debug output - show what we got
            vprint(f"           exit code: {returncode}")
            if err_text:
                stderr_preview = err_text[:200].replace('\n', ' ')
                vprint(f"           stderr: {stderr_preview}...")
            
            if is_oom:
                print(f"           FAILED (out of memory)")
                res.error_message = "out of memory"
            else:
                print(f"           FAILED (exit non-zero)")
                res.error_message = stderr or "execution failed"
            res.run_success = False
            res.qualification = qualify_variant(
                prog, var, variant_source, True, None, False, res.error_message, None,
                allow_unverified=allow_unverified_output)
        else:
            res.run_success = True
            is_gibbon_variant = var.startswith("aos") or var.startswith("soa")
            c_file = (out_dir / f"{stem}.{var}.c") if is_gibbon_variant else None
            res.qualification = qualify_variant(
                prog, var, variant_source, True, None, True, None, stdout,
                allow_unverified=allow_unverified_output,
                c_file=c_file, expect_vectorization=enable_vectorization)
            vprint(f"           qualification: {res.qualification.label}"
                  f"  (oracle={res.qualification.oracle_status}: {res.qualification.oracle_detail})"
                  f"  verified={res.qualification.verified}")
            if stdout:
                res.output  = clean_output(stdout)
                res.passes  = parse_passes(stdout)
                apply_source_classification(res, src_data)
                if enable_papi:
                    attach_papi_to_passes(
                        res,
                        iterations=iterations,
                        search_root=Path.cwd(),
                        before_snapshot=papi_before,
                        run_started_at=run_started_at,
                    )
                if enable_papi_native:
                    attach_papi_native_to_passes(res, stdout)
                    if not getattr(res, "papi_counters", None):
                        if stdout and "PAPI_NATIVE" in stdout:
                            print("           Native PAPI warning: PAPI_NATIVE lines found but could not attach to passes")
                        else:
                            print("           Native PAPI warning: no PAPI_NATIVE lines found in stdout")

                if include_build_pass:
                    build_stats, build_err = benchmark_build_pass(
                        program=prog,
                        variant=var,
                        use_mutable_cursors=compile_opts["use_mutable_cursors"],
                        programs_dir=programs_dir,
                        out_dir=out_dir,
                        iterations=iterations,
                        force=force,
                        store_scalar_field_counts=compile_opts["store_scalar_field_counts"],
                        defer_scalar_counts=compile_opts.get("defer_scalar_counts", False),
                        enable_loopification=compile_opts["enable_loopification"],
                        enable_loop_fusion=compile_opts["enable_loop_fusion"],
                        enable_selective_buffer_sharing=compile_opts["enable_selective_buffer_sharing"],
                        enable_vectorization=compile_opts["enable_vectorization"],
                        use_sse41=compile_opts.get("use_sse41", False),
                        use_no_gcc_vec=compile_opts.get("use_no_gcc_vec", False),
                        pin_cpu=pin_cpu,
                        use_no_ran=compile_opts["use_no_ran"],
                        c_arith_mode=compile_opts.get("c_arith_mode", DEFAULT_C_ARITH_MODE),
                        dump_raw=dump_raw,
                    )
                    if build_stats is not None:
                        merged_passes = {"build": build_stats}
                        merged_passes.update(res.passes)
                        res.passes = merged_passes
                        print(
                            "           [B] build: "
                            f"median={build_stats['median_time']:.4f}s  "
                            f"mean={build_stats['mean_time']:.4f}s  "
                            f"95%CI=±{fmt_ci95(build_stats.get('ci95_abs'))}  "
                            f"min={build_stats['min_time']:.4f}s  "
                            f"max={build_stats['max_time']:.4f}s  "
                            f"n={build_stats['n']}"
                        )
                    elif build_err:
                        print(f"           Build benchmark warning: {build_err}")

                # ── Print per-pass timing digest ──────────────────────────
                total_t = total_pass_time(res) or 0.0
                def _fmt_time(t: float) -> str:
                    # Avoid rounding microsecond-scale passes to 0.0000.
                    if t < 1e-3:
                        return f"{t:.6f}s"
                    return f"{t:.4f}s"

                vprint(f"           wall={rt:.2f}s  passes={len(res.passes)}"
                      f"  total_itertime={total_t:.4f}s")
                for pname, pd in res.passes.items():
                    its = pd.get("iter_times", [])
                    med = pd["median_time"]
                    mean = pd.get("mean_time", med)
                    ci95 = pd.get("ci95_abs")
                    mn  = pd["min_time"]
                    mx  = pd["max_time"]
                    n   = pd.get("n", len(its))
                    t   = pd["pass_type"][0].upper() if pd["pass_type"] != "unknown" else "?"
                    vprint(f"           [{t}] {pname}: "
                          f"median={_fmt_time(med)}  "
                          f"mean={_fmt_time(mean)}  "
                          f"95%CI=±{fmt_ci95(ci95)}  "
                          f"min={_fmt_time(mn)}  max={_fmt_time(mx)}  n={n}")

        results[var] = res

        # Cooldown between variant executions to reduce thermal/cache carryover.
        if idx < len(variants) - 1 and cooldown_seconds > 0:
            vprint(f"           waiting {cooldown_seconds:g}s before next variant run ...")
            time.sleep(cooldown_seconds)

    # For backwards compatibility, return (aos, soa) with mutable cursors
    # Also store all results globally if benchmarking immutable variants
    aos, soa = results.get("aos"), results.get("soa")
    
    # Global storage for extended results (used by new comparison table)
    if hasattr(benchmark_program, '_all_variants_results'):
        benchmark_program._all_variants_results.append({
            'program': prog,
            'aos': results.get("aos"),
            'aos_imm': results.get("aos_imm"),
            'soa': results.get("soa"),
            'soa_imm': results.get("soa_imm"),
            'ghc': results.get("ghc"),
            'mlton': results.get("mlton"),
        })
    
    # Output checks: compare all successful variants with outputs (AoS/SoA/imm/GHC/MLton).
    outputs_by_variant = {
        "aos": aos,
        "soa": soa,
        "aos_imm": results.get("aos_imm") if (benchmark_immutable or benchmark_baseline_gibbon) else None,
        "soa_imm": results.get("soa_imm") if benchmark_immutable else None,
        "ghc": results.get("ghc"),
        "mlton": results.get("mlton"),
    }
    analysis = analyze_outputs_by_variant(outputs_by_variant)
    if analysis["is_match"] is True:
        print("\n  Output check (successful variants): ✓ MATCH")
    elif analysis["is_match"] is False:
        print("\n  Output check (successful variants): ✗ MISMATCH")
    else:
        print("\n  Output check (successful variants): N/A (fewer than 2 successful variants with output)")
    if analysis["failed"]:
        failed_s = ", ".join(f"{v} ({err})" for v, err in analysis["failed"])
        print(f"  Runtime failures excluded from output matching: {failed_s}")

    if prov.eligible_pair(aos, soa) and aos.passes and soa.passes:
        aos_total = total_pass_time(aos)
        soa_total = total_pass_time(soa)
        speedup, _reason = prov.safe_speedup(aos, soa, total_pass_time)
        speedup_s = (f"{speedup:.3f}x" if speedup is not None else "N/A")
        aos_total_s = fmt(aos_total) if aos_total is not None else "N/A"
        soa_total_s = fmt(soa_total) if soa_total is not None else "N/A"
        print(f"  End-to-end (sum of pass medians, VERIFIED): AoS={aos_total_s}s, "
              f"SoA={soa_total_s}s, AoS/SoA={speedup_s}")
    elif prov.eligible_pair(aos, soa):
        print("  End-to-end (sum of pass medians): N/A -- verified, but no "
              "per-pass timing was recorded for this program")
    elif aos and soa and (aos.run_success or soa.run_success):
        print("  End-to-end (sum of pass medians): N/A -- unverified "
              f"(aos: {prov.rejection_reason(aos)}; soa: {prov.rejection_reason(soa)})")
    if aos and soa and aos.run_success and soa.run_success:
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


# Passes that exist only to CHECK the program computed the right thing, not
# to be measured. `checksumTree` folds the mapped tree down to the single
# value the independent oracle compares against -- it is the correctness
# apparatus, not a benchmark kernel, so reporting it alongside the kernels
# (or letting it inflate a pass-sum) misstates what was measured. Excluded
# from every table and from every aggregate `total_pass_time` feeds.
# The oracle still consumes its OUTPUT; only its TIMING is dropped.
VERIFICATION_PASSES = frozenset({"checksumTree"})


def is_verification_pass(pass_name: str) -> bool:
    return pass_name in VERIFICATION_PASSES


def total_pass_time(res: Optional[BenchmarkResult], pass_type: Optional[str] = None) -> Optional[float]:
    """
    End-to-end compiler time = sum of median pass times.
    Optionally restrict to a pass type ("fold"/"map"/...).

    This is the central chokepoint nearly every aggregate/speedup/table in
    the file goes through, so it enforces strict eligibility itself rather
    than trusting callers to have filtered first -- `prov.verified_result`,
    not `res.run_success` (an unverified result can still have
    `run_success=True`; it just never passed an independent oracle).
    """
    if not prov.verified_result(res) or not res.passes:
        return None
    total = 0.0
    for pname, pdata in res.passes.items():
        if is_verification_pass(pname):
            continue
        if pass_type is not None and pdata.get("pass_type") != pass_type:
            continue
        total += pdata.get("median_time", 0.0)
    return total


def _tex_escape(text: str) -> str:
    return text.replace("_", "\\_")


def _fmt_counter(v: Optional[float]) -> str:
    if v is None:
        return "--"
    # Scientific notation with 2 significant digits for readability.
    # Python format ".1e" => 2 significant digits total.
    return f"{float(v):.1e}"


def _first_present(*values):
    """Return the first value that is not None.

    Deliberately NOT `a or b`: 0, 0.0 and "" are legitimate values here (e.g.
    a pass with 0% dead ratio, or 0 uses) and `or` would incorrectly treat
    them as absent and fall through to the next argument.
    """
    for v in values:
        if v is not None:
            return v
    return None


def _papi_pair_cell(ad: Dict, sd: Dict, counter: str) -> str:
    a = (ad.get("papi_counters", {}).get(counter) or {}).get("median")
    s = (sd.get("papi_counters", {}).get(counter) or {}).get("median")
    if a is None and s is None:
        return "--"
    a_s = _fmt_counter(a)
    s_s = _fmt_counter(s)
    if a is not None and s is not None:
        if a < s:
            a_s = f"\\textbf{{{a_s}}}"
        elif s < a:
            s_s = f"\\textbf{{{s_s}}}"
    return f"{a_s}/{s_s}"


def _pass_sort_key(pname: str, *results: Optional[BenchmarkResult]) -> Tuple[int, str]:
    """
    Sort passes as: fold first, then map, then unknown; name as tiebreaker.
    """
    ptype = "unknown"
    for res in results:
        if not res:
            continue
        pd = res.passes.get(pname, {})
        t = pd.get("pass_type", "unknown")
        if t in ("fold", "map"):
            ptype = t
            break
        if ptype == "unknown" and t:
            ptype = t
    pri = 0 if ptype == "fold" else (1 if ptype == "map" else 2)
    return (pri, pname.lower())


def _short_counter_label(counter: str) -> str:
    mapping = {
        "CPU_CYCLES": "CYC",
        "INSTRUCTIONS": "INS",
        "L1D_LOAD_MISSES": "L1D",
        "L1I_LOAD_MISSES": "L1I",
        "L2D_MISSES": "L2D",
        "L2I_MISSES": "L2I",
        "LLC_LOAD_MISSES": "LLC",
        "PAPI_TOT_CYC": "TOT_CYC",
        "PAPI_L1_TCM": "L1_TCM",
        "PAPI_L1_DCM": "L1_DCM",
        "PAPI_L1_ICM": "L1_ICM",
        "PAPI_L2_TCM": "L2_TCM",
        "PAPI_L2_DCM": "L2_DCM",
        "PAPI_L2_ICM": "L2_ICM",
        "PAPI_L3_TCM": "L3_TCM",
        "PAPI_L3_DCM": "L3_DCM",
        "PAPI_L3_ICM": "L3_ICM",
    }
    if counter in mapping:
        return mapping[counter]
    if counter.startswith("PAPI_"):
        return counter.replace("PAPI_", "")
    return counter


def _program_label_compact(program_hs: str) -> str:
    """Compact program label for wide summary tables."""
    base = program_hs.replace(".hs", "")
    if base.startswith("OctTree_"):
        base = "Oct:" + base[len("OctTree_"):]
    return base.replace("_", "\\_")

# ---------------------------------------------------------------------------
# LaTeX tables
# ---------------------------------------------------------------------------
def _table_comparison_ghc_mlton(f, all_variants_results):
    f.write("\n\n")
    f.write("% ============================================================================\n")
    f.write("% Table 3: Gibbon vs GHC vs MLton Comparison\n")
    f.write("% ============================================================================\n\n")

    rows = []
    # Collect data first
    for entry in all_variants_results:
        prog = _program_label_compact(entry['program'])
        
        def get_total_or_oom(res):
            if res is None: return None, False
            if prov.verified_result(res): return total_pass_time(res), False
            is_oom = (res.error_message == "out of memory")
            return None, is_oom

        aos_t, aos_oom = get_total_or_oom(entry.get('aos'))
        soa_t, soa_oom = get_total_or_oom(entry.get('soa'))
        ghc_t, ghc_oom = get_total_or_oom(entry.get('ghc'))
        mlton_t, mlton_oom = get_total_or_oom(entry.get('mlton'))

        row_data = {
            "prog": prog,
            "aos": (aos_t, aos_oom),
            "soa": (soa_t, soa_oom),
            "ghc": (ghc_t, ghc_oom),
            "mlton": (mlton_t, mlton_oom),
        }
        rows.append(row_data)

    has_mlton = any(entry.get("mlton") is not None for entry in all_variants_results)
    f.write("\\begin{table}[htbp]\n\\centering\n")
    f.write("\\caption{Runtime comparison of Gibbon (AoS/SoA), GHC"
            + (", and MLton. " if has_mlton else ". ")
            + "Times are total median per iteration (s). "
            "\\textbf{Bold} marks the fastest time for each program.}\n")
    f.write("\\label{tab:comparison_ghc_mlton}\n\\small\n")
    f.write("\\begin{tabular}{p{3.2cm} r r r" + (" r" if has_mlton else "") + "}\n\\toprule\n")
    header = ("\\textbf{Program}"
              " & \\textbf{Gibbon-AoS} & \\textbf{Gibbon-SoA}"
              " & \\textbf{GHC}")
    if has_mlton:
        header += " & \\textbf{MLton}"
    f.write(header + " \\\\\n")
    f.write("\\midrule\n")

    # geomean collectors
    aos_times, soa_times, ghc_times, mlton_times = [], [], [], []

    for r in rows:
        cells = {}
        for variant in ["aos", "soa", "ghc", "mlton"]:
            t, is_oom = r[variant]
            if is_oom:
                cells[variant] = ("\\textit{OOM}", None)
            elif t is None:
                cells[variant] = ("--", None)
            else:
                cells[variant] = (fmt(t), t)

        valid_times = [v[1] for v in cells.values() if v[1] is not None]
        if valid_times:
            min_t = min(valid_times)
            for k, v in cells.items():
                if v[1] is not None and v[1] == min_t:
                    cells[k] = (f"\\textbf{{{v[0]}}}", v[1])
        
        # append to geomean lists
        if r["aos"][0] is not None and not r["aos"][1]: aos_times.append(r["aos"][0])
        if r["soa"][0] is not None and not r["soa"][1]: soa_times.append(r["soa"][0])
        if r["ghc"][0] is not None and not r["ghc"][1]: ghc_times.append(r["ghc"][0])
        if r["mlton"][0] is not None and not r["mlton"][1]: mlton_times.append(r["mlton"][0])

        row = (f"{r['prog']}"
               f" & {cells['aos'][0]} & {cells['soa'][0]}"
               f" & {cells['ghc'][0]}")
        if has_mlton:
            row += f" & {cells['mlton'][0]}"
        f.write(row + " \\\\\n")
    
    # Geomean row
    f.write("\\midrule\n")
    gm_aos = statistics.geometric_mean(aos_times) if aos_times else None
    gm_soa = statistics.geometric_mean(soa_times) if soa_times else None
    gm_ghc = statistics.geometric_mean(ghc_times) if ghc_times else None
    gm_mlton = statistics.geometric_mean(mlton_times) if mlton_times else None

    gm_cells = {
        "aos": (fmt(gm_aos) if gm_aos else "--", gm_aos),
        "soa": (fmt(gm_soa) if gm_soa else "--", gm_soa),
        "ghc": (fmt(gm_ghc) if gm_ghc else "--", gm_ghc),
        "mlton": (fmt(gm_mlton) if gm_mlton else "--", gm_mlton),
    }
    gm_valid = [v[1] for v in gm_cells.values() if v[1] is not None]
    if gm_valid:
        min_gm = min(gm_valid)
        for k, v in gm_cells.items():
            if v[1] is not None and v[1] == min_gm:
                gm_cells[k] = (f"\\textbf{{{v[0]}}}", v[1])

    gm_row = (f"\\textbf{{Geomean}}"
              f" & {gm_cells['aos'][0]} & {gm_cells['soa'][0]}"
              f" & {gm_cells['ghc'][0]}")
    if has_mlton:
        gm_row += f" & {gm_cells['mlton'][0]}"
    f.write(gm_row + " \\\\\n")

    f.write("\\bottomrule\n\\end{tabular}\n\\end{table}\n\n")

def _table_speedup_vs_ghc(f, all_variants_results):
    f.write("\n\n")
    f.write("% ============================================================================\n")
    f.write("% Table: Gibbon mutable speedups over GHC\n")
    f.write("% ============================================================================\n\n")

    def get_total_or_oom(res):
        if res is None:
            return None, False
        if prov.verified_result(res):
            return total_pass_time(res), False
        return None, (res is not None and res.error_message == "out of memory")

    def fmt_spd(v: Optional[float]) -> str:
        if v is None:
            return "--"
        return f"{v:.2f}" + r"$\times$"

    rows = []
    ghc_over_aos_vals = []
    ghc_over_soa_vals = []
    for entry in all_variants_results:
        prog = _program_label_compact(entry["program"])
        aos_t, aos_oom = get_total_or_oom(entry.get("aos"))
        soa_t, soa_oom = get_total_or_oom(entry.get("soa"))
        ghc_t, ghc_oom = get_total_or_oom(entry.get("ghc"))

        def speedup(num, den):
            if num is None or den is None or den <= 0.0:
                return None
            return num / den

        ghc_over_aos = speedup(ghc_t, aos_t)
        ghc_over_soa = speedup(ghc_t, soa_t)
        if ghc_over_aos is not None:
            ghc_over_aos_vals.append(ghc_over_aos)
        if ghc_over_soa is not None:
            ghc_over_soa_vals.append(ghc_over_soa)

        rows.append({
            "prog": prog,
            "ghc_over_aos": ghc_over_aos,
            "ghc_over_soa": ghc_over_soa,
            "aos_oom": aos_oom,
            "soa_oom": soa_oom,
            "ghc_oom": ghc_oom,
        })

    f.write("\\begin{table}[htbp]\n\\centering\n")
    f.write("\\caption{GHC speedups vs Gibbon mutable variants. "
            "Each entry is total median runtime speedup over all passes for one iteration. "
            "$\\text{GHC}/\\text{AoS}$ and $\\text{GHC}/\\text{SoA}$ are reported.}\n")
    f.write("\\label{tab:speedup_vs_ghc}\n\\small\n")
    f.write("\\begin{tabular}{p{3.2cm} r r}\n\\toprule\n")
    f.write("\\textbf{Program} & $\\mathbf{\\text{GHC}/\\text{AoS}}$ & $\\mathbf{\\text{GHC}/\\text{SoA}}$ \\\\\n")
    f.write("\\midrule\n")

    for r in rows:
        if r["ghc_oom"]:
            a_cell, s_cell = "\\textit{OOM}", "\\textit{OOM}"
        else:
            a_cell = "\\textit{OOM}" if r["aos_oom"] else fmt_spd(r["ghc_over_aos"])
            s_cell = "\\textit{OOM}" if r["soa_oom"] else fmt_spd(r["ghc_over_soa"])
        f.write(f"{r['prog']} & {a_cell} & {s_cell} \\\\\n")

    gm_a = statistics.geometric_mean(ghc_over_aos_vals) if ghc_over_aos_vals else None
    gm_s = statistics.geometric_mean(ghc_over_soa_vals) if ghc_over_soa_vals else None
    f.write("\\midrule\n")
    f.write(f"\\textbf{{Geomean}} & {fmt_spd(gm_a)} & {fmt_spd(gm_s)} \\\\\n")
    f.write("\\bottomrule\n\\end{tabular}\n\\end{table}\n\n")

def _table_cursor_comparison(f, all_variants_results):
    """
    Generates Table 2: Cursor mode comparison showing all 4 variants.
    Table 2 uses full executable end-to-end wall time (NOT pass-sum time).
    AOS-mut, AOS-imm, SoA-mut, SoA-imm for each program.
    """
    f.write("\n\n")
    f.write("% ============================================================================\n")
    f.write("% Table 2: Mutable vs Immutable Cursor Comparison\n")
    f.write("% ============================================================================\n\n")

    has_soa_imm = any(entry.get("soa_imm") is not None for entry in all_variants_results)
    rows = []

    # Use full executable end-to-end runtime captured around run_exe().
    def get_total_or_oom(res):
        """Returns (time, is_oom) tuple; time is full executable wall time.
        Gated on `verified_result`, not `run_success`: this feeds a speedup
        table cell, so a result that ran but never passed its independent
        oracle must render as unavailable here, not as a real time."""
        if res is None:
            return None, False
        if prov.verified_result(res):
            return res.exec_wall_time, False
        # Failed or unverified - check if it was OOM
        is_oom = (res is not None and res.error_message == "out of memory")
        return None, is_oom

    # Collapse split OctTree programs (OctTree_*.hs) into one row by summing.
    oct_entries = [e for e in all_variants_results
                   if str(e.get("program", "")).startswith("OctTree_")]

    def _agg_oct_variant(vname: str) -> Tuple[Optional[float], bool]:
        saw_variant = False
        any_oom = False
        total = 0.0
        saw_success = False
        for e in oct_entries:
            res = e.get(vname)
            if res is None:
                continue
            saw_variant = True
            t, oom = get_total_or_oom(res)
            if oom:
                any_oom = True
            elif t is not None:
                total += t
                saw_success = True
        if any_oom:
            return None, True
        if saw_success:
            return total, False
        return (None, False) if saw_variant else (None, False)

    oct_agg = None
    if oct_entries:
        oct_agg = {
            "program": "OctTree.hs",
            "aos": _agg_oct_variant("aos"),
            "aos_imm": _agg_oct_variant("aos_imm"),
            "soa": _agg_oct_variant("soa"),
            "soa_imm": _agg_oct_variant("soa_imm"),
        }

    oct_added = False
    for entry in all_variants_results:
        prog_name = str(entry.get("program", ""))
        if prog_name.startswith("OctTree_"):
            if oct_agg is None or oct_added:
                continue
            oct_added = True
            prog = "OctTree"
            aost_mut, aost_mut_oom = oct_agg["aos"]
            aost_imm, aost_imm_oom = oct_agg["aos_imm"]
            soat_mut, soat_mut_oom = oct_agg["soa"]
            soat_imm, soat_imm_oom = oct_agg["soa_imm"]
        else:
            prog = _program_label_compact(prog_name)
            aost_mut, aost_mut_oom = get_total_or_oom(entry.get('aos'))
            aost_imm, aost_imm_oom = get_total_or_oom(entry.get('aos_imm'))
            soat_mut, soat_mut_oom = get_total_or_oom(entry.get('soa'))
            soat_imm, soat_imm_oom = get_total_or_oom(entry.get('soa_imm'))

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
        }
        if has_soa_imm:
            cells["soa_imm"] = [fmt_cell(soat_imm, soat_imm_oom), soat_imm, soat_imm_oom]
        valid_times = [v[1] for v in cells.values() if v[1] is not None and not v[2]]
        if valid_times:
            min_t = min(valid_times)
            for k, v in cells.items():
                if v[1] is not None and not v[2] and v[1] == min_t:
                    v[0] = f"\\textbf{{{v[0]}}}"

        aos_mut_f = cells["aos_mut"][0]
        aos_imm_f = cells["aos_imm"][0]
        soa_mut_f = cells["soa_mut"][0]
        soa_imm_f = cells["soa_imm"][0] if has_soa_imm else None

        # Calculate speedups
        def speedup(a, s):
            if a is not None and s is not None and s > 0:
                return a / s
            return None

        spd_mut = speedup(aost_mut, soat_mut)
        spd_aos_imm_over_aos_mut = speedup(aost_imm, aost_mut)
        spd_imm = speedup(aost_imm, soat_mut)
        spd_imm_layout = speedup(aost_imm, soat_imm) if has_soa_imm else None

        spd_mut_s = _spd_cell(spd_mut) if spd_mut else "--"
        spd_aos_imm_over_aos_mut_s = _spd_cell(spd_aos_imm_over_aos_mut) if spd_aos_imm_over_aos_mut else "--"
        spd_imm_s = _spd_cell(spd_imm) if spd_imm else "--"
        spd_imm_layout_s = _spd_cell(spd_imm_layout) if spd_imm_layout else "--"

        rows.append({
            "prog": prog,
            "aos_mut": aos_mut_f,
            "aos_imm": aos_imm_f,
            "soa_mut": soa_mut_f,
            "soa_imm": soa_imm_f,
            "spd_mut": spd_mut_s,
            "spd_aos_imm_over_aos_mut": spd_aos_imm_over_aos_mut_s,
            "spd_imm": spd_imm_s,
            "spd_imm_layout": spd_imm_layout_s,
        })

    # 2A: raw times
    f.write("\\begin{table}[htbp]\n\\centering\n")
    if has_soa_imm:
        f.write("\\caption{Mutable vs immutable cursor comparison (times only). "
                "Times are full executable end-to-end wall time per run (s), not pass-sum time. "
                "\\textbf{Bold} marks the fastest time across all four variants.}\n")
    else:
        f.write("\\caption{Baseline Gibbon comparison (times only). "
                "Shown variants: AoS-mut, AoS-imm, SoA-mut. "
                "Times are full executable end-to-end wall time per run (s), not pass-sum time. "
                "\\textbf{Bold} marks the fastest time across shown variants.}\n")
    f.write("\\label{tab:cursor_comparison_times}\n\\small\n")
    f.write("\\begin{tabular}{p{3.2cm} r r r" + (" r" if has_soa_imm else "") + "}\n\\toprule\n")
    header = ("\\textbf{Program}"
              " & \\textbf{Am} & \\textbf{Ai}"
              " & \\textbf{Sm}")
    if has_soa_imm:
        header += " & \\textbf{Si}"
    f.write(header + " \\\\\n")
    f.write("\\midrule\n")
    for r in rows:
        row = (f"{r['prog']}"
               f" & {r['aos_mut']} & {r['aos_imm']}"
               f" & {r['soa_mut']}")
        if has_soa_imm:
            row += f" & {r['soa_imm']}"
        f.write(row + " \\\\\n")
    f.write("\\bottomrule\n\\end{tabular}\n\\end{table}\n\n")

    # 2B: speedups
    f.write("\\begin{table}[htbp]\n\\centering\n")
    if has_soa_imm:
        f.write("\\caption{Mutable vs immutable cursor comparison (speedups). "
                "Shown: AoS-mut/SoA-mut, AoS-imm/AoS-mut, AoS-imm/SoA-mut, AoS-imm/SoA-imm. "
                "Speedups are computed from full executable end-to-end wall time per run. "
                "${>}1{\\times}$ means the denominator is faster.}\n")
    else:
        f.write("\\caption{Baseline Gibbon comparison (speedups). "
                "Shown: AoS-mut/SoA-mut, AoS-imm/AoS-mut, AoS-imm/SoA-mut. "
                "Speedups are computed from full executable end-to-end wall time per run. "
                "${>}1{\\times}$ means the denominator is faster.}\n")
    f.write("\\label{tab:cursor_comparison_speedups}\n\\small\n")
    f.write("\\begin{tabular}{p{3.2cm} r r r" + (" r" if has_soa_imm else "") + "}\n\\toprule\n")
    header = ("\\textbf{Program}"
              " & \\textbf{Am/Sm}"
              " & \\textbf{Ai/Am}"
              " & \\textbf{Ai/Sm}")
    if has_soa_imm:
        header += " & \\textbf{Ai/Si}"
    f.write(header + " \\\\\n")
    f.write("\\midrule\n")
    for r in rows:
        row = (f"{r['prog']}"
               f" & {r['spd_mut']}"
               f" & {r['spd_aos_imm_over_aos_mut']}"
               f" & {r['spd_imm']}")
        if has_soa_imm:
            row += f" & {r['spd_imm_layout']}"
        f.write(row + " \\\\\n")
    f.write("\\bottomrule\n\\end{tabular}\n\\end{table}\n\n")


# ---------------------------------------------------------------------------
# The four-width add1Tree width/vectorization table.
#
# NOTE ON SCOPE: this table performs no timing on its own. The collection
# function below (`collect_add1tree_width_results`) exists so a future timed
# run can call it and get real `BenchmarkResult` objects with real pass
# timings -- it is plumbed through exactly like any other program's
# compile/run/qualify path (`compile_one`/`run_exe`/`qualify_variant`, the
# same functions every other row in this file goes through) so no numeric
# value it produces bypasses the verified-result contract. It is NOT invoked
# by this file's own test suite; only the RENDERING function
# (`_table_add1tree_widths`) is exercised here, against synthetic
# `BenchmarkResult`/`QualificationStatus` fixtures -- see
# test_add1tree_widths.py's `TestAdd1TreeWidthTable`.
# ---------------------------------------------------------------------------

# config name -> compile_one kwargs. "aos_mut"/"soa_mut" match this file's
# existing variant-naming convention elsewhere; "soa_loopify"/"soa_simd" are
# add1tree-table-specific configs (loopified SCALAR buffers with Gibbon's
# own vectorizer explicitly off vs. on, GCC auto-vectorization off in both
# so the two isolate Gibbon's own SIMD pass).
ADD1TREE_WIDTH_CONFIGS: Dict[str, Dict] = {
    "aos_mut": dict(use_mutable_cursors=True, use_no_gcc_vec=True),
    "soa_mut": dict(use_mutable_cursors=True, use_no_gcc_vec=True),
    "soa_loopify": dict(use_mutable_cursors=True, store_scalar_field_counts=True,
                        enable_loopification=True, use_no_gcc_vec=True),
    "soa_simd": dict(use_mutable_cursors=True, store_scalar_field_counts=True,
                     enable_loopification=True, enable_vectorization=True,
                     use_no_gcc_vec=True),
}


def _add1tree_width_of(program: str) -> Optional[int]:
    m = re.match(r"Add1TreeInt(\d+)\.hs$", program)
    return int(m.group(1)) if m else None


def collect_add1tree_width_results(programs_dir: Path, out_dir: Path, cc: str,
                                   force: bool, gibbon_exe: Optional[str],
                                   iterations: int = 1,
                                   c_arith_mode: str = DEFAULT_C_ARITH_MODE,
                                   simd_isa: str = DEFAULT_SIMD_ISA,
                                   pin_cpu: Optional[int] = None,
                                   ) -> Dict[int, Dict[str, BenchmarkResult]]:
    """Compiles and runs all four Add1TreeIntN.hs programs under the four
    ADD1TREE_WIDTH_CONFIGS, exactly the same compile_one/run_exe/
    qualify_variant path as every other row in this file. Returns
    {width: {config_name: BenchmarkResult}}. This function performs real
    executions -- callers that must not produce timing evidence must not
    call it outside a synthetic test that stubs it out.

    `iterations` is the --iterate count each configuration is run at, and
    the caller is expected to pass the driver's real --iterations value.
    The 1 default exists for structural and correctness tests only: at one
    iteration each cell is a single cold measurement with no median behind
    it, and a single cold run of these kernels is occasionally several
    times its own median.

    `c_arith_mode` defaults to the same driver-wide `unsafe` default --
    this table retains its own width policy (Int8/16/32/64 are the
    experiment) but its arithmetic mode still follows the driver default."""
    _validate_c_arith_mode(c_arith_mode)
    manifest = default_oracle_manifest()
    results: Dict[int, Dict[str, BenchmarkResult]] = {}
    for program in ADD1TREE_WIDTH_PROGRAMS:
        width = _add1tree_width_of(program)
        results[width] = {}
        for cfg_name, cfg_kwargs in ADD1TREE_WIDTH_CONFIGS.items():
            src_dir = "AOS" if cfg_name.startswith("aos") else "SOA"
            source = programs_dir / src_dir / program
            res = BenchmarkResult(program, cfg_name)
            res.arith_mode = c_arith_mode
            res.use_no_ran = program_uses_no_ran(program)
            if not source.exists():
                res.compile_success = False
                res.error_message = "source not found: %s" % source
                res.qualification = qualify_variant(
                    program, cfg_name, source, False, res.error_message,
                    False, None, None, manifest=manifest)
                results[width][cfg_name] = res
                continue
            ok, compile_time, err = compile_one(source, cfg_name, out_dir, force,
                                                use_no_ran=program_uses_no_ran(program),
                                                c_arith_mode=c_arith_mode,
                                                simd_isa=simd_isa,
                                                **cfg_kwargs)
            res.compile_success = ok
            res.compile_time = compile_time
            exe = out_dir / f"{source.stem}.{cfg_name}.exe"
            c_file = out_dir / f"{source.stem}.{cfg_name}.c"
            if ok:
                run_ok, elapsed, out, err2, rc = run_exe(exe, iterations, use_iterate_flag=True, pin_cpu=pin_cpu)
                res.run_success = run_ok
                res.run_returncode = rc
                res.run_finished_at = datetime.datetime.now().isoformat(timespec="seconds")
                res.output = out
                res.exec_wall_time = elapsed
                if run_ok and out:
                    res.passes = parse_passes(out)
                res.qualification = qualify_variant(
                    program, cfg_name, source, ok, err, run_ok, err2, out,
                    manifest=manifest, c_file=c_file if c_file.exists() else None,
                    expect_vectorization=(cfg_name == "soa_simd"))
            else:
                res.qualification = qualify_variant(
                    program, cfg_name, source, False, err, False, None, None,
                    manifest=manifest)
            results[width][cfg_name] = res
    return results


def _qual_summary(cfgs: Dict[str, Optional[BenchmarkResult]]) -> str:
    """Compact per-row qualification summary shared by the width tables:
    'OK' when every present config is VERIFIED, otherwise only the
    non-verified configs and their status label -- so a fully-qualified
    row costs one word instead of one clause per config."""
    problems = []
    for name, res in cfgs.items():
        st = getattr(res, "qualification", None) if res is not None else None
        label = st.label if st is not None else "MISSING"
        if label != "VERIFIED":
            problems.append("%s=%s" % (name, label))
    return "OK" if not problems else "; ".join(problems)


def _table_add1tree_widths(f, results_by_width: Dict[int, Dict[str, BenchmarkResult]]):
    """Integer-width add1Tree vectorization table: one row per width, every
    numeric cell gated through prov.verified_result/eligible_pair/
    safe_speedup -- an unverified, missing-oracle, failed or empty-output
    variant renders N/A with a reason and never contributes to a speedup,
    total, aggregate, plot or exported JSON numeric result (the same
    contract every other table in this file enforces, not a duplicated
    parallel eligibility check)."""
    f.write("% Integer-width add1Tree vectorization\n")
    f.write("\\begin{table}[h]\n\\centering\n")
    f.write("\\caption{Integer-width add1Tree vectorization. "
            + simd_isa_caption_note() + no_gcc_vec_caption_note() + "}\n")
    f.write("\\label{tab:add1tree_widths}\n\\small\n")
    f.write("\\resizebox{\\textwidth}{!}{%\n")
    f.write("\\begin{tabular}{lcccccccc}\n\\toprule\n")
    f.write("Width & AoS raw & SoA raw & AoS/SoA & SoA loopify & SoA SIMD & "
            "SIMD spd. & AoS-vs-SIMD & Qual. \\\\\n\\midrule\n")

    def cell(res: Optional[BenchmarkResult]) -> str:
        t = total_pass_time(res)
        return f"{t:.6f}" if t is not None else "N/A"

    for width in sorted(results_by_width.keys()):
        cfgs = results_by_width[width]
        aos = cfgs.get("aos_mut")
        soa = cfgs.get("soa_mut")
        loop = cfgs.get("soa_loopify")
        simd = cfgs.get("soa_simd")

        aos_over_soa, aos_over_soa_reason = prov.safe_speedup(aos, soa, total_pass_time)
        simd_spd, simd_reason = prov.safe_speedup(loop, simd, total_pass_time)
        aos_vs_simd, aos_vs_simd_reason = prov.safe_speedup(aos, simd, total_pass_time)

        def spd_or_na(spd, reason):
            return _spd_cell(spd) if spd is not None else ("N/A -- %s" % reason)

        row = (f"Int{width}"
               f" & {cell(aos)}"
               f" & {cell(soa)}"
               f" & {spd_or_na(aos_over_soa, aos_over_soa_reason)}"
               f" & {cell(loop)}"
               f" & {cell(simd)}"
               f" & {spd_or_na(simd_spd, simd_reason)}"
               f" & {spd_or_na(aos_vs_simd, aos_vs_simd_reason)}"
               f" & {_tex_escape(_qual_summary(cfgs))}")
        f.write(row + " \\\\\n")
    f.write("\\bottomrule\n\\end{tabular}}\n\\end{table}\n\n")


# ---------------------------------------------------------------------------
# The high-arithmetic-intensity width/vectorization table.
#
# Same scope note as ADD1TREE_WIDTH_* above: this table performs no timing
# on its own. `collect_arithintensity_width_results` is real compile/run/
# qualify plumbing for a future timed run; only the rendering function
# (`_table_arith_intensity`) is exercised by this file's own tests, against
# synthetic fixtures -- see test_arithintensity_widths.py's
# `TestArithIntensityWidthTable`.
#
# W64 SIMD EXCLUSION (the one structural difference from Add1Tree's table):
# `L3.simdCapable VecOpMul (IntS W64)` is `True` in the current compiler --
# the only packed W64 multiply helper that exists (`gib_vec_mul_int64x2`)
# spills each 128-bit register to a 2-element scalar array, calls the same
# scalar `gib_mul_i64` used on the non-vectorized path per lane, and
# reassembles the register (Codegen.hs's own comment: "NOT an
# acceleration... retained ONLY because W64 vectorization already shipped
# with them"). Enabling --opt-vectorization for a W64 MayVectorize
# multiply is therefore CORRECT but not real SIMD, and this benchmark's
# policy is that it must never be reported as one. Rather than change the
# global capability matrix (`L3.simdCapable`) to work around a codegen
# quirk unrelated to compiler correctness, ARITHINTENSITY_WIDTH_CONFIGS
# simply never builds a "soa_simd" config for width 64
# (collect_arithintensity_width_results skips it structurally, not via a
# runtime check on the result), and _table_arith_intensity hardcodes width
# 64's SIMD/speedup cells to a fixed N/A reason BEFORE consulting any
# BenchmarkResult -- so a stray or synthetic W64 "soa_simd" result, however
# constructed, can never reach that cell as a number. This is proven, not
# assumed: see TestArithIntensityWidthTable.
# test_w64_simd_column_is_always_na_even_if_a_verified_result_is_supplied.
ARITHINTENSITY_WIDTH_PROGRAMS = [
    "ArithmeticIntensityInt8.hs", "ArithmeticIntensityInt16.hs",
    "ArithmeticIntensityInt32.hs", "ArithmeticIntensityInt64.hs",
]

# Structural arithmetic-intensity accounting, derived from the accepted
# kernel's own generated-C form (4 gib_mul_i<w> + 4 gib_add_i<w>/
# gib_sub_i<w> per leaf -- confirmed by direct inspection of the emitted C
# for arithKernel, not counted from source text alone) and each width's
# byte size. Deliberately excludes loop control, address/cursor
# arithmetic, tree construction and the verification fold -- none of that
# is the kernel.
ARITH_OPS_PER_ELEMENT = 415  # 8 independent chain-pairs x 6 rounds
# of `a = a*(2b+1) + c`, plus seeding and the final sum. Raised from 8
# on 2026-09-07: at 8 ops the kernel sat at 0.162 ops/byte against an
# Int32 ridge of 2.20, i.e. 13.6x memory-bound, so the width sweep was
# measuring bytes moved rather than vectorization. It is now 4.75
# ops/byte -- compute-bound -- which is what makes the roofline
# overlay's x-axis meaningful. Counted from the generated program, not
# asserted; see the kernel comment in the .hs sources.


def arith_intensity_metrics(width: int) -> Dict[str, float]:
    width_bytes = width // 8
    bytes_loaded = width_bytes    # one Leaf field read
    bytes_stored = width_bytes    # one Leaf field written back
    return {
        "ops_per_element": ARITH_OPS_PER_ELEMENT,
        "bytes_loaded_per_element": bytes_loaded,
        "bytes_stored_per_element": bytes_stored,
        "ops_per_byte": ARITH_OPS_PER_ELEMENT / (bytes_loaded + bytes_stored),
    }


# W64 is deliberately absent from "soa_simd" -- see the module-level note
# above. Only W8/16/32 get a real Gibbon-SIMD config.
# EVERY column here disables the C compiler's own auto-vectorizer.
#
# It was previously disabled only on the Gibbon-side columns (soa_loopify,
# soa_simd) while the two raw columns kept it, which made loopification look
# like a REGRESSION: measured on Int16, the table reported raw 0.1875s against
# loopified 0.4663s -- 2.5x slower -- because the raw column was being
# vectorized by GCC and the loopified one was not. Compared honestly,
# loopification wins either way: 0.1875 -> 0.1374 with the C vectorizer on for
# both (1.36x), and 0.5184 -> 0.4651 with it off for both (1.11x).
#
# GCC helps the recursive form more than one might expect because the kernel
# is straight-line arithmetic over independent chains, which its SLP
# (basic-block) vectorizer packs even though the traversal itself is
# recursive; --no-gcc-vectorize disables SLP as well as loop vectorization.
#
# These programs exist to isolate GIBBON's SIMD pass, so the C vectorizer is
# off in every column and the table measures one thing. The absolute times are
# therefore NOT what a normal build produces -- the per-program PLDI tables
# carry the C-vectorizer-enabled configurations for that.
ARITHINTENSITY_WIDTH_CONFIGS: Dict[int, Dict[str, Dict]] = {
    width: (
        {
            "aos_mut": dict(use_mutable_cursors=True, use_no_gcc_vec=True),
            "soa_mut": dict(use_mutable_cursors=True, use_no_gcc_vec=True),
            "soa_loopify": dict(use_mutable_cursors=True, store_scalar_field_counts=True,
                                enable_loopification=True, use_no_gcc_vec=True),
            "soa_loopify_shared": dict(use_mutable_cursors=True, store_scalar_field_counts=True,
                                       enable_loopification=True,
                                       enable_selective_buffer_sharing=True,
                                       use_no_gcc_vec=True),
        } if width == 64 else
        {
            "aos_mut": dict(use_mutable_cursors=True, use_no_gcc_vec=True),
            "soa_mut": dict(use_mutable_cursors=True, use_no_gcc_vec=True),
            "soa_loopify": dict(use_mutable_cursors=True, store_scalar_field_counts=True,
                                enable_loopification=True, use_no_gcc_vec=True),
            "soa_loopify_shared": dict(use_mutable_cursors=True, store_scalar_field_counts=True,
                                       enable_loopification=True,
                                       enable_selective_buffer_sharing=True,
                                       use_no_gcc_vec=True),
            # Selective buffer sharing is ON here so this column differs from
            # soa_loopify_shared by the vectorizer alone, and matches the
            # per-program map tables, whose SoA columns also enable it.
            "soa_simd": dict(use_mutable_cursors=True, store_scalar_field_counts=True,
                             enable_loopification=True,
                             enable_selective_buffer_sharing=True,
                             enable_vectorization=True,
                             use_no_gcc_vec=True),
        }
    )
    for width in (8, 16, 32, 64)
}

W64_SIMD_NA_REASON = ("unsupported packed multiply: gib_vec_mul_int64x2 is a "
                      "legacy scalar-spill helper (Codegen.hs), not real SIMD -- "
                      "excluded from this benchmark's Gibbon-SIMD configuration "
                      "per owner policy; see BUGS.md")


def _arithintensity_width_of(program: str) -> Optional[int]:
    m = re.match(r"ArithmeticIntensityInt(\d+)\.hs$", program)
    return int(m.group(1)) if m else None


def collect_arithintensity_width_results(programs_dir: Path, out_dir: Path, cc: str,
                                         force: bool, gibbon_exe: Optional[str],
                                         iterations: int = 1,
                                         c_arith_mode: str = DEFAULT_C_ARITH_MODE,
                                   simd_isa: str = DEFAULT_SIMD_ISA,
                                   pin_cpu: Optional[int] = None,
                                         ) -> Dict[int, Dict[str, BenchmarkResult]]:
    """Same compile_one/run_exe/qualify_variant path as
    collect_add1tree_width_results. For width 64, ARITHINTENSITY_WIDTH_CONFIGS
    has no "soa_simd" entry at all, so this function structurally never
    builds one -- not a runtime skip, an absent config.

    `iterations` is the --iterate count each configuration is run at, and
    the caller is expected to pass the driver's real --iterations value.
    The 1 default exists for structural and correctness tests only: at one
    iteration each cell is a single cold measurement with no median behind
    it, and a single cold run of these kernels is occasionally several
    times its own median.

    `c_arith_mode` defaults to the driver-wide `unsafe` default -- this
    table retains its own width policy independent of it."""
    _validate_c_arith_mode(c_arith_mode)
    manifest = default_oracle_manifest()
    results: Dict[int, Dict[str, BenchmarkResult]] = {}
    for program in ARITHINTENSITY_WIDTH_PROGRAMS:
        width = _arithintensity_width_of(program)
        results[width] = {}
        for cfg_name, cfg_kwargs in ARITHINTENSITY_WIDTH_CONFIGS[width].items():
            src_dir = "AOS" if cfg_name.startswith("aos") else "SOA"
            source = programs_dir / src_dir / program
            res = BenchmarkResult(program, cfg_name)
            res.arith_mode = c_arith_mode
            res.use_no_ran = program_uses_no_ran(program)
            if not source.exists():
                res.compile_success = False
                res.error_message = "source not found: %s" % source
                res.qualification = qualify_variant(
                    program, cfg_name, source, False, res.error_message,
                    False, None, None, manifest=manifest)
                results[width][cfg_name] = res
                continue
            ok, compile_time, err = compile_one(source, cfg_name, out_dir, force,
                                                use_no_ran=program_uses_no_ran(program),
                                                c_arith_mode=c_arith_mode,
                                                simd_isa=simd_isa,
                                                **cfg_kwargs)
            res.compile_success = ok
            res.compile_time = compile_time
            exe = out_dir / f"{source.stem}.{cfg_name}.exe"
            c_file = out_dir / f"{source.stem}.{cfg_name}.c"
            if ok:
                run_ok, elapsed, out, err2, rc = run_exe(exe, iterations, use_iterate_flag=True, pin_cpu=pin_cpu)
                res.run_success = run_ok
                res.run_returncode = rc
                res.run_finished_at = datetime.datetime.now().isoformat(timespec="seconds")
                res.output = out
                res.exec_wall_time = elapsed
                if run_ok and out:
                    res.passes = parse_passes(out)
                res.qualification = qualify_variant(
                    program, cfg_name, source, ok, err, run_ok, err2, out,
                    manifest=manifest, c_file=c_file if c_file.exists() else None,
                    expect_vectorization=(cfg_name == "soa_simd"))
            else:
                res.qualification = qualify_variant(
                    program, cfg_name, source, False, err, False, None, None,
                    manifest=manifest)
            results[width][cfg_name] = res
    return results


# ---------------------------------------------------------------------------
# --pldi-submission: per-program fold/map tables across an expanded AoS/SoA
# variant matrix.
#
# Every loopified config below passes --opt-loopification WITHOUT
# --auto-loopification: every curated map function this driver times already
# carries an explicit OPT:MayVectorize annotation (verified against every
# .hs file in programs/AOS and programs/SOA before this policy was adopted),
# so structural inference is unnecessary. The one known exception,
# DomTree.hs's `computeWidths`, has a genuine parent-child dependency (the
# parent's width is computed from its recursively-produced children) and is
# correctly left unloopified either way -- its loopified-row cells report
# unchanged, non-loopified timing, which is the correct result to show, not
# a bug to work around.
PLDI_FOLD_CONFIGS: Dict[str, Dict[str, Dict]] = {
    "aos": {
        "aos_imm_notco": dict(use_mutable_cursors=False, use_no_gcc_tail_calls=True),
        "aos_imm":       dict(use_mutable_cursors=False),
        "aos_mut":       dict(use_mutable_cursors=True),
        "aos_mut_notco": dict(use_mutable_cursors=True, use_no_gcc_tail_calls=True),
    },
    "soa": {
        "soa_imm_notco": dict(use_mutable_cursors=False, use_no_gcc_tail_calls=True),
        "soa_imm":       dict(use_mutable_cursors=False),
        "soa_mut":       dict(use_mutable_cursors=True),
        "soa_mut_notco": dict(use_mutable_cursors=True, use_no_gcc_tail_calls=True),
    },
}

# Each map-table layout's first 3 rows are exactly the fold-table's rows for
# that layout (the same compiled binary's fold-pass timing feeds the fold
# table; its map-pass timing feeds the map table) -- a program is compiled
# once per config name, not once per table.
PLDI_MAP_CONFIGS: Dict[str, Dict[str, Dict]] = {
    "aos": {
        **PLDI_FOLD_CONFIGS["aos"],
        "aos_loop_gccvec_off": dict(use_mutable_cursors=True, enable_loopification=True,
                                    auto_loopification=False, use_no_gcc_vec=True),
        "aos_loop_gccvec_on":  dict(use_mutable_cursors=True, enable_loopification=True,
                                    auto_loopification=False),
    },
    "soa": {
        **PLDI_FOLD_CONFIGS["soa"],
        "soa_loop_gccvec_off_sbs_off": dict(
            use_mutable_cursors=True, store_scalar_field_counts=True,
            enable_loopification=True, auto_loopification=False, use_no_gcc_vec=True),
        "soa_loop_gccvec_off_sbs_on": dict(
            use_mutable_cursors=True, store_scalar_field_counts=True,
            enable_loopification=True, auto_loopification=False,
            enable_selective_buffer_sharing=True, use_no_gcc_vec=True),
        "soa_loop_gccvec_on_sbs_on": dict(
            use_mutable_cursors=True, store_scalar_field_counts=True,
            enable_loopification=True, auto_loopification=False,
            enable_selective_buffer_sharing=True),
        "soa_loop_gccvec_off_sbs_on_gibvec_on": dict(
            use_mutable_cursors=True, store_scalar_field_counts=True,
            enable_loopification=True, auto_loopification=False,
            enable_selective_buffer_sharing=True, enable_vectorization=True,
            use_no_gcc_vec=True),
        "soa_loop_gccvec_on_sbs_on_gibvec_on": dict(
            use_mutable_cursors=True, store_scalar_field_counts=True,
            enable_loopification=True, auto_loopification=False,
            enable_selective_buffer_sharing=True, enable_vectorization=True),
    },
}

# Programs the --pldi-submission matrix reports IN ADDITION to the curated
# campaign list. The integer-width add1Tree series is a width sweep, not a
# workload in the main AoS/SoA comparison, so it is not in DEFAULT_PROGRAMS
# -- but its fold/map split is exactly what the PLDI tables report, and the
# per-width contrast is a result in its own right.
#
# All four widths, so the sweep is complete. Int64 was briefly left out on
# the expectation that it duplicates MonoTree.hs; it does not. The two are
# comparable only in the MAP pass -- both map `Leaf x -> Leaf (x+1)` over
# an Int64 tree of similar size (MonoTree 2^23 = 8,388,608 leaves,
# Add1TreeInt64 9,227,465) -- and even there the tree SHAPES differ
# (MonoTree perfectly balanced, Add1TreeInt64 Fibonacci-shaped). Their
# folds are not comparable at all, and in any case Add1Tree's fold is
# `checksumTree`, a verification pass excluded from every table
# (VERIFICATION_PASSES), so what these four rows actually report is the
# add1Tree map at four integer widths -- a sweep MonoTree is not part of.
# Benchmark families that SHIP as one executable per timed pass (a shared
# base module plus <Family>_<pass>.hs files) but must still be REPORTED as
# one program -- same table, same rows -- exactly as when each was a single
# executable. Keyed by the program name the tables show; the value is the
# filename prefix its members share.
#
# OctTree predates this and keeps its own bespoke merge
# (_merge_octree_results), because that one also folds in ColorOctree,
# which is a separate program rather than a member of the family.
PROGRAM_MERGE_GROUPS: Dict[str, str] = {
    "PiecewiseFunctions.hs": "PiecewiseFunctions_",
}


def merge_group_members(program: str, prefix: str,
                        candidates: List[str]) -> List[str]:
    """The <Family>_<pass>.hs files present, in DEFAULT_PROGRAMS order.

    Order matters: it becomes the row order of the merged program's table,
    and DEFAULT_PROGRAMS lists these in the order the original combined
    program computed them -- so the merged table reads exactly as the
    single-executable one did. Anything not in DEFAULT_PROGRAMS is appended
    in sorted order. Empty when the family was not run (or was excluded),
    in which case nothing is merged and every program is left untouched."""
    present = [p for p in candidates if p.startswith(prefix) and p.endswith(".hs")]
    canonical = [p for p in DEFAULT_PROGRAMS if p in present]
    return canonical + sorted(p for p in present if p not in canonical)


def merge_pldi_program_groups(
        pldi_variant_results: Optional[Dict[str, Dict[str, BenchmarkResult]]],
        groups: Optional[Dict[str, str]] = None,
        ) -> Optional[Dict[str, Dict[str, BenchmarkResult]]]:
    """Fold each split family's per-pass entries back into ONE program
    entry, so the per-program tables render the family exactly as they did
    when it was a single executable: one table, one row per pass.

    Provenance is kept PER PASS (`pass_origin`), not merged into a single
    verdict: each row's number and its failure symbol come from the member
    that actually produced that pass, so one member failing blanks only its
    own row instead of the whole family's column."""
    if not pldi_variant_results:
        return pldi_variant_results
    groups = PROGRAM_MERGE_GROUPS if groups is None else groups
    out = dict(pldi_variant_results)
    for merged_name, prefix in groups.items():
        members = merge_group_members(merged_name, prefix, list(pldi_variant_results))
        if not members:
            continue
        # Which member owns each pass name, and in which order the rows
        # should appear -- learned across ALL configurations, so a pass
        # stays a row even in a configuration where its member failed.
        pass_owner: Dict[str, str] = {}
        configs: List[str] = []
        for member in members:
            for cfg, res in pldi_variant_results[member].items():
                if cfg not in configs:
                    configs.append(cfg)
                for pname in (res.passes or {}) if res is not None else {}:
                    pass_owner.setdefault(pname, member)
        merged_by_cfg: Dict[str, BenchmarkResult] = {}
        for cfg in configs:
            merged = BenchmarkResult(merged_name, cfg)
            merged.compile_success = True
            merged.run_success = True
            merged.passes = {}
            merged.pass_origin = {}
            contributors = []
            for pname, owner in pass_owner.items():
                res = pldi_variant_results[owner].get(cfg)
                merged.pass_origin[pname] = res
                if res is None:
                    continue
                if prov.verified_result(res) and res.passes and pname in res.passes:
                    merged.passes[pname] = res.passes[pname]
            for member in members:
                res = pldi_variant_results[member].get(cfg)
                if res is not None:
                    contributors.append(res)
                    if merged.adt_fields is None and res.adt_fields is not None:
                        merged.adt_fields = res.adt_fields
                        merged.adt_info = res.adt_info
                    if merged.arith_mode is None:
                        merged.arith_mode = res.arith_mode
                        merged.use_no_ran = res.use_no_ran
            merged.qualification = prov.synthesize_derived_status(
                cfg, merged_name, contributors)
            merged_by_cfg[cfg] = merged
        for member in members:
            out.pop(member, None)
        out[merged_name] = merged_by_cfg
    return out


#
# The arithmetic-intensity family is the same shape and is included for the
# same reason: one timed map pass (`arithKernel`) at four integer widths,
# with `checksumTree` as its verification fold (excluded from every table
# by VERIFICATION_PASSES). Both families therefore render map tables only.
# Built from the family constants themselves rather than retyped, so a
# width added to either family joins the PLDI matrix automatically instead
# of being silently left out of the tables (which is exactly how the
# arithmetic-intensity family came to be missing).
PLDI_EXTRA_PROGRAMS = list(ADD1TREE_WIDTH_PROGRAMS) + list(ARITHINTENSITY_WIDTH_PROGRAMS)

PLDI_ROW_LABELS: Dict[str, str] = {
    # Spelled out in full: this is the legend a reader decodes the compact
    # column symbols from, so it is the one place that must not itself
    # introduce an undefined abbreviation (no SBS, no TCO, no gcc-vec).
    # AoS/SoA are expanded in the legend caption.
    "aos_imm_notco": "AoS, recursive traversal, immutable cursors, "
                     "C tail-call optimization disabled",
    "aos_imm": "AoS, recursive traversal, immutable cursors",
    "aos_mut": "AoS, recursive traversal, mutable cursors",
    "aos_mut_notco": "AoS, recursive traversal, mutable cursors, "
                     "C tail-call optimization disabled",
    "aos_loop_gccvec_off": "AoS, loopified, C auto-vectorization disabled",
    "aos_loop_gccvec_on": "AoS, loopified, C auto-vectorization enabled",
    "soa_imm_notco": "SoA, recursive traversal, immutable cursors, "
                     "C tail-call optimization disabled",
    "soa_imm": "SoA, recursive traversal, immutable cursors",
    "soa_mut": "SoA, recursive traversal, mutable cursors",
    "soa_mut_notco": "SoA, recursive traversal, mutable cursors, "
                     "C tail-call optimization disabled",
    "soa_loop_gccvec_off_sbs_off":
        "SoA, loopified, C auto-vectorization disabled, "
        "no selective buffer sharing",
    "soa_loop_gccvec_off_sbs_on":
        "SoA, loopified, C auto-vectorization disabled, "
        "selective buffer sharing",
    "soa_loop_gccvec_on_sbs_on":
        "SoA, loopified, C auto-vectorization enabled, "
        "selective buffer sharing",
    "soa_loop_gccvec_off_sbs_on_gibvec_on":
        "SoA, loopified, C auto-vectorization disabled, "
        "selective buffer sharing, Gibbon SIMD vectorization",
    "soa_loop_gccvec_on_sbs_on_gibvec_on":
        "SoA, loopified, C auto-vectorization enabled, "
        "selective buffer sharing, Gibbon SIMD vectorization",
}


# Compact column symbols for the PLDI per-program fold/map tables.  The
# scheme is systematic so a reader can decode an unfamiliar column:
#   base letter -- A = array-of-structs (AoS), S = struct-of-arrays (SoA)
#   subscript   -- Gibbon-side codegen: r recursive traversal, i immutable
#                  cursors, m mutable cursors, \ell loopified, b selective
#                  buffer sharing, v Gibbon SIMD vectorization
#   superscript -- the C-compiler knob that differs from the column's
#                  default: +av leaves C auto-vectorization ON (loopified
#                  columns disable it), \neg t disables C tail-call opt.
# Superscripts are wrapped in \scriptscriptstyle: at plain superscript
# size the binary + is set as large as the subscript letters and reads as
# part of the name rather than as a modifier.
# PLDI_ROW_LABELS keeps the long prose spelling of each configuration;
# _table_pldi_legend pairs the two so the symbols stay decodable from
# inside the paper itself.
PLDI_COL_SYMBOLS: Dict[str, str] = {
    "aos_imm_notco": "$A_{ri}^{\\scriptscriptstyle \\neg t}$",
    "aos_imm":       "$A_{ri}$",
    "aos_mut":       "$A_{rm}$",
    "aos_mut_notco": "$A_{rm}^{\\scriptscriptstyle \\neg t}$",
    "aos_loop_gccvec_off": "$A_{\\ell}$",
    "aos_loop_gccvec_on":  "$A_{\\ell}^{\\scriptscriptstyle +av}$",
    "soa_imm_notco": "$S_{ri}^{\\scriptscriptstyle \\neg t}$",
    "soa_imm":       "$S_{ri}$",
    "soa_mut":       "$S_{rm}$",
    "soa_mut_notco": "$S_{rm}^{\\scriptscriptstyle \\neg t}$",
    "soa_loop_gccvec_off_sbs_off":          "$S_{\\ell}$",
    "soa_loop_gccvec_off_sbs_on":           "$S_{\\ell b}$",
    "soa_loop_gccvec_on_sbs_on":            "$S_{\\ell b}^{\\scriptscriptstyle +av}$",
    "soa_loop_gccvec_off_sbs_on_gibvec_on": "$S_{\\ell bv}$",
    "soa_loop_gccvec_on_sbs_on_gibvec_on":  "$S_{\\ell bv}^{\\scriptscriptstyle +av}$",
}


# ---------------------------------------------------------------------------
# Per-pass DELTA tables: what each optimization actually bought, in seconds.
#
# Every entry is (layout, symbol, baseline config, feature config, legend
# text). Each symbol's subscript names the feature using the SAME letters
# the configuration symbols use (PLDI_COL_SYMBOLS): m mutable cursors,
# \ell loopified, b selective buffer sharing, v Gibbon SIMD vectorization,
# av the C auto-vectorizer (spelled `+av` as a superscript there), t the C
# tail-call optimization (`\neg t` there). A reader who has learned the
# configuration legend can therefore read a delta column without relearning
# anything. The value rendered is (BASELINE - FEATURE) / FEATURE as a
# percentage -- identically (speedup - 1) x 100 -- so a POSITIVE number
# always means "enabling this made the pass faster", in every column of
# every table. The denominator is the FEATURE, not the baseline: against
# the baseline the scale saturates (a 5x win reads 80%, an 8x win 87.5%),
# which compresses exactly the large improvements these tables exist to
# size. See `_signed_percent` for the full argument. Either way the numbers
# are scale-free and so comparable across passes whose absolute times
# differ by orders of magnitude.
#
# That uniform orientation is a deliberate normalization of the request,
# which spelled three of the twelve columns feature-first (mutable cursors,
# selective buffer sharing, and Gibbon-vec-on-top-of-auto-vec) and asked for
# absolute values |x - y|. Magnitudes are exactly as requested; what changes
# is that the sign survives -- and it has to, because two of the columns ask
# whether one vectorizer HINDERS or HELPS the other, which an absolute value
# cannot express.
PLDI_DELTA_COLUMNS_FOLD: List[Tuple[str, str, str, str, str]] = [
    ("AoS", "$\\Delta^{A}_{m}$", "aos_imm_notco", "aos_mut_notco",
     "What mutable cursors alone bought vanilla Gibbon. BOTH sides have the "
     "C tail-call optimization disabled, so this isolates mutability: "
     "measured against $A_{ri}$ (tail calls ENABLED) it would report "
     "mutability plus whatever tail calls contributed, and mutability is "
     "precisely what puts the traversal in tail position for them to work "
     "on"),
    ("AoS", "$\\Delta^{A}_{t}$", "aos_mut_notco", "aos_mut",
     "What the C tail-call optimization bought AoS mutable. Mutable cursors "
     "are what leave the traversal in tail position, so this optimization "
     "has something to work on only once they are in use"),
    ("SoA", "$\\Delta^{S}_{m}$", "soa_imm_notco", "soa_mut_notco",
     "What mutable cursors alone bought SoA; as in AoS, both sides have the "
     "C tail-call optimization disabled so the two effects are not "
     "conflated"),
    ("SoA", "$\\Delta^{S}_{t}$", "soa_mut_notco", "soa_mut",
     "What the C tail-call optimization bought SoA mutable; as in AoS, it is "
     "mutability that leaves the traversal in tail position"),
]

PLDI_DELTA_COLUMNS_MAP: List[Tuple[str, str, str, str, str]] = [
    # Both layouts' cursor/TCO columns carry forward from the fold table.
    PLDI_DELTA_COLUMNS_FOLD[0],
    PLDI_DELTA_COLUMNS_FOLD[1],
    ("AoS", "$\\Delta^{A}_{\\ell}$", "aos_mut", "aos_loop_gccvec_off",
     "What loopification gained over recursion in AoS mutable"),
    ("AoS", "$\\Delta^{A}_{av}$", "aos_loop_gccvec_off", "aos_loop_gccvec_on",
     "What the C auto-vectorizer added to loopified AoS mutable"),
    PLDI_DELTA_COLUMNS_FOLD[2],
    PLDI_DELTA_COLUMNS_FOLD[3],
    ("SoA", "$\\Delta^{S}_{\\ell}$", "soa_mut", "soa_loop_gccvec_off_sbs_off",
     "What loopification gained over recursion in SoA mutable"),
    ("SoA", "$\\Delta^{S}_{b}$", "soa_loop_gccvec_off_sbs_off",
     "soa_loop_gccvec_off_sbs_on",
     "What selective buffer sharing added over SoA loopified"),
    ("SoA", "$\\Delta^{S}_{av}$", "soa_loop_gccvec_off_sbs_on",
     "soa_loop_gccvec_on_sbs_on",
     "What the C auto-vectorizer added over SoA loopified $+$ selective "
     "buffer sharing"),
    ("SoA", "$\\Delta^{S}_{v}$", "soa_loop_gccvec_off_sbs_on",
     "soa_loop_gccvec_off_sbs_on_gibvec_on",
     "What Gibbon SIMD vectorization added over SoA loopified $+$ selective "
     "buffer sharing"),
    ("SoA", "$\\Delta^{S}_{av|v}$", "soa_loop_gccvec_off_sbs_on_gibvec_on",
     "soa_loop_gccvec_on_sbs_on_gibvec_on",
     "Whether the C auto-vectorizer HELPS ($>0$) or HINDERS ($<0$) Gibbon "
     "vectorization --- both are already on, and this turns the C one on top"),
    ("SoA", "$\\Delta^{S}_{v|av}$", "soa_loop_gccvec_on_sbs_on",
     "soa_loop_gccvec_on_sbs_on_gibvec_on",
     "Whether Gibbon vectorization HELPS ($>0$) or HINDERS ($<0$) the C "
     "auto-vectorizer --- the mirror of the column above, adding Gibbon's "
     "vectorizer on top of the C one"),
]


def _signed_sig4(value: Optional[float]) -> str:
    """A signed delta at 4 significant digits, with an explicit `+' so the
    direction is legible at a glance in a column of mixed signs."""
    if value is None:
        return "--"
    body = _sig4(abs(value))
    return ("$-$" if value < 0 else "+") + body


def _signed_percent(baseline: Optional[float],
                    feature: Optional[float]) -> str:
    """(baseline - feature) / FEATURE, as a signed percentage.

    Percent of the FEATURE's own time, which is identically
    (speedup - 1) x 100. The denominator was the baseline, which is the
    natural reading of "this cut N% off the time" but SATURATES: a 5x win is
    80%, an 8x win 87.5%, a 100x win 99%, so large improvements compress into
    a narrow band and stop being distinguishable. Against the feature the
    scale is unbounded -- 8x reads +700% -- which is what the delta tables
    are for.

    The trade is that SLOWDOWNS now saturate instead, approaching -100% as
    the feature gets arbitrarily worse. That is the better way round here:
    these columns exist to size wins, and a slowdown is adequately conveyed
    by any negative number.

    Positive still means the feature made the pass faster. A zero (or
    negative) feature time has no meaningful percentage, so it renders `--'
    rather than dividing."""
    if baseline is None or feature is None or feature <= 0:
        return "--"
    return _signed_sig4((baseline - feature) / feature * 100.0) + "\\%"


def _pldi_delta_cell(results_for_program: Dict[str, BenchmarkResult],
                     baseline_cfg: str, feature_cfg: str,
                     pass_name: str) -> str:
    """(BASELINE - FEATURE) / FEATURE for one pass, as a percentage, or `--'.

    A delta needs BOTH measurements, so unlike a timing cell it cannot name
    a single failure mode -- if either side is missing or unverified the
    cell is `--' and the per-configuration reason is in the timing table
    above it (and in the driver's warning list)."""
    _btext, base = _pldi_cell(results_for_program.get(baseline_cfg), pass_name)
    _ftext, feat = _pldi_cell(results_for_program.get(feature_cfg), pass_name)
    return _signed_percent(base, feat)


def _render_pldi_delta_table(f, program: str,
                             results_for_program: Dict[str, BenchmarkResult],
                             columns: List[Tuple[str, str, str, str, str]],
                             pass_type: str, kind: str) -> None:
    pass_names = _pldi_pass_names(results_for_program, pass_type)
    if not pass_names:
        return
    prog_stem = program.replace(".hs", "")
    prog_display = _tex_escape(prog_stem)
    groups: List[Tuple[str, List[Tuple[str, str, str, str, str]]]] = []
    for col in columns:
        if not groups or groups[-1][0] != col[0]:
            groups.append((col[0], []))
        groups[-1][1].append(col)
    f.write(f"% -- PLDI {kind} delta table: {prog_stem} --\n")
    f.write("\\begin{table}[t]\n\\centering\n")
    f.write(
        f"\\caption{{What each optimization bought, per {kind} pass, for "
        f"\\texttt{{{prog_display}}} (percent; companion to "
        f"Table~\\ref{{tab:pldi-{kind}-{prog_stem}}}). Every column is "
        "(\\emph{baseline} $-$ \\emph{feature enabled}) / \\emph{feature "
        "enabled}, which is identically $(\\text{speedup} - 1) \\times 100$: "
        "$+100\\%$ means the feature made the pass twice as fast, $+700\\%$ "
        "eight times as fast, and a negative value means it made the pass "
        "slower. Percentages are scale-free, so they are comparable across "
        "passes whose absolute times differ widely. "
        "See "
        "Table~\\ref{tab:pldi-delta-legend} for each column's exact "
        "definition. `--' marks a pass where either side of the difference "
        "was not measured; the timing table above says which.}\n")
    f.write(f"\\label{{tab:pldi-{kind}-delta-{prog_stem}}}\n")
    if len(columns) > 8:
        f.write("\\footnotesize\\gibbonnumfont\n"
                "\\setlength{\\tabcolsep}{4pt}\n")
    else:
        f.write("\\small\\gibbonnumfont\n")
    f.write("\\begin{tabular}{l" + " r" * len(columns) + "}\n\\toprule\n")
    f.write("\\textbf{Pass}"
            + "".join(" & \\multicolumn{%d}{c}{\\textbf{%s}}" % (len(g), lbl)
                      for lbl, g in groups)
            + " \\\\\n")
    col = 2
    rules = []
    for _lbl, group in groups:
        rules.append("\\cmidrule(lr){%d-%d}" % (col, col + len(group) - 1))
        col += len(group)
    f.write("".join(rules) + "\n")
    f.write("".join(" & %s" % sym for _l, sym, _b, _fe, _d in columns)
            + " \\\\\n\\midrule\n")
    for pname in pass_names:
        cells = [_pldi_delta_cell(results_for_program, base, feat, pname)
                 for _l, _sym, base, feat, _d in columns]
        f.write(_tex_escape(pname) + "".join(" & %s" % c for c in cells)
                + " \\\\\n")
    f.write("\\bottomrule\n\\end{tabular}\n\\end{table}\n\n")


def _table_pldi_fold_deltas(f, program: str,
                            results_for_program: Dict[str, BenchmarkResult]) -> None:
    _render_pldi_delta_table(f, program, results_for_program,
                             PLDI_DELTA_COLUMNS_FOLD, "fold", "fold")


def _table_pldi_map_deltas(f, program: str,
                           results_for_program: Dict[str, BenchmarkResult]) -> None:
    _render_pldi_delta_table(f, program, results_for_program,
                             PLDI_DELTA_COLUMNS_MAP, "map", "map")


def _table_pldi_delta_legend(f) -> None:
    r"""Emitted once, beside the configuration legend: what each $\Delta$
    column means and exactly which two configurations it subtracts."""
    f.write("% -- PLDI delta-column legend --\n")
    f.write("\\begin{table}[t]\n\\centering\n")
    f.write(
        "\\caption{Key for the per-pass delta tables. Each column is "
        "(\\emph{baseline} $-$ \\emph{feature enabled}) / \\emph{feature enabled}, "
        "expressed as a percentage, which is identically "
        "$(\\text{speedup} - 1) \\times 100$: $+100\\%$ means the feature made the "
        "pass twice as fast, $+700\\%$ eight times as fast, and a negative value "
        "means it made the pass slower. Normalizing to the FEATURE rather than "
        "the baseline is deliberate -- against the baseline the scale "
        "saturates, with a 5$\\times$ win reading 80\\% and an 8$\\times$ win "
        "87.5\\%, so large improvements compress into a narrow band and stop "
        "being distinguishable. Superscript names the layout "
        "($A$ = array-of-structs, $S$ = struct-of-arrays); subscript names "
        "the feature. The two $|$-subscripted columns ask whether one "
        "vectorizer helps or hinders the other, which is why these are signed "
        "differences rather than magnitudes. Table~\\ref{tab:pldi-legend} "
        "defines the configuration symbols themselves.}\n")
    f.write("\\label{tab:pldi-delta-legend}\n\\small\\gibbonnumfont\n")
    f.write("\\begin{tabular}{c p{0.82\\linewidth}}\n\\toprule\n")
    f.write("\\textbf{Column} & \\textbf{Meaning: (baseline $-$ feature) / feature} "
            "\\\\\n\\midrule\n")
    seen = set()
    previous_layout = None
    def _formula(base_cfg: str, feat_cfg: str) -> str:
        """The column's formula, DERIVED from its configuration pair.

        Previously each legend spelled its own formula out by hand. Twelve
        hand-written copies of the arithmetic is twelve things to forget when
        the arithmetic changes -- and when the denominator moved from the
        baseline to the feature, every one of them would have silently
        contradicted the numbers above it."""
        b = PLDI_COL_SYMBOLS.get(base_cfg, base_cfg).strip("$")
        ftr = PLDI_COL_SYMBOLS.get(feat_cfg, feat_cfg).strip("$")
        return f"$({b} - {ftr}) / {ftr}$"

    for layout, sym, _base, _feat, desc in (
            PLDI_DELTA_COLUMNS_FOLD + PLDI_DELTA_COLUMNS_MAP):
        if sym in seen:
            continue
        if previous_layout is not None and layout != previous_layout:
            f.write("\\addlinespace\n")
        previous_layout = layout
        seen.add(sym)
        f.write("%s & %s: %s \\\\\n" % (sym, desc, _formula(_base, _feat)))
    f.write("\\bottomrule\n\\end{tabular}\n\\end{table}\n\n")


def collect_pldi_variant_results(programs_dir: Path, out_dir: Path, cc: str,
                                 force: bool, gibbon_exe: Optional[str],
                                 iterations: int = 1,
                                 c_arith_mode: str = DEFAULT_C_ARITH_MODE,
                                   simd_isa: str = DEFAULT_SIMD_ISA,
                                   pin_cpu: Optional[int] = None,
                                 programs: Optional[List[str]] = None,
                                 ) -> Dict[str, Dict[str, BenchmarkResult]]:
    """Compiles and runs every PLDI_MAP_CONFIGS variant for every curated
    program, using the same compile_one/run_exe/qualify_variant path as
    every other table in this file (see collect_arithintensity_width_results
    for the identical shape). Unlike the width tables, `iterations` is meant
    to be the driver's real --iterations value (passed explicitly by the
    caller), not left at the 1-iteration default: this table's numbers are
    intended for the paper, not just a structural/correctness check.

    Returns {program: {config_name: BenchmarkResult}}."""
    _validate_c_arith_mode(c_arith_mode)
    manifest = default_oracle_manifest()
    # Same source scan the main campaign runs, so these results carry
    # adt_fields and the derived dead_ratio.  `parse_passes` recovers `uses`
    # from the executable's own banner, but the ADT's total field count comes
    # only from the SOURCE -- without this the per-program tables' Uses and
    # Dead% columns have no denominator and render "--" for every row.
    source_cls_all = build_source_classification(programs_dir)
    program_list = programs if programs is not None else DEFAULT_PROGRAMS
    results: Dict[str, Dict[str, BenchmarkResult]] = {}
    for program in program_list:
        results[program] = {}
        for layout, configs in PLDI_MAP_CONFIGS.items():
            src_dir = "AOS" if layout == "aos" else "SOA"
            source = programs_dir / src_dir / program
            for cfg_name, cfg_kwargs in configs.items():
                res = BenchmarkResult(program, cfg_name)
                res.arith_mode = c_arith_mode
                res.use_no_ran = program_uses_no_ran(program)
                if not source.exists():
                    res.compile_success = False
                    res.error_message = "source not found: %s" % source
                    res.qualification = qualify_variant(
                        program, cfg_name, source, False, res.error_message,
                        False, None, None, manifest=manifest)
                    results[program][cfg_name] = res
                    continue
                ok, compile_time, err = compile_one(source, cfg_name, out_dir, force,
                                                    use_no_ran=program_uses_no_ran(program),
                                                    c_arith_mode=c_arith_mode,
                                                    simd_isa=simd_isa,
                                                    **cfg_kwargs)
                res.compile_success = ok
                res.compile_time = compile_time
                exe = out_dir / f"{source.stem}.{cfg_name}.exe"
                c_file = out_dir / f"{source.stem}.{cfg_name}.c"
                if ok:
                    run_ok, elapsed, out, err2, rc = run_exe(exe, iterations, use_iterate_flag=True, pin_cpu=pin_cpu)
                    res.run_success = run_ok
                    res.run_returncode = rc
                    res.output = out
                    res.exec_wall_time = elapsed
                    if run_ok and out:
                        res.passes = parse_passes(out)
                    apply_source_classification(
                        res, source_cls_all.get(program,
                                                {"adt_fields": None, "adt_info": None,
                                                 "pass_types": {}, "pass_uses": {}}))
                    progress().advance()
                    res.qualification = qualify_variant(
                        program, cfg_name, source, ok, err, run_ok, err2, out,
                        manifest=manifest, c_file=c_file if c_file.exists() else None,
                        expect_vectorization=cfg_kwargs.get("enable_vectorization", False))
                else:
                    res.qualification = qualify_variant(
                        program, cfg_name, source, False, err, False, None, None,
                        manifest=manifest)
                results[program][cfg_name] = res
    return results


def _sig4(value: Optional[float]) -> str:
    """A number at 4 significant digits.  %.4g switches to exponent form
    below 1e-4, which reads badly in a table, so that case is re-rendered as
    LaTeX math ($1.234 \\times 10^{-5}$) rather than left as `1.234e-05'."""
    if value is None:
        return "--"
    s = "%.4g" % value
    if "e" not in s and "E" not in s:
        return s
    mant, _, exp = s.lower().partition("e")
    return "$%s \\times 10^{%d}$" % (mant, int(exp))


def _pldi_pass_names(results_for_program: Dict[str, BenchmarkResult], pass_type: str) -> List[str]:
    """All distinct pass names of the given type ("fold"/"map") that ANY
    variant of this program reported, in first-seen order."""
    names: List[str] = []
    seen = set()
    for res in results_for_program.values():
        if res is None or not res.passes:
            continue
        for pname, pdata in res.passes.items():
            if is_verification_pass(pname):
                continue
            if pdata.get("pass_type") == pass_type and pname not in seen:
                seen.add(pname)
                names.append(pname)
    return names


# A cell with no number says WHICH failure it was, rather than collapsing
# every one to a single dash -- "did not compile" and "compiled, ran, and
# computed the wrong answer" are very different claims about a
# configuration, and a reader cannot tell them apart from one symbol.
# The driver still prints the full per-configuration detail through
# pldi_qualification_warnings(); these are the table's shorthand.
PLDI_SYM_COMPILE_FAIL = "*"    # never compiled
PLDI_SYM_RUN_FAIL = "-"        # compiled, but the executable failed to run
PLDI_SYM_WRONG_OUTPUT = "**"   # ran, but its output did not match the oracle
PLDI_SYM_NOT_MEASURED = "?"    # not run at all, or no oracle to compare against
# Ran and died on the C stack.  Distinguished from a generic run failure
# because it is not a defect: an immutable-cursor or tail-call-disabled
# configuration recurses once per element, and the curated inputs are sized
# for the loop that mutable cursors plus tail calls produce.  List.hs builds
# 100,000,000 elements, so those configurations need a stack no setting can
# provide -- the RTS already raises RLIMIT_STACK to 4GB successfully and it is
# nowhere near enough.  That is the very effect these columns exist to show,
# so the table should say so rather than report an unexplained failure.
PLDI_SYM_STACK_EXHAUSTED = "$\\ddagger$"


def _pldi_failure_symbol(res: Optional[BenchmarkResult]) -> str:
    """Which of the four no-number cases this result is.

    Read off QualificationStatus.label, which is the single place the
    driver decides what happened to a variant -- so the table cannot drift
    from the warning list or the JSON report."""
    if res is None:
        return PLDI_SYM_NOT_MEASURED
    st = getattr(res, "qualification", None)
    if st is None:
        return PLDI_SYM_NOT_MEASURED
    label = st.label
    if label == "COMPILE-FAIL":
        return PLDI_SYM_COMPILE_FAIL
    if label == "RUN-FAIL":
        rc = getattr(res, "run_returncode", None)
        # Python reports a signal death as a negative return code; a shell
        # would report 128+signal.  Accept both spellings of SIGSEGV.
        if rc in (-11, 139):
            return PLDI_SYM_STACK_EXHAUSTED
        return PLDI_SYM_RUN_FAIL
    # EMPTY-OUTPUT is grouped with WRONG: the program ran and what it
    # printed did not match what the oracle expected. Printing nothing is
    # one way for that to be true, not a separate kind of event.
    if label in ("WRONG", "EMPTY-OUTPUT"):
        return PLDI_SYM_WRONG_OUTPUT
    # VERIFIED-but-no-timing, NO-ORACLE, UNVERIFIED, NOT-REQUIRED.
    return PLDI_SYM_NOT_MEASURED


def _pldi_cell(res: Optional[BenchmarkResult],
               pass_name: str) -> Tuple[str, Optional[float]]:
    """A single timing cell, as (rendered text, comparable value).

    A cell with no measurement renders the symbol naming its failure (see
    _pldi_failure_symbol) and carries no value. The value is what
    _highlight_row_extremes ranks; it is None exactly when the cell carries
    no number, so a failed configuration can never be reported as a row's
    fastest or slowest."""
    # A merged family (one executable per timed pass) carries the member
    # result that produced each pass, so a member's failure blanks only its
    # own row rather than the family's whole column.
    origin = getattr(res, "pass_origin", None) if res is not None else None
    if origin is not None and pass_name in origin:
        res = origin[pass_name]
    if not prov.verified_result(res) or not res.passes or pass_name not in res.passes:
        return _pldi_failure_symbol(res), None
    t = res.passes[pass_name].get("median_time")
    if t is None:
        return PLDI_SYM_NOT_MEASURED, None
    return _sig4(t), t


# Row-extreme highlighting for the per-program tables. Defined in the
# generated .tex itself (see write_latex_tables) so \input-ing it needs
# only xcolor, no palette options.
COLOR_FASTEST = "gibbonfast"   # forest green
COLOR_SLOWEST = "gibbonslow"   # red


def _highlight_row_extremes(cells: List[Tuple[str, Optional[float]]]) -> List[str]:
    """Colour the fastest cell of a row green and the slowest red.

    Ranks only cells that actually carry a number, so `--' (failed or
    unverified) is never mistaken for "fastest". Colours nothing when the
    row has fewer than two distinct values -- with one measurement, or with
    every configuration identical, "fastest" and "slowest" would name the
    same cell and the colours would assert a difference that is not there."""
    values = [v for _, v in cells if v is not None]
    if len(values) < 2 or min(values) == max(values):
        return [text for text, _ in cells]
    lo, hi = min(values), max(values)
    out = []
    for text, value in cells:
        if value == lo:
            out.append("\\textcolor{%s}{%s}" % (COLOR_FASTEST, text))
        elif value == hi:
            out.append("\\textcolor{%s}{%s}" % (COLOR_SLOWEST, text))
        else:
            out.append(text)
    return out


def _table_pldi_legend(f) -> None:
    """Emitted once, ahead of the per-program tables, so the compact column
    symbols used by every one of them are decodable from the paper."""
    f.write("% -- PLDI configuration legend --\n")
    f.write("\\begin{table}[t]\n\\centering\n")
    f.write(
        "\\caption{Configuration key for the per-program fold and map tables. "
        + simd_isa_caption_note() +
        "Base letter: $A$ = array-of-structs (AoS), $S$ = struct-of-arrays (SoA). "
        "Subscripts name the Gibbon-side code generation "
        "($r$ recursive traversal, $i$ immutable cursors, $m$ mutable cursors, "
        "$\\ell$ loopified, $b$ selective buffer sharing, "
        "$v$ Gibbon SIMD vectorization). "
        "Superscripts name the C-compiler knob that differs from that column's "
        "default: $+av$ leaves C auto-vectorization enabled (loopified columns "
        "disable it), $\\neg t$ disables C tail-call optimization. "
        "The first three configurations of each layout carry the fold passes; "
        "map tables additionally report the loopified configurations.}\n")
    f.write("\\label{tab:pldi-legend}\n\\small\\gibbonnumfont\n")
    # p{} rather than l on the description: spelling every configuration
    # out in full (no SBS/TCO shorthand) makes the longest entries wider
    # than the text block, so that column has to wrap.
    f.write("\\begin{tabular}{c p{0.72\\linewidth}}\n\\toprule\n")
    f.write("\\textbf{Symbol} & \\textbf{Configuration} \\\\\n\\midrule\n")
    for i, layout in enumerate(("aos", "soa")):
        if i:
            f.write("\\addlinespace\n")
        for key in PLDI_MAP_CONFIGS[layout]:
            f.write("%s & %s \\\\\n" % (PLDI_COL_SYMBOLS.get(key, _tex_escape(key)),
                                        _tex_escape(PLDI_ROW_LABELS.get(key, key))))
    f.write("\\bottomrule\n\\end{tabular}\n\\end{table}\n\n")


def _pldi_best_of_layout_speedup(
        cells: List[Tuple[str, Optional[float]]],
        col_groups: List[Tuple[str, List[str]]]) -> str:
    """Fastest AoS configuration in this row over the fastest SoA one.

    Deliberately best-vs-best rather than a fixed pair: each layout is
    represented by whatever configuration actually served it best for THIS
    pass, so the ratio is not hostage to one configuration happening to be
    a poor showing for a particular kernel. Only measured cells are
    considered (a failed configuration has no value and cannot win), and
    the ratio is `--' unless BOTH layouts have at least one measurement --
    comparing a layout's best against a layout with nothing measured would
    be a fabricated comparison."""
    if len(col_groups) != 2:
        return "--"
    bests: List[Optional[float]] = []
    start = 0
    for _, group in col_groups:
        values = [v for _, v in cells[start:start + len(group)] if v is not None]
        bests.append(min(values) if values else None)
        start += len(group)
    aos, soa = bests
    if aos is None or soa is None or soa <= 0:
        return "--"
    return _spd_cell(aos / soa)


def _pldi_field_usage(results_for_program: Dict[str, BenchmarkResult],
                      pname: str) -> Tuple[str, str]:
    """This pass's field usage: "used/total" and the dead-field percentage.

    Read from whichever configuration recorded it -- the ADT and the pass are
    properties of the SOURCE, identical across configurations, so the first
    configuration that parsed them answers for all of them.  Same derivation
    as the legacy per-program table: `adt_total` is recovered from
    uses/(1-dead_ratio) when the annotation itself is absent.
    """
    uses = dead_r = adt_total = None
    for res in results_for_program.values():
        pdata = (getattr(res, "passes", None) or {}).get(pname) if res else None
        if not pdata:
            continue
        if uses is None:
            uses = pdata.get("uses")
        if dead_r is None:
            dead_r = pdata.get("dead_ratio")
        if adt_total is None:
            adt_total = pdata.get("adt_total") or getattr(res, "adt_fields", None)
    if adt_total is None and uses is not None and dead_r is not None and (1 - dead_r) > 0:
        adt_total = int(round(uses / (1 - dead_r)))
    uses_s = (f"{uses}/{adt_total}"
              if (uses is not None and adt_total is not None) else "--")
    dead_s = (f"{100.0 * dead_r:.0f}\\%" if dead_r is not None else "--")
    return uses_s, dead_s


def _pldi_shared_buffers(results_for_program: Dict[str, BenchmarkResult],
                         pname: str) -> Tuple[str, str]:
    """A MAP pass's shared BUFFERS: "shared/total" and the percentage.

    Buffers, not fields. A fully factored SoA value is stored as one buffer
    per scalar field PLUS the constructor stream, and a dependence-free map
    always shares that constructor stream too -- it rebuilds the same shape,
    so the tags are copied unchanged. Counting only fields therefore
    understated every map by exactly one buffer and, for a single-field ADT,
    reported 0 shared where the compiler in fact shares half the data.

    Confirmed against the generated C for PiecewiseFunctions: with selective
    buffer sharing on, `selective_share_buf0` (the constructor stream) and
    `buf2`..`buf6` appear -- six of the seven buffers -- while `buf1`, the
    coefficient the map actually rewrites, does not.

    The source annotation `shared=N` records the SCALAR fields left
    unmodified, which is what is directly readable from the pass body; the
    constructor stream is added here because it is a property of the layout,
    not of the pass.
    """
    shared = slots = total_bufs = None
    for res in results_for_program.values():
        pdata = (getattr(res, "passes", None) or {}).get(pname) if res else None
        if pdata:
            if shared is None:
                shared = pdata.get("shared")
            if slots is None:
                slots = pdata.get("shared_slots")
        info = (getattr(res, "adt_info", None) or {}) if res else {}
        if total_bufs is None:
            total_bufs = info.get("soa_total_buffers")
        if slots is None:
            slots = info.get("scalar_field_slots")
    # One buffer per scalar field plus the constructor stream. Prefer the
    # parser's own total; fall back to slots+1 if it did not report one.
    if total_bufs is None and slots is not None:
        total_bufs = slots + 1
    if shared is None or not total_bufs:
        return "--", "--"
    shared_bufs = shared + 1          # + the constructor stream
    return (f"{shared_bufs}/{total_bufs}",
            f"{100.0 * shared_bufs / total_bufs:.0f}\\%")


def _render_pldi_table(f, program: str, results_for_program: Dict[str, BenchmarkResult],
                       col_groups: List[Tuple[str, List[str]]],
                       pass_type: str, kind: str) -> None:
    """Shared renderer for _table_pldi_fold/_table_pldi_map: one table per
    program, rows = that program's passes of the given type, columns =
    compiled configuration, grouped under AoS/SoA spanning headers.  Columns
    carry the compact PLDI_COL_SYMBOLS names (see _table_pldi_legend), which
    is what keeps 13 configurations inside the text width -- the long prose
    labels are what made an earlier rows=configuration draft overflow."""
    pass_names = _pldi_pass_names(results_for_program, pass_type)
    if not pass_names:
        return
    keys = [k for _, group in col_groups for k in group]
    prog_stem = program.replace(".hs", "")
    prog_display = _tex_escape(prog_stem)
    f.write(f"% -- PLDI {kind} table: {prog_stem} --\n")
    f.write("\\begin{table}[t]\n\\centering\n")
    f.write(
        f"\\caption{{Per-pass {kind} performance for \\texttt{{{prog_display}}}. "
        + ran_caption_note(program) +
        "Times are median per iteration (s), 4 significant digits. "
        "Columns are compiled configurations; see Table~\\ref{tab:pldi-legend} "
        "for the symbol key. "
        + simd_isa_caption_note() +
        "In each row the fastest configuration is "
        "\\textcolor{" + COLOR_FASTEST + "}{green} and the slowest "
        "\\textcolor{" + COLOR_SLOWEST + "}{red}. "
        + ("\\textbf{$\\Sigma_b$} is the BUFFERS this pass leaves unmodified, "
           "out of the fully factored value's total, and "
           "\\textbf{$\\Sigma_b\\%$} that as a fraction. It is read from the "
           "pass's own source annotation -- a property of what the pass "
           "WRITES, and therefore an upper bound on what selective buffer "
           "sharing ($b$) could exploit, NOT a measurement of what the "
           "optimization achieved. Whether sharing fired is the "
           "$\\Delta^{S}_{b}$ column of the companion delta table: a pass can "
           "read $\\Sigma_b$ near 100\\% and $\\Delta^{S}_{b}$ near zero, "
           "which is what a traversal that declined loopification looks like "
           "-- sharing is implemented on the loopified form, so a pass that "
           "is not loopified is not shared either. A factored "
           "value is one buffer per scalar field plus the constructor "
           "stream, and a dependence-free map shares that constructor stream "
           "too -- it rebuilds the same shape, so the tags are copied "
           "unchanged. Counting fields alone would understate every map by "
           "one buffer. A map copies every field into the output region, so "
           "\"fields used\" is vacuously all of them and distinguishes "
           "nothing; what separates one map from another is how much of the "
           "data it merely COPIES. Recursive child fields are not buffers "
           "and are excluded from both counts. "
           if pass_type == "map" else
           "\\textbf{Uses} is the fields this pass accesses out of the benchmark "
           "ADT's total (recursive and non-recursive alike), and \\textbf{Dead\\%} "
           "the fraction it never touches -- the quantity a struct-of-arrays "
           "layout exists to exploit, since an unused field costs an AoS "
           "traversal bandwidth it cannot avoid. ") +
        "$A^{\\min}$/$S^{\\min}$ divides that row's fastest AoS configuration "
        "by its fastest SoA one, so each layout is represented by whichever "
        "configuration actually served this pass best; ${>}1{\\times}$ means "
        "SoA is faster. The minimum is taken over the columns THIS table "
        "shows and no others, so the ratio can be checked against the row "
        "above it. "
        + ("Those columns are the recursive configurations only: the "
           "loopified pair Table~\\ref{tab:summary} contrasts is absent "
           "here, because nothing in a fold is loopifiable. The two tables "
           "therefore compare different binaries of the same source, and "
           "where a program's two layouts sit within a few percent of each "
           "other that is enough to reverse which one leads. "
           if pass_type == "fold" else
           "Those columns include the pair Table~\\ref{tab:summary} "
           "contrasts, but that table reports a pass-SUM per program while "
           "each row here is one pass, so a program with several map passes "
           "can lead here and trail there. ")
        + "A cell with no time names its failure: "
        "`" + PLDI_SYM_COMPILE_FAIL + "' did not compile, "
        "`" + PLDI_SYM_RUN_FAIL + "' compiled but the executable failed to run, "
        "`" + PLDI_SYM_WRONG_OUTPUT + "' ran but its output did not match the "
        "oracle (an empty output included), "
        "`" + PLDI_SYM_STACK_EXHAUSTED + "' exhausted the C stack, and "
        "`" + PLDI_SYM_NOT_MEASURED + "' was not measured -- either not run in "
        "this campaign or having no registered oracle to check it against. "
        "A `" + PLDI_SYM_STACK_EXHAUSTED + "' is a RESULT, not a defect: that "
        "configuration recurses once per element where mutable cursors and "
        "tail calls produce a loop, and the curated inputs are sized for the "
        "loop. "
        "The benchmark driver prints a warning naming each one.}\n")
    # The 6-column fold tables sit at \small, exactly like the other
    # per-program tables; only the 13-column map tables step down one size
    # (and tighten \tabcolsep, which is local to this table environment) so
    # they still fit the text width without a \resizebox rescaling the font
    # out of step with the rest of the paper.
    f.write(f"\\label{{tab:pldi-{kind}-{prog_stem}}}\n")
    if len(keys) > 8:
        f.write("\\footnotesize\\gibbonnumfont\n"
                "\\setlength{\\tabcolsep}{4pt}\n")
    else:
        f.write("\\small\\gibbonnumfont\n")
    # One extra column beyond the configuration groups: the best-of-layout
    # speedup (see _pldi_best_of_layout_speedup). It belongs to neither
    # group, so it gets no \cmidrule and its label sits on the symbol row.
    f.write("\\begin{tabular}{l c c" + " r" * len(keys) + " r}\n\\toprule\n")
    f.write("\\textbf{Pass} & &"
            + "".join(" & \\multicolumn{%d}{c}{\\textbf{%s}}" % (len(g), lbl)
                      for lbl, g in col_groups)
            + " & \\\\\n")
    # Pass, Uses and Dead% occupy columns 1-3, so the layout groups the
    # \cmidrule underlines start at 4.
    col = 4
    rules = []
    for _, group in col_groups:
        rules.append("\\cmidrule(lr){%d-%d}" % (col, col + len(group) - 1))
        col += len(group)
    f.write("".join(rules) + "\n")
    _is_map = (pass_type == "map")
    _hdr = ("\\textbf{$\\Sigma_b$} & \\textbf{$\\Sigma_b\\%$}" if _is_map
            else "\\textbf{Uses} & \\textbf{Dead\\%}")
    f.write(" & " + _hdr
            + "".join(" & %s" % PLDI_COL_SYMBOLS.get(k, _tex_escape(k)) for k in keys)
            + " & $A^{\\min}$/$S^{\\min}$"
            + " \\\\\n\\midrule\n")
    for pname in pass_names:
        raw = [_pldi_cell(results_for_program.get(k), pname) for k in keys]
        cells = _highlight_row_extremes(raw)
        spd = _pldi_best_of_layout_speedup(raw, col_groups)
        # Plain escaped pass name, matching _table_per_program's own row
        # labels (a \texttt column would push the 13-column map tables
        # back over the text width).
        if _is_map:
            uses_s, dead_s = _pldi_shared_buffers(results_for_program, pname)
        else:
            uses_s, dead_s = _pldi_field_usage(results_for_program, pname)
        f.write(_tex_escape(pname) + " & " + uses_s + " & " + dead_s
                + "".join(" & %s" % c for c in cells)
                + " & " + spd + " \\\\\n")
    f.write("\\bottomrule\n\\end{tabular}\n\\end{table}\n\n")


def _table_pldi_fold(f, program: str, results_for_program: Dict[str, BenchmarkResult]) -> None:
    col_groups = [("AoS", list(PLDI_FOLD_CONFIGS["aos"].keys())),
                  ("SoA", list(PLDI_FOLD_CONFIGS["soa"].keys()))]
    _render_pldi_table(f, program, results_for_program, col_groups, "fold", "fold")


def _table_pldi_map(f, program: str, results_for_program: Dict[str, BenchmarkResult]) -> None:
    col_groups = [("AoS", list(PLDI_MAP_CONFIGS["aos"].keys())),
                  ("SoA", list(PLDI_MAP_CONFIGS["soa"].keys()))]
    _render_pldi_table(f, program, results_for_program, col_groups, "map", "map")


def pldi_qualification_warnings(
        pldi_variant_results: Dict[str, Dict[str, BenchmarkResult]]) -> List[str]:
    """One line per (program, configuration) whose result is not oracle-
    VERIFIED -- i.e. exactly the cells the tables render as `--'.  Replaces
    the per-table Qual. column: correctness is still checked for every cell,
    it is just reported to the operator instead of consuming table width."""
    lines: List[str] = []
    for program in sorted(pldi_variant_results):
        by_cfg = pldi_variant_results[program]
        ordered = [k for layout in ("aos", "soa") for k in PLDI_MAP_CONFIGS[layout]]
        ordered += [k for k in by_cfg if k not in ordered]
        for cfg in ordered:
            if cfg not in by_cfg:
                continue
            res = by_cfg[cfg]
            if prov.verified_result(res):
                continue
            st = getattr(res, "qualification", None) if res is not None else None
            label = st.label if st is not None else "MISSING"
            detail = getattr(st, "oracle_detail", None) if st is not None else None
            # For a RUN-FAIL the oracle never ran, so oracle_detail is empty
            # and the exit code / stderr is the only thing that says why.
            if not detail and res is not None:
                detail = getattr(res, "error_message", None)
            lines.append("%s [%s]: %s%s"
                         % (program, PLDI_ROW_LABELS.get(cfg, cfg), label,
                            " -- %s" % detail if detail else ""))
    return lines


def report_pldi_qualification_warnings(
        pldi_variant_results: Dict[str, Dict[str, BenchmarkResult]]) -> List[str]:
    lines = pldi_qualification_warnings(pldi_variant_results)
    if not lines:
        print("  ✓ Every PLDI configuration verified against its oracle")
    else:
        print("  ⚠ %d PLDI configuration(s) did not verify; their table cells "
              "render as '--':" % len(lines))
        for line in lines:
            vprint("      - %s" % line)
    return lines


def _table_arith_intensity(f, results_by_width: Dict[int, Dict[str, BenchmarkResult]]):
    """Integer-width high-arithmetic-intensity vectorization table: one row
    per width. Every numeric cell is gated through prov.verified_result/
    eligible_pair/safe_speedup EXCEPT width 64's SIMD-raw and SIMD-speedup
    cells, which are hardcoded to W64_SIMD_NA_REASON unconditionally --
    checked FIRST, before any lookup into results_by_width[64] -- so no
    BenchmarkResult for width 64's "soa_simd" (real or synthetic) can ever
    populate those two cells with a number."""
    f.write("% Integer-width high-arithmetic-intensity vectorization\n")
    f.write("\\begin{table}[h]\n\\centering\n")
    f.write("\\caption{Integer-width high-arithmetic-intensity vectorization. "
            + simd_isa_caption_note()
            + no_gcc_vec_caption_note()
            + "Selective buffer sharing is enabled from the \\textbf{SoA loopify "
              "shared} column onwards, including the SIMD column, so those cells are "
              "directly comparable with the per-program map tables, whose SoA columns "
              "also enable it. \\textbf{SIMD spd.} divides the shared column by the "
              "SIMD one -- the two differ by the vectorizer alone, so it reports what "
              "vectorization buys and nothing else; \\textbf{AoS-vs-SIMD} keeps AoS "
              "as its baseline and therefore includes every SoA-side optimization. "
            + "Int64 does not vectorize its multiplies: a packed 64-bit multiply "
              "costs seven instructions for two lanes (four under AVX2) against "
              "one \\texttt{imul} per lane scalar, so it is a measured LOSS -- "
              "1.370 instructions per source operation vectorized against 0.750 "
              "scalar. It is therefore excluded from the SIMD capability matrix, "
              "and Int64's SIMD column reports the same time as its scalar one "
              "rather than a slowdown.}\n")
    f.write("\\label{tab:arith_intensity}\n\\small\n")
    f.write("\\resizebox{\\textwidth}{!}{%\n")
    f.write("\\begin{tabular}{lccccccccccccc}\n\\toprule\n")
    f.write("Width & Ops/elem & Bytes ld/elem & Bytes st/elem & Ops/byte & "
            "AoS raw & SoA raw & SoA loopify & SoA loopify shared & SoA SIMD & "
            "SIMD spd. & AoS-vs-SIMD & Status & Qual. \\\\\n\\midrule\n")

    def cell(res: Optional[BenchmarkResult]) -> str:
        t = total_pass_time(res)
        return f"{t:.6f}" if t is not None else "N/A"

    def spd_or_na(spd, reason):
        return _spd_cell(spd) if spd is not None else ("N/A -- %s" % reason)

    for width in sorted(results_by_width.keys()):
        cfgs = results_by_width[width]
        m = arith_intensity_metrics(width)
        aos = cfgs.get("aos_mut")
        soa = cfgs.get("soa_mut")
        loop = cfgs.get("soa_loopify")
        shared = cfgs.get("soa_loopify_shared")

        if width == 64:
            # Hardcoded FIRST: no lookup into cfgs.get("soa_simd") at all --
            # there structurally is no such entry (ARITHINTENSITY_WIDTH_CONFIGS
            # never defines one for width 64), but even a caller who hand-built
            # results_by_width with a rogue "soa_simd" entry cannot make this
            # cell numeric, because this branch never reads it.
            simd_cell = "N/A"
            simd_spd_cell = "N/A"
            aos_vs_simd_cell = "N/A"
            status = "N/A (%s)" % W64_SIMD_NA_REASON.split(":", 1)[0]
        else:
            simd = cfgs.get("soa_simd")
            # Against the shared rung, not the unshared one: the two differ by
            # the vectorizer alone, so this is what vectorization buys.
            simd_spd, simd_reason = prov.safe_speedup(shared, simd, total_pass_time)
            aos_vs_simd, aos_vs_simd_reason = prov.safe_speedup(aos, simd, total_pass_time)
            simd_cell = cell(simd)
            simd_spd_cell = spd_or_na(simd_spd, simd_reason)
            aos_vs_simd_cell = spd_or_na(aos_vs_simd, aos_vs_simd_reason)
            status = "SIMD"

        row = (f"Int{width}"
               f" & {m['ops_per_element']:.0f}"
               f" & {m['bytes_loaded_per_element']:.0f}"
               f" & {m['bytes_stored_per_element']:.0f}"
               f" & {m['ops_per_byte']:.2f}"
               f" & {cell(aos)}"
               f" & {cell(soa)}"
               f" & {cell(loop)}"
               f" & {cell(shared)}"
               f" & {simd_cell}"
               f" & {simd_spd_cell}"
               f" & {aos_vs_simd_cell}"
               f" & {_tex_escape(status)}"
               f" & {_tex_escape(_qual_summary(cfgs))}")
        f.write(row + " \\\\\n")
    f.write("\\bottomrule\n\\end{tabular}}\n\\end{table}\n\n")


def merge_program_groups_in_pairs(all_results: List[Tuple],
                                  groups: Optional[Dict[str, str]] = None) -> List[Tuple]:
    """The (aos, soa) pair list with each split family folded into one pair,
    so Table 1 shows the family as ONE row rather than one row per timed
    pass. Mirrors merge_pldi_program_groups; a family whose members are all
    absent is left alone."""
    groups = PROGRAM_MERGE_GROUPS if groups is None else groups
    pairs = list(all_results)
    for merged_name, prefix in groups.items():
        by_program = {a.program: (a, s) for a, s in pairs if a and s}
        members = merge_group_members(merged_name, prefix, list(by_program))
        if not members:
            continue

        def build(index: int, variant: str) -> BenchmarkResult:
            merged = BenchmarkResult(merged_name, variant)
            merged.compile_success = True
            merged.run_success = True
            merged.passes = {}
            contributors = []
            for member in members:
                res = by_program[member][index]
                # Only a VERIFIED member contributes a pass -- same rule
                # _merge_octree_results applies to the OctTree family.
                if res is None or not prov.verified_result(res):
                    continue
                contributors.append(res)
                for pname, pdata in (res.passes or {}).items():
                    merged.passes[pname] = dict(pdata)
                if merged.adt_fields is None and res.adt_fields is not None:
                    merged.adt_fields = res.adt_fields
                    merged.adt_info = res.adt_info
                if merged.arith_mode is None:
                    merged.arith_mode = res.arith_mode
                    merged.use_no_ran = res.use_no_ran
            merged.run_success = len(merged.passes) > 0
            merged.qualification = prov.synthesize_derived_status(
                variant, merged_name, contributors)
            return merged

        merged_pair = (build(0, "aos"), build(1, "soa"))
        pairs = [(a, s) for a, s in pairs if a is None or a.program not in members]
        pairs.append(merged_pair)
    return pairs


# ---------------------------------------------------------------------------
# Empirical roofline (--roofline)
#
# Measures THIS machine's practical ceilings rather than quoting a
# datasheet: single-threaded DRAM bandwidth, and the peak rate of
# multiply-add work at each type Gibbon actually emits.
#
# Single-threaded on purpose: every Gibbon benchmark in this suite runs as
# one process with no parallelism, so an all-core ceiling would not bound
# any of them -- and on a hybrid CPU it blends fast and slow core types
# into a number no kernel can reach.
#
# Integer ceilings per width, not just FP64: Gibbon's kernels are integer
# (Int8/16/32/64) and the per-width ceilings are NOT proportional to lane
# count -- on AVX2 there is no packed 8-bit or 64-bit multiply, so those
# widths are emulated and much slower than 16-bit. A single FP64 roofline
# would say nothing about any of that. FP64 is measured too, for
# comparability with published rooflines.
ROOFLINE_SOURCE = r"""#define _POSIX_C_SOURCE 200809L
// Empirical SINGLE-THREADED roofline probe.
//
// Single-threaded on purpose: the Gibbon benchmarks this roofline is meant
// to bound run as one process with no parallelism, so an all-core ceiling
// would not bound them. On a hybrid CPU it would also blend P-core and
// E-core throughput into a number no kernel can reach.
//
// Reports, on stdout, one "KEY VALUE" line per measurement so the driver
// can parse it without regexing prose.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

/* Plain C so this builds with the same --cc the driver already uses for
   Gibbon's generated programs, rather than needing a C++ toolchain. */
static double now_s(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

// ~256 MB per array, 768 MB live: an order of magnitude past this class of
// CPU's L3, so the triad is served from DRAM rather than cache.
static const size_t STREAM_N = 32u * 1000u * 1000u;

static double bandwidth_gb_s() {
    double *A = (double *)aligned_alloc(64, STREAM_N * sizeof(double));
    double *B = (double *)aligned_alloc(64, STREAM_N * sizeof(double));
    double *C = (double *)aligned_alloc(64, STREAM_N * sizeof(double));
    if (!A || !B || !C) { fprintf(stderr, "alloc failed\n"); exit(1); }
    for (size_t i = 0; i < STREAM_N; ++i) { A[i] = 1.0; B[i] = 2.0; C[i] = 0.0; }

    double best = 0.0;
    for (int rep = 0; rep < 3; ++rep) {          // best of 3: least disturbed
        double t0 = now_s();
        for (size_t i = 0; i < STREAM_N; ++i) C[i] = A[i] + 3.0 * B[i];
        double t1 = now_s();
        // STREAM convention: 2 reads + 1 write = 24 B/element. Real DRAM
        // traffic is 32 B/element when the write allocates, so counting 24
        // makes this a CONSERVATIVE (under-)estimate of achieved bandwidth.
        double gb = (double)STREAM_N * 24.0 / 1e9;
        double bw = gb / (t1 - t0);
        if (bw > best) best = bw;
    }
    volatile double sink = C[STREAM_N / 2]; (void)sink;
    free(A); free(B); free(C);
    return best;
}

// Compute ceilings.
//
// The accumulators must live in REGISTERS, not memory: an earlier version
// used plain arrays and measured ~5.5 GFLOPS because every iteration
// reloaded and stored them, making the loop store-bound rather than
// FMA-bound. GCC/Clang vector extensions give one AVX register per
// accumulator, and 12 independent chains are enough to cover FMA latency
// (~4 cycles) across the two FMA ports.
#define ACCS 12

// A 1 the optimizer cannot see. Without this the multiply in `a*x+y` is
// folded away when x is a literal 1, and the benchmark reports roughly
// double the ops it actually executed -- which is exactly what an earlier
// revision of this file did.
static volatile double OPAQUE_SEED = 1.0;
static inline double opaque_one() { return OPAQUE_SEED; }

#define PEAK_FN(NAME, TYPE, LANES, OPNAME)                                  \
static double NAME() {                                                      \
    typedef TYPE vec __attribute__((vector_size(sizeof(TYPE) * (LANES))));  \
    vec a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, x, y;             \
    for (int j = 0; j < (LANES); ++j) {                                     \
        a0[j]=(TYPE)(j+1);  a1[j]=(TYPE)(j+2);  a2[j]=(TYPE)(j+3);          \
        a3[j]=(TYPE)(j+4);  a4[j]=(TYPE)(j+5);  a5[j]=(TYPE)(j+6);          \
        a6[j]=(TYPE)(j+7);  a7[j]=(TYPE)(j+8);  a8[j]=(TYPE)(j+9);          \
        a9[j]=(TYPE)(j+10); a10[j]=(TYPE)(j+11); a11[j]=(TYPE)(j+12);       \
        /* NOT 1: with x==1 the compiler folds a*x+y into a+y, which      \
           deletes half the work we then count. opaque_one() hides the      \
           value behind a volatile read so no constant propagation can      \
           see it. */                                                       \
        x[j] = (TYPE)opaque_one(); y[j] = (TYPE)opaque_one();               \
    }                                                                       \
    const size_t iters = 40u * 1000u * 1000u;                               \
    __asm__ __volatile__("" : "+v"(a0), "+v"(a1), "+v"(a2), "+v"(a3),               \
                      "+v"(a4), "+v"(a5), "+v"(a6), "+v"(a7));              \
    __asm__ __volatile__("" : "+v"(a8), "+v"(a9), "+v"(a10), "+v"(a11),             \
                      "+v"(x), "+v"(y));                                    \
    double t0 = now_s();                                                   \
    for (size_t it = 0; it < iters; ++it) {                                 \
        a0 = a0 * x + y;  a1 = a1 * x + y;  a2  = a2  * x + y;              \
        a3 = a3 * x + y;  a4 = a4 * x + y;  a5  = a5  * x + y;              \
        a6 = a6 * x + y;  a7 = a7 * x + y;  a8  = a8  * x + y;              \
        a9 = a9 * x + y;  a10 = a10 * x + y; a11 = a11 * x + y;             \
    }                                                                       \
    double t1 = now_s();                                                   \
    double sink = 0.0;                                                      \
    for (int j = 0; j < (LANES); ++j)                                       \
        sink += (double)(a0[j]+a1[j]+a2[j]+a3[j]+a4[j]+a5[j]                \
                       + a6[j]+a7[j]+a8[j]+a9[j]+a10[j]+a11[j]);            \
    if (sink == 1.5e-300) printf("%f", sink);   /* defeat DCE */            \
    /* one multiply + one add per lane per accumulator */                   \
    double ops = (double)iters * ACCS * (double)(LANES) * 2.0;              \
    return ops / (t1 - t0) / 1e9;                                        \
}

PEAK_FN(fp64_gflops,  double,  4, "GFLOPS")
PEAK_FN(int8_giops,   int8_t, 32, "GIOPS")
PEAK_FN(int16_giops,  int16_t,16, "GIOPS")
PEAK_FN(int32_giops,  int32_t, 8, "GIOPS")
PEAK_FN(int64_giops,  int64_t, 4, "GIOPS")

int main(void) {
    printf("BANDWIDTH_GB_S %.6f\n", bandwidth_gb_s());
    printf("FP64_GFLOPS %.6f\n", fp64_gflops());
    printf("INT8_GIOPS %.6f\n", int8_giops());
    printf("INT16_GIOPS %.6f\n", int16_giops());
    printf("INT32_GIOPS %.6f\n", int32_giops());
    printf("INT64_GIOPS %.6f\n", int64_giops());
    return 0;
}
"""

ROOFLINE_KEYS = ("BANDWIDTH_GB_S", "FP64_GFLOPS", "INT8_GIOPS",
                 "INT16_GIOPS", "INT32_GIOPS", "INT64_GIOPS")


def run_roofline_probe(out_dir: Path, cc: str, pin_cpu: Optional[int] = 0,
                       ) -> Dict[str, float]:
    """Build and run the probe; returns {measurement: value}.

    Never invokes `gibbon`, so it does not touch the shared RTS build
    directory and cannot disturb (or be disturbed by) a benchmark campaign
    running concurrently."""
    out_dir.mkdir(parents=True, exist_ok=True)
    csrc = out_dir / "roofline_probe.c"
    exe = out_dir / "roofline_probe.exe"
    csrc.write_text(ROOFLINE_SOURCE)
    # -march=native so the compiler may use this machine's widest vectors,
    # -ffast-math so it may contract multiply+add into FMA. Both are what
    # make the measured ceiling "practical" rather than scalar.
    cmd = [cc, "-O3", "-march=native", "-ffast-math", "-std=c11",
           str(csrc), "-o", str(exe)]
    print("  Building roofline probe: " + " ".join(cmd))
    proc = subprocess.run(cmd, capture_output=True, text=True)
    if proc.returncode != 0:
        raise RuntimeError("roofline probe failed to build:\n" + proc.stderr[-2000:])
    run_cmd = [str(exe)]
    if pin_cpu is not None and shutil.which("taskset"):
        # Pin so the run cannot migrate between core types mid-measurement.
        run_cmd = ["taskset", "-c", str(pin_cpu)] + run_cmd
    print("  Running roofline probe: " + " ".join(run_cmd))
    proc = subprocess.run(run_cmd, capture_output=True, text=True, timeout=1800)
    if proc.returncode != 0:
        raise RuntimeError("roofline probe failed to run (rc=%d):\n%s"
                           % (proc.returncode, proc.stderr[-2000:]))
    results: Dict[str, float] = {}
    for line in proc.stdout.splitlines():
        parts = line.split()
        if len(parts) == 2:
            try:
                results[parts[0]] = float(parts[1])
            except ValueError:
                pass
    missing = [k for k in ROOFLINE_KEYS if k not in results]
    if missing:
        raise RuntimeError("roofline probe printed no value for: %s\nstdout:\n%s"
                           % (", ".join(missing), proc.stdout))
    return results


def roofline_ridge_points(results: Dict[str, float]) -> Dict[str, float]:
    """Machine balance per ceiling: the arithmetic intensity (ops per byte)
    at which a kernel stops being memory-bound and starts being
    compute-bound. Below it bandwidth is the limit; above it the ALUs are."""
    bw = results["BANDWIDTH_GB_S"]
    return {k: results[k] / bw for k in results if k != "BANDWIDTH_GB_S"}


# Human-readable names and plot styling for each measured ceiling.
ROOFLINE_CEILINGS = [
    ("INT8_GIOPS",  "Int8 mul-add",  "8-bit integer multiply-add"),
    ("INT16_GIOPS", "Int16 mul-add", "16-bit integer multiply-add"),
    ("INT32_GIOPS", "Int32 mul-add", "32-bit integer multiply-add"),
    ("INT64_GIOPS", "Int64 mul-add", "64-bit integer multiply-add"),
    ("FP64_GFLOPS", "FP64 FMA",      "double-precision fused multiply-add"),
]


PERF_DRAM_EVENTS = ("uncore_imc_free_running/data_read/",
                    "uncore_imc_free_running/data_write/")


def perf_dram_counters_available() -> bool:
    """Whether this machine can report real DRAM traffic.

    PAPI is the driver's usual counter path but is unusable here: on this
    Alder Lake hybrid CPU `papi_avail` reports "Of 108 possible events, 0
    are available", so --enable-papi/-native produce nothing. perf's uncore
    IMC counters do work, and are a better source for a roofline anyway --
    they measure bytes that actually crossed the memory controller."""
    if not shutil.which("perf"):
        return False
    probe = subprocess.run(
        ["perf", "stat", "-a", "-e", ",".join(PERF_DRAM_EVENTS), "-x,", "sleep", "0.2"],
        capture_output=True, text=True)
    return any(ev.split("/")[1] in probe.stderr for ev in PERF_DRAM_EVENTS)


def _perf_dram_mib(exe: Path, iterations: int, cpu: int, size_param: int = 0,
                   ) -> Optional[float]:
    """Total system DRAM traffic (MiB) while `exe` runs, via perf.

    System-wide (-a) because the IMC counters are free-running and cannot
    be attributed to one process; the caller's differencing is what removes
    the machine's background traffic."""
    cmd = ["perf", "stat", "-a", "-e", ",".join(PERF_DRAM_EVENTS), "-x,", "--",
           "taskset", "-c", str(cpu), str(exe),
           "--size-param", str(size_param), "--iterate", str(iterations)]
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=3600)
    total = 0.0
    seen = False
    for line in proc.stderr.splitlines():
        parts = line.split(",")
        if len(parts) >= 3 and any(ev in parts[2] for ev in PERF_DRAM_EVENTS):
            try:
                total += float(parts[0])   # perf already reports these in MiB
                seen = True
            except ValueError:
                return None
    return total if seen else None


def measure_dram_bytes_per_iteration(exe: Path, cpu: int = 0,
                                     low: int = 5, high: int = 15,
                                     size_param: int = 0) -> Optional[float]:
    """DRAM bytes attributable to ONE iteration of the program's timed pass.

    Differential: the tree is built once regardless of --iterate, so
    running at `low` and `high` and dividing the difference by (high - low)
    removes the build's traffic AND the machine's steady background load,
    leaving the marginal cost of one kernel pass. Verified linear on this
    workload (5/10/20 iterations gave 1215 and 1139 MiB/iteration).

    Returns None if the counters are unavailable or the difference is not
    positive (which means the measurement was swamped by other activity --
    better to report nothing than a number built from noise)."""
    lo = _perf_dram_mib(exe, low, cpu, size_param)
    hi = _perf_dram_mib(exe, high, cpu, size_param)
    if lo is None or hi is None or high <= low:
        return None
    per_iter_mib = (hi - lo) / float(high - low)
    if per_iter_mib <= 0:
        return None
    return per_iter_mib * 1024.0 * 1024.0


def roofline_overlay_points(
        arithintensity_width_results: Optional[Dict[int, Dict[str, BenchmarkResult]]],
        leaf_count: Optional[int] = None,
        measured_bytes: Optional[Dict[Tuple[int, str], float]] = None,
        ) -> List[Dict]:
    """Where Gibbon's own arithmetic-intensity kernels sit on the roofline.

    y is achieved Gop/s: total kernel ops (leaves x ops-per-element) over
    the measured median pass time. The op count is analytical BY NECESSITY
    -- x86 has no retired-integer-op counter (only FP_ARITH_INST_RETIRED,
    which is floating point) -- but it is also exact, being fixed by the
    source: every Leaf gets exactly ARITH_OPS_PER_ELEMENT operations.

    x is ops/byte. TWO values are recorded per point:
      * ops_per_byte_model    -- arith_intensity_metrics: the Leaf field
                                 loaded and stored, and nothing else.
      * ops_per_byte_measured -- ops over DRAM bytes that actually crossed
                                 the memory controller, when
                                 `measured_bytes` supplies them.
    They differ by roughly 6x on this workload, because the model counts
    neither tags and cursors, nor 64-byte line granularity for a 4-byte
    field, nor the fresh output tree a map allocates. The measured value is
    the honest one and is what gets plotted; the model value is kept beside
    it so the gap stays visible rather than being quietly replaced.

    Only VERIFIED results contribute -- an unverified time is not a
    measurement of anything."""
    points: List[Dict] = []
    if not arithintensity_width_results:
        return points
    if leaf_count is None:
        try:
            sys.path.insert(0, str(Path(__file__).resolve().parent / "oracles"))
            import arithintensity_model as _m  # noqa: WPS433
            leaf_count = _m.leaf_count()
        except Exception:
            return points
    for width in sorted(arithintensity_width_results):
        metrics = arith_intensity_metrics(width)
        for cfg, res in arithintensity_width_results[width].items():
            if not prov.verified_result(res) or not res.passes:
                continue
            for pname, pdata in res.passes.items():
                if is_verification_pass(pname):
                    continue
                t_med = pdata.get("median_time")
                if not t_med or t_med <= 0:
                    continue
                total_ops = float(leaf_count) * metrics["ops_per_element"]
                point = {
                    "width": width,
                    "config": cfg,
                    "pass": pname,
                    "ops_per_byte_model": metrics["ops_per_byte"],
                    "ops_per_byte_measured": None,
                    "dram_bytes_per_iteration": None,
                    "ops_per_byte": metrics["ops_per_byte"],   # what to plot
                    "intensity_source": "analytical model",
                    "gops": total_ops / t_med / 1e9,
                    "median_time": t_med,
                    "total_ops": total_ops,
                    # Per-MEASUREMENT provenance. The campaign block says
                    # what the run as a whole used; these two say what this
                    # one point actually had behind it, which is what
                    # distinguishes a median from a single cold sample when
                    # a cell is questioned later.
                    "iterations": pdata.get("n"),
                    "measured_at": getattr(res, "run_finished_at", None),
                }
                bytes_meas = (measured_bytes or {}).get((width, cfg))
                # The model counts only the Leaf field loaded and stored. Real
                # DRAM traffic also carries tags, cursors, 64-byte line
                # granularity for a sub-line field, and the output tree a map
                # allocates, so it can only be LARGER -- measured ops/byte can
                # only be SMALLER than the model's. A measured value above the
                # model is not a tighter measurement, it is a broken counter,
                # and it is what gets plotted: an IMC counter that has stopped
                # reporting yields a differential of a few MiB against a
                # gigabyte-per-iteration kernel and an x-coordinate three
                # orders of magnitude out. Fall back to the model and say so.
                if bytes_meas and total_ops / bytes_meas <= metrics["ops_per_byte"]:
                    point["dram_bytes_per_iteration"] = bytes_meas
                    point["ops_per_byte_measured"] = total_ops / bytes_meas
                    point["ops_per_byte"] = point["ops_per_byte_measured"]
                    point["intensity_source"] = "measured DRAM traffic (perf uncore IMC)"
                elif bytes_meas:
                    point["intensity_source"] = (
                        "analytical model (rejected a DRAM reading of %.1f MB/"
                        "iteration: below the model's own lower bound on "
                        "traffic)" % (bytes_meas / 1e6))
                points.append(point)
    return points


def write_roofline_outputs(results: Dict[str, float], out_dir: Path,
                           figures_dir: Path,
                           overlay: Optional[List[Dict]] = None,
                           machine: Optional[Dict[str, str]] = None) -> Path:
    """Writes roofline.json, a standalone plot script, and (when matplotlib
    is importable) the PNG. The script is emitted unconditionally so the
    plot can be regenerated -- or redrawn with different styling -- on a
    machine that has matplotlib even if this one does not."""
    out_dir.mkdir(parents=True, exist_ok=True)
    figures_dir.mkdir(parents=True, exist_ok=True)
    payload = {
        "measurements": results,
        "ridge_points_ops_per_byte": roofline_ridge_points(results),
        "overlay": overlay or [],
        "machine": machine or {},
        "notes": {
            "threading": "single-threaded; the Gibbon benchmarks it bounds "
                         "are single-threaded, and an all-core ceiling would "
                         "not bound them",
            "bandwidth": "STREAM triad, 24 B/element (2 reads + 1 write). "
                         "Real DRAM traffic is 32 B/element when the write "
                         "allocates, so this UNDERSTATES achieved bandwidth",
            "compute": "12 independent register-resident accumulators doing "
                       "a*x+y; operands are hidden behind a volatile read so "
                       "the multiply cannot be folded away",
        },
    }
    json_path = out_dir / "roofline.json"
    json_path.write_text(json.dumps(payload, indent=2) + "\n")
    print("  \u2713 Roofline data \u2192 %s" % json_path)

    script = figures_dir / "plot_roofline.py"
    # Bake in this module's absolute path: --figures-dir can point anywhere,
    # so the script cannot find gibbon_benchmark.py by walking up from its
    # own location (an earlier version tried and failed with
    # ModuleNotFoundError whenever the figures dir was not a direct child of
    # the suite directory).
    script.write_text(
        ROOFLINE_PLOT_SCRIPT.replace("@@DRIVER_DIR@@",
                                     str(Path(__file__).resolve().parent)))
    print("  \u2713 Plot script  \u2192 %s" % script)

    png = figures_dir / "roofline.png"
    try:
        _render_roofline_png(payload, png)
        print("  \u2713 Roofline plot \u2192 %s" % png)
    except ImportError:
        print("  Note: matplotlib not importable \u2014 run "
              "`python3 %s %s` to draw it" % (script, json_path))
    return json_path


def _render_roofline_png(payload: Dict, png: Path) -> None:
    import numpy as np              # noqa: WPS433
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt  # noqa: WPS433

    results = payload["measurements"]
    bw = results["BANDWIDTH_GB_S"]
    ceilings = [(k, short, results[k]) for k, short, _long in ROOFLINE_CEILINGS
                if k in results]
    ai = np.logspace(-2, 3, 800)

    fig, ax = plt.subplots(figsize=(9.5, 6.0))
    colors = plt.cm.viridis(np.linspace(0.05, 0.85, len(ceilings)))
    for (key, short, peak), color in zip(ceilings, colors):
        ax.loglog(ai, np.minimum(peak, bw * ai), lw=2.0, color=color,
                  label="%s \u2014 %.1f G%s/s" %
                        (short, peak, "FLOP" if "FP" in key else "op"))
        ax.axvline(peak / bw, color=color, ls=":", alpha=0.35)

    # The shared memory-bound diagonal: every ceiling rides it below its
    # own ridge point, so drawing it once labels the bandwidth limit.
    ax.loglog(ai, bw * ai, color="0.35", ls="--", lw=1.2,
              label="DRAM bandwidth \u2014 %.1f GB/s" % bw)

    for pt in payload.get("overlay", []):
        ax.plot(pt["ops_per_byte"], pt["gops"], marker="o", ms=6,
                color="crimson", zorder=5)
        ax.annotate("Int%d %s" % (pt["width"], pt.get("config", "")),
                    (pt["ops_per_byte"], pt["gops"]),
                    textcoords="offset points", xytext=(6, 4), fontsize=7)

    machine = payload.get("machine", {})
    subtitle = machine.get("cpu", "")
    ax.set_title("Empirical single-threaded roofline"
                 + ("\n%s" % subtitle if subtitle else ""),
                 fontsize=13, fontweight="bold")
    ax.set_xlabel("Arithmetic intensity (ops / byte)", fontsize=11)
    ax.set_ylabel("Attainable performance (Gop/s)", fontsize=11)
    ax.grid(True, which="both", ls="-", alpha=0.25)
    ax.legend(loc="lower right", fontsize=8)
    fig.tight_layout()
    fig.savefig(png, dpi=200)
    plt.close(fig)


ROOFLINE_PLOT_SCRIPT = '''#!/usr/bin/env python3
"""Redraw the empirical roofline from roofline.json.

    python3 plot_roofline.py <roofline.json> [out.png]

Emitted alongside the data so the plot can be regenerated, or restyled,
without re-running the measurement (and on a machine that has matplotlib
even if the measuring one did not).
"""
import json
import sys
from pathlib import Path

# Absolute path to the suite directory, written in when this script was
# generated -- --figures-dir may be anywhere, so it cannot be derived from
# this file's own location.
sys.path.insert(0, "@@DRIVER_DIR@@")
from gibbon_benchmark import _render_roofline_png  # noqa: E402

if __name__ == "__main__":
    data = json.loads(Path(sys.argv[1]).read_text())
    out = Path(sys.argv[2] if len(sys.argv) > 2 else "roofline.png")
    _render_roofline_png(data, out)
    print("wrote %s" % out)
'''


def _machine_description() -> Dict[str, str]:
    """Enough provenance that a roofline can be attributed to a machine."""
    info: Dict[str, str] = {}
    try:
        for line in Path("/proc/cpuinfo").read_text().splitlines():
            if line.startswith("model name") and "cpu" not in info:
                info["cpu"] = line.split(":", 1)[1].strip()
                break
    except Exception:
        pass
    info["platform"] = platform.platform() if "platform" in globals() else sys.platform
    return info


def _run_roofline_only(args) -> int:
    """--roofline without a campaign: measure, write, and stop."""
    print("\n" + "=" * 72)
    print("EMPIRICAL ROOFLINE (single-threaded)")
    print("=" * 72)
    cc = resolve_cc(args.cc)
    machine = _machine_description()
    if machine.get("cpu"):
        print("  CPU          : %s" % machine["cpu"])
    print("  Compiler     : %s  (%s)" % (cc, cc_version(cc)))
    print("  Pinned to CPU: %d" % args.roofline_cpu)
    try:
        results = run_roofline_probe(args.output_dir, cc, pin_cpu=args.roofline_cpu)
    except RuntimeError as e:
        print("  ERROR: %s" % e, file=sys.stderr)
        return 1
    print()
    print("  %-24s %12.2f GB/s" % ("DRAM bandwidth", results["BANDWIDTH_GB_S"]))
    ridges = roofline_ridge_points(results)
    for key, short, _long in ROOFLINE_CEILINGS:
        if key in results:
            unit = "GFLOP/s" if "FP" in key else "Gop/s"
            print("  %-24s %12.2f %-8s (ridge at %.2f ops/byte)"
                  % (short, results[key], unit, ridges[key]))
    print()
    write_roofline_outputs(results, args.output_dir, args.figures_dir,
                           overlay=None, machine=machine)
    return 0


def latex_provenance_comments(campaign: Optional[Dict]) -> str:
    """The campaign block as LaTeX comment lines.

    `benchmark_results.json` records what produced a campaign, but the
    `.tex` is the file that travels into a paper and the JSON does not go
    with it.  Emitting the same block here means a table lifted out of this
    file still names the commit, the compiler binary, the C compiler, the
    machine, the iteration count and the flags behind every number in it.

    Nested dicts are flattened to `parent.child`; lists are joined with
    spaces.  A `%` inside a value would start a LaTeX comment mid-line, so
    it is escaped.
    """
    if not campaign:
        return ""
    lines: List[str] = []

    def emit(prefix: str, value) -> None:
        if isinstance(value, dict):
            for k, v in value.items():
                emit(f"{prefix}.{k}" if prefix else str(k), v)
            return
        if isinstance(value, (list, tuple)):
            value = " ".join(str(x) for x in value)
        text = "unknown" if value is None else str(value)
        lines.append("%% Provenance: %s = %s\n"
                     % (prefix, text.replace("%", "\\%")))

    emit("", campaign)
    return "".join(lines)


def write_latex_tables(all_results: List[Tuple], out_file: Path,
                       all_variants_results: Optional[List[Dict]] = None,
                       include_build_pass: bool = False,
                       show_cursor_table: bool = False,
                       add1tree_width_results: Optional[Dict[int, Dict[str, BenchmarkResult]]] = None,
                       arithintensity_width_results: Optional[Dict[int, Dict[str, BenchmarkResult]]] = None,
                       pldi_variant_results: Optional[Dict[str, Dict[str, BenchmarkResult]]] = None,
                       simd_isa: str = DEFAULT_SIMD_ISA,
                       campaign: Optional[Dict] = None):
    # Name the SIMD target in this report's captions.  One report is one ISA:
    # the driver passes a single --simd-isa to every compile it issues.
    set_report_simd_isa(simd_isa)
    # Fold split families (one executable per timed pass) back into one
    # program BEFORE any table is written, so every table below -- summary,
    # per-program, PLDI -- sees the family exactly as it saw the old single
    # executable, with no per-table special-casing.
    all_results = merge_program_groups_in_pairs(all_results)
    pldi_variant_results = merge_pldi_program_groups(pldi_variant_results)
    seen_modes = sorted({r.arith_mode for a, s in all_results for r in (a, s)
                        if r is not None and r.arith_mode is not None})
    seen_no_ran = sorted({r.use_no_ran for a, s in all_results for r in (a, s)
                         if r is not None and r.use_no_ran is not None}, key=str)
    with open(out_file, "w") as f:
        f.write("% Gibbon Benchmark Suite v3.1 – auto-generated\n")
        f.write("% Requires: \\usepackage{booktabs}, \\usepackage{graphicx} and "
                "\\usepackage{xcolor} in preamble\n")
        # Defined here rather than assumed from a palette option, so the
        # generated file \input{}s into any document that loads xcolor.
        f.write("\\providecommand{\\gibbondefinecolors}{}\n")
        f.write("\\definecolor{%s}{RGB}{0,100,0}%% dark green: row-fastest\n"
                % COLOR_FASTEST)
        f.write("\\definecolor{%s}{RGB}{204,0,0}%% red: row-slowest\n"
                % COLOR_SLOWEST)
        # Half a point up from whatever size command the table selected.
        # \f@size is the current size as a bare number, so this is relative:
        # \small stays \small-ish, \footnotesize stays \footnotesize-ish,
        # each just half a point larger, and the tables keep their relative
        # sizing rather than all collapsing to one size.
        f.write("\\makeatletter\n"
                "\\providecommand{\\gibbonnumfont}{}\n"
                "\\renewcommand{\\gibbonnumfont}{%%\n"
                "  \\fontsize{\\dimexpr\\f@size pt+1.5pt\\relax}%%\n"
                "          {\\dimexpr\\f@size pt+3.9pt\\relax}\\selectfont}\n"
                "\\makeatother\n\n")
        f.write(f"% Provenance: arithmetic mode(s) = "
                f"{', '.join(seen_modes) if seen_modes else 'unknown'}"
                f"{'  *** INCONSISTENT -- DO NOT TRUST ***' if len(seen_modes) > 1 else ''}\n")
        f.write(f"% Provenance: no-RAN in effect = "
                f"{', '.join(str(x) for x in seen_no_ran) if seen_no_ran else 'unknown'}\n")
        f.write(latex_provenance_comments(campaign))
        f.write("\n")
        _table_summary(f, all_results, all_variants_results,
                       include_build_pass=include_build_pass,
                       pldi_variant_results=pldi_variant_results)
        if pldi_variant_results:
            # The same table against STOCK Gibbon on the AoS side: what the
            # SoA layout plus its optimizations buy over the compiler as it
            # ships, rather than over AoS's own best configuration.
            _table_summary(f, all_results, all_variants_results,
                           include_build_pass=include_build_pass,
                           pldi_variant_results=pldi_variant_results,
                           aos_config=SUMMARY_VANILLA_AOS,
                           label="tab:summary-vs-vanilla",
                           lead_in=" This table repeats "
                                   "Table~\\ref{tab:summary} with vanilla "
                                   "Gibbon on the AoS side -- the compiler as "
                                   "it ships, with no optimization enabled -- "
                                   "so the speedups are what the SoA layout "
                                   "and its optimizations buy over the stock "
                                   "baseline rather than over AoS's own best "
                                   "configuration.")
        _table_papi_summary(f, all_results)
        if all_variants_results and show_cursor_table:
            _table_cursor_comparison(f, all_variants_results)
        if all_variants_results and any(e.get('ghc') or e.get('mlton') for e in all_variants_results):
            _table_comparison_ghc_mlton(f, all_variants_results)
        if all_variants_results and any(e.get('ghc') for e in all_variants_results):
            _table_speedup_vs_ghc(f, all_variants_results)
        if pldi_variant_results:
            # One legend for the whole run; every per-program table below
            # \ref{}s it rather than repeating the configuration prose.
            _table_pldi_legend(f)
            # Render exactly what was collected (--programs/--exclude-programs
            # may have narrowed it, and --programs may name something outside
            # DEFAULT_PROGRAMS), keeping the canonical order for the rest.
            canonical = DEFAULT_PROGRAMS + PLDI_EXTRA_PROGRAMS
            ordered = [p for p in canonical if p in pldi_variant_results]
            ordered += [p for p in pldi_variant_results if p not in canonical]
            _table_pldi_delta_legend(f)
            for program in ordered:
                # Each timing table is immediately followed by its delta
                # companion, so the two are read together.
                _table_pldi_fold(f, program, pldi_variant_results[program])
                _table_pldi_fold_deltas(f, program, pldi_variant_results[program])
                _table_pldi_map(f, program, pldi_variant_results[program])
                _table_pldi_map_deltas(f, program, pldi_variant_results[program])
        else:
            _table_per_program(f, all_results, all_variants_results)
        if all_variants_results and any(e.get('ghc') for e in all_variants_results):
            _table_per_program_ghc(f, all_results, all_variants_results)
        if add1tree_width_results:
            _table_add1tree_widths(f, add1tree_width_results)
        if arithintensity_width_results:
            _table_arith_intensity(f, arithintensity_width_results)
    print(f"  ✓ LaTeX tables → {out_file}")
    if all_variants_results and show_cursor_table:
        print(f"    (includes Table 2: cursor mode comparison with {len(all_variants_results)} programs)")
        has_soa_imm = any(e.get("soa_imm") is not None for e in all_variants_results)
        if has_soa_imm:
            print(f"    (per-program tables show 4 variants: mut + imm cursors)")
        else:
            print(f"    (per-program tables show baseline variants: aos, aos_imm, soa)")


def _spd_cell(spd: float, bold_threshold: float = 1.1) -> str:
    s = f"{spd:.2f}" + r"$\times$"
    return r"\textbf{" + s + "}" if spd > bold_threshold else s


def _merge_octree_results(all_results: List[Tuple]) -> Tuple[Optional[Tuple[BenchmarkResult, BenchmarkResult]], List[Tuple]]:
    pair_map: Dict[str, Tuple[BenchmarkResult, BenchmarkResult]] = {}
    for aos, soa in all_results:
        if aos and soa:
            pair_map[aos.program] = (aos, soa)

    oct_split_programs = sorted(
        p for p in pair_map.keys()
        if p.startswith("OctTree_") and p.endswith(".hs")
    )
    oct_group_members: List[str] = []
    if oct_split_programs:
        oct_group_members.extend(oct_split_programs)
    elif "OctTree.hs" in pair_map:
        oct_group_members.append("OctTree.hs")
    if oct_group_members and "ColorOctree.hs" in pair_map:
        oct_group_members.append("ColorOctree.hs")

    if not oct_group_members:
        return None, all_results

    def merge_variant(variant: str) -> BenchmarkResult:
        merged = BenchmarkResult("OctTreeCombined.hs", variant)
        merged.compile_success = True
        merged.run_success = True
        merged.passes = {}
        merged.adt_fields = None
        merged.adt_info = None

        # Prefer OctTreeBase for ADT info.
        base = pair_map.get("OctTreeBase.hs")
        if base:
            b = base[0]
            if b and b.adt_fields is not None:
                merged.adt_fields = b.adt_fields
            if b and b.adt_info is not None:
                merged.adt_info = b.adt_info

        contributors = []
        for prog_hs in oct_group_members:
            pair = pair_map.get(prog_hs)
            if not pair:
                continue
            src = pair[0] if variant.startswith("aos") else pair[1]
            # Only a VERIFIED source may contribute pass data to the merge --
            # an unverified constituent silently averaged in would launder an
            # unqualified result into an apparently-qualified one.
            if not prov.verified_result(src):
                continue
            contributors.append(src)
            if merged.adt_fields is None and src.adt_fields is not None:
                merged.adt_fields = src.adt_fields
            if merged.adt_info is None and src.adt_info is not None:
                merged.adt_info = src.adt_info
            for pname, pdata in src.passes.items():
                merged_name = pname
                if merged_name in merged.passes:
                    stem = prog_hs.replace(".hs", "")
                    merged_name = f"{stem}.{pname}"
                merged.passes[merged_name] = dict(pdata)

        merged.run_success = len(merged.passes) > 0
        merged.qualification = prov.synthesize_derived_status(
            variant, "OctTreeCombined.hs", contributors)
        return merged

    combined = (merge_variant("aos"), merge_variant("soa"))
    if not (combined[0].run_success and combined[1].run_success):
        combined = None

    skip = set(oct_split_programs)
    skip.add("OctTree.hs")
    skip.add("ColorOctree.hs")
    filtered = [(a, s) for a, s in all_results if a and a.program not in skip]

    return combined, filtered


# The two configurations the end-to-end table reports when a
# --pldi-submission run supplies them. They REPLACE the plain
# mutable-cursor Am/Sm columns in every one of the table's three groups
# (end-to-end, fold, map) rather than adding a group of their own: this is
# the AoS-vs-SoA comparison the paper makes, so it is each layout's
# most-optimized configuration on both sides, not a recursive baseline.
#
# AoS: loopified, mutable cursors, C auto-vectorizer left on.
# SoA: loopified, mutable cursors, selective buffer sharing, Gibbon SIMD
#      vectorization and the C auto-vectorizer all on.
#
# Fold passes get their numbers from these same configurations. Nothing in
# a fold is loopifiable, so the AoS fold column is in effect the recursive
# mutable result -- which is why the per-program fold tables do not bother
# showing these columns, even though the runs time every pass.
SUMMARY_LOOPIFIED_AOS = "aos_loop_gccvec_on"
# Stock Gibbon: AoS with immutable cursors and no optimization at all. The
# second summary table contrasts SoA's best against THIS rather than
# against AoS's best, which is the "what does the layout buy over the
# compiler as it ships" comparison.
SUMMARY_VANILLA_AOS = "aos_imm"
SUMMARY_LOOPIFIED_SOA = "soa_loop_gccvec_on_sbs_on_gibvec_on"


def _summary_loopified_total(
        pldi_variant_results: Optional[Dict[str, Dict[str, BenchmarkResult]]],
        program: str, config: str,
        members: Optional[List[str]] = None,
        pass_type: Optional[str] = None) -> Optional[float]:
    """Pass-sum for one program in one PLDI configuration, or None.

    `pass_type` restricts to "fold"/"map" exactly as total_pass_time does,
    so the same configuration feeds all three of the table's groups. The
    loopified configurations are run over the WHOLE program and every pass
    is timed -- the per-program fold table simply does not display their
    columns -- so the fold numbers here need no extra compiles.

    `members` is for the synthesized OctTreeCombined row: its cell is the
    SUM over the merged programs, and is None unless EVERY member is
    present and verified -- a partial sum would silently understate the
    combined row and flatter whichever layout happened to lose a member."""
    if not pldi_variant_results:
        return None
    if members:
        total = 0.0
        for member in members:
            sub = _summary_loopified_total(pldi_variant_results, member, config,
                                           pass_type=pass_type)
            if sub is None:
                return None
            total += sub
        return total
    return total_pass_time((pldi_variant_results.get(program) or {}).get(config),
                           pass_type)


def _table_summary(f, all_results, all_variants_results: Optional[List[Dict]] = None,
                   include_build_pass: bool = False,
                   pldi_variant_results: Optional[Dict[str, Dict[str, BenchmarkResult]]] = None,
                   aos_config: str = SUMMARY_LOOPIFIED_AOS,
                   soa_config: str = SUMMARY_LOOPIFIED_SOA,
                   label: str = "tab:summary",
                   lead_in: str = ""):
    """Table 1's shape, parameterized on WHICH AoS and SoA configurations
    fill its three groups, so the same renderer emits both the
    best-vs-best table and the vanilla-Gibbon-vs-best one. The column
    symbols and prose are read out of PLDI_COL_SYMBOLS/PLDI_ROW_LABELS
    rather than written out here, so a table cannot claim a configuration
    it is not actually reading."""
    """
    Table 1: one row per program.
    Program | ADT fields | SoA bufs | End-to-end AoS/SoA/Speedup
            | Fold AoS/SoA/Speedup | Map AoS/SoA/Speedup
    """
    f.write("% -- Table 1: Summary by pass type --\n")
    f.write("\\begin{table}[t]\n\\centering\n")
    include_aos_imm = False
    aos_imm_map: Dict[str, BenchmarkResult] = {}
    if all_variants_results:
        for entry in all_variants_results:
            ai = entry.get("aos_imm")
            if ai is not None:
                include_aos_imm = True
                aos_imm_map[entry.get("program", "")] = ai

    include_loopified = bool(pldi_variant_results)
    # Which programs the synthesized OctTree row merges -- mirrors
    # _merge_octree_results' own membership rule exactly, so the loopified
    # columns sum over the same set the rest of that row reports.
    _progs = {a.program for a, s in all_results if a and s}
    oct_members = sorted(p for p in _progs
                         if p.startswith("OctTree_") and p.endswith(".hs"))
    if not oct_members and "OctTree.hs" in _progs:
        oct_members = ["OctTree.hs"]
    if oct_members and "ColorOctree.hs" in _progs:
        oct_members.append("ColorOctree.hs")

    build_sentence = ("End-to-end includes the build pass. "
                      if include_build_pass else "")
    f.write(
        "\\caption{Pass-sum execution time (s, median per iteration; sum of pass medians, not full executable wall time) "
        "and speedup split by pass type. "
        + build_sentence + simd_isa_caption_note() +
        "When present, the OctTree row includes ColorOctree passes; a separate "
        "ColorOctree row reports only those passes. "
        "ADT fields = total fields in the selected benchmark ADT "
        "(prefer parsed ADT definition; fall back to {\\tt @BENCH adt\\_fields}). "
        "SoA bufs = 1 tag buffer plus one buffer for each scalar field, "
        "plus one buffer for each non-self packed field annotated Linear, "
        "plus recursively counted buffers for each non-self packed field "
        "annotated Factored; self-recursive fields add no new buffers. "
        "Speedup ${>}1{\\times}$ means the denominator is faster; "
        "\\textbf{bold} marks ${>}1.1{\\times}$."
        + ("" if not include_loopified else
           lead_in
           + " Every group contrasts the same two configurations: %s (%s) "
             "against %s (%s); Table~\\ref{tab:pldi-legend} lists both in "
             "full." % (PLDI_COL_SYMBOLS.get(aos_config, aos_config),
                        PLDI_ROW_LABELS.get(aos_config, aos_config),
                        PLDI_COL_SYMBOLS.get(soa_config, soa_config),
                        PLDI_ROW_LABELS.get(soa_config, soa_config))
           + (" Nothing in a fold is loopifiable, so neither layout's fold "
              "column gains anything from loopification; measured against "
              "the per-program fold tables, both sides of the fold group "
              "land within a few percent of that layout's recursive "
              "mutable-cursor column."
              if "loop" in aos_config else "")
           + (" These two configurations are NOT among the columns of the "
              "per-program FOLD tables, which show only the recursive "
              "variants, so that table's $A^{\\min}$/$S^{\\min}$ is a "
              "comparison between different binaries from this one and may "
              "differ from the fold ratio here -- in magnitude, and where "
              "the two layouts are within a few percent of each other, in "
              "direction. The per-program MAP tables do contain both "
              "columns. Either way a group here is a pass-SUM, so a program "
              "whose passes disagree is reported by whichever dominates the "
              "sum."
              if include_loopified else "")
           + " The OctTree row sums its merged programs, and is reported "
             "only when every one of them verified in both configurations.")
        + "}\n"
    )
    f.write("\\label{%s}\n\\small\\gibbonnumfont\n" % label)
    if include_loopified:
        # Same three groups as always -- the loopified pair REPLACES Am/Sm
        # inside each one rather than adding a fourth group, and the
        # immutable-cursor (Ai) columns drop out with them: this table
        # states the paper's AoS-vs-SoA comparison at each layout's best
        # configuration, and nothing else.
        _A = PLDI_COL_SYMBOLS.get(aos_config, _tex_escape(aos_config))
        _S = PLDI_COL_SYMBOLS.get(soa_config, _tex_escape(soa_config))
        group_sub = f" & {_A} (s) & {_S} (s) & {_A}/{_S}"
        f.write("\\begin{tabular}{l c c r r r r r r r r r}\n\\toprule\n")
        f.write(
            "\\textbf{Program} & \\textbf{ADT} & \\textbf{SoA}"
            " & \\multicolumn{3}{c}{\\textbf{End-to-end}}"
            " & \\multicolumn{3}{c}{\\textbf{Fold passes}}"
            " & \\multicolumn{3}{c}{\\textbf{Map passes}} \\\\\n"
        )
        f.write("\\cmidrule(lr){4-6}\\cmidrule(lr){7-9}\\cmidrule(lr){10-12}\n")
        f.write(" & fields & bufs" + group_sub * 3 + " \\\\\n")
    elif include_aos_imm:
        f.write("\\begin{tabular}{l c c r r r r r r r r r r r r r r r}\n\\toprule\n")
        f.write(
            "\\textbf{Program} & \\textbf{ADT} & \\textbf{SoA}"
            " & \\multicolumn{5}{c}{\\textbf{End-to-end}}"
            " & \\multicolumn{5}{c}{\\textbf{Fold passes}}"
            " & \\multicolumn{5}{c}{\\textbf{Map passes}} \\\\\n"
        )
        f.write("\\cmidrule(lr){4-8}\\cmidrule(lr){9-13}\\cmidrule(lr){14-18}\n")
        f.write(
            " & fields & bufs"
            " & Am (s) & Ai (s) & Sm (s) & Am/Sm & Ai/Sm"
            " & Am (s) & Ai (s) & Sm (s) & Am/Sm & Ai/Sm"
            " & Am (s) & Ai (s) & Sm (s) & Am/Sm & Ai/Sm \\\\\n"
        )
    else:
        f.write("\\begin{tabular}{l c c r r r r r r r r r}\n\\toprule\n")
        f.write(
            "\\textbf{Program} & \\textbf{ADT} & \\textbf{SoA}"
            " & \\multicolumn{3}{c}{\\textbf{End-to-end}}"
            " & \\multicolumn{3}{c}{\\textbf{Fold passes}}"
            " & \\multicolumn{3}{c}{\\textbf{Map passes}} \\\\\n"
        )
        f.write("\\cmidrule(lr){4-6}\\cmidrule(lr){7-9}\\cmidrule(lr){10-12}\n")
        f.write(
            " & fields & bufs"
            " & Am (s) & Sm (s) & Am/Sm"
            " & Am (s) & Sm (s) & Am/Sm"
            " & Am (s) & Sm (s) & Am/Sm \\\\\n"
        )
    f.write("\\midrule\n")

    combined, filtered = _merge_octree_results(all_results)
    summary_results = ([combined] if combined else []) + filtered
    if combined:
        pair_map: Dict[str, Tuple[BenchmarkResult, BenchmarkResult]] = {}
        for aos, soa in all_results:
            if aos and soa:
                pair_map[aos.program] = (aos, soa)
        color_pair = pair_map.get("ColorOctree.hs")
        if color_pair:
            summary_results.append(color_pair)

    for aos, soa in summary_results:
        if not (aos and soa and aos.run_success and soa.run_success):
            continue
        prog_raw = aos.program.replace(".hs", "")
        prog     = ("OctTree" if prog_raw == "OctTreeCombined" else prog_raw).replace("_", "\\_")
        adt      = getattr(aos, "adt_fields", None)
        adt_str  = str(adt) if adt is not None else "--"
        adt_info = getattr(aos, "adt_info", None)
        bufs_str = str(adt_info["soa_total_buffers"]) if adt_info else "--"

        # `total_pass_time` itself requires `prov.verified_result`, so an
        # unverified `aos`/`soa`/`ai_res` yields None here regardless of the
        # row-level gate above.
        at = total_pass_time(aos)
        st = total_pass_time(soa)
        ai_res = aos_imm_map.get(aos.program)
        ait = total_pass_time(ai_res)
        af = total_pass_time(aos, "fold")
        aif = total_pass_time(ai_res, "fold")
        sf = total_pass_time(soa, "fold")
        am = total_pass_time(aos, "map")
        aim = total_pass_time(ai_res, "map")
        sm = total_pass_time(soa, "map")

        # Every operand here can now legitimately be None (an unverified
        # result's total_pass_time), not just absent-because-run_success-was-
        # False -- so every comparison must be None-guarded, not just truthy
        # for the already-guarded ones.  A raw `af > 0` on a None operand
        # crashes instead of rendering "--".
        tspd_s = _spd_cell(at / st) if at and st and st > 0 else "--"
        t_ai_sm_s = _spd_cell(ait / st) if ait and st and st > 0 else "--"
        fspd_s = _spd_cell(af / sf) if af and sf and sf > 0 else "--"
        f_ai_sm_s = _spd_cell(aif / sf) if aif and sf and sf > 0 else "--"
        mspd_s = _spd_cell(am / sm) if am and sm and sm > 0 else "--"
        m_ai_sm_s = _spd_cell(aim / sm) if aim and sm and sm > 0 else "--"

        if include_loopified:
            # One (AoS, SoA, ratio) triple per group, all three read off the
            # SAME pair of most-optimized configurations -- only the
            # pass_type filter differs.
            members = oct_members if aos.program == "OctTreeCombined.hs" else None
            cells = ""
            for ptype in (None, "fold", "map"):
                al = _summary_loopified_total(pldi_variant_results, aos.program,
                                              aos_config, members, ptype)
                sl = _summary_loopified_total(pldi_variant_results, aos.program,
                                              soa_config, members, ptype)
                spd = _spd_cell(al / sl) if al and sl and sl > 0 else "--"
                cells += (f" & {fmt(al) if al and al > 0 else '--'}"
                          f" & {fmt(sl) if sl and sl > 0 else '--'}"
                          f" & {spd}")
            f.write(f"{prog} & {adt_str} & {bufs_str}{cells} \\\\\n")
            continue

        if include_aos_imm:
            f.write(
                f"{prog} & {adt_str} & {bufs_str}"
                f" & {fmt(at) if at and at > 0 else '--'}"
                f" & {fmt(ait) if ait and ait > 0 else '--'}"
                f" & {fmt(st) if st and st > 0 else '--'}"
                f" & {tspd_s}"
                f" & {t_ai_sm_s}"
                f" & {fmt(af) if af and af > 0 else '--'}"
                f" & {fmt(aif) if aif and aif > 0 else '--'}"
                f" & {fmt(sf) if sf and sf > 0 else '--'}"
                f" & {fspd_s}"
                f" & {f_ai_sm_s}"
                f" & {fmt(am) if am and am > 0 else '--'}"
                f" & {fmt(aim) if aim and aim > 0 else '--'}"
                f" & {fmt(sm) if sm and sm > 0 else '--'}"
                f" & {mspd_s}"
                f" & {m_ai_sm_s} \\\\\n"
            )
        else:
            f.write(
                f"{prog} & {adt_str} & {bufs_str}"
                f" & {fmt(at) if at and at > 0 else '--'}"
                f" & {fmt(st) if st and st > 0 else '--'}"
                f" & {tspd_s}"
                f" & {fmt(af) if af and af > 0 else '--'}"
                f" & {fmt(sf) if sf and sf > 0 else '--'}"
                f" & {fspd_s}"
                f" & {fmt(am) if am and am > 0 else '--'}"
                f" & {fmt(sm) if sm and sm > 0 else '--'}"
                f" & {mspd_s} \\\\\n"
            )

    f.write("\\bottomrule\n\\end{tabular}\n\\end{table}\n\n\n")


def _collect_papi_counter_names(all_results: List[Tuple]) -> List[str]:
    counters = set()
    for aos, soa in all_results:
        for res in (aos, soa):
            if not res:
                continue
            for pdata in res.passes.values():
                for c in (pdata.get("papi_counters") or {}).keys():
                    counters.add(c)
    if _PAPI_COUNTER_ORDER:
        ordered = [c for c in _PAPI_COUNTER_ORDER if c in counters]
        ordered += sorted(c for c in counters if c not in set(ordered))
        return ordered
    return sorted(counters)


def _papi_total_for_result(res: Optional[BenchmarkResult], counter: str) -> Optional[float]:
    """PAPI ratios require verified executions with valid counters on both
    sides -- `prov.verified_result`, matching `total_pass_time`'s gate."""
    if not prov.verified_result(res):
        return None
    total = 0.0
    seen = False
    for pdata in res.passes.values():
        v = ((pdata.get("papi_counters") or {}).get(counter) or {}).get("median")
        if v is None:
            continue
        total += float(v)
        seen = True
    return total if seen else None


def _table_papi_summary(f, all_results):
    """
    Counter summary split into two compact tables:
      1) Speedups only (AoS/SoA)
      2) Counter totals as AoS/SoA value pairs
    Totals are sums of per-pass median counter values.
    """
    combined, filtered = _merge_octree_results(all_results)
    summary_results = ([combined] if combined else []) + filtered

    counters = _collect_papi_counter_names(summary_results)
    if not counters:
        return

    is_native = any(not str(c).startswith("PAPI_") for c in counters)
    counter_kind = "Native PAPI metrics" if is_native else "PAPI counters"

    short = [f"{_short_counter_label(c)} (Am/Sm)" for c in counters]

    # ------------------------------------------------------------------
    # Table A: speedup only
    # ------------------------------------------------------------------
    f.write("% -- Table: Counter Speedup Summary --\n")
    f.write("\\begin{table}[t]\n\\centering\n")
    f.write(
        f"\\caption{{{counter_kind} speedup summary across all passes. "
        "For each program and metric, speedup is AoS/SoA where each side is the sum "
        "of per-pass median counter values. "
        "${>}1{\\times}$ means SoA reports fewer events.}}\n"
    )
    f.write("\\label{tab:papi_summary_speedup}\n\\small\n")
    f.write("\\begin{tabular}{l" + (" r" * len(counters)) + "}\n\\toprule\n")
    hdr = "\\textbf{Program}"
    for c in short:
        hdr += f" & \\textbf{{{_tex_escape(c)}}}"
    f.write(hdr + " \\\\\n")
    f.write("\\midrule\n")

    spd_map: Dict[str, List[float]] = {c: [] for c in counters}
    for aos, soa in summary_results:
        if not (aos and soa and aos.run_success and soa.run_success):
            continue
        prog_raw = aos.program.replace(".hs", "")
        row = ("OctTree" if prog_raw == "OctTreeCombined" else prog_raw).replace("_", "\\_")
        for c in counters:
            at = _papi_total_for_result(aos, c)
            st = _papi_total_for_result(soa, c)
            if at is not None and st is not None and st > 0:
                spd = at / st
                spd_map[c].append(spd)
                row += f" & {_spd_cell(spd)}"
            else:
                row += " & --"
        f.write(row + " \\\\\n")
    gm_row = "\\textbf{Geomean}"
    for c in counters:
        vals = spd_map.get(c, [])
        gm_row += f" & {(_spd_cell(statistics.geometric_mean(vals)) if vals else '--')}"
    f.write("\\midrule\n")
    f.write(gm_row + " \\\\\n")
    f.write("\\bottomrule\n\\end{tabular}\n\\end{table}\n\n\n")

    # ------------------------------------------------------------------
    # Table B: raw counter totals (AoS/SoA in one cell)
    # ------------------------------------------------------------------
    f.write("% -- Table: Counter Totals Summary --\n")
    f.write("\\begin{table}[t]\n\\centering\n")
    f.write(
        f"\\caption{{{counter_kind} totals across all passes (baseline variants). "
        "Each entry is (Am/Sm), where Am and Sm are sums of per-pass median counter values.}}\n"
    )
    f.write("\\label{tab:papi_summary_values}\n\\small\n")
    f.write("\\begin{tabular}{l" + (" r" * len(counters)) + "}\n\\toprule\n")
    hdr = "\\textbf{Program}"
    for c in short:
        hdr += f" & \\textbf{{{_tex_escape(c)}}}"
    f.write(hdr + " \\\\\n")
    f.write("\\midrule\n")

    for aos, soa in summary_results:
        if not (aos and soa and aos.run_success and soa.run_success):
            continue
        prog_raw = aos.program.replace(".hs", "")
        row = ("OctTree" if prog_raw == "OctTreeCombined" else prog_raw).replace("_", "\\_")
        for c in counters:
            at = _papi_total_for_result(aos, c)
            st = _papi_total_for_result(soa, c)
            if at is None and st is None:
                row += " & --"
            else:
                a_s = _fmt_counter(at)
                s_s = _fmt_counter(st)
                if at is not None and st is not None:
                    if at < st:
                        a_s = f"\\textbf{{{a_s}}}"
                    elif st < at:
                        s_s = f"\\textbf{{{s_s}}}"
                row += f" & {a_s}/{s_s}"
        f.write(row + " \\\\\n")

    f.write("\\bottomrule\n\\end{tabular}\n\\end{table}\n\n\n")


def _table_per_program(f, all_results, all_variants_results=None):
    """
    One table per program showing per-pass performance.
    
    If all_variants_results is None (default):
        Shows 2 variants: AoS-mut, SoA-mut
    If all_variants_results is provided:
        Shows 4 variants: AoS-mut, AoS-imm, SoA-mut, SoA-imm
    """
    def _merge_pass_results(
        members: List[str],
        pair_map: Dict[str, Tuple[BenchmarkResult, BenchmarkResult]],
        variant: str,
        merged_program_name: str,
    ) -> BenchmarkResult:
        merged = BenchmarkResult(merged_program_name, variant)
        merged.compile_success = True
        merged.run_success = True
        merged.adt_fields = None   # Mixed ADTs (Octree + ColorOctree); suppress Uses/Dead% columns.
        merged.adt_info = None
        merged.passes = {}
        contributors = []
        for prog_hs in members:
            pair = pair_map.get(prog_hs)
            if not pair:
                continue
            src = pair[0] if variant.startswith("aos") else pair[1]
            # Only a VERIFIED source contributes -- see `_merge_octree_results`.
            if not prov.verified_result(src):
                continue
            contributors.append(src)
            for pname, pdata in src.passes.items():
                merged_name = pname
                # If a name collision ever appears, keep both by prefixing source stem.
                if merged_name in merged.passes:
                    stem = prog_hs.replace(".hs", "")
                    merged_name = f"{stem}.{pname}"
                mp = dict(pdata)
                if src.adt_fields is not None:
                    mp["adt_total"] = src.adt_fields
                merged.passes[merged_name] = mp
        merged.run_success = len(merged.passes) > 0
        merged.qualification = prov.synthesize_derived_status(
            variant, merged_program_name, contributors)
        return merged

    # Build a mapping from program name to variant results
    variants_map = {}
    if all_variants_results:
        for entry in all_variants_results:
            variants_map[entry['program']] = entry

    pair_map = {}
    for aos, soa in all_results:
        if aos and soa:
            pair_map[aos.program] = (aos, soa)

    oct_split_programs = sorted(
        p for p in pair_map.keys()
        if p.startswith("OctTree_") and p.endswith(".hs")
    )
    oct_group_members: List[str] = []
    if oct_split_programs:
        oct_group_members.extend(oct_split_programs)
    elif "OctTree.hs" in pair_map:
        oct_group_members.append("OctTree.hs")
    if oct_group_members and "ColorOctree.hs" in pair_map:
        oct_group_members.append("ColorOctree.hs")

    skip_program_tables = set(oct_split_programs)
    skip_program_tables.add("OctTree.hs")
    if "ColorOctree.hs" in pair_map:
        skip_program_tables.add("ColorOctree.hs")

    program_pairs: List[Tuple[BenchmarkResult, BenchmarkResult]] = []
    combined_entry: Optional[Tuple[BenchmarkResult, BenchmarkResult]] = None

    if oct_group_members:
        combined_prog = "OctTreeCombined.hs"
        oct_aos = _merge_pass_results(oct_group_members, pair_map, "aos", combined_prog)
        oct_soa = _merge_pass_results(oct_group_members, pair_map, "soa", combined_prog)
        if oct_aos.run_success and oct_soa.run_success:
            combined_entry = (oct_aos, oct_soa)
            program_pairs.append(combined_entry)

        if all_variants_results and combined_entry:
            variant_pair_map = {}
            for prog_hs, row in variants_map.items():
                variant_pair_map[prog_hs] = (row.get("aos_imm"), row.get("soa_imm"))
            oct_aos_imm = _merge_pass_results(oct_group_members, variant_pair_map, "aos_imm", combined_prog)
            oct_soa_imm = _merge_pass_results(oct_group_members, variant_pair_map, "soa_imm", combined_prog)
            variants_map[combined_prog] = {
                "program": combined_prog,
                "aos": oct_aos,
                "aos_imm": oct_aos_imm if oct_aos_imm.run_success else None,
                "soa": oct_soa,
                "soa_imm": oct_soa_imm if oct_soa_imm.run_success else None,
            }

    for aos, soa in all_results:
        if not (aos and soa):
            continue

        prog_hs = aos.program
        if prog_hs in skip_program_tables:
            continue

        program_pairs.append((aos, soa))

    for aos, soa in program_pairs:
        if not (aos and soa):
            continue

        prog_hs  = aos.program
        if prog_hs in skip_program_tables:
            continue
        prog     = ("OctTree" if prog_hs == "OctTreeCombined.hs"
                    else prog_hs.replace(".hs", ""))
        pdisplay = prog.replace("_", "\\_")
        
        # Get optional extra variants if available
        aos_imm = None
        soa_imm = None
        ghc = None
        if prog_hs in variants_map:
            aos_imm = variants_map[prog_hs].get('aos_imm')
            soa_imm = variants_map[prog_hs].get('soa_imm')
        
        show_4_variants = (aos_imm is not None or soa_imm is not None)
        include_soa_imm = (soa_imm is not None)
        show_ghc = False
        
        # Skip unless the core mutable AoS/SoA pair is independently verified.
        # Every per-pass cell below reads `aos.passes`/`soa.passes` directly
        # (not through `total_pass_time`), so this row-level gate is what
        # keeps an unverified median out of this table.
        if not prov.eligible_pair(aos, soa):
            continue
        
        adt      = getattr(aos, "adt_fields", None)
        adt_info = getattr(aos, "adt_info", None)
        soa_total_bufs = adt_info["soa_total_buffers"] if adt_info else None
        # For the synthetic OctTree table, prefer OctTreeBase buffers if present.
        oct_base = pair_map.get("OctTreeBase.hs")
        if oct_base:
            ob = oct_base[0]  # AoS variant
            if ob and ob.adt_info and ob.adt_info.get("soa_total_buffers") is not None:
                soa_total_bufs = ob.adt_info["soa_total_buffers"]
        if prog == "OctTree" and soa_total_bufs is None:
            for k, (oa, _) in pair_map.items():
                if k.startswith("OctTree_") and oa and oa.adt_info:
                    soa_total_bufs = oa.adt_info.get("soa_total_buffers")
                    break
        passes   = sorted(
            {p for p in (list(aos.passes) + list(soa.passes))
             if not is_verification_pass(p)},
            key=lambda p: _pass_sort_key(p, aos, soa, aos_imm, soa_imm, ghc),
        )
        if not passes:
            continue

        type_name = adt_info["type_name"] if adt_info else None
        adt_note  = ""
        if prog == "OctTree":
            if soa_total_bufs is not None:
                adt_note += f", OctTree SoA uses {soa_total_bufs} buffers"
            co = pair_map.get("ColorOctree.hs")
            if co and co[0] and co[0].adt_info and co[0].adt_info.get("soa_total_buffers") is not None:
                adt_note += f"; ColorOctree SoA uses {co[0].adt_info['soa_total_buffers']} buffers"
        else:
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
        papi_counter_set = {
            c
            for p in passes
            for c in (
                list((aos.passes.get(p, {}).get("papi_counters") or {}).keys()) +
                list((soa.passes.get(p, {}).get("papi_counters") or {}).keys()) +
                (list((aos_imm.passes.get(p, {}).get("papi_counters") or {}).keys())
                 if (aos_imm and aos_imm.run_success) else []) +
                (list((soa_imm.passes.get(p, {}).get("papi_counters") or {}).keys())
                 if (soa_imm and soa_imm.run_success) else [])
            )
        }
        if _PAPI_COUNTER_ORDER:
            papi_counter_names_all = [c for c in _PAPI_COUNTER_ORDER if c in papi_counter_set]
            papi_counter_names_all += sorted(c for c in papi_counter_set if c not in set(papi_counter_names_all))
        else:
            papi_counter_names_all = sorted(papi_counter_set)
        # Keep runtime table compact; emit PAPI counters in a separate table below.
        papi_counter_names: List[str] = []
        papi_colspec = ""
        papi_header_suffix = "".join(
            f" & \\textbf{{{_tex_escape(counter)} (A/S)}}"
            for counter in papi_counter_names
        )
        papi_empty_suffix = "".join(" & --" for _ in papi_counter_names)

        # Table header depends on whether we show 2 or 4 variants
        if show_4_variants:
            if has_uses:
                if include_soa_imm:
                    if show_ghc:
                        f.write("\\begin{tabular}{l c c r r r r r r r r r r r r" + papi_colspec + "}\n\\toprule\n")
                    else:
                        f.write("\\begin{tabular}{l c c r r r r r r r r r" + papi_colspec + "}\n\\toprule\n")
                else:
                    if show_ghc:
                        f.write("\\begin{tabular}{l c c r r r r r r r r r r r" + papi_colspec + "}\n\\toprule\n")
                    else:
                        f.write("\\begin{tabular}{l c c r r r r r r r r" + papi_colspec + "}\n\\toprule\n")
                f.write(
                    "\\textbf{Pass} & \\textbf{T}"
                    " & \\textbf{Uses} & \\textbf{Dead\\%}"
                    " & \\textbf{Am} & \\textbf{Ai}"
                    " & \\textbf{Sm}"
                    + (" & \\textbf{Si}" if include_soa_imm else "")
                    +
                    " & \\textbf{Am/Sm}"
                    " & \\textbf{Ai/Am}"
                    " & \\textbf{Ai/Sm}"
                    + (" & \\textbf{Ai/Si}" if include_soa_imm else "")
                    + (" & \\textbf{GHC} & \\textbf{GHC/Am} & \\textbf{GHC/Sm}" if show_ghc else "")
                    + f"{papi_header_suffix} \\\\\n"
                )
            else:
                if include_soa_imm:
                    if show_ghc:
                        f.write("\\begin{tabular}{l c r r r r r r r r r r r" + papi_colspec + "}\n\\toprule\n")
                    else:
                        f.write("\\begin{tabular}{l c r r r r r r r r" + papi_colspec + "}\n\\toprule\n")
                else:
                    if show_ghc:
                        f.write("\\begin{tabular}{l c r r r r r r r r r r" + papi_colspec + "}\n\\toprule\n")
                    else:
                        f.write("\\begin{tabular}{l c r r r r r r r" + papi_colspec + "}\n\\toprule\n")
                f.write(
                    "\\textbf{Pass} & \\textbf{T}"
                    " & \\textbf{Am} & \\textbf{Ai}"
                    " & \\textbf{Sm}"
                    + (" & \\textbf{Si}" if include_soa_imm else "")
                    +
                    " & \\textbf{Am/Sm}"
                    " & \\textbf{Ai/Am}"
                    " & \\textbf{Ai/Sm}"
                    + (" & \\textbf{Ai/Si}" if include_soa_imm else "")
                    + (" & \\textbf{GHC} & \\textbf{GHC/Am} & \\textbf{GHC/Sm}" if show_ghc else "")
                    + f"{papi_header_suffix} \\\\\n"
                )
        else:
            # Original 2-variant table
            if has_uses:
                if show_ghc:
                    f.write("\\begin{tabular}{l c c r r r r r r r" + papi_colspec + "}\n\\toprule\n")
                else:
                    f.write("\\begin{tabular}{l c c r r r r" + papi_colspec + "}\n\\toprule\n")
                f.write(
                    "\\textbf{Pass} & \\textbf{T}"
                    " & \\textbf{Uses} & \\textbf{Dead\\%}"
                    " & \\textbf{AoS med$\\pm$err} & \\textbf{SoA med$\\pm$err} & \\textbf{Speedup}"
                    + (" & \\textbf{GHC} & \\textbf{GHC/Am} & \\textbf{GHC/Sm}" if show_ghc else "")
                    + f"{papi_header_suffix} \\\\\n"
                )
            else:
                if show_ghc:
                    f.write("\\begin{tabular}{l c r r r r r r" + papi_colspec + "}\n\\toprule\n")
                else:
                    f.write("\\begin{tabular}{l c r r r" + papi_colspec + "}\n\\toprule\n")
                f.write(
                    "\\textbf{Pass} & \\textbf{T}"
                    " & \\textbf{AoS med$\\pm$err} & \\textbf{SoA med$\\pm$err} & \\textbf{Speedup}"
                    + (" & \\textbf{GHC} & \\textbf{GHC/Am} & \\textbf{GHC/Sm}" if show_ghc else "")
                    + f"{papi_header_suffix} \\\\\n"
                )
        f.write("\\midrule\n")

        speedups_mut = []
        speedups_aos_imm_over_aos_mut = []
        speedups_imm = []
        speedups_imm_layout = []
        speedups_ghc_over_aos_mut = []
        speedups_ghc_over_soa_mut = []
        
        octree_passes = []
        color_passes = []
        if prog == "OctTree":
            for pname in passes:
                if pname in ("paletteEntriesQuantized", "quantizationErrorProxy"):
                    color_passes.append(pname)
                else:
                    octree_passes.append(pname)
        else:
            octree_passes = passes

        for pname in octree_passes:
            ad   = aos.passes.get(pname, {})
            sd   = soa.passes.get(pname, {})
            
            ptype = ad.get("pass_type") or sd.get("pass_type") or "unknown"
            tchar = "F" if ptype == "fold" else ("M" if ptype == "map" else "?")
            pdisp = pname.replace("_", "\\_")

            uses   = _first_present(ad.get("uses"), sd.get("uses"))
            dead_r = _first_present(ad.get("dead_ratio"), sd.get("dead_ratio"))
            papi_cells_s = "".join(
                f" & {_papi_pair_cell(ad, sd, counter)}"
                for counter in papi_counter_names
            )

            if show_4_variants:
                # Get data for all 4 variants
                def get_time_info(res, pname):
                    """Get (display, median_time, is_oom) for a pass.  Gated
                    on `prov.verified_result`: a per-pass median from a
                    result that ran but never passed its independent oracle
                    must render as unavailable, not as a real time."""
                    if res is None:
                        return "--", None, False
                    if not prov.verified_result(res):
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
                soat_imm, soat_imm_v, soat_imm_oom = get_time_info(soa_imm, pname) if include_soa_imm else ("--", None, False)
                ghct, ghct_v, ghct_oom = get_time_info(ghc, pname) if show_ghc else ("--", None, False)

                # Bold only the fastest available time across all 4 variants.
                cells = {
                    "aos_mut": [aost_mut, aost_mut_v, aost_mut_oom],
                    "aos_imm": [aost_imm, aost_imm_v, aost_imm_oom],
                    "soa_mut": [soat_mut, soat_mut_v, soat_mut_oom],
                }
                if include_soa_imm:
                    cells["soa_imm"] = [soat_imm, soat_imm_v, soat_imm_oom]
                if show_ghc:
                    cells["ghc"] = [ghct, ghct_v, ghct_oom]
                valid_times = [v[1] for v in cells.values() if v[1] is not None and not v[2]]
                if valid_times:
                    min_t = min(valid_times)
                    for _, v in cells.items():
                        if v[1] is not None and not v[2] and v[1] == min_t:
                            v[0] = f"\\textbf{{{v[0]}}}"

                aost_mut = cells["aos_mut"][0]
                aost_imm = cells["aos_imm"][0]
                soat_mut = cells["soa_mut"][0]
                soat_imm = cells["soa_imm"][0] if include_soa_imm else "--"
                if show_ghc:
                    ghct = cells["ghc"][0]
                
                # Calculate speedups
                def calc_spd(a_res, s_res, pname):
                    if prov.eligible_pair(a_res, s_res):
                        at = a_res.passes.get(pname, {}).get("median_time", 0.0)
                        st = s_res.passes.get(pname, {}).get("median_time", 0.0)
                        if at > 0 and st > 0:
                            return at / st
                    return None
                
                spd_mut = calc_spd(aos, soa, pname)
                spd_aos_imm_over_aos_mut = calc_spd(aos_imm, aos, pname)
                spd_imm = calc_spd(aos_imm, soa, pname)
                spd_imm_layout = calc_spd(aos_imm, soa_imm, pname) if include_soa_imm else None
                spd_ghc_over_aos_mut = calc_spd(ghc, aos, pname) if show_ghc else None
                spd_ghc_over_soa_mut = calc_spd(ghc, soa, pname) if show_ghc else None
                
                spd_mut_s = _spd_cell(spd_mut) if spd_mut else "--"
                spd_aos_imm_over_aos_mut_s = _spd_cell(spd_aos_imm_over_aos_mut) if spd_aos_imm_over_aos_mut else "--"
                spd_imm_s = _spd_cell(spd_imm) if spd_imm else "--"
                spd_imm_layout_s = _spd_cell(spd_imm_layout) if spd_imm_layout else "--"
                spd_ghc_over_aos_mut_s = _spd_cell(spd_ghc_over_aos_mut) if spd_ghc_over_aos_mut else "--"
                spd_ghc_over_soa_mut_s = _spd_cell(spd_ghc_over_soa_mut) if spd_ghc_over_soa_mut else "--"
                
                if spd_mut:
                    speedups_mut.append(spd_mut)
                if spd_aos_imm_over_aos_mut:
                    speedups_aos_imm_over_aos_mut.append(spd_aos_imm_over_aos_mut)
                if spd_imm:
                    speedups_imm.append(spd_imm)
                if spd_imm_layout:
                    speedups_imm_layout.append(spd_imm_layout)
                if spd_ghc_over_aos_mut:
                    speedups_ghc_over_aos_mut.append(spd_ghc_over_aos_mut)
                if spd_ghc_over_soa_mut:
                    speedups_ghc_over_soa_mut.append(spd_ghc_over_soa_mut)
                
                # Write row
                imm_layout_cols = (
                    f" & {soat_imm} & {spd_imm_layout_s}" if include_soa_imm else ""
                )
                if has_uses:
                    adt_total = ad.get("adt_total") or sd.get("adt_total") or adt
                    if adt_total is None and uses is not None and dead_r is not None and (1 - dead_r) > 0:
                        adt_total = int(round(uses / (1 - dead_r)))
                    uses_s = f"{uses}/{adt_total}" if (uses is not None and adt_total is not None) else "--"
                    dead_s = f"{dead_r*100:.0f}\\%" if dead_r is not None else "--"
                    f.write(f"{pdisp} & {tchar} & {uses_s} & {dead_s}"
                            f" & {aost_mut} & {aost_imm}"
                            f" & {soat_mut}"
                            f"{imm_layout_cols}"
                            f" & {spd_mut_s}"
                            f" & {spd_aos_imm_over_aos_mut_s}"
                            f" & {spd_imm_s}"
                            f"{f' & {ghct} & {spd_ghc_over_aos_mut_s} & {spd_ghc_over_soa_mut_s}' if show_ghc else ''}"
                            f"{papi_cells_s} \\\\\n")
                else:
                    f.write(f"{pdisp} & {tchar}"
                            f" & {aost_mut} & {aost_imm}"
                            f" & {soat_mut}"
                            f"{imm_layout_cols}"
                            f" & {spd_mut_s}"
                            f" & {spd_aos_imm_over_aos_mut_s}"
                            f" & {spd_imm_s}"
                            f"{f' & {ghct} & {spd_ghc_over_aos_mut_s} & {spd_ghc_over_soa_mut_s}' if show_ghc else ''}"
                            f"{papi_cells_s} \\\\\n")
            
            else:
                # Original 2-variant logic
                at_s = ad.get("median_time", 0.0)
                st_s = sd.get("median_time", 0.0)
                if at_s == 0.0 and st_s == 0.0:
                    continue

                spd   = at_s / st_s if st_s > 0 else 0.0
                ghd   = ghc.passes.get(pname, {}) if (show_ghc and prov.verified_result(ghc)) else {}

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
                gh_t  = ghd.get("median_time", 0.0) if ghd else 0.0
                gh_e  = ghd.get("stderr", 0.0) if ghd else 0.0
                gh_f  = fmt_pm(gh_t, gh_e) if gh_t > 0 else "--"
                spd_ghc_over_aos_mut = (gh_t / at_s) if (show_ghc and gh_t > 0 and at_s > 0) else None
                spd_ghc_over_soa_mut = (gh_t / st_s) if (show_ghc and gh_t > 0 and st_s > 0) else None
                spd_ghc_over_aos_mut_s = _spd_cell(spd_ghc_over_aos_mut) if spd_ghc_over_aos_mut else "--"
                spd_ghc_over_soa_mut_s = _spd_cell(spd_ghc_over_soa_mut) if spd_ghc_over_soa_mut else "--"

                if has_uses:
                    adt_total = ad.get("adt_total") or sd.get("adt_total") or adt
                    if adt_total is None and uses is not None and dead_r is not None and (1 - dead_r) > 0:
                        adt_total = int(round(uses / (1 - dead_r)))
                    uses_s = f"{uses}/{adt_total}" if (uses is not None and adt_total is not None) else "--"
                    dead_s = f"{dead_r*100:.0f}\\%" if dead_r is not None else "--"
                    f.write(f"{pdisp} & {tchar} & {uses_s} & {dead_s}"
                            f" & {at_f_r} & {st_f_r} & {spd_s}"
                            f"{f' & {gh_f} & {spd_ghc_over_aos_mut_s} & {spd_ghc_over_soa_mut_s}' if show_ghc else ''}"
                            f"{papi_cells_s} \\\\\n")
                else:
                    f.write(f"{pdisp} & {tchar}"
                            f" & {at_f_r} & {st_f_r} & {spd_s}"
                            f"{f' & {gh_f} & {spd_ghc_over_aos_mut_s} & {spd_ghc_over_soa_mut_s}' if show_ghc else ''}"
                            f"{papi_cells_s} \\\\\n")

                if spd > 0:
                    speedups_mut.append(spd)
                if spd_ghc_over_aos_mut:
                    speedups_ghc_over_aos_mut.append(spd_ghc_over_aos_mut)
                if spd_ghc_over_soa_mut:
                    speedups_ghc_over_soa_mut.append(spd_ghc_over_soa_mut)

        if prog == "OctTree" and color_passes:
            f.write("\\midrule\n")
            for pname in color_passes:
                ad   = aos.passes.get(pname, {})
                sd   = soa.passes.get(pname, {})

                ptype = ad.get("pass_type") or sd.get("pass_type") or "unknown"
                tchar = "F" if ptype == "fold" else ("M" if ptype == "map" else "?")
                pdisp = pname.replace("_", "\\_")

                uses   = _first_present(ad.get("uses"), sd.get("uses"))
                dead_r = _first_present(ad.get("dead_ratio"), sd.get("dead_ratio"))
                papi_cells_s = "".join(
                    f" & {_papi_pair_cell(ad, sd, counter)}"
                    for counter in papi_counter_names
                )

                if show_4_variants:
                    def get_time_info(res, pname):
                        """Get (display, median_time, is_oom) for a pass.
                        Gated on `prov.verified_result`, matching the other
                        get_time_info above."""
                        if res is None:
                            return "--", None, False
                        if not prov.verified_result(res):
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
                    soat_imm, soat_imm_v, soat_imm_oom = get_time_info(soa_imm, pname) if include_soa_imm else ("--", None, False)
                    ghct, ghct_v, ghct_oom = get_time_info(ghc, pname) if show_ghc else ("--", None, False)

                    cells = {
                        "aos_mut": [aost_mut, aost_mut_v, aost_mut_oom],
                        "aos_imm": [aost_imm, aost_imm_v, aost_imm_oom],
                        "soa_mut": [soat_mut, soat_mut_v, soat_mut_oom],
                    }
                    if include_soa_imm:
                        cells["soa_imm"] = [soat_imm, soat_imm_v, soat_imm_oom]
                    if show_ghc:
                        cells["ghc"] = [ghct, ghct_v, ghct_oom]
                    valid_times = [v[1] for v in cells.values() if v[1] is not None and not v[2]]
                    if valid_times:
                        min_t = min(valid_times)
                        for _, v in cells.items():
                            if v[1] is not None and not v[2] and v[1] == min_t:
                                v[0] = f"\\textbf{{{v[0]}}}"

                    aost_mut = cells["aos_mut"][0]
                    aost_imm = cells["aos_imm"][0]
                    soat_mut = cells["soa_mut"][0]
                    soat_imm = cells["soa_imm"][0] if include_soa_imm else "--"
                    if show_ghc:
                        ghct = cells["ghc"][0]

                    spd_mut = calc_spd(aos, soa, pname)
                    spd_aos_imm_over_aos_mut = calc_spd(aos_imm, aos, pname)
                    spd_imm = calc_spd(aos_imm, soa, pname)
                    spd_imm_layout = calc_spd(aos_imm, soa_imm, pname) if include_soa_imm else None
                    spd_ghc_over_aos_mut = calc_spd(ghc, aos, pname) if show_ghc else None
                    spd_ghc_over_soa_mut = calc_spd(ghc, soa, pname) if show_ghc else None

                    spd_mut_s = _spd_cell(spd_mut) if spd_mut else "--"
                    spd_aos_imm_over_aos_mut_s = _spd_cell(spd_aos_imm_over_aos_mut) if spd_aos_imm_over_aos_mut else "--"
                    spd_imm_s = _spd_cell(spd_imm) if spd_imm else "--"
                    spd_imm_layout_s = _spd_cell(spd_imm_layout) if spd_imm_layout else "--"
                    spd_ghc_over_aos_mut_s = _spd_cell(spd_ghc_over_aos_mut) if spd_ghc_over_aos_mut else "--"
                    spd_ghc_over_soa_mut_s = _spd_cell(spd_ghc_over_soa_mut) if spd_ghc_over_soa_mut else "--"

                    if spd_mut:
                        speedups_mut.append(spd_mut)
                    if spd_aos_imm_over_aos_mut:
                        speedups_aos_imm_over_aos_mut.append(spd_aos_imm_over_aos_mut)
                    if spd_imm:
                        speedups_imm.append(spd_imm)
                    if spd_imm_layout:
                        speedups_imm_layout.append(spd_imm_layout)
                    if spd_ghc_over_aos_mut:
                        speedups_ghc_over_aos_mut.append(spd_ghc_over_aos_mut)
                    if spd_ghc_over_soa_mut:
                        speedups_ghc_over_soa_mut.append(spd_ghc_over_soa_mut)

                    imm_layout_cols = (
                        f" & {soat_imm} & {spd_imm_layout_s}" if include_soa_imm else ""
                    )
                    if has_uses:
                        adt_total = ad.get("adt_total") or sd.get("adt_total") or adt
                        if adt_total is None and uses is not None and dead_r is not None and (1 - dead_r) > 0:
                            adt_total = int(round(uses / (1 - dead_r)))
                        uses_s = f"{uses}/{adt_total}" if (uses is not None and adt_total is not None) else "--"
                        dead_s = f"{dead_r*100:.0f}\\%" if dead_r is not None else "--"
                        f.write(f"{pdisp} & {tchar} & {uses_s} & {dead_s}"
                                f" & {aost_mut} & {aost_imm}"
                                f" & {soat_mut}"
                                f"{imm_layout_cols}"
                                f" & {spd_mut_s}"
                                f" & {spd_aos_imm_over_aos_mut_s}"
                                f" & {spd_imm_s}"
                                f"{f' & {ghct} & {spd_ghc_over_aos_mut_s} & {spd_ghc_over_soa_mut_s}' if show_ghc else ''}"
                                f"{papi_cells_s} \\\\\n")
                    else:
                        f.write(f"{pdisp} & {tchar}"
                                f" & {aost_mut} & {aost_imm}"
                                f" & {soat_mut}"
                                f"{imm_layout_cols}"
                                f" & {spd_mut_s}"
                                f" & {spd_aos_imm_over_aos_mut_s}"
                                f" & {spd_imm_s}"
                                f"{f' & {ghct} & {spd_ghc_over_aos_mut_s} & {spd_ghc_over_soa_mut_s}' if show_ghc else ''}"
                                f"{papi_cells_s} \\\\\n")
                else:
                    at_s = ad.get("median_time", 0.0)
                    st_s = sd.get("median_time", 0.0)
                    if at_s == 0.0 and st_s == 0.0:
                        continue

                    spd   = at_s / st_s if st_s > 0 else 0.0
                    ghd   = ghc.passes.get(pname, {}) if (show_ghc and prov.verified_result(ghc)) else {}

                    a_err = ad.get("stderr", 0.0)
                    s_err = sd.get("stderr", 0.0)
                    at_f  = fmt_pm(at_s, a_err) if at_s > 0 else "--"
                    st_f  = fmt_pm(st_s, s_err) if st_s > 0 else "--"

                    if spd > 1.1:
                        at_f_r, st_f_r = at_f, f"\\textbf{{{st_f}}}"
                    elif 0 < spd < 0.9:
                        at_f_r, st_f_r = f"\\textbf{{{at_f}}}", st_f
                    else:
                        at_f_r, st_f_r = at_f, st_f

                    spd_s = _spd_cell(spd) if spd > 0 else "--"
                    gh_t  = ghd.get("median_time", 0.0) if ghd else 0.0
                    gh_e  = ghd.get("stderr", 0.0) if ghd else 0.0
                    gh_f  = fmt_pm(gh_t, gh_e) if gh_t > 0 else "--"
                    spd_ghc_over_aos_mut = (gh_t / at_s) if (show_ghc and gh_t > 0 and at_s > 0) else None
                    spd_ghc_over_soa_mut = (gh_t / st_s) if (show_ghc and gh_t > 0 and st_s > 0) else None
                    spd_ghc_over_aos_mut_s = _spd_cell(spd_ghc_over_aos_mut) if spd_ghc_over_aos_mut else "--"
                    spd_ghc_over_soa_mut_s = _spd_cell(spd_ghc_over_soa_mut) if spd_ghc_over_soa_mut else "--"

                    if has_uses:
                        adt_total = ad.get("adt_total") or sd.get("adt_total") or adt
                        if adt_total is None and uses is not None and dead_r is not None and (1 - dead_r) > 0:
                            adt_total = int(round(uses / (1 - dead_r)))
                        uses_s = f"{uses}/{adt_total}" if (uses is not None and adt_total is not None) else "--"
                        dead_s = f"{dead_r*100:.0f}\\%" if dead_r is not None else "--"
                        f.write(f"{pdisp} & {tchar} & {uses_s} & {dead_s}"
                                f" & {at_f_r} & {st_f_r} & {spd_s}"
                                f"{f' & {gh_f} & {spd_ghc_over_aos_mut_s} & {spd_ghc_over_soa_mut_s}' if show_ghc else ''}"
                                f"{papi_cells_s} \\\\\n")
                    else:
                        f.write(f"{pdisp} & {tchar}"
                                f" & {at_f_r} & {st_f_r} & {spd_s}"
                                f"{f' & {gh_f} & {spd_ghc_over_aos_mut_s} & {spd_ghc_over_soa_mut_s}' if show_ghc else ''}"
                                f"{papi_cells_s} \\\\\n")

                    if spd > 0:
                        speedups_mut.append(spd)
                    if spd_ghc_over_aos_mut:
                        speedups_ghc_over_aos_mut.append(spd_ghc_over_aos_mut)
                    if spd_ghc_over_soa_mut:
                        speedups_ghc_over_soa_mut.append(spd_ghc_over_soa_mut)

        # Totals row.  The outer row gate only guarantees aos/soa are
        # verified -- aos_imm/soa_imm/ghc are independent operands here and
        # must be checked on their own (the "verified mutable, unverified
        # immutable" case): `prov.verified_result`, not `run_success`.
        def get_total(res):
            if prov.verified_result(res):
                return total_pass_time(res)
            return None
        
        aost_mut_tot = get_total(aos)
        aost_imm_tot = get_total(aos_imm) if aos_imm else None
        soat_mut_tot = get_total(soa)
        soat_imm_tot = get_total(soa_imm) if soa_imm else None
        ghc_tot = get_total(ghc) if show_ghc else None
        
        def fmt_total(t):
            return fmt(t) if t is not None else "--"
        
        sp_mut_tot = aost_mut_tot / soat_mut_tot if (aost_mut_tot and soat_mut_tot) else None
        sp_aos_imm_over_aos_mut_tot = aost_imm_tot / aost_mut_tot if (aost_imm_tot and aost_mut_tot) else None
        sp_imm_tot = aost_imm_tot / soat_mut_tot if (aost_imm_tot and soat_mut_tot) else None
        sp_imm_layout_tot = aost_imm_tot / soat_imm_tot if (aost_imm_tot and soat_imm_tot) else None
        sp_ghc_over_aos_mut_tot = ghc_tot / aost_mut_tot if (ghc_tot and aost_mut_tot) else None
        sp_ghc_over_soa_mut_tot = ghc_tot / soat_mut_tot if (ghc_tot and soat_mut_tot) else None
        
        if show_4_variants:
            total_cells = {
                "aos_mut": [fmt_total(aost_mut_tot), aost_mut_tot],
                "aos_imm": [fmt_total(aost_imm_tot), aost_imm_tot],
                "soa_mut": [fmt_total(soat_mut_tot), soat_mut_tot],
            }
            if include_soa_imm:
                total_cells["soa_imm"] = [fmt_total(soat_imm_tot), soat_imm_tot]
            if show_ghc:
                total_cells["ghc"] = [fmt_total(ghc_tot), ghc_tot]
            total_valid = [v[1] for v in total_cells.values() if v[1] is not None]
            if total_valid:
                min_tot = min(total_valid)
                for _, v in total_cells.items():
                    if v[1] is not None and v[1] == min_tot:
                        v[0] = f"\\textbf{{{v[0]}}}"

            extra_cols = "& & " if has_uses else ""
            ghc_total_suffix = ""
            if show_ghc:
                ghc_total_suffix = (
                    f" & {total_cells['ghc'][0]}"
                    f" & {_spd_cell(sp_ghc_over_aos_mut_tot) if sp_ghc_over_aos_mut_tot else '--'}"
                    f" & {_spd_cell(sp_ghc_over_soa_mut_tot) if sp_ghc_over_soa_mut_tot else '--'}"
                )
            soa_imm_total_suffix = f" & {total_cells['soa_imm'][0]}" if include_soa_imm else ""
            imm_layout_total_suffix = (
                f" & {_spd_cell(sp_imm_layout_tot) if sp_imm_layout_tot else '--'}"
                if include_soa_imm else ""
            )
            f.write("\\midrule\n")
            f.write(f"\\textbf{{Total}} & {extra_cols}"
                    f"& {total_cells['aos_mut'][0]} & {total_cells['aos_imm'][0]}"
                    f" & {total_cells['soa_mut'][0]}"
                    f"{soa_imm_total_suffix}"
                    f" & {_spd_cell(sp_mut_tot) if sp_mut_tot else '--'}"
                    f" & {_spd_cell(sp_aos_imm_over_aos_mut_tot) if sp_aos_imm_over_aos_mut_tot else '--'}"
                    f" & {_spd_cell(sp_imm_tot) if sp_imm_tot else '--'}"
                    f"{imm_layout_total_suffix}"
                    f"{ghc_total_suffix}"
                    f"{papi_empty_suffix} \\\\\n")
            if speedups_mut:
                gm_mut = statistics.geometric_mean(speedups_mut)
                gm_aos_imm_over_aos_mut = (
                    statistics.geometric_mean(speedups_aos_imm_over_aos_mut)
                    if speedups_aos_imm_over_aos_mut else None
                )
                gm_imm = statistics.geometric_mean(speedups_imm) if speedups_imm else None
                gm_imm_layout = (
                    statistics.geometric_mean(speedups_imm_layout)
                    if speedups_imm_layout else None
                )
                gm_ghc_over_aos_mut = (
                    statistics.geometric_mean(speedups_ghc_over_aos_mut)
                    if speedups_ghc_over_aos_mut else None
                )
                gm_ghc_over_soa_mut = (
                    statistics.geometric_mean(speedups_ghc_over_soa_mut)
                    if speedups_ghc_over_soa_mut else None
                )
                ghc_gm_suffix = ""
                if show_ghc:
                    ghc_gm_suffix = (
                        f" & & {_spd_cell(gm_ghc_over_aos_mut) if gm_ghc_over_aos_mut else '--'}"
                        f" & {_spd_cell(gm_ghc_over_soa_mut) if gm_ghc_over_soa_mut else '--'}"
                    )
                imm_layout_gm_suffix = (
                    f" & {_spd_cell(gm_imm_layout) if gm_imm_layout else '--'}"
                    if include_soa_imm else ""
                )
                pre_speed_cells = "& & & &" if include_soa_imm else "& & &"
                f.write(f"\\textbf{{Geomean}} & {extra_cols}"
                        f"{pre_speed_cells} {_spd_cell(gm_mut)}"
                        f" & {_spd_cell(gm_aos_imm_over_aos_mut) if gm_aos_imm_over_aos_mut else '--'}"
                        f" & {_spd_cell(gm_imm) if gm_imm else '--'}"
                        f"{imm_layout_gm_suffix}"
                        f"{ghc_gm_suffix}"
                        f"{papi_empty_suffix} \\\\\n")
        else:
            extra_cols = "& & " if has_uses else ""
            ghc_total_suffix = ""
            if show_ghc:
                ghc_total_suffix = (
                    f" & {fmt_total(ghc_tot)}"
                    f" & {_spd_cell(sp_ghc_over_aos_mut_tot) if sp_ghc_over_aos_mut_tot else '--'}"
                    f" & {_spd_cell(sp_ghc_over_soa_mut_tot) if sp_ghc_over_soa_mut_tot else '--'}"
                )
            f.write("\\midrule\n")
            f.write(f"\\textbf{{Total}} & {extra_cols}"
                    f"& {fmt_total(aost_mut_tot)} & {fmt_total(soat_mut_tot)} & {_spd_cell(sp_mut_tot) if sp_mut_tot else '--'}"
                    f"{ghc_total_suffix}"
                    f"{papi_empty_suffix} \\\\\n")
            if speedups_mut:
                gm = statistics.geometric_mean(speedups_mut)
                gm_ghc_over_aos_mut = (
                    statistics.geometric_mean(speedups_ghc_over_aos_mut)
                    if speedups_ghc_over_aos_mut else None
                )
                gm_ghc_over_soa_mut = (
                    statistics.geometric_mean(speedups_ghc_over_soa_mut)
                    if speedups_ghc_over_soa_mut else None
                )
                ghc_gm_suffix = ""
                if show_ghc:
                    ghc_gm_suffix = (
                        f" & & {_spd_cell(gm_ghc_over_aos_mut) if gm_ghc_over_aos_mut else '--'}"
                        f" & {_spd_cell(gm_ghc_over_soa_mut) if gm_ghc_over_soa_mut else '--'}"
                    )
                f.write(f"\\textbf{{Geomean}} & {extra_cols}"
                        f"& & & {_spd_cell(gm)}"
                        f"{ghc_gm_suffix}"
                        f"{papi_empty_suffix} \\\\\n")

        f.write("\\bottomrule\n\\end{tabular}\n\\end{table}\n\n\n")
        _table_per_program_papi_one_pair(
            f, prog, pdisplay, passes,
            aos, soa, papi_counter_names_all,
            pair_label="Am/Sm", label_suffix="mut"
        )
        if aos_imm is not None and soa_imm is not None:
            _table_per_program_papi_one_pair(
                f, prog, pdisplay, passes,
                aos_imm, soa_imm, papi_counter_names_all,
                pair_label="Ai/Si", label_suffix="imm"
            )


def _table_per_program_papi_one_pair(
    f, prog: str, pdisplay: str, passes: List[str],
    left: BenchmarkResult, right: BenchmarkResult,
    counters: List[str], pair_label: str, label_suffix: str
) -> None:
    if not counters:
        return
    # Self-defending: a caller-side filter alone is not the contract.
    # `aos`/`soa` happen to be pre-filtered by the caller's row gate, but
    # `aos_imm`/`soa_imm` are not -- so this function enforces its own
    # eligibility regardless of which pair it was handed.
    if not prov.eligible_pair(left, right):
        return
    f.write(f"% -- Table: {prog} PAPI {pair_label} --\n")
    f.write("\\begin{table}[t]\n\\centering\n")
    f.write(
        f"\\caption{{Per-pass PAPI counters for \\texttt{{{pdisplay}}} ({pair_label}). "
        "Each cell is median counter value pair per pass. "
        "Counter headers are abbreviated for compactness: "
        "CYC=CPU cycles, L1D/L1I/L2D/L2I=cache misses, LLC=LLC load misses.}}\n"
    )
    f.write(f"\\label{{tab:{prog}_papi_{label_suffix}}}\n\\small\n")
    f.write("\\setlength{\\tabcolsep}{4pt}\n")
    f.write("\\begin{tabular}{l c" + (" r" * len(counters)) + "}\n\\toprule\n")
    hdr = "\\textbf{Pass} & \\textbf{T}"
    for c in counters:
        hdr += f" & \\textbf{{{_tex_escape(_short_counter_label(c))} ({_tex_escape(pair_label)})}}"
    f.write(hdr + " \\\\\n")
    f.write("\\midrule\n")

    octree_passes = []
    color_passes = []
    if prog == "OctTree":
        for pname in passes:
            if pname in ("paletteEntriesQuantized", "quantizationErrorProxy"):
                color_passes.append(pname)
            else:
                octree_passes.append(pname)
    else:
        octree_passes = passes

    for pname in octree_passes:
        ad = left.passes.get(pname, {})
        sd = right.passes.get(pname, {})
        has_any = any(
            ((ad.get("papi_counters", {}).get(c) or {}).get("median") is not None) or
            ((sd.get("papi_counters", {}).get(c) or {}).get("median") is not None)
            for c in counters
        )
        if not has_any:
            continue
        ptype = ad.get("pass_type") or sd.get("pass_type") or "unknown"
        tchar = "F" if ptype == "fold" else ("M" if ptype == "map" else "?")
        pname_tex = pname.replace("_", "\\_")
        row = f"{pname_tex} & {tchar}"
        for c in counters:
            row += f" & {_papi_pair_cell(ad, sd, c)}"
        f.write(row + " \\\\\n")

    if prog == "OctTree" and color_passes:
        f.write("\\midrule\n")
        for pname in color_passes:
            ad = left.passes.get(pname, {})
            sd = right.passes.get(pname, {})
            has_any = any(
                ((ad.get("papi_counters", {}).get(c) or {}).get("median") is not None) or
                ((sd.get("papi_counters", {}).get(c) or {}).get("median") is not None)
                for c in counters
            )
            if not has_any:
                continue
            ptype = ad.get("pass_type") or sd.get("pass_type") or "unknown"
            tchar = "F" if ptype == "fold" else ("M" if ptype == "map" else "?")
            pname_tex = pname.replace("_", "\\_")
            row = f"{pname_tex} & {tchar}"
            for c in counters:
                row += f" & {_papi_pair_cell(ad, sd, c)}"
            f.write(row + " \\\\\n")

    f.write("\\midrule\n")
    total_row = "\\textbf{Total} & "
    for c in counters:
        at = _papi_total_for_result(left, c)
        st = _papi_total_for_result(right, c)
        total_row += f" & {_fmt_counter(at)}/{_fmt_counter(st)}"
    f.write(total_row + " \\\\\n")
    f.write("\\bottomrule\n\\end{tabular}\n\\end{table}\n\n\n")


def _table_per_program_ghc(f, all_results, all_variants_results):
    """
    One additional table per program for GHC comparison only.
    Columns: GHC runtime, GHC/Am, GHC/Sm.
    """
    variants_map = {entry["program"]: entry for entry in all_variants_results}
    pair_map = {}
    for aos, soa in all_results:
        if aos and soa:
            pair_map[aos.program] = (aos, soa)

    def _merge_passes(member_programs: List[str], merged_name: str):
        aos_m = BenchmarkResult(merged_name, "aos")
        soa_m = BenchmarkResult(merged_name, "soa")
        ghc_m = BenchmarkResult(merged_name, "ghc")
        for res in (aos_m, soa_m, ghc_m):
            res.compile_success = True
            res.run_success = True
            res.passes = {}

        contributors = {"aos": [], "soa": [], "ghc": []}
        for prog_hs in member_programs:
            pair = pair_map.get(prog_hs)
            row = variants_map.get(prog_hs, {})
            if not pair:
                continue
            for variant_name, src in (("aos", pair[0]), ("soa", pair[1]), ("ghc", row.get("ghc"))):
                # Only a VERIFIED source contributes -- see `_merge_octree_results`.
                if not prov.verified_result(src):
                    continue
                contributors[variant_name].append(src)
                dst = aos_m if variant_name == "aos" else (soa_m if variant_name == "soa" else ghc_m)
                for pname, pdata in src.passes.items():
                    out_name = pname
                    if out_name in dst.passes:
                        out_name = f"{prog_hs.replace('.hs', '')}.{pname}"
                    dst.passes[out_name] = dict(pdata)

        aos_m.run_success = len(aos_m.passes) > 0
        soa_m.run_success = len(soa_m.passes) > 0
        ghc_m.run_success = len(ghc_m.passes) > 0
        aos_m.qualification = prov.synthesize_derived_status("aos", merged_name, contributors["aos"])
        soa_m.qualification = prov.synthesize_derived_status("soa", merged_name, contributors["soa"])
        ghc_m.qualification = prov.synthesize_derived_status("ghc", merged_name, contributors["ghc"])
        return aos_m, soa_m, ghc_m

    oct_split_programs = sorted(
        p for p in pair_map.keys()
        if p.startswith("OctTree_") and p.endswith(".hs")
    )
    oct_group_members: List[str] = []
    if oct_split_programs:
        oct_group_members.extend(oct_split_programs)
    elif "OctTree.hs" in pair_map:
        oct_group_members.append("OctTree.hs")
    if oct_group_members and "ColorOctree.hs" in pair_map:
        oct_group_members.append("ColorOctree.hs")

    skip_program_tables = set(oct_split_programs)
    skip_program_tables.add("OctTree.hs")
    if "ColorOctree.hs" in pair_map:
        skip_program_tables.add("ColorOctree.hs")

    grouped_rows: List[Tuple[str, BenchmarkResult, BenchmarkResult, BenchmarkResult]] = []
    if oct_group_members:
        aos_m, soa_m, ghc_m = _merge_passes(oct_group_members, "OctTreeCombined.hs")
        if (prov.verified_result(aos_m) and prov.verified_result(soa_m)
                and prov.verified_result(ghc_m)):
            grouped_rows.append(("OctTree", aos_m, soa_m, ghc_m))

    for aos, soa in all_results:
        if not aos or not soa:
            continue
        prog_hs = aos.program
        if prog_hs in skip_program_tables:
            continue
        ghc = variants_map.get(prog_hs, {}).get("ghc")
        if not (prov.eligible_pair(aos, soa) and prov.verified_result(ghc)):
            continue
        grouped_rows.append((prog_hs.replace(".hs", ""), aos, soa, ghc))

    for prog, aos, soa, ghc in grouped_rows:
        pdisplay = prog.replace("_", "\\_")
        passes = sorted(
            set(list(aos.passes.keys()) + list(soa.passes.keys()) + list(ghc.passes.keys())),
            key=lambda p: _pass_sort_key(p, aos, soa, ghc),
        )
        if not passes:
            continue

        f.write(f"% -- Table: {prog} GHC Comparison --\n")
        f.write("\\begin{table}[t]\n\\centering\n")
        f.write(
            f"\\caption{{Per-pass GHC comparison for \\texttt{{{pdisplay}}}. "
            "Times are median per iteration (s); $\\pm$ shows standard error. "
            "$\\text{GHC}/\\text{Am}$ and $\\text{GHC}/\\text{Sm}$ are speedups.}}\n"
        )
        f.write(f"\\label{{tab:{prog}_ghc}}\n\\small\n")
        f.write("\\begin{tabular}{l c r r r}\n\\toprule\n")
        f.write("\\textbf{Pass} & \\textbf{T} & \\textbf{GHC} & \\textbf{GHC/Am} & \\textbf{GHC/Sm} \\\\\n")
        f.write("\\midrule\n")

        ghc_over_am_vals = []
        ghc_over_sm_vals = []
        octree_passes = []
        color_passes = []
        if prog == "OctTree":
            for pname in passes:
                if pname in ("paletteEntriesQuantized", "quantizationErrorProxy"):
                    color_passes.append(pname)
                else:
                    octree_passes.append(pname)
        else:
            octree_passes = passes

        for pname in octree_passes + (color_passes if prog == "OctTree" else []):
            if prog == "OctTree" and color_passes and pname == color_passes[0]:
                f.write("\\midrule\n")
            ad = aos.passes.get(pname, {})
            sd = soa.passes.get(pname, {})
            gd = ghc.passes.get(pname, {})
            ptype = ad.get("pass_type") or sd.get("pass_type") or gd.get("pass_type") or "unknown"
            tchar = "F" if ptype == "fold" else ("M" if ptype == "map" else "?")

            at = ad.get("median_time", 0.0)
            st = sd.get("median_time", 0.0)
            gt = gd.get("median_time", 0.0)
            ge = gd.get("stderr", 0.0)
            ghc_cell = fmt_pm(gt, ge) if gt > 0 else "--"

            g_over_a = (gt / at) if (gt > 0 and at > 0) else None
            g_over_s = (gt / st) if (gt > 0 and st > 0) else None
            if g_over_a is not None:
                ghc_over_am_vals.append(g_over_a)
            if g_over_s is not None:
                ghc_over_sm_vals.append(g_over_s)

            pname_tex = pname.replace("_", "\\_")
            f.write(
                f"{pname_tex} & {tchar}"
                f" & {ghc_cell}"
                f" & {(_spd_cell(g_over_a) if g_over_a else '--')}"
                f" & {(_spd_cell(g_over_s) if g_over_s else '--')} \\\\\n"
            )

        a_tot = sum(p.get("median_time", 0.0) for p in aos.passes.values())
        s_tot = sum(p.get("median_time", 0.0) for p in soa.passes.values())
        g_tot = sum(p.get("median_time", 0.0) for p in ghc.passes.values())
        g_over_a_tot = (g_tot / a_tot) if (g_tot > 0 and a_tot > 0) else None
        g_over_s_tot = (g_tot / s_tot) if (g_tot > 0 and s_tot > 0) else None
        gm_g_over_a = statistics.geometric_mean(ghc_over_am_vals) if ghc_over_am_vals else None
        gm_g_over_s = statistics.geometric_mean(ghc_over_sm_vals) if ghc_over_sm_vals else None

        f.write("\\midrule\n")
        f.write(
            f"\\textbf{{Total}} &"
            f" & {fmt(g_tot)}"
            f" & {(_spd_cell(g_over_a_tot) if g_over_a_tot else '--')}"
            f" & {(_spd_cell(g_over_s_tot) if g_over_s_tot else '--')} \\\\\n"
        )
        f.write(
            f"\\textbf{{Geomean}} &"
            f" & --"
            f" & {(_spd_cell(gm_g_over_a) if gm_g_over_a else '--')}"
            f" & {(_spd_cell(gm_g_over_s) if gm_g_over_s else '--')} \\\\\n"
        )
        f.write("\\bottomrule\n\\end{tabular}\n\\end{table}\n\n\n")


def compile_latex_preview(tex_file: Path, out_dir: Path):
    out_dir.mkdir(parents=True, exist_ok=True)
    # This document is nothing BUT tables, and LaTeX floats do not survive
    # that.  Two failures, both reproduced at a full run's scale (~150
    # tables):
    #
    #   * \\textfraction reserves 20% of every page for body text, and with no
    #     body text LaTeX defers every `[t]` table -- leaving a BLANK first
    #     page and flushing the tables after it.
    #   * The float queue holds ~18 deferred floats.  Past that, pdflatex
    #     reports "Too many unprocessed floats" and then "Fatal error
    #     occurred, no output PDF file produced" -- the preview silently
    #     produced NO pdf at all for a full campaign.
    #
    # So the preview renders the tables in place rather than as floats.
    # `\\@captype` keeps \\caption numbering them as tables, so captions,
    # \\label and \\ref all behave exactly as before.
    #
    # Preview-only: the generated .tex keeps `[t]`, which is the correct
    # placement when it is \\input into a real paper that does have text.
    wrapper = (
        "\\documentclass{article}\n"
        "\\usepackage{booktabs}\n"
        "\\usepackage{graphicx}\n"
        "\\usepackage{xcolor}\n"
        "\\usepackage[margin=0.5in,a3paper]{geometry}\n"
        "\\makeatletter\n"
        "\\renewenvironment{table}[1][]%\n"
        "  {\\par\\medskip\\noindent\\begin{minipage}{\\linewidth}\\def\\@captype{table}}%\n"
        "  {\\end{minipage}\\par\\medskip}\n"
        "\\makeatother\n"
        "\\begin{document}\\pagestyle{empty}\n"
        f"\\input{{{tex_file.name}}}\n"
        "\\end{document}\n"
    )
    tmp = out_dir / "table_preview.tex"
    tmp.write_text(wrapper)
    if tex_file.parent.resolve() != out_dir.resolve():
        shutil.copy(tex_file, out_dir / tex_file.name)
    try:
        # TWO passes: \ref{} (the per-program tables all cite the
        # configuration legend) resolves out of the .aux file written by the
        # previous run, so a single pass renders every cross-reference as
        # "??" in the caption. The second pass is what fills them in.
        for _ in range(2):
            subprocess.run(
                ["pdflatex", "-interaction=nonstopmode",
                 "-output-directory", str(out_dir), str(tmp)],
                capture_output=True, timeout=60,
            )
        pdf = out_dir / "table_preview.pdf"
        print(f"  {'✓ Table PDF → ' + str(pdf) if pdf.exists() else 'Note: pdflatex produced no PDF'}")
        log = out_dir / "table_preview.log"
        if log.exists():
            undefined = sorted({m for m in re.findall(
                r"Reference `([^']+)' on page \d+ undefined", log.read_text(errors="replace"))})
            if undefined:
                print("  ⚠ still-undefined LaTeX references (will render as '??'): "
                      + ", ".join(undefined))
    except FileNotFoundError:
        print("  Note: pdflatex not found – skipping PDF preview")
    except Exception as e:
        print(f"  Note: PDF preview skipped ({e})")

# ---------------------------------------------------------------------------
# Text + JSON reports
# ---------------------------------------------------------------------------
def write_text_report(all_results: List[Tuple], out_file: Path,
                      all_variants_results: Optional[List[Dict]] = None):
    variants_map: Dict[str, Dict] = {}
    if all_variants_results:
        for entry in all_variants_results:
            variants_map[entry["program"]] = entry

    mismatch_details: List[Tuple[str, Dict]] = []

    # State the campaign-wide arithmetic mode / no-RAN policy in the report
    # itself, and verify every result actually agrees with it -- a
    # mixed-mode report must never be presented as one configuration.
    seen_modes = {r.arith_mode for a, s in all_results for r in (a, s)
                  if r is not None and r.arith_mode is not None}
    seen_no_ran = {r.use_no_ran for a, s in all_results for r in (a, s)
                   if r is not None and r.use_no_ran is not None}
    arith_line = (", ".join(sorted(seen_modes)) if seen_modes else "unknown")
    if len(seen_modes) > 1:
        arith_line += "  *** INCONSISTENT ACROSS RESULTS -- DO NOT TRUST AGGREGATES ***"
    no_ran_line = (", ".join(str(x) for x in sorted(seen_no_ran, key=str)) if seen_no_ran else "unknown")
    lines = ["=" * 72, "GIBBON BENCHMARK REPORT v3.1",
             "=" * 72, f"Generated: {time.strftime('%Y-%m-%d %H:%M:%S')}",
             f"Arithmetic mode (--c-arithmetic): {arith_line}",
             f"No-RAN (--no-ran) in effect: {no_ran_line}", ""]
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
            if not prov.verified_result(res):
                lines.append(f"  {tag}: UNVERIFIED -- {prov.rejection_reason(res)} "
                             "(no qualified timing; ran but not independently verified)")
                continue
            total = total_pass_time(res) or 0.0
            lines.append(f"  {tag}: {total:.4f}s total  [VERIFIED]")
            for pname, pd in res.passes.items():
                t     = pd["pass_type"][0].upper() if pd["pass_type"] != "unknown" else "?"
                uses  = pd.get("uses")
                dr    = pd.get("dead_ratio")
                n_it  = pd.get("n", len(pd.get("iter_times", [])))
                med   = pd["median_time"]
                mean  = pd.get("mean_time", med)
                ci95  = pd.get("ci95_abs")
                ann   = ""
                if uses is not None and adt:
                    ann += f"  uses={uses}/{adt}  dead={dr*100:.0f}%"
                lines.append(
                    f"    [{t}] {pname}: median={med:.4f}s  "
                    f"mean={mean:.4f}s  95%CI=±{fmt_ci95(ci95)}  (n={n_it}){ann}"
                )
        if prov.eligible_pair(aos, soa):
            speedup, _reason = prov.safe_speedup(aos, soa, total_pass_time)
            lines.append(f"  Speedup: {speedup:.3f}×" if speedup is not None else "  Speedup: N/A")
        else:
            lines.append("  Speedup: N/A -- unverified "
                         f"(aos: {prov.rejection_reason(aos)}; soa: {prov.rejection_reason(soa)})")

        ventry = variants_map.get(aos.program)
        if ventry is not None:
            analysis = analyze_outputs_by_variant({
                "aos": ventry.get("aos"),
                "aos_imm": ventry.get("aos_imm"),
                "soa": ventry.get("soa"),
                "soa_imm": ventry.get("soa_imm"),
                "ghc": ventry.get("ghc"),
                "mlton": ventry.get("mlton"),
            })
            status = analysis["is_match"]
            if status is None:
                lines.append("  Output match (successful variants): N/A (fewer than 2 successful variants with output)")
            else:
                lines.append(f"  Output match (successful variants): {'YES' if status else 'NO'}")
            if analysis["failed"]:
                failed_s = ", ".join(f"{v} ({err})" for v, err in analysis["failed"])
                lines.append(f"  Runtime failures excluded from output matching: {failed_s}")
            if status is False:
                mismatch_details.append((aos.program, analysis))
        else:
            analysis = analyze_outputs_by_variant({
                "aos": aos,
                "soa": soa,
                "ghc": None,
                "mlton": None,
            })
            status = analysis["is_match"]
            if status is None:
                lines.append("  Output match: N/A (fewer than 2 successful variants with output)")
            else:
                lines.append(f"  Output match: {'YES' if status else 'NO'}")
            if analysis["failed"]:
                failed_s = ", ".join(f"{v} ({err})" for v, err in analysis["failed"])
                lines.append(f"  Runtime failures excluded from output matching: {failed_s}")
            if status is False:
                mismatch_details.append((aos.program, analysis))

    if mismatch_details:
        lines.append("")
        lines.append("=" * 72)
        lines.append("OFFENDING PROGRAMS (OUTPUT MISMATCH AMONG SUCCESSFUL VARIANTS)")
        lines.append("=" * 72)
        for prog, analysis in mismatch_details:
            lines.append(f"\nProgram: {prog}")
            for variants, out in analysis["groups"]:
                lines.append(f"  Variants: {', '.join(variants)}")
                lines.append("  Output:")
                out_lines = out.splitlines() if out else ["<empty>"]
                for ln in out_lines:
                    lines.append(f"    {ln}")

    prov.atomic_write_text(out_file, "\n".join(lines))
    print(f"  ✓ Text report → {out_file}")


def _ser_result(r: Optional[BenchmarkResult]) -> Optional[Dict]:
    """Serialize one variant's result.  Diagnostic/provenance fields
    (compile/run status, error, ADT/buffer/PAPI-file metadata) are always
    present -- a status/provenance report may retain a labelled row for an
    ineligible result.  `passes` (the raw per-pass numeric timing data) is
    populated ONLY when `prov.verified_result(r)` is true; otherwise it is
    `None` with `passes_omitted_reason` explaining why, so nothing downstream
    can mistake an absent value for a real one.  `qualification` carries the
    full QualificationStatus (oracle status/detail, cross-variant status,
    codegen evidence, `verified`, `eligible_for_reporting`, semantic output)."""
    if r is None:
        return None
    adt_info = getattr(r, "adt_info", None)
    verified = prov.verified_result(r)
    rec = {
        "compile_success":  r.compile_success,
        "run_success":      r.run_success,
        "error":            r.error_message,
        "verified":         verified,
        "arith_mode":       getattr(r, "arith_mode", None),
        "use_no_ran":       getattr(r, "use_no_ran", None),
        "qualification":    r.qualification.as_dict() if r.qualification else None,
        "adt_fields":       getattr(r, "adt_fields", None),
        "adt_type":         adt_info["type_name"] if adt_info else None,
        "aos_buffers":      1,
        "soa_total_buffers": adt_info["soa_total_buffers"] if adt_info else None,
        "nonrec_field_slots": adt_info["nonrec_field_slots"] if adt_info else None,
        "papi_file":        getattr(r, "papi_file", None),
        "papi_counters":    getattr(r, "papi_counters", []),
        "papi_regions_total": getattr(r, "papi_regions_total", 0),
        "papi_regions_used": getattr(r, "papi_regions_used", 0),
    }
    if verified:
        rec["passes"] = {k: {kk: vv for kk, vv in v.items() if kk != "iter_times"}
                         for k, v in r.passes.items()}
        rec["passes_omitted_reason"] = None
    else:
        rec["passes"] = None
        rec["passes_omitted_reason"] = prov.rejection_reason(r)
    return rec


def campaign_provenance(args) -> Dict[str, object]:
    """Everything needed to attribute a number to a run.

    The recorded campaign block used to hold three fields, none of which
    identified the run: no commit, no machine, no compiler, no flags, no
    iteration count.  A later reader could not tell whether a difference from
    a recorded value came from a code change or from a different machine, so
    the numbers could only be re-derived, never compared.

    The Gibbon binary is identified by content, not by path: it is routinely
    built from a worktree other than REPO_ROOT, so the repository's HEAD alone
    can name a commit that did not produce it.
    """
    gib = resolve_gibbon()
    gib_info: Dict[str, object] = {"path": str(gib.path) if gib.path else None,
                                   "resolved_via": gib.origin,
                                   "sha256": gib.sha256}
    if gib.path:
        try:
            if not gib_info["sha256"]:
                h = hashlib.sha256()
                with open(gib.path, "rb") as fh:
                    for chunk in iter(lambda: fh.read(1 << 20), b""):
                        h.update(chunk)
                gib_info["sha256"] = h.hexdigest()
            st = os.stat(gib.path)
            gib_info["size_bytes"] = st.st_size
            gib_info["mtime"] = datetime.datetime.fromtimestamp(
                st.st_mtime).isoformat(timespec="seconds")
        except OSError as e:
            gib_info["error"] = str(e)

    def _git(*a) -> Optional[str]:
        try:
            r = subprocess.run(["git", "-C", str(REPO_ROOT), *a],
                               capture_output=True, text=True, timeout=20)
            return r.stdout.strip() if r.returncode == 0 else None
        except Exception:
            return None

    return {
        "gibbon": gib_info,
        "repo": {"root": str(REPO_ROOT), "head": _git("rev-parse", "HEAD"),
                 "describe": _git("describe", "--always", "--dirty"),
                 "branch": _git("rev-parse", "--abbrev-ref", "HEAD"),
                 "dirty_tracked_files": len([
                     l for l in (_git("status", "--porcelain") or "").splitlines()
                     if l.strip()])},
        "cc": prov.cc_identity(resolve_cc()),
        "machine": _machine_description(),
        "timing": {"iterations": getattr(args, "iterations", None),
                   "warmup_runs": getattr(args, "warmup_runs", None),
                   "warmup_iterations": getattr(args, "warmup_iterations", None),
                   "cooldown_seconds": getattr(args, "cooldown_seconds", None),
                   "size_param": getattr(args, "size_param", None),
                   "pin_cpu": getattr(args, "pin_cpu", None)},
        "codegen": {"simd_isa": getattr(args, "simd_isa", None),
                    "c_arithmetic": getattr(args, "c_arithmetic", None),
                    "sse41": getattr(args, "use_sse41", None),
                    "no_gcc_vectorize": getattr(args, "use_no_gcc_vec", None),
                    "use_ran": getattr(args, "use_ran", None),
                    "store_scalar_field_counts": getattr(args, "store_scalar_field_counts", None),
                    "loopification": getattr(args, "enable_loopification", None),
                    "loop_fusion": getattr(args, "enable_loop_fusion", None),
                    "selective_buffer_sharing": getattr(args, "enable_selective_buffer_sharing", None),
                    "vectorization": getattr(args, "enable_vectorization", None)},
        "driver_argv": sys.argv,
    }


def write_json_results(all_results: List[Tuple], out_file: Path,
                       all_variants_results: Optional[List[Dict]] = None,
                       campaign_extra: Optional[Dict] = None):
    variants_map: Dict[str, Dict] = {}
    if all_variants_results:
        for entry in all_variants_results:
            variants_map[entry["program"]] = entry

    data = []
    for aos, soa in all_results:
        if not aos or not soa:
            continue
        rec = {
            "program": aos.program,
            "aos": _ser_result(aos),
            "soa": _ser_result(soa),
            # Diagnostic only -- AoS/SoA agreeing is NOT an oracle and must
            # never be read as a qualified/verified claim.  See "verified"
            # and "qualification" above for the real gate.
            "output_match": outputs_match(aos, soa),  # backwards-compatible: mutable AoS vs SoA
            "output_match_mutable": outputs_match(aos, soa),
        }
        ventry = variants_map.get(aos.program)
        if ventry is not None:
            aos_imm = ventry.get("aos_imm")
            soa_imm = ventry.get("soa_imm")
            ghc_res = ventry.get("ghc")
            mlton_res = ventry.get("mlton")
            rec["aos_imm"] = _ser_result(aos_imm)
            rec["soa_imm"] = _ser_result(soa_imm)
            rec["ghc"] = _ser_result(ghc_res)
            rec["mlton"] = _ser_result(mlton_res)
            rec["output_match_all_variants"] = outputs_match_all([
                ventry.get("aos"),
                aos_imm,
                ventry.get("soa"),
                soa_imm,
                ghc_res,
                mlton_res,
            ])
        data.append(rec)
    # Campaign-wide arithmetic-mode/no-RAN provenance, plus a mechanical
    # check that this report never silently mixes artifacts built under
    # different arithmetic-mode policies (a report is not one configuration
    # if the results inside it disagree about what that configuration was).
    flat_records = [rv for rec in data for k, rv in rec.items()
                     if k in ("aos", "soa", "aos_imm", "soa_imm") and rv is not None]
    consistency_error = check_arithmetic_mode_consistency(flat_records)
    modes_present = sorted({rv.get("arith_mode") for rv in flat_records
                            if rv.get("arith_mode") is not None})
    no_ran_present = sorted({rv.get("use_no_ran") for rv in flat_records
                             if rv.get("use_no_ran") is not None}, key=str)
    report = {
        "report_schema": prov.REPORT_SCHEMA,
        "generated_at": __import__("datetime").datetime.now().isoformat(timespec="seconds"),
        "campaign": {
            "c_arithmetic_modes_present": modes_present,
            "no_ran_values_present": no_ran_present,
            "arithmetic_mode_consistency_error": consistency_error,
            **(campaign_extra or {}),
        },
        "results": data,
    }
    if consistency_error:
        print(f"  *** WARNING: {consistency_error} ***")
    prov.atomic_write_text(out_file, json.dumps(report, indent=2))
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
    # Every figure plots only independently VERIFIED pairs -- no artist/data
    # point may be emitted for a result that merely compiled and ran.
    good = [(a, s) for a, s in all_results if prov.eligible_pair(a, s)]
    if not good:
        print("  No verified results to plot (all results are unverified, "
              "failed, or lack an independent oracle).")
        return
    print(f"\nGenerating figures ... ({len(good)} verified program(s) of "
          f"{len(all_results)} attempted)")
    _fig_speedup_fold_map(good, out_dir / "speedup_comparison")
    _fig_per_program(good, out_dir)
    _fig_dead_vs_speedup(good, out_dir / "dead_vs_speedup")
    _fig_heatmaps(good, out_dir)
    _fig_breakdown(good, out_dir / "pass_breakdown_all")
    print(f"\n  All figures written to {out_dir}/")

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------
# ---------------------------------------------------------------------------
# Correctness / provenance qualification mode
# ---------------------------------------------------------------------------

VARIANT_FAMILY_LAYOUT = {"aos": ("Linear", "AOS-LINEAR-SOURCE-MARKER"),
                         "soa": ("Factored", "SOA-FACTORED-SOURCE-MARKER")}


def _imported_module_texts(source: Path) -> List[str]:
    """Text of every locally-resolvable `import Foo` module used by `source`,
    read from Foo.hs alongside it.  A program like the OctTree_* family
    declares its ADT (and layout annotation) in a shared module -- e.g.
    `import OctTreeBase` -- rather than in the file itself, so a check that
    only reads `source` never sees the annotation at all."""
    try:
        text = Path(source).read_text(errors="replace")
    except OSError:
        return []
    out = []
    for m in re.finditer(r"^\s*import\s+([A-Za-z][A-Za-z0-9_.']*)", text, re.MULTILINE):
        mod_file = Path(source).parent / (m.group(1) + ".hs")
        try:
            out.append(mod_file.read_text(errors="replace"))
        except OSError:
            pass
    return out


def _source_layout_evidence(source: Path, variant: str) -> Tuple[bool, str]:
    """Read back the source we recorded and confirm it is the layout family the
    variant claims.  This is what detects a swapped AoS/SoA input: the check
    consults the file at the recorded absolute path, not the variant name.

    The layout annotation is looked for in `source` itself AND in any module
    it locally imports (see `_imported_module_texts`), since some programs
    (e.g. the OctTree_* family) declare their ADT in a shared module."""
    fam = "aos" if variant.startswith("aos") else ("soa" if variant.startswith("soa") else None)
    if fam is None:
        return True, "layout check not applicable to %s" % variant
    want_ann, want_marker = VARIANT_FAMILY_LAYOUT[fam]
    try:
        text = Path(source).read_text(errors="replace")
    except OSError as e:
        return False, "cannot read recorded source: %s" % e
    text = "\n".join([text] + _imported_module_texts(source))
    ann_ok = ('"%s"' % want_ann) in text
    # The explicit source marker is opt-in: only programs that declare one (the
    # qualification fixture does) are held to it.  Requiring it universally
    # would falsely condemn every existing benchmark source.
    declares_marker = any(m in text for _, m in VARIANT_FAMILY_LAYOUT.values())
    marker_ok = (want_marker in text) if declares_marker else True
    if ann_ok and marker_ok:
        detail = 'annotation "%s"' % want_ann
        if declares_marker:
            detail += " and %s" % want_marker
        return True, detail + " present"
    missing = []
    if not ann_ok:
        missing.append('annotation "%s"' % want_ann)
    if declares_marker and not marker_ok:
        missing.append(want_marker)
    return False, "recorded source is not %s: missing %s" % (fam.upper(), ", ".join(missing))


def _codegen_evidence(c_file: Optional[Path], variant: str,
                      expect_vectorization: bool) -> Tuple[str, List[str]]:
    """Structural evidence from the generated C.  Recorded SEPARATELY from
    semantic correctness and from timing -- it never makes a wrong answer look
    acceptable."""
    notes: List[str] = []
    if c_file is None or not Path(c_file).exists():
        return "MISSING", ["generated C not found"]
    try:
        txt = Path(c_file).read_text(errors="replace")
    except OSError as e:
        return "MISSING", ["generated C unreadable: %s" % e]
    is_soa = variant.startswith("soa")
    # A FullyFactored SoA layout passes one cursor PER BUFFER, so it emits
    # cursor ARRAYS (`GibCursor x[N]`).  A plain `GibCursor *` appears in AoS
    # too, so counting it would make this check vacuous.
    arrays = len(re.findall(r"GibCursor\s+\**\w+\[\d+\]", txt))
    narrow = len(re.findall(r"\bGibInt8\b", txt))
    notes.append("cursor-array (SoA) declarations: %d" % arrays)
    notes.append("GibInt8 (narrow width) uses: %d" % narrow)
    if is_soa and arrays == 0:
        return "FAIL", notes + ["SoA variant emitted no cursor-array declarations"]
    if narrow == 0:
        return "FAIL", notes + ["fixture declares Int8 but no GibInt8 appears in generated C"]
    if expect_vectorization:
        simd = sorted(set(re.findall(r"gib_vec_[a-z0-9_]+|_mm_[a-z0-9_]+", txt)))
        notes.append("SIMD helpers: %s" % (", ".join(simd[:4]) if simd else "none"))
        if not simd:
            return "FAIL", notes + ["vectorization requested but no SIMD helper emitted"]
    return "OK", notes


_ORACLE_MANIFEST: Optional["prov.OracleManifest"] = None


def default_oracle_manifest() -> "prov.OracleManifest":
    """THE oracle manifest for this process.  Loaded once so full benchmark
    mode and --correctness-only consult the identical entries."""
    global _ORACLE_MANIFEST
    if _ORACLE_MANIFEST is None:
        _ORACLE_MANIFEST = prov.OracleManifest.load_default(Path(__file__).resolve().parent)
    return _ORACLE_MANIFEST


def qualify_variant(program: str, variant: str, source: Optional[Path],
                    compile_ok: bool, compile_err: Optional[str],
                    exec_ok: bool, exec_err: Optional[str],
                    raw_stdout: Optional[str],
                    manifest: Optional["prov.OracleManifest"] = None,
                    allow_unverified: bool = False,
                    c_file: Optional[Path] = None,
                    expect_vectorization: bool = False,
                    check_layout: bool = True) -> "prov.QualificationStatus":
    """Build a QualificationStatus.  THE single oracle-check code path: full
    benchmark mode (`benchmark_program`) and `--correctness-only`
    (`run_correctness_qualification`) both call this, so there is exactly one
    place that decides "did this variant pass an independent oracle" -- never
    a second, parallel implementation that could drift from it.

    Layout and codegen evidence are recorded here too (when `source`/`c_file`
    are given) because a swapped AoS/SoA source or missing SoA structural
    evidence is exactly the kind of thing that must sink the oracle verdict,
    not just decorate it -- see `_source_layout_evidence`/`_codegen_evidence`.
    """
    st = prov.QualificationStatus(variant, str(source) if source else program)
    st.allow_unverified = bool(allow_unverified)
    st.compile_status = prov.COMPILE_OK if compile_ok else prov.COMPILE_FAIL
    if not compile_ok:
        st.notes.append("compile failed: %s" % (compile_err or "")[:400])
        return st

    st.exec_status = prov.EXEC_OK if exec_ok else prov.EXEC_FAIL
    if not exec_ok:
        st.notes.append("run failed: %s" % (exec_err or "")[:300])
        return st

    st.semantic_output = prov.semantic_output(raw_stdout or "")
    st.timing_status = "PRESENT" if re.search(r"^\s*SELFTIMED:", raw_stdout or "", re.M) else "ABSENT"
    manifest = manifest if manifest is not None else default_oracle_manifest()
    # Always ask for a real oracle.  `allow_unverified` is an escape applied
    # AFTER the fact (QualificationStatus.allow_unverified), so the result is
    # labelled UNVERIFIED and `verified` stays False -- it must not be
    # recoloured as "not required" and silently treated as a pass.
    st.oracle_status, st.oracle_detail = manifest.check(program, raw_stdout or "", required=True)

    lay_ok = True
    if check_layout and source is not None and Path(source).exists():
        lay_ok, lay_why = _source_layout_evidence(source, variant)
        st.notes.append("layout: %s" % lay_why)
        if not lay_ok:
            st.oracle_status = prov.ORACLE_FAIL
            st.oracle_detail = lay_why

    if c_file is not None:
        cg_status, cg_notes = _codegen_evidence(c_file, variant, expect_vectorization)
        # A layout mismatch (wrong source swapped in) makes the codegen
        # evidence meaningless too -- it is evidence about the WRONG program.
        st.codegen_status = cg_status if lay_ok else "FAIL"
        st.notes.extend(cg_notes)

    return st


def run_correctness_qualification(args) -> int:
    """Compile + run each selected variant ONCE, check an independent oracle,
    record full provenance, and emit no performance claim.

    Deliberately uses the same compile_one/run_exe construction as full
    benchmark mode -- a parallel test-only path would prove nothing about the
    driver that actually measures.
    """
    here = Path(__file__).resolve().parent
    programs_dir = Path(args.programs_dir).resolve() if args.programs_dir else here / "programs"
    out_dir = Path(args.output_dir).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)
    manifest = prov.OracleManifest.load_default(here)
    program = args.correctness_only
    stem = Path(program).stem

    variants = args.variants or ["aos_mut", "soa_mut"]
    res = resolve_gibbon()
    cc_info = prov.cc_identity(resolve_cc())

    print("=" * 78)
    print("CORRECTNESS / PROVENANCE QUALIFICATION  (no timing is produced)")
    print("=" * 78)
    print(f"  program      : {stem}")
    print(f"  gibbon       : {res.path}  [origin={res.origin} sha256={(res.sha256 or '')[:16]}]")
    print(f"  C compiler   : {cc_info['path']}  ({cc_info.get('version')})")
    print(f"  oracle       : {manifest.path}")
    print(f"  output dir   : {out_dir}")
    print(f"  size-param   : {args.size_param}   iterations: 1   warmups: 0   cooldown: 0")
    print(f"  arithmetic   : {getattr(args, 'c_arithmetic', DEFAULT_C_ARITH_MODE)}  (--c-arithmetic)")
    print()

    statuses: List[prov.QualificationStatus] = []
    records: List[Dict] = []

    for variant in variants:
        src_dir = "AOS" if variant.startswith("aos") else "SOA"
        source = (programs_dir / src_dir / f"{stem}.hs").resolve()
        rec: Dict = {"variant": variant, "source": str(source)}
        print(f"--- {variant} ---")
        if not source.exists():
            st = qualify_variant(stem, variant, source, False, "source not found",
                                 False, None, None, manifest=manifest,
                                 allow_unverified=args.allow_unverified_output)
            st.notes.append("source not found: %s" % source)
            print(f"  source NOT FOUND: {source}")
            statuses.append(st); records.append(rec); continue
        print(f"  source       : {source}")

        opt = dict(store_scalar_field_counts=args.store_scalar_field_counts,
                   enable_loopification=args.enable_loopification,
                   enable_loop_fusion=args.enable_loop_fusion,
                   enable_selective_buffer_sharing=args.enable_selective_buffer_sharing,
                   enable_vectorization=args.enable_vectorization,
                   use_sse41=getattr(args, 'use_sse41', False),
                   use_no_gcc_vec=getattr(args, 'use_no_gcc_vec', False))
        ok, secs, err = compile_one(source, variant, out_dir, args.force_recompile,
                                    use_mutable_cursors=True,
                                    c_arith_mode=getattr(args, "c_arithmetic", DEFAULT_C_ARITH_MODE),
                                    simd_isa=getattr(args, "simd_isa", DEFAULT_SIMD_ISA),
                                    **opt)
        if not ok:
            st = qualify_variant(stem, variant, source, False, err, False, None, None,
                                 manifest=manifest, allow_unverified=args.allow_unverified_output)
            print(f"  COMPILE FAILED")
            statuses.append(st); records.append(rec); continue

        exe = out_dir / f"{stem}.{variant}.exe"
        c_file = out_dir / f"{stem}.{variant}.c"
        bi = out_dir / f"{stem}.{variant}.buildinfo.json"
        try:
            meta = json.loads(bi.read_text())
        except Exception:
            meta = {}
        rec["compile_argv"] = (meta.get("fingerprint") or {}).get("argv")
        rec["compiler"] = (meta.get("fingerprint") or {}).get("compiler")
        rec["cc"] = (meta.get("fingerprint") or {}).get("cc")
        rec["artifacts"] = meta.get("artifacts")
        rec["repo"] = meta.get("repo")
        rec["c_arithmetic"] = meta.get("c_arithmetic")
        rec["use_no_ran"] = meta.get("use_no_ran")

        argv_log: List[List[str]] = []
        rok, elapsed, out, rerr, rc = run_exe(exe, 1, use_iterate_flag=False,
                                              size_param=args.size_param,
                                              record_argv=argv_log)
        rec["run_argv"] = argv_log[0] if argv_log else None
        rec["returncode"] = rc
        if not rok:
            st = qualify_variant(stem, variant, source, True, None, False,
                                 "rc=%s: %s" % (rc, rerr), None,
                                 manifest=manifest, allow_unverified=args.allow_unverified_output)
            print(f"  RUN FAILED (rc={rc})")
            statuses.append(st); records.append(rec); continue

        st = qualify_variant(stem, variant, source, True, None, True, None, out,
                             manifest=manifest, allow_unverified=args.allow_unverified_output,
                             c_file=c_file, expect_vectorization=args.enable_vectorization)

        rec["semantic_output"] = st.semantic_output
        rec["oracle"] = {"status": st.oracle_status, "detail": st.oracle_detail}
        rec["codegen"] = {"status": st.codegen_status, "notes": st.notes}
        print(f"  compile argv : {' '.join(rec['compile_argv'] or [])}")
        print(f"  run argv     : {' '.join(rec['run_argv'] or [])}")
        print(f"  semantic out : {st.semantic_output!r}")
        print(f"  oracle       : {st.oracle_status}  ({st.oracle_detail})")
        print(f"  codegen      : {st.codegen_status}")
        for note in st.notes:
            print(f"  note         : {note}")
        statuses.append(st); records.append(rec)

    xv = prov.cross_variant_check(statuses)
    for st in statuses:
        st.cross_variant_status = xv
    print()
    print("--- summary ---")
    for st in statuses:
        print(f"  {st.variant:<16} {st.label:<14} oracle={st.oracle_status:<12} "
              f"codegen={st.codegen_status} eligible={st.eligible_for_reporting}")
    print(f"  cross-variant : {xv}")
    code = prov.campaign_exit_code(statuses)
    if xv == prov.XVAR_DISAGREE:
        code = 1
    print(f"  VERDICT       : {'QUALIFIED' if code == 0 else 'NOT QUALIFIED'}  (exit {code})")
    print("  NOTE: this mode makes no performance claim.")

    report = {"mode": "correctness-only",
              "program": stem,
              "gibbon": res.as_dict(),
              "cc": cc_info,
              "size_param": args.size_param,
              "iterations": 1, "warmups": 0, "cooldown": 0,
              "c_arithmetic": getattr(args, "c_arithmetic", DEFAULT_C_ARITH_MODE),
              "cross_variant_status": xv,
              "exit_code": code,
              "results": [dict(r, status=s.as_dict())
                          for r, s in zip(records, statuses)]}
    prov.atomic_write_text(out_dir / f"{stem}.qualification.json",
                           json.dumps(report, indent=2, sort_keys=True))
    print(f"  wrote {out_dir / (stem + '.qualification.json')}")
    return code


def build_parser() -> argparse.ArgumentParser:
    """The CLI, built separately from `main` so it can be exercised without
    running a campaign.

    Flag DEFAULTS are load-bearing here -- `--pin-cpu` decides whether the
    driver touches CPU affinity at all -- and a default nobody can reach in
    a test is a default nobody checks."""
    ap = argparse.ArgumentParser(
        description="Gibbon Benchmark Suite v3.1",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=textwrap.dedent("""\
          Diagnosing timing discrepancies vs manual runs:
            1. Run with --dump-raw to save every exe's full stdout to
               benchmark_output/raw_output/*.stdout.txt  then inspect ITER TIMES lines.
            2. For publication-style runs, keep --iterations high enough for
               uncertainty estimates and leave the default warmup enabled.
               For cold single-run debugging, use --iterations 1 --warmup-runs 0.
            3. Run with --clean to force recompilation and rule out stale exes.
               Every run prints the exact exe path and its mtime for verification.
        """),
    )
    ap.add_argument("--programs-dir",   type=Path, default=Path("programs"))
    ap.add_argument("--output-dir",     type=Path, default=Path("benchmark_output"))
    ap.add_argument("--iterations",     type=int,  default=20,
                    help="Number of timed iterations passed as --iterate N to each measured exe run. "
                         "Use enough samples for confidence intervals; use --iterations 1 "
                         "--warmup-runs 0 to match a cold manual run. (default: 20)")
    ap.add_argument("--warmup-runs", type=int, default=1,
                    help="Untimed executable launches before each measured variant run. "
                         "Warmups are discarded and reduce first-run/cache effects. Default: 1.")
    ap.add_argument("--warmup-iterations", type=int, default=1,
                    help="--iterate value used for each warmup launch. Default: 1.")
    ap.add_argument("--cooldown-seconds", type=float, default=3.0,
                    help="Sleep between variant executions to reduce carryover. Default: 3.0; use 0 to disable.")
    ap.add_argument("--programs",       nargs="+",
                    help="Run only these benchmarks instead of the full default list. "
                         "Names may be given as `Trie`, `Trie.hs`, or a path.")
    ap.add_argument("--exclude-programs", nargs="+", default=[], metavar="PATTERN",
                    help="Drop these benchmarks from the run -- the full default list, "
                         "or whatever --programs selected. Use it to leave a broken or "
                         "slow benchmark out of a full evaluation without retyping every "
                         "other name. Each entry is a shell-style glob matched "
                         "case-insensitively against the program names, so a whole "
                         "family comes out in one entry -- e.g. '*oct*ree*' drops all "
                         "nine octree benchmarks (OctTree_*.hs is spelled Oct+Tree, "
                         "ColorOctree.hs is Color+Octree, so 'OctTree*' alone leaves the "
                         "latter in). Quote patterns so your shell does not expand them "
                         "first. Matching is anchored to the whole name, so a plain name "
                         "still matches only itself. "
                         "Applies to the main AoS/SoA campaign and to the "
                         "--pldi-submission variant matrix; the opt-in width families "
                         "(--add1tree-widths / --arithintensity-widths) have their own "
                         "fixed program lists and are unaffected. A pattern that matches "
                         "no program in the run is an error, not a silent no-op.")
    ap.add_argument("--cc", default=None,
                    help=f"C compiler Gibbon shells out to (passed as `gibbon --cc`). "
                         f"Default: {PREFERRED_CC} if present, else gcc. Pinned deliberately: "
                         f"GCC 15 fails to register-promote SoA traversal cursors and inflates "
                         f"SoA fold times by ~2.7x; GCC 16 does not. The chosen compiler and its "
                         f"version are recorded in the report.")
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
    ap.add_argument("--include-build-pass", action="store_true",
                    help="Also benchmark build-only executables and include build timing "
                         "in end-to-end totals and paper tables. Default: off.")
    ap.add_argument("--benchmark-immutable", "--benchmark-imm", action="store_true",
                    help="Also compile and benchmark immutable cursor variants "
                         "(aos_imm, soa_imm) in addition to mutable cursor variants. "
                         "Generates Table 2 showing 4-way comparison.")
    ap.add_argument("--bencmark-baseline-gibbon", "--benchmark-baseline-gibbon",
                    dest="benchmark_baseline_gibbon", action="store_true",
                    help="Baseline Gibbon mode: compile/benchmark aos, soa, aos_imm "
                         "(excludes soa_imm). Generates comparison tables without SoA-imm columns.")
    ap.add_argument("--benchmark-ghc", action="store_true",
                    help="Also compile and benchmark GHC variant (programs/GHC/*.hs).")
    ap.add_argument("--benchmark-mlton", action="store_true",
                    help="Also compile and benchmark MLton variant (programs/MLTON/*.sml).")
    ap.add_argument("--add1tree-widths", action="store_true",
                    help="Also run the four-width add1Tree family "
                         "(ADD1TREE_WIDTH_PROGRAMS) and emit the 'Integer-width add1Tree "
                         "vectorization' table. Narrow opt-in, same pattern as "
                         "--benchmark-ghc/--benchmark-mlton: not part of DEFAULT_PROGRAMS, "
                         "does not affect any other table or aggregate.")
    ap.add_argument("--arithintensity-widths", action="store_true",
                    help="Also run the four-width "
                         "high-arithmetic-intensity family (ARITHINTENSITY_WIDTH_PROGRAMS) "
                         "and emit the 'Integer-width high-arithmetic-intensity "
                         "vectorization' table. Narrow opt-in, same pattern as "
                         "--add1tree-widths. Width 64's Gibbon-SIMD column is always N/A "
                         "(unsupported packed multiply -- see BUGS.md); this flag never "
                         "enables Gibbon vectorization for the W64 variant.")
    ap.add_argument("--roofline", action="store_true",
                    help="Measure this machine's PRACTICAL roofline and plot it: "
                         "single-threaded DRAM bandwidth (STREAM triad past LLC) "
                         "and the peak multiply-add rate for FP64 and for 8/16/32/64-bit "
                         "integers, which is what actually bounds Gibbon's kernels. "
                         "Compiled -O3 -march=native -ffast-math so the ceiling is the "
                         "vectorized one, and pinned to one core. Writes roofline.json, "
                         "a standalone plot script, and roofline.png. Independent of the "
                         "benchmark campaign -- it never invokes gibbon, so it cannot "
                         "disturb a run in progress.")
    ap.add_argument("--roofline-overlay", action="store_true",
                    help="With --roofline, also plot Gibbon's own ArithmeticIntensity "
                         "kernels as points on the roofline, using the suite's existing "
                         "ops/byte metric and the measured pass times. Implies "
                         "--arithintensity-widths, since it needs those measurements.")
    ap.add_argument("--roofline-cpu", type=int, default=0, metavar="N",
                    help="Which CPU to pin the roofline probe to (default: 0). On a "
                         "hybrid CPU choose a performance core; an efficiency core "
                         "measures a genuinely lower ceiling.")
    ap.add_argument("--pldi-submission", action="store_true",
                    help="For every DEFAULT_PROGRAMS entry, compile and run the full AoS/SoA "
                         "variant matrix (recursive immutable/mutable/mutable-no-TCO, plus "
                         "loopified gcc-vec on/off, plus for SoA selective-buffer-sharing and "
                         "Gibbon-vectorization on/off -- up to 13 configs per program) and emit "
                         "one separate fold-pass table and one separate map-pass table per "
                         "program, replacing the combined per-program table for this run. Every "
                         "loopified config uses --opt-loopification alone (no "
                         "--auto-loopification): every curated map function already carries an "
                         "explicit OPT:MayVectorize annotation. Substantially more compiles than "
                         "a normal run; narrow opt-in, same pattern as --add1tree-widths.")
    ap.add_argument("-v", "--verbose", dest="verbose", action="store_true",
                    help="Print the full per-compile log (paths, mtimes, per-variant "
                         "status) and disable the pinned progress display. Use this "
                         "when investigating one specific compile; the default is a "
                         "two-line progress display with warnings and failures still "
                         "printed in full.")
    ap.add_argument("--no-progress", dest="no_progress", action="store_true",
                    help="Disable the pinned progress display without turning the "
                         "full per-compile log back on. Implied when stdout is not a "
                         "terminal, so redirecting to a file never writes escape "
                         "sequences.")
    ap.add_argument("--pin-cpu", dest="pin_cpu", nargs="?",
                    default="none", const="auto", metavar="auto|N|none",
                    help="OPT-IN. Pin every timed run to one CPU so a measurement "
                         "cannot migrate between cores mid-run, and keep the driver "
                         "and the compiles off that CPU. OMIT THIS FLAG and nothing "
                         "is pinned and no affinity is set anywhere -- runs are "
                         "scheduled by the kernel exactly as they were before "
                         "pinning existed. Bare `--pin-cpu` picks a performance "
                         "core automatically, avoiding CPU 0 and its SMT siblings "
                         "because CPU 0 carries most interrupt work; `--pin-cpu N` "
                         "pins to CPU N; `--pin-cpu none` is the same as omitting "
                         "it. Pinning is off by default because it is not free: "
                         "confining every run to a single core also confines it to "
                         "that core's private L1/L2 and to one SMT sibling's share "
                         "of the shared units, and on this suite it made some "
                         "benchmarks measurably WORSE rather than merely quieter. "
                         "Turn it on when run-to-run variance is what you are "
                         "fighting, and compare against an unpinned baseline before "
                         "trusting either.")
    ap.add_argument("--simd-isa", dest="simd_isa",
                    choices=list(SIMD_ISA_CHOICES), default=DEFAULT_SIMD_ISA,
                    help="SIMD instruction set EVERY configuration is compiled for -- "
                         "both Gibbon's own vectorizer (which takes its register width "
                         "from it) and the C compiler's auto-vectorizer (which gets the "
                         "matching -m flag). Passed explicitly to every compile so all "
                         "columns of a comparison target the same hardware. "
                         f"Driver default: {DEFAULT_SIMD_ISA}. "
                         "`sse2` = 128-bit, no -m flag (the x86-64 baseline). "
                         "`avx2` = 256-bit, -mavx2. `native` = 256-bit for Gibbon, "
                         "-march=native for the C compiler -- avoid it for comparisons "
                         "on an AVX-512 machine, where it lets the C compiler go wider "
                         "than Gibbon's vectorizer can.")
    ap.add_argument("--c-arithmetic", dest="c_arithmetic",
                    choices=list(C_ARITH_MODES), default=DEFAULT_C_ARITH_MODE,
                    help="Scalar C arithmetic mode passed EXPLICITLY as "
                         "gibbon --c-arithmetic=<mode> for every Gibbon compile "
                         "this driver issues -- never left to Gibbon's own "
                         "compiler default (which is `portable`). Driver default: "
                         f"{DEFAULT_C_ARITH_MODE}. "
                         "`portable` = deterministic RTS-helper add/sub/mul, no C "
                         "flag needed. `wrapv` = native C operators + Gibbon's own "
                         "-fwrapv on every C compile/link path it controls. "
                         "`unsafe` = native C operators, NO -fwrapv or equivalent -- "
                         "an artifact compiled under one mode is never reused under "
                         "another (the mode is part of the content-addressed build "
                         "fingerprint).")

    ap.add_argument("--enable-papi", action="store_true",
                    help="Compile with --enable-papi, export PAPI_EVENTS, parse papi_hl_output JSON, "
                         "and add PAPI columns to tables.")
    ap.add_argument("--enable-papi-native", "--enable-papi_native",
                    dest="enable_papi_native", action="store_true",
                    help="Compile with --enable-papi-native, parse PAPI_NATIVE stdout lines, "
                         "and add native PAPI columns to tables.")
    ap.add_argument("--defer-scalar-counts", dest="defer_scalar_counts",
                    action="store_true",
                    help="Compile SoA variants with --defer-scalar-counts: the "
                         "producer batches its per-element count increments into "
                         "one global counter and flushes at growth and after a "
                         "call, instead of bumping a footer per element. "
                         "Requires --store-scalar-field-counts (there is nothing "
                         "to defer without the footers), and the compiler rejects "
                         "the pair with --gen-gc. Off by default.")
    ap.add_argument("--store-scalar-field-counts", action="store_true",
                    help="Enable scalar-count footer metadata for SoA builders annotated with OPT:StoreScalarCounts. "
                         "This flag is not passed to AoS variants.")
    ap.add_argument("--opt-loopification", dest="enable_loopification", action="store_true",
                    help="Enable map-traversal loopification. The benchmark harness always also "
                         "passes --auto-loopification when this is on, so supported maps loopify "
                         "structurally -- no manual OPT:MayVectorize annotation is required for "
                         "these driver-driven compiles. For an SoA target this requires "
                         "--store-scalar-field-counts (the compiler exits with an error otherwise, "
                         "whenever an SoA candidate exists); AoS flat-map loopification has no such "
                         "requirement.")
    ap.add_argument("--opt-loop-fusion", dest="enable_loop_fusion", action="store_true",
                    help="Enable post-loopification loop fusion for fully factored SoA scalar-buffer "
                         "loops. Requires --opt-loopification to also be on (the compiler exits with "
                         "an error otherwise). This flag is not passed to AoS variants.")
    ap.add_argument("--opt-selective-buffer-sharing", dest="enable_selective_buffer_sharing", action="store_true",
                    help="Enable post-loopification selective sharing for unchanged fully factored SoA "
                         "buffers. Requires --opt-loopification to also be on (the compiler exits with "
                         "an error otherwise). This flag is not passed to AoS variants.")
    ap.add_argument("--opt-vectorization", dest="enable_vectorization", action="store_true",
                    help="Enable SIMD vectorization for supported loopified fully factored SoA "
                         "scalar-buffer loops. Requires --opt-loopification to also be on (the "
                         "compiler exits with an error otherwise). This flag is not passed to AoS "
                         "variants.")
    # Tombstone for the removed whole-program width mode.  Recognized ONLY so it
    # can be rejected with an actionable message; it is suppressed from --help,
    # stores nothing, and never reaches configuration.  Integer width is a
    # property of the source program (`Int8`/`Int16`/`Int32`/`Int64`; bare `Int`
    # is `Int64`), not of a benchmark run, and a mixed-width program has no
    # single width for a flag to select.
    # --- correctness / provenance qualification -------------------------------
    ap.add_argument("--variants", nargs="+", default=None,
                    help="Variants to qualify with --correctness-only "
                         "(default: aos_mut soa_mut).")
    ap.add_argument("--force-recompile", action="store_true",
                    help="Recompile even when the content-addressed fingerprint says "
                         "the artifacts are current.")
    ap.add_argument("--correctness-only", metavar="PROGRAM", default=None,
                    help="Qualify PROGRAM for correctness and provenance instead of "
                         "benchmarking it: compile the selected variants, run each once "
                         "with no warmup or cooldown, check an INDEPENDENT oracle, record "
                         "compiler/artifact/codegen provenance, and emit no performance "
                         "claim.  Exits nonzero on any compile, run, oracle or "
                         "cross-variant failure.")
    ap.add_argument("--allow-unverified-output", action="store_true",
                    help="Permit a program with no independent oracle to proceed.  The "
                         "result is labelled UNVERIFIED and is excluded from "
                         "correctness-qualified performance tables; it is NOT treated as "
                         "a pass.")
    ap.add_argument("--size-param", type=int, default=0,
                    help="Value passed to each executable as --size-param. "
                         "Default 0, which is the historical driver behaviour.")
    ap.add_argument("--int32", "--gibbon-int32", dest="removed_int32_mode",
                    action="store_true", help=argparse.SUPPRESS)
    ap.add_argument("--sse4.1", "--gibbon-sse41", dest="use_sse41", action="store_true",
                    help="Compile Gibbon variants with --sse4.1 (adds -msse4.1 to the generated C). "
                         "-msse4.1 affects the whole translation unit, including the scalar tail and "
                         "GCC's own auto-vectorizer, so a scalar baseline must be compiled at the same "
                         "ISA for the comparison to isolate the effect of Gibbon's vectorizer. It is "
                         "NOT independent of Gibbon's own codegen: it raises the selected ISA, and "
                         "Gibbon then emits _mm_mullo_epi32 for the W32 multiply and _mm_cmpeq_epi64 "
                         "for the 64-bit compare, instead of the baseline SSE2 sequences.")
    ap.add_argument("--no-gcc-vectorize", dest="use_no_gcc_vec", action="store_true",
                    help="Compile Gibbon variants with --no-gcc-vectorize (disables the C compiler's "
                         "own loop AND SLP auto-vectorization on the generated C only, not the RTS -- "
                         "gcc gets -fno-tree-loop-vectorize -fno-tree-slp-vectorize, clang gets "
                         "-fno-vectorize -fno-slp-vectorize). Leaves explicit SIMD intrinsics intact, "
                         "which is what isolates Gibbon's own vectorizer from the C compiler's. Without "
                         "this, a run with --opt-vectorization off is still auto-vectorized by the C "
                         "compiler and is NOT a scalar baseline.")
    ap.add_argument("--reclaim-iterate-regions", dest="reclaim_iterate_regions",
                    action="store_true",
                    help="Compile EVERY variant with Gibbon's "
                         "--reclaim-iterate-regions, so the region chunks each "
                         "--iterate iteration grows are freed instead of stranded. "
                         "Without it, memory grows by one whole output value per "
                         "iteration (929 MB/iteration for a 100M-element list -- an "
                         "OOM kill at --iterate 101), which puts a hard ceiling on "
                         "how many iterations a large benchmark can run. Applied "
                         "uniformly to every configuration in the run: a campaign "
                         "where some columns reclaim and others do not is not "
                         "comparable. Expect large benchmarks to get FASTER as well "
                         "as smaller -- the un-fixed loop makes the kernel supply "
                         "fresh zeroed pages for memory it has leaked, and that cost "
                         "is an artifact of the leak, not of the workload.")
    ap.add_argument("--use-ran", "--enable-ran", dest="use_ran", action="store_true",
                    help="Compile Gibbon variants with random-access nodes enabled by omitting --no-ran. Does not add GHC/MLton variants.")
    return ap


def resolve_pin_cpu_arg(raw) -> Optional[int]:
    """Turn the raw --pin-cpu value into a CPU number, or None for "do not
    pin". None is what the flag resolves to when it is OMITTED, and it must
    mean NO affinity call anywhere -- see `reserve_pin_cpu`, which returns
    early on None rather than narrowing the driver's own mask."""
    if raw is None:
        return None
    text = str(raw).strip().lower()
    if text in ("none", "off", ""):
        return None
    if text == "auto":
        return default_pin_cpu()
    return int(text)


def main():
    ap = build_parser()
    args = ap.parse_args()
    # Set BEFORE anything reads it -- the run banner and every compile do.
    # This lived further down and the banner, printed above it, always reported
    # "off" even when the flag was given.
    set_reclaim_iterate_regions(args.reclaim_iterate_regions)

    if getattr(args, "correctness_only", None):
        return run_correctness_qualification(args)

    # Reject the removed whole-program width mode before ANY status output,
    # output-directory creation or compilation happens.
    if getattr(args, "removed_int32_mode", False):
        print("error: --int32/--gibbon-int32 has been removed; use explicit Int32 "
              "source types.\n"
              "       Integer width is declared by the source program (Int8/Int16/"
              "Int32/Int64;\n"
              "       bare Int means Int64), so a benchmark flag can no longer "
              "reinterpret it.\n"
              "       Write an explicit-width source variant instead.",
              file=sys.stderr)
        return 2

    global SELECTED_CC
    SELECTED_CC = resolve_cc(args.cc)
    print(f"  C compiler   : {SELECTED_CC}  ({cc_version(SELECTED_CC)})")

    if args.enable_papi and args.enable_papi_native:
        ap.error("Choose only one mode: --enable-papi OR --enable-papi-native")
    if args.benchmark_immutable and args.benchmark_baseline_gibbon:
        ap.error("Choose only one mode: --benchmark-imm OR --bencmark-baseline-gibbon")

    try:
        programs_to_run = resolve_program_selection(args.programs, args.exclude_programs,
                                                    programs_dir=args.programs_dir)
    except ProgramSelectionError as e:
        ap.error(str(e))

    # --verbose restores the full log AND turns the bar off: the two are
    # alternatives, since a two-line bar is unreadable beside a scrolling log.
    import bench_progress
    _display = bench_progress.ProgressDisplay(
        enabled=not (args.verbose or args.no_progress))
    set_progress(_display)
    # Quiet ONLY while the bar is actually visible. If the display is off --
    # output redirected to a file, --no-progress, or a dumb terminal -- the
    # log is the only progress signal there is, so it stays in full.
    set_verbosity(bool(args.verbose) or not _display.enabled)
    # Phase totals are registered up front so the bar shows overall
    # completion, not just progress through whichever phase is running.
    _n_variants = 4 if (args.benchmark_immutable or args.benchmark_baseline_gibbon) else 2
    _display.add_phase("campaign", "campaign",
                       len(programs_to_run) * _n_variants)
    if args.pldi_submission:
        try:
            _pldi_n = len(resolve_program_selection(
                args.programs, args.exclude_programs,
                default_programs=DEFAULT_PROGRAMS + PLDI_EXTRA_PROGRAMS,
                programs_dir=args.programs_dir))
        except ProgramSelectionError:
            _pldi_n = len(programs_to_run)
        _display.add_phase(
            "pldi", "variant matrix",
            _pldi_n * sum(len(v) for v in PLDI_MAP_CONFIGS.values()))
    # Writing tables and running pdflatex takes seconds, nothing like a
    # benchmark unit, so it is shown as a phase but excluded from the estimate.
    _display.add_phase("report", "tables", 1, estimate=False)
    _display.install()
    _display.start_phase("campaign")

    if args.roofline and not (args.roofline_overlay or args.generate_paper):
        # Standalone: measure, write, done. No compiles, no campaign.
        return _run_roofline_only(args)

    print("\n" + "=" * 72)
    print("GIBBON BENCHMARK SUITE v3.1")
    print("=" * 72)
    print(f"  Programs dir : {args.programs_dir}")
    print(f"  Output dir   : {args.output_dir}")
    print(f"  Iterations   : {args.iterations} timed samples per pass (--iterate N)")
    print(f"  Warmup       : {args.warmup_runs} run(s) × --iterate {args.warmup_iterations}")
    print(f"  Cooldown     : {args.cooldown_seconds:g}s between variants")
    print(f"  Programs     : {len(programs_to_run)}")
    if args.exclude_programs:
        # Report the programs actually dropped, not the raw patterns -- with
        # globs allowed, `OctTree*` alone does not say which eight it took.
        kept = set(programs_to_run)
        dropped = [normalize_program_name(p)
                   for p in (args.programs or DEFAULT_PROGRAMS)
                   if normalize_program_name(p) not in kept]
        print(f"  Excluded     : {len(dropped)} ({', '.join(dropped)})")
    print(f"  Force recomp : {'YES  (--clean)' if args.clean else 'no  (smart mtime check)'}")
    print(f"  Paper mode   : {'YES' if args.generate_paper else 'no'}")
    print(f"  Dump raw     : {'YES → benchmark_output/raw_output/' if args.dump_raw else 'no'}")
    print(f"  Build pass   : {'YES (included in totals/tables)' if args.include_build_pass else 'no'}")
    print(f"  Scalar counts: {'enabled for SoA (--store-scalar-field-counts)' if args.store_scalar_field_counts else 'off'}"
          + (", deferred delivery (--defer-scalar-counts)"
             if args.store_scalar_field_counts and args.defer_scalar_counts else ""))
    print(f"  Loopification: {'enabled (--opt-loopification + --auto-loopification)' if args.enable_loopification else 'off'}")
    print(f"  Loop fusion  : {'enabled for SoA (--opt-loop-fusion)' if args.enable_loop_fusion else 'off'}")
    print(f"  Selective sh.: {'enabled for SoA (--opt-selective-buffer-sharing)' if args.enable_selective_buffer_sharing else 'off'}")
    print(f"  Vectorization: {'enabled for SoA (--opt-vectorization)' if args.enable_vectorization else 'off'}")
    # Width is a source property, and a mixed-width program has none globally, so
    # the suite header states the rule rather than a value.
    print(f"  Int width    : declared by each source (bare Int = Int64)")
    print(f"  SSE4.1       : {'enabled (--sse4.1)' if args.use_sse41 else 'off (baseline SSE2)'}")
    print(f"  GCC autovec  : {'DISABLED (--no-gcc-vectorize)' if args.use_no_gcc_vec else 'enabled (default -O3)'}")
    print(f"  RAN          : {'enabled (omit --no-ran)' if args.use_ran else 'disabled (--no-ran)'}")
    print(f"  Region reclaim: "
          + ("ON (--reclaim-iterate-regions; per-iteration chunks freed, "
             "peak memory flat in iteration count)"
             if RECLAIM_ITERATE_REGIONS else
             "off (default; memory grows one output value per --iterate "
             "iteration -- pass --reclaim-iterate-regions)"))
    args.pin_cpu = resolve_pin_cpu_arg(args.pin_cpu)
    _reserved = reserve_pin_cpu(args.pin_cpu)
    print(f"  Pinned CPU   : "
          + (f"{args.pin_cpu} (--pin-cpu; timed runs cannot migrate between cores"
             + ("; reserved -- driver and compiles excluded from it)" if _reserved
                else "; NOT reserved -- driver may share it)")
             if args.pin_cpu is not None
             else "none (default: no affinity set; runs may migrate between "
                  "P- and E-cores -- pass --pin-cpu to pin)"))
    print(f"  SIMD ISA     : {args.simd_isa}  (--simd-isa; driver default: {DEFAULT_SIMD_ISA}; "
          f"Gibbon vectorizer and C auto-vectorizer both target it)")
    print(f"  Arithmetic   : {args.c_arithmetic}  (--c-arithmetic; driver default: {DEFAULT_C_ARITH_MODE}; "
          f"{'no -fwrapv' if args.c_arithmetic == 'unsafe' else ('Gibbon adds -fwrapv' if args.c_arithmetic == 'wrapv' else 'RTS-helper calls')})")
    if args.benchmark_immutable:
        imm_s = "YES  (4 variants: aos, aos_imm, soa, soa_imm)"
    elif args.benchmark_baseline_gibbon:
        imm_s = "YES  (baseline: aos, aos_imm, soa)"
    else:
        imm_s = "no  (2 variants: aos, soa)"
    print(f"  Immutable    : {imm_s}")
    print(f"  GHC          : {'YES' if args.benchmark_ghc else 'no'}")
    print(f"  MLton        : {'YES' if args.benchmark_mlton else 'no'}")
    papi_mode = ("native" if args.enable_papi_native else ("high-level" if args.enable_papi else "off"))
    print(f"  PAPI mode    : {papi_mode}")
    print(f"  CPU cores    : {multiprocessing.cpu_count()}")
    
    # Show which gibbon compiler will be used and its mtime
    _res = resolve_gibbon()
    if _res.path is not None:
        print(f"  Gibbon       : {_res.path}")
        vprint(f"                 origin={_res.origin} sha256={(_res.sha256 or '')[:16]}")
    else:
        print(f"  Gibbon       : NOT RESOLVED (set GIBBON_EXE or build gibbon)")
    _cc = prov.cc_identity(resolve_cc())
    print(f"  C compiler   : {_cc['path']}")
    vprint(f"                 {_cc.get('version') or 'version unknown'}")
    for comp in ["ghc", "mlton"]:
        if comp == "ghc" and not args.benchmark_ghc: continue
        if comp == "mlton" and not args.benchmark_mlton: continue
        info = get_compiler_info(comp)
        if info:
            path, t = info
            print(f"  Compiler     : {path}")
        else:
            print(f"  Compiler     : {comp} NOT FOUND in PATH")

    global _PAPI_SELECTED_EVENTS, _PAPI_COUNTER_ORDER
    if args.enable_papi:
        _PAPI_SELECTED_EVENTS = select_preferred_papi_events()
        _PAPI_COUNTER_ORDER = list(_PAPI_SELECTED_EVENTS)
        if _PAPI_SELECTED_EVENTS:
            papi_events_str = ",".join(_PAPI_SELECTED_EVENTS)
            os.environ["PAPI_EVENTS"] = papi_events_str
            print(f"  PAPI_EVENTS  : {papi_events_str}")
            print(f"  Export cmd   : export PAPI_EVENTS=\"{papi_events_str}\"")
        else:
            print("  PAPI warning : no preferred PAPI events found via papi_avail")
    elif args.enable_papi_native:
        _PAPI_COUNTER_ORDER = select_preferred_papi_native_metrics()
        print(f"  Native PAPI metrics: {', '.join(_PAPI_COUNTER_ORDER)}")

    print("=" * 72)

    args.output_dir.mkdir(parents=True, exist_ok=True)
    source_cls_all = build_source_classification(args.programs_dir)

    # Initialize global storage for extended results (used by new comparison table)
    # Always initialize this to capture GHC/MLton results if requested
    benchmark_program._all_variants_results = []

    all_results: List[Tuple] = []
    for prog in programs_to_run:
        progress().item(prog.replace(".hs", ""), "campaign")
        aos, soa = benchmark_program(
            prog, args.programs_dir, args.output_dir,
            args.iterations, args.clean, source_cls_all,
            pin_cpu=args.pin_cpu,
            dump_raw=args.dump_raw,
            include_build_pass=args.include_build_pass,
            benchmark_immutable=args.benchmark_immutable,
            benchmark_baseline_gibbon=args.benchmark_baseline_gibbon,
            benchmark_ghc=args.benchmark_ghc,
            benchmark_mlton=args.benchmark_mlton,
            enable_papi=args.enable_papi,
            enable_papi_native=args.enable_papi_native,
            store_scalar_field_counts=args.store_scalar_field_counts,
            defer_scalar_counts=args.defer_scalar_counts,
            enable_loopification=args.enable_loopification,
            enable_loop_fusion=args.enable_loop_fusion,
            enable_selective_buffer_sharing=args.enable_selective_buffer_sharing,
            enable_vectorization=args.enable_vectorization,
            use_sse41=args.use_sse41,
            use_no_gcc_vec=args.use_no_gcc_vec,
            use_ran=args.use_ran,
            warmup_runs=args.warmup_runs,
            warmup_iterations=args.warmup_iterations,
            cooldown_seconds=args.cooldown_seconds,
            allow_unverified_output=args.allow_unverified_output,
            c_arith_mode=args.c_arithmetic,
        )
        progress().advance(2)   # one AoS + one SoA variant
        all_results.append((aos, soa))

    extended_results = getattr(benchmark_program, '_all_variants_results', [])
    verified_count = sum(1 for a, s in all_results if prov.eligible_pair(a, s))

    if args.benchmark_immutable:
        ok = sum(
            1 for e in extended_results
            if all(
                r is not None and r.run_success
                for r in [e.get("aos"), e.get("aos_imm"), e.get("soa"), e.get("soa_imm")]
            )
        )
        match = sum(
            1 for e in extended_results
            if all(
                r is not None and r.run_success
                for r in [e.get("aos"), e.get("aos_imm"), e.get("soa"), e.get("soa_imm")]
            ) and analyze_outputs_by_variant({
                "aos": e.get("aos"),
                "aos_imm": e.get("aos_imm"),
                "soa": e.get("soa"),
                "soa_imm": e.get("soa_imm"),
            })["is_match"] is True
        )
    elif args.benchmark_baseline_gibbon:
        ok = sum(
            1 for e in extended_results
            if all(
                r is not None and r.run_success
                for r in [e.get("aos"), e.get("aos_imm"), e.get("soa")]
            )
        )
        match = sum(
            1 for e in extended_results
            if all(
                r is not None and r.run_success
                for r in [e.get("aos"), e.get("aos_imm"), e.get("soa")]
            ) and analyze_outputs_by_variant({
                "aos": e.get("aos"),
                "aos_imm": e.get("aos_imm"),
                "soa": e.get("soa"),
            })["is_match"] is True
        )
    else:
        ok    = sum(1 for a, s in all_results if a and s and a.run_success and s.run_success)
        match = sum(1 for a, s in all_results
                    if a and s and a.run_success and s.run_success and outputs_match(a, s))

    print(f"\n\n{'='*72}")
    match_den = ok if ok > 0 else 0
    if args.benchmark_immutable:
        print(f"DONE  –  {ok}/{len(all_results)} succeeded (all 4 variants)  |  {match}/{match_den} output matches (successful variants)")
    elif args.benchmark_baseline_gibbon:
        print(f"DONE  –  {ok}/{len(all_results)} succeeded (baseline variants)  |  {match}/{match_den} output matches (successful variants)")
    else:
        print(f"DONE  –  {ok}/{len(all_results)} succeeded  |  {match}/{match_den} output matches")
    # "succeeded"/"output matches" above are run-health/cross-variant
    # diagnostics -- compiling, running, and two variants agreeing with EACH
    # OTHER is not an oracle and is not a performance claim. This is the ONE
    # line that says how many programs may contribute a number to any
    # table, plot, or report below.
    if verified_count == 0:
        print(f"VERIFIED (independent oracle PASS, mutable AoS/SoA) – 0/{len(all_results)}: "
              "NO VERIFIED RESULTS. No speedup, aggregate, plot, or qualified "
              "table entry will be produced; see the JSON report's "
              "'qualification'/'passes_omitted_reason' fields for why each "
              "program was rejected.")
    else:
        print(f"VERIFIED (independent oracle PASS, mutable AoS/SoA) – {verified_count}/{len(all_results)}")
    print(f"{'='*72}")

    print("\nWriting reports ...")
    write_text_report(all_results, args.report, extended_results)
    campaign_block = campaign_provenance(args)
    write_json_results(all_results, args.json, extended_results,
                       campaign_extra=campaign_block)

    if args.generate_paper:
        print(f"\n{'='*72}")
        print("Generating conference paper materials ...")
        print(f"{'='*72}")
        add1tree_width_results = None
        if args.add1tree_widths:
            print("  Collecting Add1TreeIntN.hs width results ...")
            add1tree_width_results = collect_add1tree_width_results(
                args.programs_dir, args.output_dir, resolve_cc(args.cc),
                args.force_recompile, gibbon_exe=None, iterations=args.iterations,
                c_arith_mode=args.c_arithmetic,
                simd_isa=args.simd_isa, pin_cpu=args.pin_cpu)
        arithintensity_width_results = None
        if args.arithintensity_widths or args.roofline_overlay:
            print("  Collecting ArithmeticIntensityIntN.hs width results ...")
            arithintensity_width_results = collect_arithintensity_width_results(
                args.programs_dir, args.output_dir, resolve_cc(args.cc),
                args.force_recompile, gibbon_exe=None, iterations=args.iterations,
                c_arith_mode=args.c_arithmetic,
                simd_isa=args.simd_isa, pin_cpu=args.pin_cpu)
        if args.roofline:
            # After the campaign, so the overlay has measurements to place.
            print("  Measuring the machine's empirical roofline ...")
            try:
                rl = run_roofline_probe(args.output_dir, resolve_cc(args.cc),
                                        pin_cpu=args.roofline_cpu)
                measured_bytes = None
                if args.roofline_overlay and arithintensity_width_results:
                    measured_bytes = {}
                    if perf_dram_counters_available():
                        print("  Measuring real DRAM traffic per kernel "
                              "(perf uncore IMC, differential) ...")
                        for width, cfgs in sorted(arithintensity_width_results.items()):
                            for cfg, res in cfgs.items():
                                if not prov.verified_result(res):
                                    continue
                                exe = (args.output_dir /
                                       ("ArithmeticIntensityInt%d.%s.exe" % (width, cfg)))
                                if not exe.exists():
                                    continue
                                b = measure_dram_bytes_per_iteration(
                                    exe, cpu=args.roofline_cpu)
                                if b:
                                    measured_bytes[(width, cfg)] = b
                                    vprint("      Int%-2d %-12s %8.1f MB/iteration"
                                          % (width, cfg, b / 1e6))
                    else:
                        print("  Note: no usable DRAM counters (PAPI reports 0 "
                              "available events on this CPU and perf's uncore "
                              "IMC events are absent) -- the overlay will use "
                              "the ANALYTICAL byte count, which understates "
                              "real traffic several-fold.")
                write_roofline_outputs(
                    rl, args.output_dir, args.figures_dir,
                    overlay=(roofline_overlay_points(
                        arithintensity_width_results,
                        measured_bytes=measured_bytes)
                             if args.roofline_overlay else None),
                    machine=_machine_description())
            except RuntimeError as e:
                print("  ⚠ roofline measurement failed: %s" % e, file=sys.stderr)
        pldi_variant_results = None
        if args.pldi_submission:
            # The campaign list PLUS the width-sweep extras, run through the
            # same selection logic so --programs / --exclude-programs narrow
            # this matrix too (rather than silently re-running everything at
            # 13 configs apiece). An explicit --programs still wins outright.
            try:
                pldi_programs = resolve_program_selection(
                    args.programs, args.exclude_programs,
                    default_programs=DEFAULT_PROGRAMS + PLDI_EXTRA_PROGRAMS,
                    programs_dir=args.programs_dir)
            except ProgramSelectionError as e:
                ap.error(str(e))
            progress().finish_phase()
            progress().start_phase("pldi")
            print("  Collecting PLDI submission fold/map variant matrix "
                  f"({len(pldi_programs)} programs x up to 13 configs each) ...")
            pldi_variant_results = collect_pldi_variant_results(
                args.programs_dir, args.output_dir, resolve_cc(args.cc),
                args.force_recompile, gibbon_exe=None, iterations=args.iterations,
                c_arith_mode=args.c_arithmetic, simd_isa=args.simd_isa,
                pin_cpu=args.pin_cpu, programs=pldi_programs)
            report_pldi_qualification_warnings(pldi_variant_results)
        # Get extended results if they were collected
        progress().finish_phase()
        progress().start_phase("report")
        progress().item("LaTeX tables and PDF preview", "writing")
        write_latex_tables(
            all_results,
            args.latex_table,
            extended_results,
            include_build_pass=args.include_build_pass,
            show_cursor_table=(args.benchmark_immutable or args.benchmark_baseline_gibbon),
            add1tree_width_results=add1tree_width_results,
            arithintensity_width_results=arithintensity_width_results,
            pldi_variant_results=pldi_variant_results,
            simd_isa=args.simd_isa,
            campaign=campaign_block,
        )
        compile_latex_preview(args.latex_table, args.figures_dir)
        # Release the terminal before the closing summary, so the final
        # report is plain scrollback rather than sitting above a live bar.
        progress().finish_phase()
        progress().close()
        if HAS_PLOT_LIBS:
            generate_all_figures(all_results, args.figures_dir)
        else:
            print("  Skipping figures: matplotlib/numpy not installed.")
        print(f"\n  LaTeX  : {args.latex_table}")
        if HAS_PLOT_LIBS:
            print(f"  Figs   : {args.figures_dir}/")


if __name__ == "__main__":
    # Propagate main()'s return value.  It already returned 2 on a fatal
    # configuration error, but the status was discarded, so a caller could not
    # tell a rejected configuration from a successful run.
    sys.exit(main())
