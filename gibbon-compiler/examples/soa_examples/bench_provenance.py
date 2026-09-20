#!/usr/bin/env python3
"""Provenance, freshness and semantic-correctness core for the SoA benchmark
driver.

`gibbon_benchmark.py` imports this module; there is deliberately no second
implementation for tests to drift from.  Everything here is pure or does only
filesystem reads, so it is unit-testable without compiling anything.

Why this exists
---------------
The driver used to decide "is this executable still good?" from mtimes plus the
compile-command string, and it decided "is the answer right?" from AoS and SoA
agreeing.  Both are unsound:

  * a source, an imported module, the compiler, the RTS or the artifact itself
    can change while its timestamp is unchanged or older, and the driver would
    reuse a stale executable;
  * two variants can agree on the same wrong answer.

So: freshness is content-addressed over an explicit dependency closure, and
correctness requires an INDEPENDENT oracle per variant, with cross-variant
agreement kept only as an additional diagnostic.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

# Bump when the fingerprint's *meaning* changes, so old sidecars are rejected
# rather than silently misinterpreted.
BUILD_INFO_SCHEMA = 3

# Bump when full-mode JSON report *fields* change meaning. A report written
# under an older/missing schema has no QualificationStatus and must be
# rejected for qualified-metric generation rather than silently read as if
# every value were verified -- see `report_schema_supports_qualified_metrics`.
REPORT_SCHEMA = 1

# ---------------------------------------------------------------------------
# Hashing helpers
# ---------------------------------------------------------------------------

def file_sha256(p: Path) -> Optional[str]:
    """Content hash of a file, or None if it cannot be read."""
    try:
        h = hashlib.sha256()
        with open(p, "rb") as fh:
            for chunk in iter(lambda: fh.read(1 << 20), b""):
                h.update(chunk)
        return h.hexdigest()
    except OSError:
        return None


def text_sha256(s: str) -> str:
    return hashlib.sha256(s.encode("utf-8", "replace")).hexdigest()


# ---------------------------------------------------------------------------
# Compiler resolution  (ONE rule, used for argv, fingerprint, status and run)
# ---------------------------------------------------------------------------

class CompilerResolution:
    """Where the Gibbon executable came from, and what it is."""

    def __init__(self, path: Optional[Path], origin: str, sha: Optional[str]):
        self.path = path
        self.origin = origin          # "GIBBON_EXE" | "cabal" | "PATH" | "unresolved"
        self.sha256 = sha

    def as_dict(self) -> Dict:
        return {"path": str(self.path) if self.path else None,
                "origin": self.origin,
                "sha256": self.sha256}

    def __repr__(self) -> str:
        return "CompilerResolution(%r, %r)" % (str(self.path), self.origin)


def resolve_gibbon_exe(repo_root: Path, env: Optional[Dict[str, str]] = None
                       ) -> CompilerResolution:
    """Resolve the Gibbon compiler to ONE absolute path.

    Precedence, documented and tested:

        1. $GIBBON_EXE            -- an explicit override always wins
        2. `cabal list-bin exe:gibbon` run in gibbon-compiler/
        3. `gibbon` on $PATH

    The returned path is what must be placed in argv[0], hashed into the build
    fingerprint, printed in the status block and recorded in the report.  The
    old code resolved here but then executed the bare string "gibbon", so a
    `GIBBON_EXE` override was reported while a different PATH binary was
    actually invoked.
    """
    env = os.environ if env is None else env

    env_exe = env.get("GIBBON_EXE")
    if env_exe:
        p = Path(env_exe).expanduser()
        if p.exists():
            p = p.resolve()
            return CompilerResolution(p, "GIBBON_EXE", file_sha256(p))

    try:
        r = subprocess.run(["cabal", "list-bin", "exe:gibbon"],
                           cwd=str(repo_root / "gibbon-compiler"),
                           capture_output=True, text=True)
        if r.returncode == 0:
            p = Path(r.stdout.strip())
            if p.exists():
                p = p.resolve()
                return CompilerResolution(p, "cabal", file_sha256(p))
    except Exception:
        pass

    which = shutil.which("gibbon", path=env.get("PATH"))
    if which:
        p = Path(which).resolve()
        if p.exists():
            return CompilerResolution(p, "PATH", file_sha256(p))

    return CompilerResolution(None, "unresolved", None)


def cc_identity(cc: str) -> Dict[str, Optional[str]]:
    """Absolute path and version banner of the C compiler actually used.

    The version matters: the same `gcc` path can be a different compiler after
    an upgrade, which changes the executable without changing any argv.
    """
    path = shutil.which(cc) or cc
    ver = None
    try:
        r = subprocess.run([cc, "--version"], capture_output=True, text=True)
        if r.returncode == 0:
            ver = r.stdout.splitlines()[0].strip() if r.stdout else None
    except Exception:
        pass
    return {"cc": cc, "path": str(Path(path).resolve()) if Path(path).exists() else path,
            "version": ver}


# ---------------------------------------------------------------------------
# Dependency closure
# ---------------------------------------------------------------------------

_IMPORT_RE = re.compile(r'^\s*import\s+(?:qualified\s+)?([A-Z][A-Za-z0-9_.\']*)')


def local_import_closure(source: Path, extra_roots: Sequence[Path] = ()) -> List[Path]:
    """Transitively resolve a Gibbon/Haskell source's LOCAL module imports.

    Only modules that exist as files next to the source (or under `extra_roots`)
    are followed; library imports such as `Gibbon.Vector` resolve to nothing
    here and are covered instead by the compiler hash.

    Returns a sorted list of existing dependency paths, excluding `source`.
    """
    source = source.resolve()
    roots = [source.parent] + [Path(r).resolve() for r in extra_roots]
    seen: Dict[Path, None] = {}
    stack = [source]
    while stack:
        cur = stack.pop()
        try:
            text = cur.read_text(errors="replace")
        except OSError:
            continue
        for line in text.splitlines():
            m = _IMPORT_RE.match(line)
            if not m:
                continue
            rel = Path(*m.group(1).split("."))
            for root in roots:
                for cand in (root / rel.with_suffix(".hs"),
                             root / (rel.name + ".hs")):
                    if cand.exists():
                        cand = cand.resolve()
                        if cand != source and cand not in seen:
                            seen[cand] = None
                            stack.append(cand)
                        break
    return sorted(seen)


def rts_inputs(repo_root: Path) -> List[Path]:
    """RTS files that can change the linked executable without changing argv or
    the Gibbon binary.

    Deliberately the RTS *sources* and its Makefile, NOT the build products in
    gibbon-rts/build.  Every `gibbon` invocation re-runs the RTS make rule, and
    the resulting `gibbon_rts.o` is not byte-reproducible (it is an LTO object),
    so hashing it would report "RTS input changed" on every single run and
    disable artifact reuse entirely.  The build products are a function of these
    sources plus the compile flags, and both are already tracked, so the closure
    stays sound while remaining stable.
    """
    out: List[Path] = []
    rts_c = repo_root / "gibbon-rts" / "rts-c"
    if rts_c.is_dir():
        out.extend(sorted(p for p in rts_c.iterdir()
                          if p.suffix in (".c", ".h") and p.is_file()))
    mk = repo_root / "gibbon-rts" / "Makefile"
    if mk.exists():
        out.append(mk)
    return out


# Environment variables that can change what gets built or how it runs.
TRACKED_ENV = ("GIBBONDIR", "GIBBON_EXE", "GIBBON_TRIALS", "GIBBON_SIZE",
               "CC", "PAPI_EVENTS")


def tracked_env(env: Optional[Dict[str, str]] = None) -> Dict[str, str]:
    env = os.environ if env is None else env
    return {k: env[k] for k in TRACKED_ENV if k in env}


def repo_state(repo_root: Path) -> Dict[str, Optional[str]]:
    """HEAD plus a fingerprint of uncommitted work, for traceability only.

    This is NOT part of the freshness decision -- the dependency closure is --
    but a recorded measurement must be attributable to a tree state.
    """
    head = dirty = None
    try:
        r = subprocess.run(["git", "rev-parse", "HEAD"], cwd=str(repo_root),
                           capture_output=True, text=True)
        if r.returncode == 0:
            head = r.stdout.strip()
        d = subprocess.run(["git", "status", "--porcelain"], cwd=str(repo_root),
                           capture_output=True, text=True)
        if d.returncode == 0:
            dirty = text_sha256(d.stdout) if d.stdout.strip() else None
    except Exception:
        pass
    return {"head": head, "dirty_fingerprint": dirty}


# ---------------------------------------------------------------------------
# Build fingerprint
# ---------------------------------------------------------------------------

def build_fingerprint(source: Path,
                      argv: Sequence[str],
                      compiler: CompilerResolution,
                      cc_info: Dict[str, Optional[str]],
                      repo_root: Path,
                      driver_path: Optional[Path] = None,
                      env: Optional[Dict[str, str]] = None,
                      extra_roots: Sequence[Path] = ()) -> Dict:
    """Everything that can change the produced executable.

    If an input cannot be read, its hash is recorded as None, which will never
    compare equal to a later successful read -- so an untrackable input forces a
    recompile rather than an optimistic reuse.
    """
    source = source.resolve()
    deps = local_import_closure(source, extra_roots)
    return {
        "schema": BUILD_INFO_SCHEMA,
        "source": {"path": str(source), "sha256": file_sha256(source)},
        "deps": [{"path": str(d), "sha256": file_sha256(d)} for d in deps],
        "compiler": compiler.as_dict(),
        "cc": cc_info,
        "argv": list(argv),
        "rts": [{"path": str(p), "sha256": file_sha256(p)}
                for p in rts_inputs(repo_root)],
        "env": tracked_env(env),
        "driver": {"path": str(driver_path) if driver_path else None,
                   "sha256": file_sha256(driver_path) if driver_path else None},
    }


def fingerprint_differences(old: Optional[Dict], new: Dict) -> List[str]:
    """Human-readable reasons `old` does not describe `new`.  Empty == match."""
    if not isinstance(old, dict):
        return ["build metadata missing or unreadable"]
    if old.get("schema") != new.get("schema"):
        return ["build metadata schema %r != %r" % (old.get("schema"), new["schema"])]

    diffs: List[str] = []
    if old.get("source") != new.get("source"):
        os_, ns = old.get("source") or {}, new["source"]
        if os_.get("path") != ns.get("path"):
            diffs.append("source path changed (%s -> %s)" % (os_.get("path"), ns.get("path")))
        else:
            diffs.append("source contents changed")
    if old.get("argv") != new.get("argv"):
        diffs.append("compile command changed")
    if old.get("compiler") != new.get("compiler"):
        oc, nc = old.get("compiler") or {}, new["compiler"]
        if oc.get("path") != nc.get("path"):
            diffs.append("gibbon executable changed (%s -> %s)" % (oc.get("path"), nc.get("path")))
        else:
            diffs.append("gibbon executable contents changed")
    if old.get("cc") != new.get("cc"):
        diffs.append("C compiler identity/version changed")
    if old.get("env") != new.get("env"):
        diffs.append("tracked environment changed")
    if old.get("driver") != new.get("driver"):
        diffs.append("benchmark driver changed")

    om = {d["path"]: d["sha256"] for d in (old.get("deps") or [])}
    nm = {d["path"]: d["sha256"] for d in new["deps"]}
    if om != nm:
        for p in sorted(set(om) | set(nm)):
            if om.get(p) != nm.get(p):
                diffs.append("imported module changed: %s" % Path(p).name)
                break
    orts = {d["path"]: d["sha256"] for d in (old.get("rts") or [])}
    nrts = {d["path"]: d["sha256"] for d in new["rts"]}
    if orts != nrts:
        for p in sorted(set(orts) | set(nrts)):
            if orts.get(p) != nrts.get(p):
                diffs.append("RTS input changed: %s" % Path(p).name)
                break
    return diffs


def artifacts_intact(meta: Dict, c_file: Optional[Path], exe: Path) -> List[str]:
    """Verify the recorded artifacts are byte-for-byte the ones we built.

    Catches an executable or generated C file that was edited, replaced or
    truncated after the build -- including with its mtime restored.
    """
    problems: List[str] = []
    rec = meta.get("artifacts") or {}
    for key, path in (("exe", exe), ("c_file", c_file)):
        if path is None:
            continue
        want = (rec.get(key) or {}).get("sha256")
        if want is None:
            problems.append("no recorded hash for %s" % key)
            continue
        if not Path(path).exists():
            problems.append("%s missing" % key)
            continue
        if file_sha256(Path(path)) != want:
            problems.append("%s was modified after the build" % key)
    return problems


def decide_recompile(buildinfo_file: Path,
                     fingerprint: Dict,
                     c_file: Optional[Path],
                     exe: Path) -> Tuple[bool, str]:
    """The freshness decision.  Content-addressed; mtimes are not consulted."""
    if not exe.exists():
        return True, "exe missing"
    if c_file is not None and not Path(c_file).exists():
        return True, "generated C missing"
    if not buildinfo_file.exists():
        return True, "build metadata missing"
    try:
        meta = json.loads(buildinfo_file.read_text())
    except Exception:
        return True, "build metadata unreadable"

    diffs = fingerprint_differences(meta.get("fingerprint"), fingerprint)
    if diffs:
        return True, diffs[0]
    bad = artifacts_intact(meta, c_file, exe)
    if bad:
        return True, bad[0]
    return False, "artifacts verified (content-addressed)"


def write_buildinfo_atomic(buildinfo_file: Path, fingerprint: Dict,
                           c_file: Optional[Path], exe: Path,
                           repo_root: Path, extra: Optional[Dict] = None) -> None:
    """Install build metadata only after a SUCCESSFUL build, atomically.

    Written to a temp file in the same directory and renamed, so a crash can
    never leave metadata that half-describes an executable.
    """
    meta = {
        "schema": BUILD_INFO_SCHEMA,
        "fingerprint": fingerprint,
        "artifacts": {
            "exe": {"path": str(exe), "sha256": file_sha256(exe)},
            "c_file": ({"path": str(c_file), "sha256": file_sha256(Path(c_file))}
                       if c_file is not None else None),
        },
        "repo": repo_state(repo_root),
        "compiled_at": __import__("datetime").datetime.now().isoformat(timespec="seconds"),
    }
    if extra:
        meta.update(extra)
    buildinfo_file.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp = tempfile.mkstemp(dir=str(buildinfo_file.parent), suffix=".tmp")
    try:
        with os.fdopen(fd, "w") as fh:
            json.dump(meta, fh, indent=2, sort_keys=True)
        os.replace(tmp, buildinfo_file)
    except Exception:
        try:
            os.unlink(tmp)
        except OSError:
            pass
        raise


# ---------------------------------------------------------------------------
# Semantic output: benchmark protocol vs program data
# ---------------------------------------------------------------------------
#
# Note [Benchmark protocol grammar]
# ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
# The driver must strip the benchmark protocol (timing, pass banners, GC noise)
# and keep everything else, because everything else is the program's answer.
#
# The old filter was `_GC_RE.search(line)` -- an UNANCHORED substring test.  Any
# program value line that merely contained "SIZE:", "SELFTIMED:", "ITER TIMES:"
# or "Running pass" was deleted in full.  Measured before this change:
#
#     "result SIZE: 3"                -> discarded entirely
#     "Running pass count = 7"        -> discarded entirely
#     "total SELFTIMED: 9"            -> discarded entirely
#     "ITER TIMES: [0.0] trailing 5"  -> discarded entirely
#
# So a program could print a wrong answer and the driver would compare empty
# text.  This is the same defect class previously seen in the Haskell test
# harness's own output-comparison logic from unanchored substring matching.
#
# Every rule below therefore matches the WHOLE line (after stripping horizontal
# whitespace) and requires the payload shape the emitters actually produce.
# Anything that does not match completely is program data and is preserved,
# including token order and multiplicity.
#
# This is a benchmark-specific protocol -- unlike tests/OutputCompare.hs it also
# drops `ITERS:`/`SIZE:` and the pass banners, because here the oracle files
# hold program values only.  It is strictly *stricter* than the old behaviour
# about preserving program data, which is the property that matters.

_NUM = r"[-+]?\d+(?:\.\d+)?(?:[eE][-+]?\d+)?"

_PROTOCOL_LINE_RES = [
    re.compile(r"ITER\s+TIMES:\s*\[\s*(?:%s\s*(?:,\s*%s\s*)*)?\]" % (_NUM, _NUM)),
    re.compile(r"itertime:\s*%s" % _NUM),
    re.compile(r"ITERS:\s*%s" % _NUM),
    re.compile(r"SIZE:\s*%s" % _NUM),
    re.compile(r"BATCHTIME:\s*%s" % _NUM),
    re.compile(r"SELFTIMED:\s*%s" % _NUM),
    re.compile(r"Running\s+pass\s+.*?:"),
    re.compile(r"Running\s+program\s+.*?:"),
    re.compile(r"End"),
    re.compile(r"PAPI_NATIVE\s+\S+.*"),
    re.compile(r"INFO_TABLE:.*"),
    re.compile(r"Initialized\s+footer\s+at.*"),
    re.compile(r"(?:GibOldgenChunkFooter|GibRegionInfo).*"),
    re.compile(r"refcount:.*outset:.*"),
    re.compile(r"(?:Total\s+allocated\s+bytes|Total\s+copied\s+bytes|ALLOC_TOTAL|GC_TOTAL):.*"),
]


def is_protocol_line(line: str) -> bool:
    """True iff the ENTIRE line is one recognized benchmark-protocol record."""
    s = line.strip()
    if not s:
        return False
    return any(r.fullmatch(s) for r in _PROTOCOL_LINE_RES)


def semantic_lines(raw: str) -> List[str]:
    """Program data only: protocol records removed, everything else preserved
    verbatim and in order."""
    return [ln.strip() for ln in raw.splitlines()
            if ln.strip() and not is_protocol_line(ln)]


def semantic_output(raw: str) -> Optional[str]:
    """Normalized semantic output, or None when the program said nothing."""
    lines = semantic_lines(raw)
    return "\n".join(lines) if lines else None


def semantic_tokens(raw: str) -> List[str]:
    """Comparison unit: whitespace-insensitive but order- and
    multiplicity-preserving, so a missing, duplicated or reordered value fails."""
    return semantic_output(raw).split() if semantic_output(raw) else []


# ---------------------------------------------------------------------------
# Independent oracle
# ---------------------------------------------------------------------------
#
# "Both variants printed the same text" is NOT an oracle: they can be wrong
# together.  An oracle entry is an expected value that was produced WITHOUT
# running Gibbon, plus a record of how.

ORACLE_PROVENANCES = ("hand-derived", "racket-reference", "python-model",
                      "reference-implementation")

ORACLE_PASS = "PASS"
ORACLE_FAIL = "FAIL"
ORACLE_MISSING = "MISSING"
ORACLE_NOT_REQUIRED = "NOT_REQUIRED"


class OracleEntry:
    def __init__(self, program: str, expected: str, provenance: str,
                 note: str = "", source: Optional[str] = None):
        if provenance not in ORACLE_PROVENANCES:
            raise ValueError("oracle %r: provenance %r must be one of %s"
                             % (program, provenance, ", ".join(ORACLE_PROVENANCES)))
        self.program = program
        self.expected = expected
        self.provenance = provenance
        self.note = note
        self.source = source

    def check(self, raw_output: str) -> Tuple[str, str]:
        got = semantic_tokens(raw_output)
        want = self.expected.split()
        if got == want:
            return ORACLE_PASS, "matches %s oracle" % self.provenance
        if not got:
            return ORACLE_FAIL, "semantic output is empty; oracle expects %r" % self.expected.strip()
        for i, (a, b) in enumerate(zip(want, got)):
            if a != b:
                return ORACLE_FAIL, ("first difference at token %d: expected %r, got %r"
                                     % (i, a, b))
        return ORACLE_FAIL, ("expected %d tokens, got %d" % (len(want), len(got)))


class OracleManifest:
    """A manifest maps a program stem to an independently derived expected
    result.  Entries live beside the driver so future width-family fixtures
    (e.g. additional integer-width program variants) can be added without
    touching driver code."""

    def __init__(self, entries: Dict[str, OracleEntry], path: Optional[Path] = None):
        self.entries = entries
        self.path = path

    @classmethod
    def load(cls, path: Path) -> "OracleManifest":
        data = json.loads(Path(path).read_text())
        entries: Dict[str, OracleEntry] = {}
        for program, spec in data.get("oracles", {}).items():
            expected = spec.get("expected")
            if expected is None and spec.get("expected_file"):
                expected = (Path(path).parent / spec["expected_file"]).read_text()
            if expected is None:
                raise ValueError("oracle %r has neither expected nor expected_file" % program)
            entries[program] = OracleEntry(program, expected,
                                           spec["provenance"],
                                           spec.get("note", ""),
                                           spec.get("expected_file"))
        return cls(entries, Path(path))

    @classmethod
    def load_default(cls, base_dir: Path) -> "OracleManifest":
        p = Path(base_dir) / "oracles" / "manifest.json"
        return cls.load(p) if p.exists() else cls({}, p)

    def lookup(self, program: str) -> Optional[OracleEntry]:
        return self.entries.get(Path(program).stem) or self.entries.get(program)

    def check(self, program: str, raw_output: str,
              required: bool = True) -> Tuple[str, str]:
        entry = self.lookup(program)
        if entry is None:
            return ((ORACLE_MISSING, "no independent oracle for %s" % Path(program).stem)
                    if required else
                    (ORACLE_NOT_REQUIRED, "oracle not required for %s" % Path(program).stem))
        return entry.check(raw_output)


# ---------------------------------------------------------------------------
# Result model and report eligibility
# ---------------------------------------------------------------------------
#
# `run_success` used to be overloaded to mean "compiled", "ran", "produced
# output" and "is trustworthy".  These are separate facts.

COMPILE_OK, COMPILE_FAIL = "OK", "FAIL"
EXEC_OK, EXEC_FAIL = "OK", "FAIL"
XVAR_AGREE, XVAR_DISAGREE, XVAR_NA = "AGREE", "DISAGREE", "NOT_APPLICABLE"


class QualificationStatus:
    """Per-variant verdict.  `eligible_for_reporting` is the only thing a
    performance table may consult."""

    def __init__(self, variant: str, program: str):
        self.variant = variant
        self.program = program
        self.compile_status = COMPILE_FAIL
        self.exec_status = EXEC_FAIL
        self.oracle_status = ORACLE_MISSING
        self.oracle_detail = ""
        self.cross_variant_status = XVAR_NA
        self.codegen_status: Optional[str] = None
        self.timing_status = "ABSENT"
        self.semantic_output: Optional[str] = None
        self.allow_unverified = False
        self.notes: List[str] = []

    @property
    def verified(self) -> bool:
        """The ONE strict eligibility condition: compiled, ran, produced
        non-empty semantic output, and PASSED an independent oracle.

        This is the only predicate a speedup, aggregate, geometric mean, plot,
        paper table, headline console comparison, or correctness-qualified
        JSON field may consult.  `ORACLE_NOT_REQUIRED` is deliberately NOT
        sufficient here even though nothing in this codebase produces it
        today (`OracleManifest.check` is always called with `required=True`):
        a result the caller merely decided not to check is not the same as a
        result an independent oracle passed, and treating it as verified
        would silently reopen exactly the hole this property exists to close.
        See Note [eligible_for_reporting means verified]."""
        return (self.compile_status == COMPILE_OK
                and self.exec_status == EXEC_OK
                and self.semantic_output is not None
                and self.oracle_status == ORACLE_PASS)

    # Note [eligible_for_reporting means verified]
    # ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    # This used to be a second, WEAKER predicate: it returned True whenever
    # `allow_unverified and oracle_status == ORACLE_MISSING`, even though its
    # own docstring said "PASSED an independent oracle" and the invariant
    # elsewhere is that an UNVERIFIED result must never produce a speedup
    # claim.  Those two statements contradicted each other, and the weaker
    # one was live: full benchmark mode never even constructed a
    # QualificationStatus, so nothing had exercised this path end to end.
    # `eligible_for_reporting` now means exactly `verified`.
    # An `--allow-unverified-output` run gets its own, separate,
    # non-reporting predicate: `eligible_for_exploratory_output`.
    eligible_for_reporting = verified

    @property
    def eligible_for_exploratory_output(self) -> bool:
        """Permits `--allow-unverified-output` to retain a result's raw
        output, raw timing and provenance in a clearly UNVERIFIED diagnostic
        artifact when no oracle exists for it yet.

        This must NEVER be consulted by a speedup, aggregate, geometric mean,
        plot, paper table, PAPI comparison, "best result" selection, or any
        JSON field whose name implies a qualified metric.  Only `verified`
        (== `eligible_for_reporting`) may gate those.  Compiling and running
        successfully is not enough on its own: this still requires non-empty
        semantic output, and an oracle FAIL still refuses it -- the escape is
        only for a MISSING oracle, never for a wrong answer."""
        if self.compile_status != COMPILE_OK or self.exec_status != EXEC_OK:
            return False
        if self.semantic_output is None:
            return False
        if self.oracle_status == ORACLE_PASS:
            return True
        return bool(self.allow_unverified and self.oracle_status == ORACLE_MISSING)

    @property
    def label(self) -> str:
        if self.compile_status != COMPILE_OK:
            return "COMPILE-FAIL"
        if self.exec_status != EXEC_OK:
            return "RUN-FAIL"
        if self.semantic_output is None:
            return "EMPTY-OUTPUT"
        if self.oracle_status == ORACLE_PASS:
            return "VERIFIED"
        if self.oracle_status == ORACLE_FAIL:
            return "WRONG"
        if self.oracle_status == ORACLE_MISSING:
            return "UNVERIFIED" if self.allow_unverified else "NO-ORACLE"
        return "NOT-REQUIRED"

    @classmethod
    def from_dict(cls, d: Dict) -> "QualificationStatus":
        """Inverse of 'as_dict' for the stored fields; the derived ones
        (label, verified, eligibility) are recomputed, never read back."""
        st = cls(d.get("variant", ""), d.get("program", ""))
        for name in ("compile_status", "exec_status", "oracle_status",
                     "oracle_detail", "cross_variant_status", "codegen_status",
                     "timing_status", "semantic_output", "allow_unverified"):
            if name in d:
                setattr(st, name, d[name])
        st.notes = list(d.get("notes") or [])
        return st

    def as_dict(self) -> Dict:
        return {"variant": self.variant, "program": self.program,
                "compile_status": self.compile_status,
                "exec_status": self.exec_status,
                "oracle_status": self.oracle_status,
                "oracle_detail": self.oracle_detail,
                "cross_variant_status": self.cross_variant_status,
                "codegen_status": self.codegen_status,
                "timing_status": self.timing_status,
                "label": self.label,
                "verified": self.verified,
                "eligible_for_reporting": self.eligible_for_reporting,
                "eligible_for_exploratory_output": self.eligible_for_exploratory_output,
                "allow_unverified": self.allow_unverified,
                "semantic_output": self.semantic_output,
                "notes": self.notes}


def campaign_exit_code(statuses: Sequence[QualificationStatus]) -> int:
    """Nonzero if ANY selected variant failed to compile, failed to run,
    produced empty output, contradicted its oracle, lacked a required oracle,
    or disagreed with a variant it should match."""
    if not statuses:
        return 1
    for st in statuses:
        if st.compile_status != COMPILE_OK or st.exec_status != EXEC_OK:
            return 1
        if st.semantic_output is None:
            return 1
        if st.oracle_status == ORACLE_FAIL:
            return 1
        if st.oracle_status == ORACLE_MISSING and not st.allow_unverified:
            return 1
        if st.cross_variant_status == XVAR_DISAGREE:
            return 1
    return 0


def cross_variant_check(statuses: Sequence[QualificationStatus]) -> str:
    """Additional diagnostic only -- never a substitute for the oracle."""
    outs = [s.semantic_output for s in statuses if s.semantic_output is not None]
    if len(outs) < 2:
        return XVAR_NA
    first = outs[0].split()
    return XVAR_AGREE if all(o.split() == first for o in outs[1:]) else XVAR_DISAGREE


# ---------------------------------------------------------------------------
# Eligibility helpers -- the ONLY place a numeric performance sink may ask
# "is this trustworthy?"
#
# Every sink takes an object with a `.qualification` attribute (an
# `Optional[QualificationStatus]`) -- typically `gibbon_benchmark.BenchmarkResult`,
# but any object shaped that way works, including the synthetic merged results
# `_merge_octree_results`/`_merge_pass_results` build.  A caller-side filter
# alone is not the contract: these helpers are meant to be called from INSIDE
# every sink, not just once by whichever function happens to run first.
# ---------------------------------------------------------------------------

def verified_result(result) -> bool:
    """True iff `result` is non-None and its attached QualificationStatus is
    strictly verified (independent oracle PASS).  This is the single gate
    every numeric performance sink must consult -- directly, not through a
    weaker proxy like `compile_success`, `run_success`, `result.output` being
    truthy, or membership in some caller-filtered list."""
    if result is None:
        return False
    st = getattr(result, "qualification", None)
    return bool(st is not None and st.verified)


def verified_results_only(results) -> List:
    """Filter an iterable of results (None entries allowed) down to the
    strictly verified ones."""
    return [r for r in results if verified_result(r)]


def eligible_pair(lhs, rhs) -> bool:
    """A ratio/speedup between two results is defined only when BOTH operands
    are independently verified.  Never infer one variant's correctness from
    another verified variant -- each side must carry its own oracle PASS."""
    return verified_result(lhs) and verified_result(rhs)


def rejection_reason(result) -> str:
    """Human-readable reason a result is not eligible, for a diagnostic row
    (never for a numeric cell)."""
    if result is None:
        return "no result"
    st = getattr(result, "qualification", None)
    if st is None:
        return "not qualified (no QualificationStatus attached)"
    if st.compile_status != COMPILE_OK:
        return "compile failed"
    if st.exec_status != EXEC_OK:
        return "execution failed"
    if st.semantic_output is None:
        return "empty semantic output"
    if st.oracle_status == ORACLE_FAIL:
        return "oracle FAIL: %s" % st.oracle_detail
    if st.oracle_status == ORACLE_MISSING:
        return ("UNVERIFIED (no oracle, --allow-unverified-output)"
                if st.allow_unverified else "no independent oracle")
    return "not verified"


def safe_speedup(lhs, rhs, metric) -> Tuple[Optional[float], str]:
    """`metric(lhs) / metric(rhs)`, defined only when both `lhs` and `rhs`
    are independently verified AND `metric` returns a present, positive-
    denominator pair.  `metric` is a callable `result -> Optional[float]`
    (e.g. a closure over `total_pass_time`).

    Returns `(value_or_None, reason)`.  `reason` is `"ok"` on success and a
    human-readable explanation otherwise -- an absent operand must render as
    "N/A -- <reason>", never as 0, 1, infinity, or a silently omitted cell
    that reads the same as a real result."""
    if not eligible_pair(lhs, rhs):
        parts = []
        if not verified_result(lhs):
            parts.append("numerator: %s" % rejection_reason(lhs))
        if not verified_result(rhs):
            parts.append("denominator: %s" % rejection_reason(rhs))
        return None, "; ".join(parts) or "not eligible"
    a, b = metric(lhs), metric(rhs)
    if a is None or b is None:
        return None, "required metric absent"
    if b <= 0:
        return None, "denominator not positive"
    return a / b, "ok"


def synthesize_derived_status(variant: str, program: str,
                              contributing) -> Optional["QualificationStatus"]:
    """A verified status for a value MECHANICALLY DERIVED from zero or more
    already-verified results (e.g. `_merge_octree_results` summing several
    split programs' pass times into one row).  Verified only if every
    contributor that was consulted was itself verified, and only if there was
    at least one -- an empty merge is not vacuously verified.

    This never re-checks an oracle: it is sound only because it is built
    exclusively from constituents that already passed one, and the note
    records exactly which quantity that is."""
    contributors = [c for c in contributing if c is not None]
    if not contributors or not all(verified_result(c) for c in contributors):
        return None
    st = QualificationStatus(variant, program)
    st.compile_status = COMPILE_OK
    st.exec_status = EXEC_OK
    st.semantic_output = "<derived: merge of %d verified results>" % len(contributors)
    st.oracle_status = ORACLE_PASS
    st.oracle_detail = ("derived from %d independently verified result(s); no oracle "
                        "re-checked at this merge" % len(contributors))
    st.notes.append("synthesized by merging already-verified per-program results")
    return st


def report_schema_supports_qualified_metrics(doc: Dict) -> Tuple[bool, str]:
    """Can this JSON report document be used as a source of QUALIFIED
    performance metrics (e.g. by a later paper/report generation step that
    reads a saved report back in)?

    A report written before per-variant qualification tracking was added --
    or any document missing `report_schema`/per-variant `status` -- carries
    no QualificationStatus at all, so there is nothing to check `verified`
    against.  It must be
    rejected outright for that purpose rather than silently treated as if
    every value in it were verified.  It remains fine to read for its raw
    diagnostic content (old-style tables, provenance, etc.)."""
    if not isinstance(doc, dict):
        return False, "not a JSON object"
    if doc.get("report_schema") != REPORT_SCHEMA:
        return False, ("report_schema %r != %r (missing or legacy report; no "
                       "QualificationStatus to verify against)"
                       % (doc.get("report_schema"), REPORT_SCHEMA))
    return True, "ok"


def atomic_write_text(path: Path, text: str) -> None:
    """Replace a report/raw-output file only on success, so a stale prior file
    can never masquerade as the current result."""
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp = tempfile.mkstemp(dir=str(path.parent), suffix=".tmp")
    try:
        with os.fdopen(fd, "w") as fh:
            fh.write(text)
        os.replace(tmp, path)
    except Exception:
        try:
            os.unlink(tmp)
        except OSError:
            pass
        raise
