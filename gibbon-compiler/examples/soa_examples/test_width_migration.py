#!/usr/bin/env python3
"""Adversarial width-migration regression checks for the curated
DEFAULT_PROGRAMS benchmarks (BW-03).

Parses each curated DEFAULT_PROGRAMS source's `data T = C1 f1 f2 ... | C2
...` declaration into an explicit, enumerated list of (constructor, field
index, type) triples -- not a naive whole-file regex -- and checks it
against a hand-maintained width manifest for that program. This is meant
to fail loudly on exactly these regression classes: a bare `Int` field
reappearing in a curated ADT, KDTree's fields drifting off Int64, an
AoS/SoA field-width disagreement, and an oracle for a VW-24-blocked
program silently being "fixed" to match the known-wrong compiled output
instead of staying an honest, independently derived value.

This does not invoke Gibbon or gcc: it is a fast, static, repeatable check
over the source text and oracles/manifest.json, meant to run in CI/unit-test
time, not benchmark time.
"""
import json
import re
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROGRAMS_AOS = HERE / "programs" / "AOS"
PROGRAMS_SOA = HERE / "programs" / "SOA"
MANIFEST = HERE / "oracles" / "manifest.json"

PRIM_TYPES = ("Int8", "Int16", "Int32", "Int64", "Int")

# ---------------------------------------------------------------------------
# A small, real parser for `data T = C1 f1 f2 ... | C2 ... | C3` blocks.
# ---------------------------------------------------------------------------


def parse_data_decl(source_text: str, type_name: str):
    """Returns {constructor_name: [field_type, ...]} for `data type_name = ...`
    in source_text, considering only PRIMITIVE integer field types (Int8/16/32/64/
    bare Int) at each position -- a recursive-type field (the ADT itself) is
    recorded as None so field indices still line up across AoS/SoA."""
    m = re.search(r"^data\s+%s\b" % re.escape(type_name), source_text, re.MULTILINE)
    if not m:
        raise AssertionError("no `data %s = ...` found" % type_name)
    start = m.start()
    # Slice from the decl to the next top-level declaration (a line starting
    # at column 0 with a lowercase identifier, `{-#`, or another `data`), so
    # we don't accidentally swallow the rest of the file.
    rest = source_text[start:]
    end_m = re.search(r"\n(?=[a-z{])", rest[1:])
    block = rest if end_m is None else rest[: end_m.start() + 1]
    # Drop everything up to and including the `=`.
    eq = block.index("=")
    body = block[eq + 1:]
    # Strip Haskell `--` line comments (but keep the newlines for constructor splitting).
    body = re.sub(r"--[^\n]*", "", body)
    constructors = {}
    for chunk in body.split("|"):
        tokens = chunk.split()
        if not tokens:
            continue
        cname = tokens[0]
        fields = []
        for tok in tokens[1:]:
            if tok == type_name:
                fields.append(None)
            elif tok in PRIM_TYPES:
                fields.append(tok)
            # anything else (another type name in a shared-ADT family,
            # stray punctuation) is ignored -- not expected in these programs.
        constructors[cname] = fields
    return constructors


class TestDataDeclParser(unittest.TestCase):
    def test_parses_simple_two_constructor_adt(self):
        src = """
-- comment
data List = Cons Int32 List | Nil
"""
        got = parse_data_decl(src, "List")
        self.assertEqual(got["Cons"], ["Int32", None])
        self.assertEqual(got["Nil"], [])

    def test_parses_multiline_adt_with_comments(self):
        src = """
data KDTree
  = KDNode Int64    -- splitDim
           Int64    -- splitVal
           KDTree KDTree
  | KDLeaf Int64
           Int64
  | KDEmpty
"""
        got = parse_data_decl(src, "KDTree")
        self.assertEqual(got["KDNode"], ["Int64", "Int64", None, None])
        self.assertEqual(got["KDLeaf"], ["Int64", "Int64"])
        self.assertEqual(got["KDEmpty"], [])


# ---------------------------------------------------------------------------
# Width manifest: for every curated program's ADT, the expected field width
# per constructor.
#
# All 22 ordinary curated DEFAULT_PROGRAMS benchmarks use Int64
# consistently -- there is no two-tier distinction between KDTree and
# everyone else, and no Int32 (or narrower) exception anywhere in this
# inventory. The dedicated BW-01/BW-02 width EXPERIMENTS
# (Add1TreeInt8/16/32/64.hs, ArithIntensityInt8/16/32/64.hs and their
# private correctness fixtures/lane-tail harnesses) are explicitly OUT of
# DEFAULT_PROGRAMS and retain their deliberate per-width variants -- they
# are governed by test_add1tree_widths.py/test_arithintensity_widths.py,
# not this file; see TestBW01BW02NotSweptByOrdinaryPolicy below for the
# direct non-interference check.
# ---------------------------------------------------------------------------

INT64_EVERYWHERE = "Int64Everywhere"

WIDTH_MANIFEST = {
    # (source_stem, adt_type_name): expected -- every entry is
    # INT64_EVERYWHERE now; the dict form (rather than a flat set) is kept
    # so the rest of this module's machinery (which was built around a
    # per-(stem,type) manifest) needs no restructuring.
    ("List", "List"): INT64_EVERYWHERE,
    ("MonoTree", "Tree"): INT64_EVERYWHERE,
    ("LinearListReduction", "List"): INT64_EVERYWHERE,
    ("reduceNestedList", "List"): INT64_EVERYWHERE,
    ("reduceNestedList", "ListA"): INT64_EVERYWHERE,
    ("TernaryTree", "Tree"): INT64_EVERYWHERE,
    ("DomTree", "DOM"): INT64_EVERYWHERE,
    ("DecisionTree", "DTree"): INT64_EVERYWHERE,
    # Split out of DecisionTree.hs on 2026-09-06; same DTree ADT verbatim.
    ("DecisionTreeClassify", "DTree"): INT64_EVERYWHERE,
    ("ObjectGraph", "Heap"): INT64_EVERYWHERE,
    ("Trie", "Trie"): INT64_EVERYWHERE,
    # The PW ADT lives in PiecewiseFunctionsBase.hs since the 2026-09-06
    # split; all eight PiecewiseFunctions_<pass>.hs members import it, the
    # same way the eight OctTree_* rows share OctTreeBase's Octree.
    ("PiecewiseFunctionsBase", "PW"): INT64_EVERYWHERE,
    ("DBQuery", "Query"): INT64_EVERYWHERE,
    ("Compiler", "IR"): INT64_EVERYWHERE,
    ("KDTree", "KDTree"): INT64_EVERYWHERE,
    ("OctTreeBase", "Octree"): INT64_EVERYWHERE,
    ("ColorOctree", "ColorOctree"): INT64_EVERYWHERE,
}

# Every DEFAULT_PROGRAMS row, frozen from gibbon_benchmark.py and mapped to
# the source STEM that declares its
# semantic ADT -- several rows share a stem (the 8 OctTree_* rows all
# import OctTreeBase.hs's `Octree`; LinearListReduction/reduceNestedList
# and List are separate `List`-named ADTs in separate files/stems). Used
# to derive the "ordinary inventory" from DEFAULT_PROGRAMS explicitly,
# rather than only from WIDTH_MANIFEST's keys, so a newly added
# DEFAULT_PROGRAMS row whose stem nobody added to WIDTH_MANIFEST yet is
# still caught (by TestDefaultProgramsInventory below) instead of silently
# escaping every other check in this file.
DEFAULT_PROGRAMS_TO_STEM = {
    "Compiler.hs": "Compiler",
    "DBQuery.hs": "DBQuery",
    "DecisionTree.hs": "DecisionTree",
    "DecisionTreeClassify.hs": "DecisionTreeClassify",
    "DomTree.hs": "DomTree",
    "KDTree.hs": "KDTree",
    "LinearListReduction.hs": "LinearListReduction",
    "reduceNestedList.hs": "reduceNestedList",
    "List.hs": "List",
    "MonoTree.hs": "MonoTree",
    "ObjectGraph.hs": "ObjectGraph",
    "OctTree_sumMass.hs": "OctTreeBase",
    "OctTree_sumEnergy.hs": "OctTreeBase",
    "OctTree_countActive.hs": "OctTreeBase",
    "OctTree_countParticles.hs": "OctTreeBase",
    "OctTree_barnesHutPotential.hs": "OctTreeBase",
    "OctTree_fmmPotential.hs": "OctTreeBase",
    "OctTree_scaleEnergy.hs": "OctTreeBase",
    "OctTree_clearFlags.hs": "OctTreeBase",
    # Split 2026-09-06 into one executable per timed pass (a shared
    # PiecewiseFunctionsBase.hs plus these), the same shape as the
    # OctTree family. The tables fold them back into one program.
    "PiecewiseFunctions_norm2Estimate.hs": "PiecewiseFunctionsBase",
    "PiecewiseFunctions_truncateTolViolations.hs": "PiecewiseFunctionsBase",
    "PiecewiseFunctions_compressMass.hs": "PiecewiseFunctionsBase",
    "PiecewiseFunctions_autorefineMaxLevel.hs": "PiecewiseFunctionsBase",
    "PiecewiseFunctions_pmapCutHistogram.hs": "PiecewiseFunctionsBase",
    "PiecewiseFunctions_lbDeuxLoadProxy.hs": "PiecewiseFunctionsBase",
    "PiecewiseFunctions_addConstPW.hs": "PiecewiseFunctionsBase",
    "PiecewiseFunctions_diffPW.hs": "PiecewiseFunctionsBase",
    "TernaryTree.hs": "TernaryTree",
    "Trie.hs": "Trie",
    "ColorOctree.hs": "ColorOctree",
}


class TestDefaultProgramsInventory(unittest.TestCase):
    """Derives the ordinary-benchmark inventory from the REAL, live
    DEFAULT_PROGRAMS list in gibbon_benchmark.py and compares it against
    the frozen DEFAULT_PROGRAMS_TO_STEM map above -- so a newly added or
    removed DEFAULT_PROGRAMS row is caught here explicitly, rather than
    silently being governed (or not) by whatever WIDTH_MANIFEST happens to
    already contain. If this test fails because a program was added, the
    fix is to migrate its source to Int64, add it to
    DEFAULT_PROGRAMS_TO_STEM, and (if it declares a new ADT) to
    WIDTH_MANIFEST -- not to weaken this check."""

    def test_default_programs_matches_frozen_inventory(self):
        import gibbon_benchmark as gb
        live = set(gb.DEFAULT_PROGRAMS)
        frozen = set(DEFAULT_PROGRAMS_TO_STEM)
        self.assertEqual(
            live, frozen,
            "gibbon_benchmark.DEFAULT_PROGRAMS has drifted from this file's "
            "frozen inventory -- added: %s, removed: %s" %
            (sorted(live - frozen), sorted(frozen - live)))

    def test_every_stem_in_the_inventory_has_a_width_manifest_entry(self):
        stems_with_manifest = {stem for (stem, _type) in WIDTH_MANIFEST}
        missing = sorted(set(DEFAULT_PROGRAMS_TO_STEM.values()) - stems_with_manifest)
        self.assertEqual(missing, [], "stem(s) with no WIDTH_MANIFEST entry: %s" % missing)


class TestBW01BW02NotSweptByOrdinaryPolicy(unittest.TestCase):
    """The dedicated variable-width experiments (Add1TreeInt8/16/32/64.hs,
    ArithIntensityInt8/16/32/64.hs) are deliberately excluded from
    DEFAULT_PROGRAMS and must keep their own distinct, per-width ADT
    fields -- this all-Int64 policy must never sweep them in. Their own
    width correctness is governed by test_add1tree_widths.py/
    test_arithintensity_widths.py; this is only the direct
    non-interference check that they are not accidentally part of the
    ordinary-benchmark inventory this file enforces."""

    ADD1TREE_STEMS = ["Add1TreeInt8", "Add1TreeInt16", "Add1TreeInt32", "Add1TreeInt64"]

    def test_add1tree_width_experiments_are_not_in_the_ordinary_inventory(self):
        for stem in self.ADD1TREE_STEMS:
            self.assertNotIn(stem, DEFAULT_PROGRAMS_TO_STEM.values())
            self.assertNotIn((stem, "Add1Tree"), WIDTH_MANIFEST)

    def test_add1tree_width_experiments_still_declare_distinct_widths(self):
        # A cheap, direct confirmation (not a full re-audit -- that is
        # test_add1tree_widths.py's job) that these 4 fixtures still each
        # declare THEIR OWN width, i.e. the all-Int64 policy did not
        # flatten them by accident.
        want = {"Add1TreeInt8": "Int8", "Add1TreeInt16": "Int16",
                "Add1TreeInt32": "Int32", "Add1TreeInt64": "Int64"}
        for stem, width in want.items():
            for dirpath in (PROGRAMS_AOS, PROGRAMS_SOA):
                path = dirpath / (stem + ".hs")
                if not path.exists():
                    continue
                text = path.read_text()
                self.assertIn(width, text,
                               "%s: expected to still declare %s somewhere" % (path, width))

    def test_arithintensity_width_experiments_still_declare_distinct_widths(self):
        want = {"ArithIntensityInt8": "Int8", "ArithIntensityInt16": "Int16",
                "ArithIntensityInt32": "Int32", "ArithIntensityInt64": "Int64"}
        for stem, width in want.items():
            for dirpath in (PROGRAMS_AOS, PROGRAMS_SOA):
                path = dirpath / (stem + ".hs")
                if not path.exists():
                    continue
                text = path.read_text()
                self.assertIn(width, text,
                               "%s: expected to still declare %s somewhere" % (path, width))


def _check_widths(fields, expected):
    """Returns a list of human-readable mismatch descriptions (empty if OK)."""
    problems = []
    if expected == INT64_EVERYWHERE:
        want = "Int64"
        for i, f in enumerate(fields):
            if f is None:
                continue
            if f != want:
                problems.append("field %d is %r, want %r" % (i, f, want))
        return problems
    # explicit per-position list
    if len(fields) != len(expected):
        problems.append("field count %d != expected %d" % (len(fields), len(expected)))
        return problems
    for i, (f, want) in enumerate(zip(fields, expected)):
        if f != want:
            problems.append("field %d is %r, want %r" % (i, f, want))
    return problems


class TestCuratedADTWidths(unittest.TestCase):
    """Fails loudly if a bare `Int` field reappears, if any curated
    program's ADT stops matching the all-Int64 policy, or if AoS/SoA
    disagree -- in EITHER the AOS or the SOA copy."""

    def test_every_curated_adt_matches_its_width_policy(self):
        failures = []
        for (stem, type_name), expected in WIDTH_MANIFEST.items():
            for variant, dirpath in (("AOS", PROGRAMS_AOS), ("SOA", PROGRAMS_SOA)):
                path = dirpath / (stem + ".hs")
                if not path.exists():
                    failures.append("%s: %s missing" % (variant, path))
                    continue
                text = path.read_text()
                try:
                    ctors = parse_data_decl(text, type_name)
                except AssertionError as e:
                    failures.append("%s %s: %s" % (variant, stem, e))
                    continue
                for cname, fields in ctors.items():
                    exp = expected[cname] if isinstance(expected, dict) else expected
                    problems = _check_widths(fields, exp)
                    for p in problems:
                        failures.append("%s %s.%s %s: %s" % (variant, stem, type_name, cname, p))
        self.assertEqual(failures, [], "\n" + "\n".join(failures))

    def test_no_bare_int_field_in_any_curated_adt(self):
        """House style: an ADT field declares its width EXPLICITLY
        (`Int64`), never as a bare `Int` -- both mean the same thing under
        the all-Int64 policy, but a bare `Int` field reads ambiguously next
        to a program that used to be Int32 and is silent about whether it
        was actually migrated on purpose. `test_every_curated_adt_matches_
        its_width_policy` above would also catch this indirectly (a bare
        `Int` field parses as `"Int"`, not `"Int64"`, so it already fails
        the width-policy match) -- this test is kept as an independent,
        directly-computed cross-check rather than relying on that
        implication alone."""
        bare_int_hits = []
        for (stem, type_name), _expected in WIDTH_MANIFEST.items():
            for variant, dirpath in (("AOS", PROGRAMS_AOS), ("SOA", PROGRAMS_SOA)):
                path = dirpath / (stem + ".hs")
                if not path.exists():
                    continue
                ctors = parse_data_decl(path.read_text(), type_name)
                for cname, fields in ctors.items():
                    if "Int" in fields:
                        bare_int_hits.append("%s %s.%s.%s has a bare Int field" %
                                              (variant, stem, type_name, cname))
        self.assertEqual(bare_int_hits, [])

    def test_aos_and_soa_field_widths_agree(self):
        """AoS/SoA structural equivalence: the same program's ADT must have
        the identical field-width sequence in both layout copies."""
        mismatches = []
        for (stem, type_name), _expected in WIDTH_MANIFEST.items():
            aos_path = PROGRAMS_AOS / (stem + ".hs")
            soa_path = PROGRAMS_SOA / (stem + ".hs")
            if not (aos_path.exists() and soa_path.exists()):
                continue
            aos_ctors = parse_data_decl(aos_path.read_text(), type_name)
            soa_ctors = parse_data_decl(soa_path.read_text(), type_name)
            if aos_ctors.keys() != soa_ctors.keys():
                mismatches.append("%s.%s: constructor sets differ: %s vs %s" %
                                   (stem, type_name, sorted(aos_ctors), sorted(soa_ctors)))
                continue
            for cname in aos_ctors:
                if aos_ctors[cname] != soa_ctors[cname]:
                    mismatches.append("%s.%s.%s: AOS=%s SOA=%s" %
                                       (stem, type_name, cname, aos_ctors[cname], soa_ctors[cname]))
        self.assertEqual(mismatches, [])


class TestOracleManifestGuards(unittest.TestCase):
    """Guards on oracles/manifest.json itself: every DEFAULT_PROGRAMS row
    has a registered oracle, and the VW-24-blocked rows' oracle values are
    pinned away from their known real (buggy) outputs -- this is the
    direct regression check against "an oracle gets silently edited to
    match Gibbon's own wrong output": pasting Gibbon's output into the
    oracle turns it into a tautology and would hide VW-24 forever."""

    EXPECTED_STEMS = [
        "List", "MonoTree", "LinearListReduction", "reduceNestedList", "TernaryTree",
        "DomTree", "DecisionTree", "DecisionTreeClassify",
        "ObjectGraph", "Trie", "PiecewiseFunctions",
        "DBQuery", "Compiler", "KDTree",
        "OctTree_sumMass", "OctTree_sumEnergy", "OctTree_countActive",
        "OctTree_countParticles", "OctTree_barnesHutPotential", "OctTree_fmmPotential",
        "OctTree_scaleEnergy", "OctTree_clearFlags", "ColorOctree",
    ]

    # (oracle_key, known real/buggy compiled output at --size-param 0) --
    # the registered "expected" value must NEVER equal this: a match here
    # means someone pasted Gibbon's own (VW-24-wrong) output into the
    # oracle instead of keeping the honest, independently-derived value,
    # which would silently let a VW-24 result enter qualified metrics.
    # NOTE: these are the Int32-era buggy values (frozen when VW-24 was
    # fixed for that width); the Int64 migration did not re-derive "what a
    # VW-24 regression would look like at Int64" (that would require
    # deliberately reproducing the bug) -- this is a known, explicitly
    # flagged gap, not a silently accepted one.
    KNOWN_BUGGY_OUTPUTS = {
        "OctTree_sumEnergy": "1477896046",
        "OctTree_countActive": "2773",
        "OctTree_barnesHutPotential": "0",
        "OctTree_fmmPotential": "0",
        "OctTree_scaleEnergy": "1057845708",
        "OctTree_clearFlags": "2773",
        "ColorOctree": "'#(524288 0)",
    }

    @classmethod
    def setUpClass(cls):
        cls.manifest = json.loads(MANIFEST.read_text())["oracles"]

    def test_every_default_program_has_an_oracle_entry(self):
        missing = [s for s in self.EXPECTED_STEMS if s not in self.manifest]
        self.assertEqual(missing, [], "no oracle registered for: %s" % missing)

    def test_vw24_blocked_oracles_are_not_pinned_to_the_known_buggy_output(self):
        offenders = []
        for stem, buggy in self.KNOWN_BUGGY_OUTPUTS.items():
            entry = self.manifest.get(stem)
            if entry is None:
                continue
            if entry.get("expected") == buggy:
                offenders.append(stem)
        self.assertEqual(
            offenders, [],
            "oracle(s) pinned to Gibbon's own known-wrong VW-24 output "
            "(this would silently let a wrong result enter qualified "
            "metrics): %s" % offenders)

    def test_every_oracle_entry_declares_independent_provenance(self):
        bad = []
        for stem in self.EXPECTED_STEMS:
            entry = self.manifest.get(stem)
            if entry is None:
                continue
            prov = entry.get("provenance")
            if prov not in ("hand-derived", "racket-reference", "python-model",
                             "reference-implementation"):
                bad.append((stem, prov))
        self.assertEqual(bad, [])


class TestVW24CurrentInt64OracleCoverage(unittest.TestCase):
    """VW-24 is fixed for the required --no-ran (plain --packed
    --use-mutable-cursors) path. `TestOracleManifestGuards` above is a
    DENY check (the manifest must never equal the old Int32-era
    known-wrong value) and is kept -- it costs nothing and remains a valid
    tripwire. This class adds the POSITIVE check: every VW-24-relevant
    manifest entry must equal a value independently re-derived from the
    current (Int64) oracle model, not merely "not equal to some other
    wrong number".

    Regression-pinned rather than re-running the live model here: the
    model materializes the whole 8-ary tree (~19M nodes) and takes over a
    minute, too slow for a fast unit suite. These values were captured by
    running the live model directly (`python3 -c "import octtree_model as
    m; t=m.build_tree(); ..."`, oracles/ directory) and confirmed to match
    oracles/manifest.json exactly -- not copied from Gibbon's own
    output."""

    RE_DERIVED_INT64 = {
        "OctTree_sumMass": 50331639,
        "OctTree_sumEnergy": 179362502472,
        "OctTree_countActive": 18680,
        "OctTree_countParticles": 16777216,
        "OctTree_barnesHutPotential": 70613843,
        "OctTree_fmmPotential": 229379432,
        "OctTree_scaleEnergy": 300158116707,
        "OctTree_clearFlags": 18680,
    }
    RE_DERIVED_COLOROCTREE = "'#(16777216 24540)"

    @classmethod
    def setUpClass(cls):
        cls.manifest = json.loads(MANIFEST.read_text())["oracles"]

    def test_octree_family_manifest_matches_current_int64_rederivation(self):
        mismatches = []
        for stem, expected in self.RE_DERIVED_INT64.items():
            got = self.manifest[stem].get("expected")
            if str(got) != str(expected):
                mismatches.append((stem, got, expected))
        self.assertEqual(mismatches, [],
                         "manifest value drifted from the current Int64 "
                         "re-derivation: %s" % mismatches)

    def test_coloroctree_manifest_matches_current_int64_rederivation(self):
        self.assertEqual(self.manifest["ColorOctree"].get("expected"),
                         self.RE_DERIVED_COLOROCTREE)

    def test_rederived_values_are_distinct_from_the_known_int32_era_buggy_ones(self):
        # Sanity: the positive values above must not accidentally equal the
        # negative guard's pinned buggy strings -- if they did, the two
        # checks would be testing the same thing instead of independently
        # covering "wrong" and "right".
        buggy = TestOracleManifestGuards.KNOWN_BUGGY_OUTPUTS
        for stem, expected in self.RE_DERIVED_INT64.items():
            if stem in buggy:
                self.assertNotEqual(str(expected), buggy[stem])


# ---------------------------------------------------------------------------
# Whole-program semantic-width consistency (Int64 throughout).
#
# TestCuratedADTWidths (above) only checks stored ADT field declarations.
# This section's stronger property is that FUNCTIONS operating on that
# semantic data -- arguments, results, accumulators -- use the same width.
# This section parses top-level `name :: T1 -> T2 -> ... -> Tn` signatures
# (single-line, as every migrated function in this suite is written) and
# checks the FINAL (return) type against a hand-maintained manifest,
# function by function -- the same "explicit enumerated check, not a
# whole-file regex" discipline as parse_data_decl above.
# ---------------------------------------------------------------------------

_SIG_RE = re.compile(r"^([A-Za-z_][A-Za-z0-9_']*)\s*::\s*(.+)$", re.MULTILINE)


def parse_function_signatures(source_text: str):
    """Returns {func_name: return_type_str} for every single-line top-level
    `name :: ... -> ReturnType` signature found. Only the FINAL arrow
    segment is kept (the return type); multi-line signatures and signatures
    without `->` (nullary bindings) are not returned by this pass, since no
    function audited here is declared that way."""
    sigs = {}
    for m in _SIG_RE.finditer(source_text):
        name, rhs = m.group(1), m.group(2)
        if "->" not in rhs:
            continue
        ret = rhs.split("->")[-1].strip()
        sigs[name] = ret
    return sigs


class TestFunctionSignatureParser(unittest.TestCase):
    def test_parses_return_type_of_multi_arg_signature(self):
        src = "countSmallLeaves :: Int -> DTree -> Int\n"
        self.assertEqual(parse_function_signatures(src)["countSmallLeaves"], "Int")

    def test_ignores_nullary_bindings(self):
        src = "gibbon_main =\n  let x = 1 in x\n"
        self.assertNotIn("gibbon_main", parse_function_signatures(src))


# Representative functions whose RETURN TYPE must be exactly Int64: all 22
# ordinary curated benchmarks use Int64 consistently, including KDTree,
# which is not a special case -- there is no two-tier
# KDTree-vs-everyone-else split anywhere in this file. This is an
# ALLOW-list: it only catches a regression in a function it already names.
# The comprehensive counterpart is TestNoUnauthorizedNarrowWidth below (a
# DENY-by-default scan with NO exceptions, since every build-side helper in
# this inventory was already Int64 even under the old policy -- narrow
# width is no longer legitimate ANYWHERE in these 22 programs, semantic or
# build-side).
MUST_BE_INT64 = {
    ("List", "sumList"): "Int64",
    ("List", "sumListAcc"): "Int64",
    ("List", "length"): "Int64",
    ("List", "mkList"): "List",  # mkList :: Int64 -> List
    ("LinearListReduction", "mkList"): "List",
    ("LinearListReduction", "reduce"): "Int",
    ("reduceNestedList", "mkList"): "List",
    ("reduceNestedList", "mkListA"): "ListA",
    ("reduceNestedList", "reduce"): "Int",
    ("TernaryTree", "sumTree"): "Int",
    ("TernaryTree", "rightmost"): "Int",
    ("MonoTree", "sumTree"): "Int",
    ("MonoTree", "sumTreeAcc"): "Int",
    ("MonoTree", "mkTree"): "Tree",
    ("ObjectGraph", "totalHeapSize"): "Int",
    ("ObjectGraph", "sumObjIds"): "Int",
    ("ObjectGraph", "countMarked"): "Int",
    ("ObjectGraph", "liveBytes"): "Int",
    ("ObjectGraph", "deadBytes"): "Int",
    ("Trie", "sumPrefixFreq"): "Int",
    ("Trie", "countTerminals"): "Int",
    ("Trie", "sumSubtreeHints"): "Int",
    ("Compiler", "instCountPass"): "Int",
    ("Compiler", "latencyModelPass"): "Int",
    ("Compiler", "blockCountPass"): "Int",
    ("Compiler", "castInstCountPass"): "Int",
    ("Compiler", "memoryOpStatsPass"): "Int",
    ("Compiler", "branchStatsPass"): "Int",
    ("Compiler", "throughputModelPass"): "Int",
    ("DomTree", "countPositioned"): "Int",
    ("DomTree", "getWidth"): "Int",
    ("DomTree", "sumArea"): "Int",
    ("DomTree", "sumTextWidth"): "Int",
    ("DomTree", "maxBottom"): "Int",
    ("DecisionTree", "countNodes"): "Int",
    ("DecisionTree", "countLeaves"): "Int",
    ("DecisionTree", "treeDepth"): "Int",
    ("DecisionTree", "sumSamples"): "Int",
    ("DecisionTree", "sumImpurity"): "Int",
    ("DecisionTree", "sumPathLengths"): "Int",
    ("DecisionTree", "inferenceCost"): "Int",
    # These four moved to DecisionTreeClassify.hs in the 2026-09-06 split;
    # their signatures are unchanged, only the file they live in.
    ("DecisionTreeClassify", "classify"): "Int",
    ("DecisionTreeClassify", "classifyDepth"): "Int",
    ("DecisionTreeClassify", "classifyDepthBatch"): "Int",
    ("DecisionTreeClassify", "classifyBatch"): "Int",
    ("PiecewiseFunctions", "truncateTolViolations"): "Int",
    ("PiecewiseFunctions", "compressMass"): "Int",
    ("PiecewiseFunctions", "norm2Estimate"): "Int",
    ("PiecewiseFunctions", "autorefineMaxLevel"): "Int",
    ("PiecewiseFunctions", "pmapCutHistogram"): "Int",
    ("PiecewiseFunctions", "lbDeuxLoadProxy"): "Int",
    ("DBQuery", "sumCost"): "Int",
    ("DBQuery", "sumRows"): "Int",
    ("DBQuery", "countJoins"): "Int",
    ("DBQuery", "sumMemory"): "Int",
    ("DBQuery", "hashJoinPressure"): "Int",
    ("DBQuery", "filterSelectivitySkew"): "Int",
    ("OctTreeBase", "massOf"): "Int64",
    ("OctTreeBase", "weightedPos"): "Int64",
    ("OctTreeBase", "countOf"): "Int64",
    ("OctTreeBase", "momentumOf"): "Int64",
    ("OctTreeBase", "sumMass"): "Int64",
    ("OctTreeBase", "sumEnergy"): "Int64",
    ("OctTreeBase", "countActive"): "Int64",
    ("OctTreeBase", "countParticles"): "Int64",
    ("OctTreeBase", "barnesHutPotential"): "Int64",
    ("OctTreeBase", "fmmUpSeries"): "Int64",
    ("OctTreeBase", "fmmDownSeries"): "Int64",
    ("OctTreeBase", "fmmPotential"): "Int64",
    ("ColorOctree", "cSumR"): "Int64",
    ("ColorOctree", "cSumG"): "Int64",
    ("ColorOctree", "cSumB"): "Int64",
    ("ColorOctree", "cCount"): "Int64",
    ("ColorOctree", "paletteEntriesQuantized"): "Int64",
    ("ColorOctree", "quantizationErrorProxy"): "Int64",
    # KDTree: no longer a separate "KDTREE_MUST_STAY_INT64" table -- it is
    # audited the same way as every other program now.
    ("KDTree", "nearestDist"): "Int",
    ("KDTree", "sumMassInRange"): "Int",
    ("KDTree", "dist3"): "Int",
}

# There is no Int32-by-default policy in this inventory, so there is no
# "why is this one function allowed to be Int64" table to maintain: Int64
# is the default and ONLY authorized width for every one of these 22
# programs, semantic or build-side.


class TestNoUnauthorizedNarrowWidth(unittest.TestCase):
    """Deny-by-default scan: parses EVERY top-level function signature in
    every ordinary curated program (both layouts, KDTree included) and
    fails on any `Int8`/`Int16`/`Int32` token anywhere in it -- argument or
    return position. This has NO exception table: every build-side
    helper/loop-counter/Vector-index boundary in this inventory is already
    Int64, so there is no legitimate reason for a narrower width to appear
    anywhere in these 22 programs. This is the direct, comprehensive
    counterpart to MUST_BE_INT64's allow-list -- it catches a newly added
    (or newly regressed) function that nobody remembered to keep at Int64,
    without needing a table update to be CAUGHT."""

    ORDINARY_STEMS = sorted({stem for (stem, _type) in WIDTH_MANIFEST})

    def test_no_narrow_width_anywhere_in_the_ordinary_inventory(self):
        narrow = re.compile(r"\bInt(8|16|32)\b")
        failures = []
        for stem in self.ORDINARY_STEMS:
            for variant_dir in (PROGRAMS_AOS, PROGRAMS_SOA):
                path = variant_dir / (stem + ".hs")
                if not path.exists():
                    continue
                text = path.read_text()
                for m in _SIG_RE.finditer(text):
                    func_name, rhs = m.group(1), m.group(2)
                    if narrow.search(rhs):
                        failures.append("%s %s.%s :: %s -- unauthorized narrow width "
                                         "(Int8/16/32 no longer legitimate anywhere in "
                                         "the ordinary curated inventory)" %
                                         (variant_dir.name, stem, func_name, rhs.strip()))
        self.assertEqual(failures, [], "\n" + "\n".join(failures))

    def test_no_narrow_width_token_anywhere_in_the_file_at_all(self):
        """Stronger than the signature-only scan above: a raw token search
        across the WHOLE file (bodies, local let-bindings, everything) --
        catches a narrow width hiding somewhere `_SIG_RE` wouldn't look,
        e.g. inside a multi-line signature or a `data` field this test
        module doesn't separately enumerate. Comments are excluded (they
        legitimately discuss the superseded Int32 policy for context)."""
        narrow = re.compile(r"\bInt(8|16|32)\b")
        failures = []
        for stem in self.ORDINARY_STEMS:
            for variant_dir in (PROGRAMS_AOS, PROGRAMS_SOA):
                path = variant_dir / (stem + ".hs")
                if not path.exists():
                    continue
                for lineno, line in enumerate(path.read_text().splitlines(), 1):
                    code = line.split("--", 1)[0]
                    if narrow.search(code):
                        failures.append("%s:%d: %s" % (path, lineno, line.strip()))
        self.assertEqual(failures, [], "\n" + "\n".join(failures))


# Reviewed, concrete API boundaries where an integer-width CONVERSION
# (toInt8/toInt16/toInt32/toInt64) is still legitimate in the ordinary
# curated inventory. Deliberately EMPTY: every toInt32/toInt16/toInt8 call
# that used to sit at an Int64-build-side-value -> Int32-semantic-field
# boundary is now a redundant identity conversion (both sides are Int64)
# and has been removed from every one of these 22 programs; Gibbon.Vector's
# index parameter was already Int64 too, so DecisionTree's old
# `nth fv (toInt64 feature)` boundary conversion is also gone. Kept
# (rather than deleted) so a future conversion reintroduced at a genuine
# new API boundary has an obvious, reviewed place to explain itself instead
# of silently slipping past TestNoObsoleteWidthConversions below.
LEGITIMATE_WIDTH_CONVERSIONS = {}


class TestNoObsoleteWidthConversions(unittest.TestCase):
    """No `toInt32`/`toInt16`/`toInt8` call may remain anywhere in the
    ordinary curated inventory (semantic or build-side) -- every one of
    them was either a narrowing conversion into a now-Int64 field
    (redundant identity conversion, removed) or has no remaining
    justification. `toInt64` calls are checked against
    LEGITIMATE_WIDTH_CONVERSIONS (currently empty -- see above); an
    unlisted `toInt64` is presumptively an avoidable widen with no
    corresponding real boundary."""

    def test_no_toint8_toint16_toint32_anywhere(self):
        pattern = re.compile(r"\btoInt(8|16|32)\b")
        hits = []
        for stem in sorted({stem for (stem, _type) in WIDTH_MANIFEST}):
            for dirpath in (PROGRAMS_AOS, PROGRAMS_SOA):
                path = dirpath / (stem + ".hs")
                if not path.exists():
                    continue
                for lineno, line in enumerate(path.read_text().splitlines(), 1):
                    code = line.split("--", 1)[0]
                    if pattern.search(code):
                        hits.append("%s:%d: %s" % (path, lineno, line.strip()))
        self.assertEqual(hits, [], "\n" + "\n".join(hits))

    def test_toint64_only_at_reviewed_boundaries(self):
        pattern = re.compile(r"\btoInt64\b")
        hits = []
        reviewed_stems = {s for (s, _f) in LEGITIMATE_WIDTH_CONVERSIONS}
        for stem in sorted({stem for (stem, _type) in WIDTH_MANIFEST}):
            for dirpath in (PROGRAMS_AOS, PROGRAMS_SOA):
                path = dirpath / (stem + ".hs")
                if not path.exists():
                    continue
                text = path.read_text()
                if not pattern.search(text):
                    continue
                # Any occurrence at all is unexpected right now, since
                # LEGITIMATE_WIDTH_CONVERSIONS is currently empty.
                if stem not in reviewed_stems:
                    for lineno, line in enumerate(text.splitlines(), 1):
                        code = line.split("--", 1)[0]
                        if pattern.search(code):
                            hits.append("%s:%d: %s" % (path, lineno, line.strip()))
        self.assertEqual(hits, [], "\n" + "\n".join(hits))

    def test_reviewed_boundary_table_entries_are_not_stale(self):
        """If LEGITIMATE_WIDTH_CONVERSIONS ever gains an entry, it must
        stay honest: the named function must still actually exist, in both
        layouts, in every one of these 22 programs."""
        failures = []
        for (stem, func_name) in LEGITIMATE_WIDTH_CONVERSIONS:
            for variant_dir in (PROGRAMS_AOS, PROGRAMS_SOA):
                path = variant_dir / (stem + ".hs")
                if not path.exists():
                    failures.append("%s: %s missing" % (variant_dir.name, path))
                    continue
                full_sig = _full_signature(path.read_text(), func_name)
                if full_sig is None:
                    failures.append("%s %s.%s: no signature found (stale entry?)" %
                                     (variant_dir.name, stem, func_name))
        self.assertEqual(failures, [], "\n" + "\n".join(failures))


def _full_signature(source_text: str, func_name: str):
    """Returns the FULL right-hand side of `func_name :: ...` (every arrow
    segment, not just the return type), or None if not found. Complements
    parse_function_signatures (which discards everything but the final
    segment) for checks that must see argument types too."""
    m = re.search(r"^%s\s*::\s*(.+)$" % re.escape(func_name), source_text, re.MULTILINE)
    return m.group(1).strip() if m else None


class TestSemanticFunctionWidths(unittest.TestCase):
    """Fails when any ordinary curated program's function drifts off
    Int64, or when AoS and SoA disagree on a function's width -- the
    whole-program analogue of TestCuratedADTWidths above, which only
    covers stored ADT fields."""

    def _sig(self, variant_dir, stem, func_name):
        path = variant_dir / (stem + ".hs")
        self.assertTrue(path.exists(), "%s missing" % path)
        sigs = parse_function_signatures(path.read_text())
        self.assertIn(func_name, sigs, "%s: no signature found for %s" % (path, func_name))
        return sigs[func_name]

    def test_must_be_int64_functions_are_int64(self):
        failures = []
        for (stem, func_name), expected in MUST_BE_INT64.items():
            for variant_dir in (PROGRAMS_AOS, PROGRAMS_SOA):
                got = self._sig(variant_dir, stem, func_name)
                if got != expected:
                    failures.append("%s %s.%s: got %r, want %r" %
                                     (variant_dir.name, stem, func_name, got, expected))
        self.assertEqual(failures, [], "\n" + "\n".join(failures))

    def test_aos_and_soa_agree_on_every_audited_function_signature(self):
        mismatches = []
        for stem, func_name in MUST_BE_INT64:
            aos_sig = self._sig(PROGRAMS_AOS, stem, func_name)
            soa_sig = self._sig(PROGRAMS_SOA, stem, func_name)
            if aos_sig != soa_sig:
                mismatches.append("%s.%s: AOS=%r SOA=%r" %
                                   (stem, func_name, aos_sig, soa_sig))
        self.assertEqual(mismatches, [])

    def test_aos_and_soa_agree_on_every_function_signature_in_every_curated_program(self):
        """Stronger than the audited-table-only check above: EVERY function
        name that parses a return-type signature in a curated program's
        AoS copy must have the identical return type in its SoA copy (and
        vice versa) -- not just the ones already named in MUST_BE_INT64.
        Catches a signature drift on a function nobody thought to add to
        that table."""
        stems = sorted({stem for (stem, _type) in WIDTH_MANIFEST})
        mismatches = []
        for stem in stems:
            aos_path = PROGRAMS_AOS / (stem + ".hs")
            soa_path = PROGRAMS_SOA / (stem + ".hs")
            if not (aos_path.exists() and soa_path.exists()):
                continue
            aos_sigs = parse_function_signatures(aos_path.read_text())
            soa_sigs = parse_function_signatures(soa_path.read_text())
            for name in sorted(set(aos_sigs) & set(soa_sigs)):
                if aos_sigs[name] != soa_sigs[name]:
                    mismatches.append("%s.%s: AOS=%r SOA=%r" %
                                       (stem, name, aos_sigs[name], soa_sigs[name]))
        self.assertEqual(mismatches, [], "\n" + "\n".join(mismatches))

    def test_no_avoidable_immediately_nested_width_round_trip(self):
        """A direct `toInt64 (toInt32 ...)` or `toInt32 (toInt64 ...)` is
        never meaningful in this suite. Redundant with
        TestNoObsoleteWidthConversions (neither toInt32 nor toInt64 should
        exist at all in this inventory any more), kept as a cheap,
        independent cross-check specifically for the round-trip shape."""
        pattern = re.compile(r"toInt64\s*\(\s*toInt32|toInt32\s*\(\s*toInt64")
        hits = []
        stems = {stem for stem, _ in WIDTH_MANIFEST}
        for dirpath in (PROGRAMS_AOS, PROGRAMS_SOA):
            for stem in stems:
                path = dirpath / (stem + ".hs")
                if not path.exists():
                    continue
                if pattern.search(path.read_text()):
                    hits.append(str(path))
        self.assertEqual(hits, [])


class TestNarrowWidthContractComments(unittest.TestCase):
    """Comments that assert the opposite of the code, and have before.

    Five contract comments across the compiler and the RTS header claimed
    narrow-width support was absent or unsafe while the code implemented it.
    One of them is emitted verbatim into every generated `.c`, so a maintainer
    reading a generated file was told in-band that W8 multiply loops stay
    scalar, thirty lines above the packed W8 multiply.  One had already been
    corrected once and was wrong again afterwards.

    A comment that has been wrong twice needs a test rather than a third
    correction, so these are phrase-greps over the tree.  They are deliberately
    about the CLAIM, not about any particular wording of the fix: if narrow
    widths are ever genuinely withdrawn, delete the corresponding assertion
    along with the support.
    """

    SRC = HERE.parent.parent / "src"
    RTS = HERE.parent.parent.parent / "gibbon-rts" / "rts-c"

    def _sources(self):
        for root, suffixes in ((self.SRC, (".hs",)), (self.RTS, (".h", ".c"))):
            if not root.exists():
                continue
            for path in sorted(root.rglob("*")):
                if path.suffix in suffixes and path.is_file():
                    yield path

    def _assert_absent(self, pattern, why):
        rx = re.compile(pattern, re.I | re.S)
        hits = []
        for path in self._sources():
            try:
                text = path.read_text()
            except (OSError, UnicodeDecodeError):
                continue
            if rx.search(text):
                hits.append(str(path))
        self.assertEqual(hits, [], why)

    def test_no_source_claims_narrow_width_codegen_is_unsafe(self):
        # Lower.hs propagates `intPrimWidth` into every L4 prim and `L4.Ty`
        # carries `IntTy IntWidth`, so there is no width erasure point.
        self._assert_absent(
            r"width\s+erasure\s+point|narrow-width\s+code\s+generation\s+is\s+"
            r"therefore\s+unsafe",
            "a comment still claims narrow-width codegen is unsafe or erased",
        )

    def test_no_source_claims_narrow_simd_stays_scalar(self):
        # `gib_vec_mul_int8x16` exists and `simdCapable` enables VecOpMul for
        # IntS W8; `simdScalarEnabled` is True for every scalar.
        self._assert_absent(
            r"no\s+packed\s+8-bit\s+multiply\s+at\s+all|"
            r"no\s+emitted\s+helpers\s+yet",
            "a comment still claims W8/W16 have no SIMD helpers",
        )

    def test_no_source_references_compatDefaultIntWidth(self):
        # The function does not exist anywhere in the tree, and bare `Int`
        # maps to W64, not to a 32-bit default.
        self._assert_absent(
            r"compatDefaultIntWidth",
            "a comment cites Gibbon.L0.Typecheck.compatDefaultIntWidth, "
            "which does not exist",
        )

    def test_no_source_claims_the_conversions_are_unimplemented(self):
        # All sixteen toInt8/16/32/64 source/destination pairs work.
        #
        # `\s` alone will not span a comment continuation: the real text wrapped
        # as "not yet\n-- implemented", so the gap has to admit the leading `--`
        # or `*` that starts the next comment line.
        self._assert_absent(
            r"toInt(8|16|32|64)[^.]{0,240}?planned\s*(?:--|\*)?\s*but"
            r"\s*(?:--|\*)?\s*not\s*(?:--|\*)?\s*yet\s*(?:--|\*)?\s*implemented",
            "a comment still claims the width-conversion primitives are unimplemented",
        )


if __name__ == "__main__":
    unittest.main()
