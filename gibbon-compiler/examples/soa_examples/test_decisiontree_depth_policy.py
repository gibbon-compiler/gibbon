#!/usr/bin/env python3
"""Permanent regression tests for the DecisionTree.hs committed-depth
reduction (a benchmark-size policy exception for VW-38 -- see BUGS.md).

These tests lock down the STATIC, fast-to-check facts: the
depth-to-node-count identity, that AoS/SoA agree on the new depth, that
the query/batch counts and Int64 policy are untouched, that mandatory
flags are still unconditional for this program, that a stale (old-depth)
artifact is invalidated by the content-addressed fingerprint, and that
DecisionTree's eligibility is governed by the SAME generic mechanism as
every other program -- no benchmark-name special case exists anywhere in
the driver.

Real compiles (the actual qualification-passes-at-depth-14 evidence) are
run directly through the real driver and are NOT re-run here (each takes
~45-100s; inappropriate for a fast unit suite).
"""
import re
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROGRAMS_AOS = HERE / "programs" / "AOS"
PROGRAMS_SOA = HERE / "programs" / "SOA"
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE / "oracles"))
REPO_ROOT = HERE.parents[2]

import decisiontree_model as model  # noqa: E402
import gibbon_benchmark as gb  # noqa: E402
import bench_provenance as prov  # noqa: E402

# The classification half's depth -- unchanged by the 2026-09-06 split.
SELECTED_DEPTH = 14
SELECTED_LEAVES = 987
SELECTED_NODES = 1973
# The folds half's depth, raised by that split so the nine folds are
# timeable at all (they ran 12-23 microseconds at depth 14).
FOLD_DEPTH = 32
FOLD_LEAVES = 5702887
FOLD_NODES = 11405773
OLD_DEPTH = 35
OLD_LEAVES = 24157817
OLD_NODES = 48315633


def _fib(n: int) -> int:
    """Standalone closed-form-adjacent Fibonacci, Fib(1)=Fib(2)=1 --
    deliberately NOT sharing any code with decisiontree_model.py's
    memoized recursion, so agreement between the two is a genuine
    independent cross-check, not the same function called twice."""
    if n <= 2:
        return 1
    a, b = 1, 1
    for _ in range(n - 2):
        a, b = b, a + b
    return b


class TestDepthToNodeCountIdentity(unittest.TestCase):
    """buildTree is a full binary tree (every Node has exactly two
    children): leaves(d) = Fib(d+2); nodes(d) = 2*leaves(d) - 1. Checked
    two independent ways -- the closed-form Fibonacci above, and the
    model's own memoized recursion (mirroring the Haskell spec, not
    compiled Gibbon output) -- and cross-checked against real compiled
    output at both the selected and the former committed depth."""

    def test_closed_form_matches_memoized_recursion_over_a_range(self):
        for d in range(-5, 40):
            leaves = model.count_leaves(d)
            nodes = model.count_nodes(d)
            self.assertEqual(leaves, _fib(d + 2), "leaves(%d) mismatch" % d)
            self.assertEqual(nodes, 2 * leaves - 1, "nodes(%d) != 2*leaves-1" % d)
            self.assertEqual(nodes, model.count_leaves(d) + (model.count_nodes(d) - model.count_leaves(d)))

    def test_selected_depth_matches_real_compiled_output(self):
        # '#(nodes leaves depth imp samples feat0 small cost paths pdepth batch)
        self.assertEqual(model.count_nodes(SELECTED_DEPTH), SELECTED_NODES)
        self.assertEqual(model.count_leaves(SELECTED_DEPTH), SELECTED_LEAVES)

    def test_former_committed_depth_matches_historical_record(self):
        # Cross-validates the identity against the number this program
        # itself printed at the former depth 35, before the committed
        # depth was reduced to 14 (see BUGS.md VW-38), not a value
        # invented for this test.
        self.assertEqual(model.count_nodes(OLD_DEPTH), OLD_NODES)
        self.assertEqual(model.count_leaves(OLD_DEPTH), OLD_LEAVES)

    def test_oracle_module_d0_is_the_selected_depth(self):
        # D0 remains the CLASSIFICATION depth after the split.
        self.assertEqual(model.D0, model.SIZE_PARAM + SELECTED_DEPTH)
        self.assertEqual(model.CLASSIFY_D0, model.SIZE_PARAM + SELECTED_DEPTH)

    def test_oracle_module_fold_depth(self):
        self.assertEqual(model.FOLD_D0, model.SIZE_PARAM + FOLD_DEPTH)
        self.assertEqual(model.count_leaves(FOLD_DEPTH), FOLD_LEAVES)
        self.assertEqual(model.count_nodes(FOLD_DEPTH), FOLD_NODES)

    def test_split_preserves_the_pre_split_committed_tuple(self):
        # The split re-partitioned the model, it did not change any
        # semantics: at one shared depth the model still produces the exact
        # 11-tuple the combined program committed.
        self.assertEqual(model.expected_combined(SELECTED_DEPTH),
                         "'#(1973 987 15 983433 610 0 987 14 6255 1907500 -210000)")

    def test_classify_half_workload_did_not_move(self):
        # Its two values are bit-for-bit the last two of that tuple.
        self.assertEqual(model.expected_classify(), "'#(1907500 -210000)")


class TestAosSoaSelectedDepthAgreement(unittest.TestCase):
    def _text(self, layout, program="DecisionTree.hs"):
        return (PROGRAMS_AOS if layout == "AOS" else PROGRAMS_SOA).joinpath(
            program).read_text()

    def test_both_layouts_declare_the_selected_depth(self):
        # Each half declares ITS OWN depth, and both layouts of a half agree.
        pat = re.compile(r"buildTree\s*\(sizeParam\s*\+\s*(\d+)\)")
        for program, want in (("DecisionTree.hs", FOLD_DEPTH),
                              ("DecisionTreeClassify.hs", SELECTED_DEPTH)):
            for layout in ("AOS", "SOA"):
                m = pat.search(self._text(layout, program))
                self.assertIsNotNone(
                    m, "%s/%s: buildTree call site not found" % (layout, program))
                self.assertEqual(int(m.group(1)), want,
                                 "%s/%s declares depth %s, expected %d" %
                                 (layout, program, m.group(1), want))

    # `test_each_half_binds_exactly_one_tree` used to live here. It enforced that
    # each program binds at most one tree, to dodge a SoA + --use-mutable-cursors
    # defect asserted in a comment and recorded nowhere else -- no reproducer, no
    # error text, no mechanism. It does not reproduce: sixteen configurations,
    # including the real program with a second tree bound in the same
    # gibbon_main under the full optimisation stack, all give correct and
    # unchanged values. See TWO-TREES in llm-notes BUGS.md for the evidence and a
    # reproduction recipe. Constraining the corpus shape against an
    # uncharacterised defect costs freedom and returns no evidence; if it comes
    # back, it should come back as a reproducer.

    def test_halves_do_not_overlap_in_passes(self):
        folds = self._text("AOS")
        classify = self._text("AOS", "DecisionTreeClassify.hs")
        # Slice at the DEFINITION -- the file header discusses
        # `gibbon_main` in prose well before it.
        folds_main = folds[folds.index("\ngibbon_main ="):]
        classify_main = classify[classify.index("\ngibbon_main ="):]
        for name in ("countNodes", "sumImpurity", "sumPathLengths"):
            self.assertIn(name, folds_main)
            self.assertNotIn(name, classify_main)
        for name in ("classifyDepthBatch", "classifyBatch"):
            self.assertIn(name, classify_main)
            self.assertNotIn(name, folds_main)

    def test_no_stale_depth_35_literal_remains_in_the_build_call(self):
        pat = re.compile(r"buildTree\s*\(sizeParam\s*\+\s*35\)")
        for program in ("DecisionTree.hs", "DecisionTreeClassify.hs"):
            for layout in ("AOS", "SOA"):
                self.assertIsNone(
                    pat.search(self._text(layout, program)),
                    "%s/%s still calls buildTree at the old depth 35"
                    % (layout, program))

    def test_layouts_differ_only_in_annotations_not_workload(self):
        aos = self._text("AOS").splitlines()
        soa = self._text("SOA").splitlines()
        # Same technique test_width_migration.py's own AoS/SoA parity
        # checks use: a real diff, not a hand-picked substring.
        import difflib
        diff = list(difflib.unified_diff(aos, soa, lineterm=""))
        # Skip the two file-header lines by position, not by a "---"/"+++"
        # prefix: a removed Haskell comment ("-" + "-- ...") also starts
        # with "---", and filtering on the prefix silently drops it.
        changed = [l for l in diff[2:] if l.startswith(("+", "-"))]
        # A line that names the layout (a header comment saying the type is
        # Linear or Factored) differs between the two files by that word
        # alone; it is the annotation restated, not a workload change.
        import re
        def layout_blind(body):
            return re.sub(r"\b(Linear|Factored)\b", "LAYOUT", body)
        removed = {layout_blind(l[1:]) for l in changed if l.startswith("-")}
        added = {layout_blind(l[1:]) for l in changed if l.startswith("+")}
        for line in changed:
            body = line[1:]
            counterpart = added if line.startswith("-") else removed
            allowed = ("ANN" in body or "Vidush" in body or body.strip() == ""
                       or layout_blind(body) in counterpart)
            self.assertTrue(allowed, "unexpected AoS/SoA divergence: %r" % line)


class TestQueryAndBatchCountsUnchanged(unittest.TestCase):
    """The query/batch counts must remain unchanged by the depth reduction
    and by the 2026-09-06 fold/classify split."""

    def _text(self, layout, program="DecisionTree.hs"):
        return (PROGRAMS_AOS if layout == "AOS" else PROGRAMS_SOA).joinpath(
            program).read_text()

    def test_batch_counts_and_fvsize_unchanged_in_source(self):
        for layout in ("AOS", "SOA"):
            text = self._text(layout, "DecisionTreeClassify.hs")
            self.assertIn("classifyDepthBatch tree 32 250000", text)
            self.assertIn("classifyBatch tree 32 1000000", text)

    def test_model_uses_the_same_unchanged_batch_counts(self):
        import inspect
        src = inspect.getsource(model.expected_classify)
        self.assertIn("250000", src)
        self.assertIn("1000000", src)
        self.assertIn(", 32,", src)


class TestSemanticInt64Unchanged(unittest.TestCase):
    def test_dtree_fields_still_int64(self):
        text = (PROGRAMS_AOS / "DecisionTree.hs").read_text()
        m = re.search(r"data DTree\s*=.*?(?=\n\n)", text, re.S)
        self.assertIsNotNone(m)
        body = m.group(0)
        self.assertNotIn("Int32", body)
        self.assertNotIn("Int16", body)
        self.assertNotIn("Int8", body)
        self.assertEqual(body.count("Int64"), 5)  # 2 Leaf fields + 3 Node fields


class TestMandatoryFlagsUnconditionalForDecisionTree(unittest.TestCase):
    def test_no_program_override_for_decisiontree(self):
        self.assertNotIn("DecisionTree.hs", gb.PROGRAM_COMPILE_OVERRIDES)
        gb._validate_no_ran_overrides()

    def test_build_gibbon_command_still_unconditional_regardless_of_program_name(self):
        # build_gibbon_command takes no program-name parameter at all --
        # --packed/--no-ran cannot be conditioned on "is this DecisionTree".
        import inspect
        params = [p.lower() for p in inspect.signature(gb.build_gibbon_command).parameters]
        self.assertNotIn("program", params)
        cmd = gb.build_gibbon_command(Path("DecisionTree.hs"), "soa", Path("P.c"),
                                      Path("P.exe"), "gcc")
        self.assertIn("--packed", cmd)
        self.assertIn("--no-ran", cmd)


class TestOldDepthArtifactInvalidation(unittest.TestCase):
    """A buildinfo.json recorded against the OLD (depth-35) source content
    must never be treated as current after the source is edited -- the
    fingerprint hashes actual file content, not a version label."""

    def test_old_source_hash_forces_recompile(self):
        with tempfile.TemporaryDirectory() as td:
            td = Path(td)
            src, exe, cfile = td / "DecisionTree.hs", td / "D.exe", td / "D.c"
            exe.write_text("#!/bin/true\n")
            cfile.write_text("/* c */\n")
            buildinfo = td / "D.buildinfo.json"
            comp = prov.CompilerResolution(td / "gibbon", "GIBBON_EXE", "h")
            cc = {"cc": "gcc", "path": "/usr/bin/gcc", "version": "v"}
            cmd = gb.build_gibbon_command(src, "soa", cfile, exe, "gcc")

            src.write_text("-- old depth-35 committed source (simulated)\n"
                           "buildTree (sizeParam + 35)\n")
            old_fp = prov.build_fingerprint(src, cmd, comp, cc, REPO_ROOT)
            prov.write_buildinfo_atomic(buildinfo, old_fp, cfile, exe, REPO_ROOT)

            src.write_text("-- new depth-14 committed source (simulated)\n"
                           "buildTree (sizeParam + 14)\n")
            new_fp = prov.build_fingerprint(src, cmd, comp, cc, REPO_ROOT)
            recompile, reason = prov.decide_recompile(buildinfo, new_fp, cfile, exe)
            self.assertTrue(recompile, "an edited (old-depth) source was NOT invalidated: %r" % reason)

    def test_real_decisiontree_source_no_longer_hashes_to_a_stale_recorded_value(self):
        # The actual sources on disk right now must not match a frozen
        # hash of the OLD depth-35 file -- i.e. the edit really happened
        # and is really what gets hashed (not a cached/derived value).
        # After the 2026-09-06 split each half declares its own depth.
        for program, depth in (("DecisionTree.hs", FOLD_DEPTH),
                               ("DecisionTreeClassify.hs", SELECTED_DEPTH)):
            text = (PROGRAMS_AOS / program).read_text()
            self.assertNotIn("sizeParam + 35", text)
            self.assertIn("sizeParam + %d" % depth, text)


class TestEligibilityHasNoNameSpecialCase(unittest.TestCase):
    """Restoring DecisionTree's numeric eligibility must be an automatic
    consequence of its qualification now passing (because the workload is
    smaller), not a code change that carves out its name. Verified by
    showing the string never appears in the driver's decision logic."""

    def test_gibbon_benchmark_source_names_decisiontree_only_where_allowed(self):
        """The name may appear only in program lists and in the RAN exception
        table -- never in eligibility or qualification logic.

        A program list is a line holding nothing but quoted `.hs` names
        (optionally opening or closing the literal): DEFAULT_PROGRAMS, and
        any grouping of programs for presentation. Such a line cannot carry a
        decision about the program it names.

        The invariant this class protects is that numeric eligibility is a
        consequence of the oracle qualification passing, not of a name being
        carved out. A COMPILE-FLAG policy is a different thing: it changes how
        a program is built, is stated and justified in
        RAN_ENABLED_PROGRAMS, is reported in every table that shows the
        program, and leaves the qualification path untouched -- the program is
        still checked against its oracle in exactly the same way. So that
        mention is allowed by name here, and anything else still fails.
        """
        import re
        src = (HERE / "gibbon_benchmark.py").read_text()
        hits = [ln for ln in src.splitlines() if "DecisionTree" in ln]
        program_list_line = re.compile(
            r'^(\w+(\s*:\s*[\w\[\], ]+)?\s*=\s*[\(\[]\s*)?'
            r'("[\w.]+\.hs",?\s*)+[\)\]]?,?$')
        allowed_program_list = [h for h in hits
                                if program_list_line.match(h.strip())]
        allowed_ran = [h for h in hits if h.strip().startswith('"DecisionTreeClassify.hs":')]
        default_programs = src[src.index("DEFAULT_PROGRAMS = ["):]
        default_programs = default_programs[:default_programs.index("]")]
        self.assertIn('"DecisionTree.hs"', default_programs,
                      "expected the DEFAULT_PROGRAMS entry: %r" % hits)
        self.assertLessEqual(len(allowed_ran), 1,
                             "at most one RAN_ENABLED_PROGRAMS entry: %r" % hits)
        unexpected = [h for h in hits
                      if h not in allowed_program_list and h not in allowed_ran]
        self.assertEqual(unexpected, [],
                         "DecisionTree named outside the program list and the "
                         "RAN exception table: %r" % unexpected)

    def test_the_ran_exception_does_not_touch_qualification(self):
        """The RAN entry must be a compile-flag policy only.

        If the name ever leaked into how a result is judged VERIFIED, the
        eligibility carve-out this class exists to prevent would be back.
        """
        import gibbon_benchmark as gb
        import inspect
        for fn in (gb.qualify_variant, gb.program_uses_no_ran):
            src = inspect.getsource(fn)
            self.assertNotIn("DecisionTree", src,
                             f"{fn.__name__} must not name a program")

    def test_bench_provenance_has_no_decisiontree_special_case(self):
        src = (HERE / "bench_provenance.py").read_text()
        self.assertNotIn("DecisionTree", src)

    def test_a_verified_decisiontree_result_is_eligible_exactly_like_any_other_program(self):
        aos = gb.BenchmarkResult("DecisionTree.hs", "aos")
        soa = gb.BenchmarkResult("DecisionTree.hs", "soa")
        for r, t in ((aos, 1.0), (soa, 0.9)):
            st = prov.QualificationStatus(r.variant, r.program)
            st.compile_status = prov.COMPILE_OK
            st.exec_status = prov.EXEC_OK
            st.oracle_status = prov.ORACLE_PASS
            st.semantic_output = "'#(1973 987 15 983433 610 0 987 14 6255 1907500 -210000)"
            r.qualification = st
            r.compile_success = True
            r.run_success = True
            r.passes = {"classifyBatch": {"median_time": t, "pass_type": "fold"}}
        self.assertTrue(prov.verified_result(aos))
        self.assertTrue(prov.verified_result(soa))
        self.assertTrue(prov.eligible_pair(aos, soa))
        spd, reason = prov.safe_speedup(aos, soa, gb.total_pass_time)
        self.assertIsNotNone(spd, reason)


if __name__ == "__main__":
    unittest.main(verbosity=2)
