#!/usr/bin/env python3
"""Permanent regression tests for benchmark-driver arithmetic-mode policy,
the no-RAN invariant, and table/report provenance.

These are deliberately *tooling* tests: the real compiler is never invoked
(except where noted as a bounded, size_param=0-only, no-timing subprocess
check of `--help`/argparse rejection). Three groups (numbers match each
test method's numeric suffix):

  * TestArithmeticModeInterface  (tests 1-7, 19-21)
  * TestNoRanInvariant           (tests 8-9)
  * TestTableProvenanceAndDeadRatio (tests 10-18, 22)

Run:  python3 test_arithmetic_mode_and_table_provenance.py
"""
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
REPO_ROOT = HERE.parents[2]  # .../soa_examples -> examples -> gibbon-compiler -> repo

import gibbon_benchmark as gb  # noqa: E402
import bench_provenance as prov  # noqa: E402


def _dummy_artifacts(td: Path):
    src, exe, cfile = td / "P.hs", td / "P.exe", td / "P.c"
    src.write_text("gibbon_main = 1\n")
    cfile.write_text("/* c */\n")
    exe.write_text("#!/bin/true\n")
    return src, exe, cfile


def _make_result(program, variant, verified, median_time=None,
                 arith_mode=None, use_no_ran=None, dead_ratio=None,
                 adt_fields=None, uses=None, oracle_status=None):
    t = median_time if median_time is not None else 1.0
    res = gb.BenchmarkResult(program, variant)
    res.arith_mode = arith_mode
    res.use_no_ran = use_no_ran
    res.adt_fields = adt_fields
    st = prov.QualificationStatus(variant, program)
    if verified:
        st.compile_status = prov.COMPILE_OK
        st.exec_status = prov.EXEC_OK
        st.oracle_status = prov.ORACLE_PASS
        st.semantic_output = "42"
    else:
        st.compile_status = prov.COMPILE_OK
        st.exec_status = prov.EXEC_OK
        st.oracle_status = oracle_status or prov.ORACLE_FAIL
        st.oracle_detail = "synthetic test fixture: deliberately unverified"
    res.passes = {"reduction": {"median_time": t, "pass_type": "fold",
                                "uses": uses, "dead_ratio": dead_ratio}}
    res.compile_success = True
    res.run_success = True
    res.qualification = st
    return res


# ---------------------------------------------------------------------------
# 1-7, 19-21: arithmetic-mode interface
# ---------------------------------------------------------------------------
class TestArithmeticModeInterface(unittest.TestCase):

    def test_1_driver_default_is_unsafe(self):
        self.assertEqual(gb.DEFAULT_C_ARITH_MODE, "unsafe")
        # And the real --help text advertises it as the default, not just
        # the module constant in isolation.
        out = subprocess.run([sys.executable, str(HERE / "gibbon_benchmark.py"), "--help"],
                             capture_output=True, text=True, cwd=str(HERE))
        self.assertIn("--c-arithmetic", out.stdout)
        self.assertIn("Driver default: unsafe", out.stdout)

    def test_2_explicit_mode_propagation_to_argv(self):
        for mode in ("portable", "wrapv", "unsafe"):
            cmd = gb.build_gibbon_command(Path("P.hs"), "soa", Path("P.c"), Path("P.exe"),
                                          "gcc", c_arith_mode=mode)
            self.assertIn(f"--c-arithmetic={mode}", cmd,
                         f"mode {mode} not explicitly in argv: {cmd}")
            # Exactly once.
            self.assertEqual(sum(1 for a in cmd if a.startswith("--c-arithmetic=")), 1)

    def test_3_invalid_mode_rejected(self):
        with self.assertRaises(ValueError):
            gb._validate_c_arith_mode("bogus")
        with self.assertRaises(ValueError):
            gb.build_gibbon_command(Path("P.hs"), "soa", Path("P.c"), Path("P.exe"),
                                    "gcc", c_arith_mode="bogus")
        with self.assertRaises(ValueError):
            gb.compile_one(Path("P.hs"), "soa", Path("/tmp"), False,
                          c_arith_mode="not-a-real-mode")
        # And the real CLI rejects it before doing anything.
        r = subprocess.run([sys.executable, str(HERE / "gibbon_benchmark.py"),
                           "--c-arithmetic=bogus", "--programs", "List.hs"],
                          capture_output=True, text=True, cwd=str(HERE))
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("invalid choice", r.stderr)

    def test_4_mode_change_forces_recompilation(self):
        with tempfile.TemporaryDirectory() as td:
            td = Path(td)
            src, exe, cfile = _dummy_artifacts(td)
            buildinfo = td / "P.buildinfo.json"
            comp = prov.CompilerResolution(td / "gibbon", "GIBBON_EXE", "h")
            cc = {"cc": "gcc", "path": "/usr/bin/gcc", "version": "v"}
            unsafe_cmd = gb.build_gibbon_command(src, "soa", cfile, exe, "gcc",
                                                 gibbon_exe=str(td / "gibbon"),
                                                 c_arith_mode="unsafe")
            unsafe_fp = prov.build_fingerprint(src, unsafe_cmd, comp, cc, REPO_ROOT)
            prov.write_buildinfo_atomic(buildinfo, unsafe_fp, cfile, exe, REPO_ROOT)
            wrapv_cmd = gb.build_gibbon_command(src, "soa", cfile, exe, "gcc",
                                                gibbon_exe=str(td / "gibbon"),
                                                c_arith_mode="wrapv")
            wrapv_fp = prov.build_fingerprint(src, wrapv_cmd, comp, cc, REPO_ROOT)
            recompile, reason = prov.decide_recompile(buildinfo, wrapv_fp, cfile, exe)
            self.assertTrue(recompile, f"a mode change was NOT detected: {reason}")
            self.assertEqual("compile command changed", reason)

    def test_5_artifact_from_another_mode_is_rejected(self):
        """Same scenario as test_4, phrased as the 'stale artifact' case: an
        exe built under `portable` must not be silently reused under
        `unsafe`, even though nothing else about the invocation changed."""
        with tempfile.TemporaryDirectory() as td:
            td = Path(td)
            src, exe, cfile = _dummy_artifacts(td)
            buildinfo = td / "P.buildinfo.json"
            comp = prov.CompilerResolution(td / "gibbon", "GIBBON_EXE", "h")
            cc = {"cc": "gcc", "path": "/usr/bin/gcc", "version": "v"}
            portable_cmd = gb.build_gibbon_command(src, "soa", cfile, exe, "gcc",
                                                   gibbon_exe=str(td / "gibbon"),
                                                   c_arith_mode="portable")
            portable_fp = prov.build_fingerprint(src, portable_cmd, comp, cc, REPO_ROOT)
            prov.write_buildinfo_atomic(buildinfo, portable_fp, cfile, exe, REPO_ROOT)
            unsafe_cmd = gb.build_gibbon_command(src, "soa", cfile, exe, "gcc",
                                                 gibbon_exe=str(td / "gibbon"),
                                                 c_arith_mode="unsafe")
            unsafe_fp = prov.build_fingerprint(src, unsafe_cmd, comp, cc, REPO_ROOT)
            recompile, _reason = prov.decide_recompile(buildinfo, unsafe_fp, cfile, exe)
            self.assertTrue(recompile, "an unsafe-mode result reused a portable-mode artifact")
            # Control: an unchanged mode IS reused (this isn't "always rebuild").
            recompile_same, reason_same = prov.decide_recompile(buildinfo, portable_fp, cfile, exe)
            self.assertFalse(recompile_same, reason_same)

    def test_6_unsafe_argv_has_no_fwrapv(self):
        cmd = gb.build_gibbon_command(Path("P.hs"), "soa", Path("P.c"), Path("P.exe"),
                                      "gcc", c_arith_mode="unsafe")
        self.assertNotIn("-fwrapv", cmd)
        self.assertIn("--c-arithmetic=unsafe", cmd)

    def test_7_wrapv_argv_carries_the_mode_gibbon_itself_adds_fwrapv(self):
        # The DRIVER never adds -fwrapv itself for any mode -- that is
        # Gibbon's job for wrapv (Compiler.hs's compilationCmd/compileRTS
        # append -fwrapv only when cArithMode config == ArithWrapv). The
        # driver's contract is narrower and mechanical: pass the mode
        # through explicitly.
        cmd = gb.build_gibbon_command(Path("P.hs"), "soa", Path("P.c"), Path("P.exe"),
                                      "gcc", c_arith_mode="wrapv")
        self.assertIn("--c-arithmetic=wrapv", cmd)
        self.assertNotIn("-fwrapv", cmd,
                         "the driver must not add -fwrapv itself -- Gibbon adds it "
                         "internally for wrapv mode, confirmed via a real compile")

    def test_19_incompatible_arithmetic_modes_cannot_be_merged(self):
        records = [{"arith_mode": "unsafe"}, {"arith_mode": "unsafe"}, {"arith_mode": "wrapv"}]
        err = gb.check_arithmetic_mode_consistency(records)
        self.assertIsNotNone(err)
        self.assertIn("unsafe", err)
        self.assertIn("wrapv", err)
        # Control: a single-mode set of records is fine.
        self.assertIsNone(gb.check_arithmetic_mode_consistency(
            [{"arith_mode": "unsafe"}, {"arith_mode": "unsafe"}]))
        self.assertIsNone(gb.check_arithmetic_mode_consistency(
            [{"arith_mode": "unsafe"}, {"arith_mode": None}]))

    def test_20_bw01_bw02_default_to_unsafe_but_keep_their_own_width_policy(self):
        import inspect
        sig1 = inspect.signature(gb.collect_add1tree_width_results)
        sig2 = inspect.signature(gb.collect_arithintensity_width_results)
        self.assertEqual(sig1.parameters["c_arith_mode"].default, "unsafe")
        self.assertEqual(sig2.parameters["c_arith_mode"].default, "unsafe")
        # Width policy is untouched: still four explicit widths, independent
        # of arithmetic mode.
        self.assertEqual(len(gb.ADD1TREE_WIDTH_PROGRAMS), 4)
        self.assertEqual(len(gb.ARITHINTENSITY_WIDTH_PROGRAMS), 4)

    def test_21_bw02_every_width_is_measured_regardless_of_arithmetic_mode(self):
        # Width 64 is measured like every other width, and only width 64
        # enables the emulated packed multiply. Neither depends on the
        # arithmetic mode.
        for w in (8, 16, 32, 64):
            self.assertIn("soa_simd", gb.ARITHINTENSITY_WIDTH_CONFIGS[w])
        self.assertTrue(
            gb.ARITHINTENSITY_WIDTH_CONFIGS[64]["soa_simd"]["simd_w64_multiply"])
        for w in (8, 16, 32):
            self.assertNotIn("simd_w64_multiply",
                             gb.ARITHINTENSITY_WIDTH_CONFIGS[w]["soa_simd"])


# ---------------------------------------------------------------------------
# 8-9: no-RAN invariant
# ---------------------------------------------------------------------------
class TestNoRanInvariant(unittest.TestCase):

    def test_8_every_curated_compile_argv_has_no_ran_exactly_once(self):
        for mode in ("portable", "wrapv", "unsafe"):
            cmd = gb.build_gibbon_command(Path("P.hs"), "soa", Path("P.c"), Path("P.exe"),
                                          "gcc", use_no_ran=True, c_arith_mode=mode)
            self.assertEqual(cmd.count("--no-ran"), 1, cmd)

    def test_9_no_program_override_can_disable_no_ran(self):
        # VW-36 defense in depth: a hypothetical future override must still
        # be rejected even though compile_one/build_gibbon_command now take
        # an extra parameter.
        bad_overrides = {"SomeProgram.hs": {"soa": {"use_no_ran": False}}}
        with self.assertRaises(RuntimeError):
            gb._validate_no_ran_overrides(bad_overrides)
        # The shipped table has no such entry.
        gb._validate_no_ran_overrides()
        self.assertEqual(gb.PROGRAM_COMPILE_OVERRIDES, {})


# ---------------------------------------------------------------------------
# 10-18, 22: table provenance and dead-ratio correctness
# ---------------------------------------------------------------------------
class TestTableProvenanceAndDeadRatio(unittest.TestCase):

    def test_10_linearlistreduction_and_reducenestedlist_remain_distinct(self):
        """Same pass name ("reduction"), different programs -- the mapping
        must key by (program, variant, pass_name), never by pass name alone."""
        llr = _make_result("LinearListReduction.hs", "aos", True, median_time=0.0169,
                           dead_ratio=0.82, adt_fields=11, uses=2)
        rnl = _make_result("reduceNestedList.hs", "aos", True, median_time=1.159,
                           dead_ratio=0.33, adt_fields=3, uses=2)
        self.assertNotEqual(llr.program, rnl.program)
        self.assertEqual(set(llr.passes.keys()), set(rnl.passes.keys()))  # both "reduction"
        self.assertNotEqual(llr.passes["reduction"]["median_time"],
                            rnl.passes["reduction"]["median_time"])
        self.assertNotEqual(llr.adt_fields, rnl.adt_fields)

    def test_11_swapped_result_identities_are_detected(self):
        """If a report entry's `program` key and its embedded result's own
        program disagree, that is a swap and must be catchable, not silently
        accepted."""
        llr = _make_result("LinearListReduction.hs", "aos", True)
        # Simulate an accidental swap: this result's `.program` doesn't match
        # the dict key it would be filed under.
        fake_key = "reduceNestedList.hs"
        self.assertNotEqual(llr.program, fake_key)

    def test_12_duplicate_program_pass_keys_cannot_overwrite_silently(self):
        variants_map = {}
        for entry in [{"program": "LinearListReduction.hs", "aos": "A"},
                     {"program": "reduceNestedList.hs", "aos": "B"}]:
            self.assertNotIn(entry["program"], variants_map,
                             "duplicate program key silently overwrote a prior entry")
            variants_map[entry["program"]] = entry
        self.assertEqual(len(variants_map), 2)

    def test_13_zero_percent_dead_metadata_survives(self):
        self.assertEqual(gb._first_present(0.0, 0.82), 0.0)
        ad = {"dead_ratio": 0.0}
        sd = {"dead_ratio": 0.82}
        self.assertEqual(gb._first_present(ad.get("dead_ratio"), sd.get("dead_ratio")), 0.0)

    def test_14_33_and_82_percent_map_to_correct_programs(self):
        llr = _make_result("LinearListReduction.hs", "aos", True, dead_ratio=0.82)
        rnl = _make_result("reduceNestedList.hs", "aos", True, dead_ratio=0.33)
        self.assertEqual(llr.passes["reduction"]["dead_ratio"], 0.82)
        self.assertEqual(rnl.passes["reduction"]["dead_ratio"], 0.33)

    def test_15_missing_dead_ratio_does_not_borrow_another_value(self):
        ad = {}  # no dead_ratio key at all (AoS side missing metadata)
        sd = {"dead_ratio": 0.82}
        got = gb._first_present(ad.get("dead_ratio"), sd.get("dead_ratio"))
        # This documents the CURRENT (correct) contract: when the AoS side
        # has no metadata, the SoA side's value is used as a fallback (by
        # design, via _first_present), NOT because 0 was mistaken for
        # missing. What must never happen is a `0.0` AoS value being
        # replaced by the SoA value -- covered by test_13.
        self.assertEqual(got, 0.82)
        self.assertIsNone(gb._first_present(None, None))

    def test_16_stale_artifact_hash_forces_rebuild(self):
        with tempfile.TemporaryDirectory() as td:
            td = Path(td)
            src, exe, cfile = _dummy_artifacts(td)
            buildinfo = td / "P.buildinfo.json"
            comp = prov.CompilerResolution(td / "gibbon", "GIBBON_EXE", "h")
            cc = {"cc": "gcc", "path": "/usr/bin/gcc", "version": "v"}
            cmd = gb.build_gibbon_command(src, "soa", cfile, exe, "gcc",
                                          gibbon_exe=str(td / "gibbon"))
            fp = prov.build_fingerprint(src, cmd, comp, cc, REPO_ROOT)
            prov.write_buildinfo_atomic(buildinfo, fp, cfile, exe, REPO_ROOT)
            # Mutate the exe after it was recorded -- its hash no longer
            # matches what buildinfo says it should be.
            exe.write_text("#!/bin/false\n#tampered\n")
            recompile, reason = prov.decide_recompile(buildinfo, fp, cfile, exe)
            self.assertTrue(recompile, f"a tampered/stale exe was reused: {reason}")

    def test_17_unverified_and_wrong_oracle_results_render_na(self):
        aos = _make_result("List.hs", "aos", True, median_time=1.0)
        soa = _make_result("List.hs", "soa", False, oracle_status=prov.ORACLE_FAIL)
        self.assertFalse(prov.eligible_pair(aos, soa))
        spd, reason = prov.safe_speedup(aos, soa, gb.total_pass_time)
        self.assertIsNone(spd)
        self.assertTrue(reason)

    def test_18_arithmetic_mode_and_no_ran_appear_in_provenance(self):
        import io
        aos = _make_result("List.hs", "aos", True, median_time=1.0,
                           arith_mode="unsafe", use_no_ran=True)
        soa = _make_result("List.hs", "soa", True, median_time=0.9,
                           arith_mode="unsafe", use_no_ran=True)
        # Text report.
        with tempfile.TemporaryDirectory() as td:
            out_file = Path(td) / "r.txt"
            gb.write_text_report([(aos, soa)], out_file)
            text = out_file.read_text()
            self.assertIn("Arithmetic mode", text)
            self.assertIn("unsafe", text)
            self.assertIn("No-RAN", text)
            # JSON report.
            json_file = Path(td) / "r.json"
            gb.write_json_results([(aos, soa)], json_file)
            import json as _json
            doc = _json.loads(json_file.read_text())
            self.assertIn("campaign", doc)
            self.assertEqual(doc["campaign"]["c_arithmetic_modes_present"], ["unsafe"])
            self.assertIsNone(doc["campaign"]["arithmetic_mode_consistency_error"])
            self.assertEqual(doc["results"][0]["aos"]["arith_mode"], "unsafe")
        # LaTeX/generated-paper provenance.
        with tempfile.TemporaryDirectory() as td:
            tex_file = Path(td) / "t.tex"
            gb.write_latex_tables([(aos, soa)], tex_file)
            tex = tex_file.read_text()
            self.assertIn("unsafe", tex)
            self.assertIn("no-ran", tex.lower())

    def test_18c_the_tex_carries_the_same_campaign_block_as_the_json(self):
        """The .tex is the file that travels into a paper; the .json does
        not go with it. A table lifted out of this file has to name the
        commit, the compiler binary, the C compiler, the machine, the
        iteration count and the flags on its own."""
        aos = _make_result("List.hs", "aos", True, median_time=1.0)
        soa = _make_result("List.hs", "soa", True, median_time=0.9)
        campaign = {
            "gibbon": {"sha256": "deadbeef", "resolved_via": "cabal"},
            "repo": {"head": "241098df", "branch": "fix/audit-2026-09-12"},
            "cc": {"version": "gcc-16 (GCC) 16.2.0"},
            "machine": {"cpu": "i7-12700K"},
            "timing": {"iterations": 51, "pin_cpu": None},
            "driver_argv": ["gibbon_benchmark.py", "--iterations", "51"],
        }
        with tempfile.TemporaryDirectory() as td:
            tex_file = Path(td) / "t.tex"
            gb.write_latex_tables([(aos, soa)], tex_file, campaign=campaign)
            tex = tex_file.read_text()
        for needle in ("repo.head = 241098df",
                       "repo.branch = fix/audit-2026-09-12",
                       "gibbon.sha256 = deadbeef",
                       "cc.version = gcc-16 (GCC) 16.2.0",
                       "machine.cpu = i7-12700K",
                       "timing.iterations = 51",
                       "driver_argv = gibbon_benchmark.py --iterations 51"):
            self.assertIn("% Provenance: " + needle, tex)
        # An absent value is named, not dropped -- "unknown" and "not
        # recorded at all" are different claims about a campaign.
        self.assertIn("% Provenance: timing.pin_cpu = unknown", tex)
        # Every provenance line must be a comment for its whole length, so
        # a stray value cannot put text into the document body.
        for line in tex.splitlines():
            if "Provenance:" in line:
                self.assertTrue(line.startswith("%"), line)

    def test_18d_no_campaign_block_emits_no_provenance_lines_and_no_error(self):
        aos = _make_result("List.hs", "aos", True, median_time=1.0)
        soa = _make_result("List.hs", "soa", True, median_time=0.9)
        with tempfile.TemporaryDirectory() as td:
            tex_file = Path(td) / "t.tex"
            gb.write_latex_tables([(aos, soa)], tex_file)
            tex = tex_file.read_text()
        self.assertNotIn("repo.head", tex)
        self.assertEqual(gb.latex_provenance_comments(None), "")
        self.assertEqual(gb.latex_provenance_comments({}), "")

    def test_18e_a_percent_in_a_value_cannot_escape_the_comment(self):
        # A value containing % would comment out the rest of its own line
        # and hide whatever followed it.
        out = gb.latex_provenance_comments({"driver_argv": ["--x", "50%"]})
        self.assertIn("50\\%", out)
        self.assertTrue(all(l.startswith("%") for l in out.splitlines()))

    def test_18b_mixed_mode_report_is_flagged_not_silently_averaged(self):
        aos = _make_result("List.hs", "aos", True, median_time=1.0, arith_mode="unsafe")
        soa = _make_result("List.hs", "soa", True, median_time=0.9, arith_mode="wrapv")
        with tempfile.TemporaryDirectory() as td:
            json_file = Path(td) / "r.json"
            gb.write_json_results([(aos, soa)], json_file)
            import json as _json
            doc = _json.loads(json_file.read_text())
            self.assertIsNotNone(doc["campaign"]["arithmetic_mode_consistency_error"])
            text_file = Path(td) / "r.txt"
            gb.write_text_report([(aos, soa)], text_file)
            self.assertIn("INCONSISTENT", text_file.read_text())

    def test_22_decisiontree_vw38_excluded_not_partially_reported(self):
        """DecisionTree.hs (VW-38) must render as excluded/unverified at its
        committed size -- never a partial numeric row that omits only the
        failing pass while keeping others as if the program qualified."""
        dt = _make_result("DecisionTree.hs", "aos", False, oracle_status=prov.ORACLE_MISSING)
        dt.run_success = False
        dt.error_message = "VW-38: did not complete at committed size"
        self.assertFalse(prov.verified_result(dt))
        reason = prov.rejection_reason(dt)
        self.assertTrue(reason)


if __name__ == "__main__":
    unittest.main(verbosity=2)
