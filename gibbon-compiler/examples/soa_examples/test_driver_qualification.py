#!/usr/bin/env python3
"""Adversarial regression tests for the benchmark driver's provenance and
correctness machinery.

Every case here corresponds to a weakness measured in the pre-fix driver.  The
tests mutate inputs and assert that the REAL production decision changes; none
of them re-implements driver logic.

No compiler is invoked: these are fast and run anywhere.  The end-to-end CLI
qualification is exercised separately by
`gibbon_benchmark.py --correctness-only DriverQualify`.

Run:  python3 test_driver_qualification.py
"""
import json
import os
import sys
import tempfile
import re
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import bench_provenance as prov
import gibbon_benchmark as gb

REPO_ROOT = Path("/workdisk/git/gibbon")


def _fp(source, argv, compiler, cc, root, driver=None):
    return prov.build_fingerprint(source, argv, compiler, cc, root, driver_path=driver)


class Scenario:
    """A complete built artifact set, so a test can mutate one input and ask the
    production freshness decision what it now thinks."""

    def __init__(self, tmp: Path, src_text="module M where\ngibbon_main = 1\n"):
        self.dir = tmp
        self.dir.mkdir(parents=True, exist_ok=True)
        self.src = self.dir / "M.hs"; self.src.write_text(src_text)
        self.exe = self.dir / "M.soa_mut.exe"; self.exe.write_text("ELF")
        self.c = self.dir / "M.soa_mut.c"; self.c.write_text("/* c */")
        self.bi = self.dir / "M.soa_mut.buildinfo.json"
        self.compiler = prov.CompilerResolution(self.dir / "gibbonA", "GIBBON_EXE", "hashA")
        self.cc = {"cc": "gcc", "path": "/usr/bin/gcc", "version": "gcc 16.2.0"}
        self.argv = ["/abs/gibbon", "--cc", "gcc", str(self.src)]
        self.install()

    def fingerprint(self, **over):
        return _fp(over.get("source", self.src),
                   over.get("argv", self.argv),
                   over.get("compiler", self.compiler),
                   over.get("cc", self.cc),
                   REPO_ROOT)

    def install(self):
        prov.write_buildinfo_atomic(self.bi, self.fingerprint(), self.c, self.exe, REPO_ROOT)

    def decide(self, **over):
        return prov.decide_recompile(self.bi, self.fingerprint(**over), self.c, self.exe)

    @staticmethod
    def rewrite_preserving_mtime(path: Path, text: str):
        """Change content while restoring the timestamp -- the case an
        mtime-based check cannot see."""
        st = path.stat()
        path.write_text(text)
        os.utime(path, (st.st_atime, st.st_mtime))


class TestFreshnessIsContentAddressed(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())

    def test_unchanged_inputs_reuse_artifacts(self):
        s = Scenario(self.tmp / "a")
        need, why = s.decide()
        self.assertFalse(need, "unchanged inputs must reuse; got %r" % why)

    def test_source_change_with_restored_mtime_forces_rebuild(self):
        s = Scenario(self.tmp / "b")
        Scenario.rewrite_preserving_mtime(s.src, "module M where\ngibbon_main = 999\n")
        need, why = s.decide()
        self.assertTrue(need, "a changed source must rebuild even with its mtime restored")
        self.assertIn("source contents changed", why)

    def test_imported_module_change_forces_rebuild(self):
        s = Scenario(self.tmp / "c", "module M where\nimport Helper\ngibbon_main = 1\n")
        helper = s.dir / "Helper.hs"; helper.write_text("module Helper where\nk = 1\n")
        s.install()
        Scenario.rewrite_preserving_mtime(helper, "module Helper where\nk = 2\n")
        need, why = s.decide()
        self.assertTrue(need)
        self.assertIn("imported module changed", why)

    def test_compiler_binary_change_forces_rebuild(self):
        s = Scenario(self.tmp / "d")
        other = prov.CompilerResolution(s.dir / "gibbonA", "GIBBON_EXE", "hashB")
        need, why = s.decide(compiler=other)
        self.assertTrue(need)
        self.assertIn("gibbon executable contents changed", why)

    def test_cc_version_change_forces_rebuild(self):
        s = Scenario(self.tmp / "e")
        need, why = s.decide(cc={"cc": "gcc", "path": "/usr/bin/gcc", "version": "gcc 17.0.0"})
        self.assertTrue(need)
        self.assertIn("C compiler", why)

    def test_flag_change_forces_rebuild(self):
        s = Scenario(self.tmp / "f")
        need, why = s.decide(argv=s.argv + ["--opt-vectorization"])
        self.assertTrue(need)
        self.assertIn("compile command changed", why)

    def test_tampered_generated_c_forces_rebuild(self):
        s = Scenario(self.tmp / "g")
        Scenario.rewrite_preserving_mtime(s.c, "/* TAMPERED */")
        need, why = s.decide()
        self.assertTrue(need)
        self.assertIn("c_file was modified", why)

    def test_tampered_executable_forces_rebuild(self):
        s = Scenario(self.tmp / "h")
        Scenario.rewrite_preserving_mtime(s.exe, "REPLACED")
        need, why = s.decide()
        self.assertTrue(need)
        self.assertIn("exe was modified", why)

    def test_malformed_metadata_forces_rebuild(self):
        s = Scenario(self.tmp / "i")
        s.bi.write_text("{ not json")
        need, why = s.decide()
        self.assertTrue(need)
        self.assertIn("unreadable", why)

    def test_metadata_from_a_different_source_forces_rebuild(self):
        s = Scenario(self.tmp / "j")
        other = s.dir / "Other.hs"; other.write_text("module Other where\ngibbon_main = 1\n")
        need, why = s.decide(source=other)
        self.assertTrue(need)
        self.assertIn("source path changed", why)

    def test_schema_bump_rejects_old_metadata(self):
        s = Scenario(self.tmp / "k")
        meta = json.loads(s.bi.read_text())
        meta["fingerprint"]["schema"] = prov.BUILD_INFO_SCHEMA - 1
        s.bi.write_text(json.dumps(meta))
        need, why = s.decide()
        self.assertTrue(need)
        self.assertIn("schema", why)

    def test_missing_metadata_forces_rebuild(self):
        s = Scenario(self.tmp / "l")
        s.bi.unlink()
        need, why = s.decide()
        self.assertTrue(need)

    def test_rts_sources_are_tracked_but_build_products_are_not(self):
        """The closure must include RTS sources (they change the executable) and
        exclude gibbon-rts/build (regenerated on every gibbon invocation, which
        would disable reuse entirely)."""
        names = {p.name for p in prov.rts_inputs(REPO_ROOT)}
        self.assertIn("gibbon_rts.c", names)
        self.assertIn("gibbon_rts.h", names)
        self.assertNotIn("gibbon_rts.o", names)
        self.assertNotIn("libgibbon_rts_ng.so", names)


class TestCompilerResolution(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())

    def test_gibbon_exe_wins_and_is_the_argv0(self):
        fake = self.tmp / "gibbonFAKE"; fake.write_text("#!/bin/sh\n"); fake.chmod(0o755)
        res = prov.resolve_gibbon_exe(REPO_ROOT, env={"GIBBON_EXE": str(fake), "PATH": "/usr/bin"})
        self.assertEqual(res.origin, "GIBBON_EXE")
        self.assertEqual(res.path, fake.resolve())
        cmd = gb.build_gibbon_command(Path("/x/S.hs"), "soa_mut", Path("/x/S.c"),
                                      Path("/x/S.exe"), "gcc", gibbon_exe=str(res.path))
        self.assertEqual(cmd[0], str(res.path),
                         "argv[0] must BE the resolved compiler, not the name 'gibbon'")

    def test_resolution_records_a_content_hash(self):
        fake = self.tmp / "g2"; fake.write_text("binary-ish"); fake.chmod(0o755)
        res = prov.resolve_gibbon_exe(REPO_ROOT, env={"GIBBON_EXE": str(fake)})
        self.assertEqual(res.sha256, prov.file_sha256(fake))

    def test_unresolvable_compiler_is_reported_not_guessed(self):
        res = prov.resolve_gibbon_exe(Path("/nonexistent"), env={"PATH": "/nonexistent"})
        self.assertEqual(res.origin, "unresolved")
        self.assertIsNone(res.path)


class TestSemanticNormalization(unittest.TestCase):
    """The pre-fix filter used an unanchored substring search, so any program
    line CONTAINING a protocol word was deleted in full."""

    def test_program_data_containing_protocol_words_is_kept(self):
        for probe in ("result SIZE: 3", "Running pass count = 7",
                      "total SELFTIMED: 9", "ITER TIMES: [0.0] trailing 5",
                      "End of report 5", "the ITERS: field is 4"):
            self.assertFalse(prov.is_protocol_line(probe), probe)
            self.assertEqual(prov.semantic_output(probe), probe)
            self.assertEqual(gb.clean_output(probe), probe)

    def test_real_protocol_records_are_dropped(self):
        for probe in ("SIZE: 1", "ITERS: 5", "SELFTIMED: 4.2e-07",
                      "BATCHTIME: 1.0", "ITER TIMES: [0.1, 0.2]", "ITER TIMES: []",
                      "End", "Running pass bump (map, uses=4): ",
                      "Running program X: ", "itertime: 0.5"):
            self.assertTrue(prov.is_protocol_line(probe), probe)
            self.assertIsNone(prov.semantic_output(probe), probe)

    def test_malformed_near_misses_are_kept(self):
        for probe in ("SELFTIMED:", "SELFTIMED: abc", "SIZE: 1 extra",
                      "ITER TIMES: [0.0", "XSIZE: 1"):
            self.assertFalse(prov.is_protocol_line(probe), probe)

    def test_value_beside_timing_is_preserved(self):
        self.assertEqual(prov.semantic_output("SELFTIMED: 1.0e-2\n43\n"), "43")

    def test_order_and_multiplicity_are_significant(self):
        e = prov.OracleEntry("p", "1 2 3", "hand-derived")
        self.assertEqual(e.check("1\n2\n3\n")[0], prov.ORACLE_PASS)
        for bad in ("1\n3\n2\n", "1\n2\n", "1\n2\n2\n3\n", "1\n2\n4\n"):
            self.assertEqual(e.check(bad)[0], prov.ORACLE_FAIL, bad)

    def test_empty_semantic_output_is_not_a_pass(self):
        e = prov.OracleEntry("p", "42", "hand-derived")
        self.assertEqual(e.check("SIZE: 1\nEnd\n")[0], prov.ORACLE_FAIL)


class TestOracleAndEligibility(unittest.TestCase):
    def _st(self, oracle, out="1712", allow=False, xvar=prov.XVAR_NA):
        st = prov.QualificationStatus("soa_mut", "P")
        st.compile_status = prov.COMPILE_OK
        st.exec_status = prov.EXEC_OK
        st.semantic_output = out
        st.oracle_status = oracle
        st.allow_unverified = allow
        st.cross_variant_status = xvar
        return st

    def test_equal_but_wrong_variants_do_not_pass(self):
        """The headline defect: AoS and SoA agreeing is not an oracle."""
        a = self._st(prov.ORACLE_FAIL, "43")
        b = self._st(prov.ORACLE_FAIL, "43")
        self.assertEqual(prov.cross_variant_check([a, b]), prov.XVAR_AGREE)
        self.assertFalse(a.verified)
        self.assertFalse(a.eligible_for_reporting)
        self.assertNotEqual(prov.campaign_exit_code([a, b]), 0)

    def test_missing_oracle_fails_unless_explicitly_allowed(self):
        st = self._st(prov.ORACLE_MISSING)
        self.assertFalse(st.eligible_for_reporting)
        self.assertNotEqual(prov.campaign_exit_code([st]), 0)
        st.allow_unverified = True
        self.assertEqual(st.label, "UNVERIFIED")
        self.assertFalse(st.verified, "an unverified result is never 'verified'")
        self.assertEqual(prov.campaign_exit_code([st]), 0)

    def test_failed_or_empty_variant_is_not_success(self):
        bad = self._st(prov.ORACLE_PASS); bad.exec_status = prov.EXEC_FAIL
        self.assertNotEqual(prov.campaign_exit_code([bad]), 0)
        empty = self._st(prov.ORACLE_PASS, out=None)
        self.assertFalse(empty.eligible_for_reporting)
        self.assertNotEqual(prov.campaign_exit_code([empty]), 0)

    def test_one_good_one_bad_variant_fails_the_campaign(self):
        good = self._st(prov.ORACLE_PASS)
        bad = self._st(prov.ORACLE_PASS); bad.compile_status = prov.COMPILE_FAIL
        self.assertNotEqual(prov.campaign_exit_code([good, bad]), 0)

    def test_cross_variant_disagreement_fails(self):
        a = self._st(prov.ORACLE_PASS, "1712", xvar=prov.XVAR_DISAGREE)
        self.assertNotEqual(prov.campaign_exit_code([a]), 0)

    def test_empty_selection_is_a_failure(self):
        self.assertNotEqual(prov.campaign_exit_code([]), 0)

    def test_oracle_provenance_is_mandatory_and_checked(self):
        with self.assertRaises(ValueError):
            prov.OracleEntry("p", "1", "copied-from-gibbon")
        for good in prov.ORACLE_PROVENANCES:
            prov.OracleEntry("p", "1", good)

    def test_shipped_manifest_is_loadable_and_declares_provenance(self):
        m = prov.OracleManifest.load_default(HERE)
        e = m.lookup("DriverQualify")
        self.assertIsNotNone(e, "the qualification fixture must have an oracle")
        self.assertIn(e.provenance, prov.ORACLE_PROVENANCES)
        self.assertEqual(e.expected.split(), ["DRIVER-QUALIFY", "1712"])


class TestAtomicOutputs(unittest.TestCase):
    def test_report_is_replaced_atomically_and_never_left_stale(self):
        tmp = Path(tempfile.mkdtemp()); target = tmp / "r.json"
        prov.atomic_write_text(target, "OLD")
        try:
            prov.atomic_write_text(target, None)  # type: ignore[arg-type]
        except Exception:
            pass
        self.assertEqual(target.read_text(), "OLD",
                         "a failed write must not truncate the previous report")
        self.assertEqual(list(tmp.glob("*.tmp")), [], "temp files must be cleaned up")
        prov.atomic_write_text(target, "NEW")
        self.assertEqual(target.read_text(), "NEW")

    def test_buildinfo_is_only_installed_for_a_successful_build(self):
        tmp = Path(tempfile.mkdtemp())
        bi = tmp / "b.json"
        self.assertFalse(bi.exists())
        exe = tmp / "e"; exe.write_text("x")
        prov.write_buildinfo_atomic(bi, {"schema": prov.BUILD_INFO_SCHEMA}, None, exe, REPO_ROOT)
        self.assertTrue(bi.exists())
        meta = json.loads(bi.read_text())
        self.assertEqual(meta["artifacts"]["exe"]["sha256"], prov.file_sha256(exe))


class TestNoWeakPathRemains(unittest.TestCase):
    def test_superseded_decision_helpers_are_gone(self):
        self.assertFalse(hasattr(gb, "needs_recompilation"),
                         "the mtime-based freshness decision must not remain callable")
        self.assertFalse(hasattr(gb, "_legacy_get_gibbon_exe"),
                         "a second compiler resolution must not remain callable")

    def test_command_construction_never_grows_a_width_flag(self):
        for flag in ("--int32", "--gibbon-int32", "--32-bit"):
            cmd = gb.build_gibbon_command(Path("/x/S.hs"), "soa_mut", Path("/x/S.c"),
                                          Path("/x/S.exe"), "gcc", gibbon_exe="/abs/gibbon")
            self.assertNotIn(flag, cmd)


class TestBannerProtocolConformance(unittest.TestCase):
    """Program banners and end-of-pass markers must be spelled the way the
    protocol filter recognises them, and no oracle value may carry protocol
    text.

    The failure this prevents: bench_provenance.is_protocol_line strips only
    whole lines matching `Running program ...:`, `Running pass ...:` and
    `End`. Three programs printed banners that missed by capitalisation or
    wording ("Running Program", "Running Data base Query Pass", "Running the
    Compiler IR Program"), and one printed "End: " instead of "End". Each
    survived into the semantic output, and each was compensated for by
    baking that protocol text INTO the committed oracle value -- so the
    oracle was silently comparing banner text alongside program data, and
    any file copying such a banner (as the 2026-09-06 PiecewiseFunctions
    split did) got 104 spurious WRONG verdicts."""

    def _sources(self):
        for layout in ("AOS", "SOA"):
            for path in sorted((HERE / "programs" / layout).glob("*.hs")):
                yield path

    def test_every_printed_banner_is_stripped_by_the_protocol_filter(self):
        offenders = []
        for path in self._sources():
            for lineno, line in enumerate(path.read_text().splitlines(), 1):
                m = re.search(r'quote "(Running[^"]*)"', line)
                if m and not prov.is_protocol_line(m.group(1)):
                    offenders.append("%s:%d %r" % (path.name, lineno, m.group(1)))
        self.assertEqual(offenders, [], "banner(s) the protocol filter will "
                         "leave in the semantic output:\n  " + "\n  ".join(offenders))

    def test_every_end_marker_is_stripped_by_the_protocol_filter(self):
        offenders = []
        for path in self._sources():
            for lineno, line in enumerate(path.read_text().splitlines(), 1):
                m = re.search(r'quote "(End[^"]*)"', line)
                if m and not prov.is_protocol_line(m.group(1)):
                    offenders.append("%s:%d %r" % (path.name, lineno, m.group(1)))
        self.assertEqual(offenders, [], "end-marker(s) the protocol filter "
                         "will leave in the semantic output:\n  " + "\n  ".join(offenders))

    def test_no_oracle_value_contains_protocol_text(self):
        manifest = json.loads((HERE / "oracles" / "manifest.json").read_text())
        offenders = []
        for name, spec in manifest["oracles"].items():
            expected = spec.get("expected")
            if expected is None:
                continue
            for line in expected.splitlines():
                if prov.is_protocol_line(line) or line.strip().startswith("Running"):
                    offenders.append("%s: %r" % (name, line))
        self.assertEqual(offenders, [], "oracle value(s) carrying protocol "
                         "text rather than program data alone:\n  "
                         + "\n  ".join(offenders))


if __name__ == "__main__":
    unittest.main(verbosity=2)
