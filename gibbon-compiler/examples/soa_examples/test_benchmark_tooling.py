#!/usr/bin/env python3
"""Focused tests for the SoA benchmark tooling after the removal of the
whole-program `--int32` width mode.

These are deliberately *tooling* tests: they run no compiler and launch no
benchmark.  They pin the properties that make the driver trustworthy again:

  * integer width is a source property, so no code path may reconstruct a
    whole-program width flag;
  * the old spellings fail loudly and early, rather than being silently ignored;
  * an executable built by the old mode cannot be reused, because its recorded
    command signature no longer matches.

Run:  python3 test_benchmark_tooling.py
"""
import json
import py_compile
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
REPO_ROOT = HERE.parents[2]  # .../soa_examples -> examples -> gibbon-compiler -> repo

ACTIVE_SCRIPTS = [
    "gibbon_benchmark.py",
    "benchmark_layout_versions.py",
    "check_intensity_codegen.py",
]

# Every spelling of the removed whole-program width mode.
REMOVED_FLAGS = ["--int32", "--gibbon-int32", "--32-bit"]


def run_script(name, *args):
    return subprocess.run([sys.executable, str(HERE / name), *args],
                          capture_output=True, text=True, cwd=str(HERE))


class TestScriptsAreWellFormed(unittest.TestCase):
    def test_all_active_scripts_compile(self):
        for name in ACTIVE_SCRIPTS + ["test_benchmark_tooling.py"]:
            with self.subTest(script=name):
                py_compile.compile(str(HERE / name), doraise=True)

    def test_driver_imports(self):
        import gibbon_benchmark  # noqa: F401

    def test_no_module_level_use_int32_state(self):
        import gibbon_benchmark as gb
        leaked = [n for n in dir(gb) if "int32" in n.lower()]
        self.assertEqual([], leaked, f"module still exposes width state: {leaked}")


class TestCommandConstruction(unittest.TestCase):
    """The pure seam: build a command without touching the filesystem."""

    def build(self, variant="soa", **kw):
        import gibbon_benchmark as gb
        return gb.build_gibbon_command(
            Path("/src/SOA/P.hs"), variant,
            Path("/out/P.c"), Path("/out/P.exe"), "gcc", **kw)

    def test_no_removed_width_flag_is_ever_emitted(self):
        # Sweep every boolean knob in both positions; none may resurrect a
        # whole-program width flag.
        import itertools
        keys = ["use_mutable_cursors", "enable_papi", "enable_papi_native",
                "store_scalar_field_counts", "enable_loopification",
                "enable_loop_fusion", "enable_selective_buffer_sharing",
                "enable_vectorization", "use_sse41", "use_no_gcc_vec",
                "use_no_ran"]
        for variant in ("aos", "soa", "aos_imm", "soa_imm"):
            for bits in itertools.product((False, True), repeat=len(keys)):
                cmd = self.build(variant, **dict(zip(keys, bits)))
                for bad in REMOVED_FLAGS:
                    self.assertNotIn(bad, cmd)

    def test_build_command_takes_no_width_argument(self):
        import inspect, gibbon_benchmark as gb
        params = inspect.signature(gb.build_gibbon_command).parameters
        self.assertFalse([p for p in params if "int32" in p or "width" in p],
                         "command construction must not accept a width knob")

    def test_aos_does_not_receive_soa_only_flags(self):
        cmd = self.build("aos", store_scalar_field_counts=True,
                         enable_selective_buffer_sharing=True,
                         enable_vectorization=True)
        for soa_only in ("--store-scalar-field-counts",
                         "--opt-selective-buffer-sharing",
                         "--opt-vectorization"):
            self.assertNotIn(soa_only, cmd)

    def test_soa_receives_requested_optimization_flags(self):
        cmd = self.build("soa", store_scalar_field_counts=True,
                         enable_loopification=True,
                         enable_selective_buffer_sharing=True,
                         enable_vectorization=True)
        for expected in ("--store-scalar-field-counts", "--opt-loopification",
                         "--auto-loopification",
                         "--opt-selective-buffer-sharing",
                         "--opt-vectorization"):
            self.assertIn(expected, cmd)

    def test_sse41_and_no_gcc_vectorize_are_independent_of_gibbon_simd(self):
        only_sse = self.build("soa", use_sse41=True)
        self.assertIn("--sse4.1", only_sse)
        self.assertNotIn("--opt-vectorization", only_sse)

        only_novec = self.build("soa", use_no_gcc_vec=True)
        self.assertIn("--no-gcc-vectorize", only_novec)
        self.assertNotIn("--opt-vectorization", only_novec)

        only_gibbon = self.build("soa", enable_vectorization=True)
        self.assertIn("--opt-vectorization", only_gibbon)
        self.assertNotIn("--sse4.1", only_gibbon)
        self.assertNotIn("--no-gcc-vectorize", only_gibbon)

    def test_no_gcc_tail_calls_flag(self):
        with_it = self.build("soa", use_no_gcc_tail_calls=True)
        self.assertIn("--no-gcc-tail-calls", with_it)
        without_it = self.build("soa")
        self.assertNotIn("--no-gcc-tail-calls", without_it)

    def test_auto_loopification_defaults_to_paired_with_opt_loopification(self):
        # Every existing caller that doesn't know about auto_loopification
        # must keep getting today's paired behavior unchanged.
        cmd = self.build("soa", enable_loopification=True)
        self.assertIn("--opt-loopification", cmd)
        self.assertIn("--auto-loopification", cmd)

    def test_auto_loopification_false_omits_auto_loopification_flag(self):
        # The --pldi-submission variant matrix relies on this: every curated
        # map function it times already carries an explicit OPT:MayVectorize
        # annotation, so structural inference is unnecessary and must not be
        # silently re-added.
        cmd = self.build("soa", enable_loopification=True, auto_loopification=False)
        self.assertIn("--opt-loopification", cmd)
        self.assertNotIn("--auto-loopification", cmd)

    def test_auto_loopification_false_is_a_no_op_without_loopification(self):
        cmd = self.build("soa", auto_loopification=False)
        self.assertNotIn("--opt-loopification", cmd)
        self.assertNotIn("--auto-loopification", cmd)

    def test_paths_are_placed_correctly(self):
        cmd = self.build("soa")
        self.assertEqual("/src/SOA/P.hs", cmd[-1])
        self.assertEqual("/out/P.c", cmd[cmd.index("--cfile") + 1])
        self.assertEqual("/out/P.exe", cmd[cmd.index("--exefile") + 1])

    def test_signature_changes_when_configuration_changes(self):
        a = " ".join(self.build("soa"))
        b = " ".join(self.build("soa", enable_vectorization=True))
        self.assertNotEqual(a, b)


class TestRemovedCliSpellings(unittest.TestCase):
    def test_gibbon_benchmark_rejects_old_spellings(self):
        for flag in ("--int32", "--gibbon-int32"):
            with self.subTest(flag=flag):
                r = run_script("gibbon_benchmark.py", flag)
                self.assertEqual(2, r.returncode)
                self.assertIn("has been removed", r.stderr)
                self.assertIn("Int32", r.stderr)
                # Nothing may be printed or built before the rejection.
                self.assertEqual("", r.stdout.strip())

    def test_layout_driver_rejects_old_spellings(self):
        for flag in ("--32-bit", "--int32"):
            with self.subTest(flag=flag):
                r = run_script("benchmark_layout_versions.py", flag)
                self.assertEqual(2, r.returncode)
                self.assertIn("has been removed", r.stderr)
                self.assertEqual("", r.stdout.strip())

    def test_intensity_checker_rejects_the_int32_path(self):
        r = run_script("check_intensity_codegen.py", "--int32")
        self.assertEqual(2, r.returncode)
        self.assertIn("has been removed", r.stderr)
        self.assertEqual("", r.stdout.strip())

    def test_help_advertises_no_active_width_option(self):
        for name in ACTIVE_SCRIPTS:
            with self.subTest(script=name):
                out = run_script(name, "--help").stdout
                # The option list must not offer one.  Prose explaining that the
                # mode was removed is expected and allowed.
                offered = [ln for ln in out.splitlines()
                           if ln.lstrip().startswith("--")
                           and any(f in ln for f in REMOVED_FLAGS)]
                self.assertEqual([], offered, f"{name} still offers {offered}")


class TestStaleArtifactInvalidation(unittest.TestCase):
    def test_old_int32_signature_forces_recompilation(self):
        """An exe built by the removed mode must not be reused.

        The cache compares the recorded compile-command signature, and the
        migrated driver no longer emits `--int32`, so the signatures differ.
        """
        import gibbon_benchmark as gb
        import bench_provenance as prov
        with tempfile.TemporaryDirectory() as td:
            td = Path(td)
            src, exe, cfile = td / "P.hs", td / "P.exe", td / "P.c"
            src.write_text("gibbon_main = 1\n")
            cfile.write_text("/* c */\n")
            exe.write_text("#!/bin/true\n")
            buildinfo = td / "P.buildinfo.json"
            comp = prov.CompilerResolution(td / "gibbon", "GIBBON_EXE", "h")
            cc = {"cc": "gcc", "path": "/usr/bin/gcc", "version": "v"}
            now_cmd = gb.build_gibbon_command(src, "soa", cfile, exe, "gcc",
                                              gibbon_exe=str(td / "gibbon"))
            old_cmd = now_cmd[:1] + ["--int32"] + now_cmd[1:]
            # Metadata as if built by the removed width mode.
            old_fp = prov.build_fingerprint(src, old_cmd, comp, cc, REPO_ROOT)
            prov.write_buildinfo_atomic(buildinfo, old_fp, cfile, exe, REPO_ROOT)
            new_fp = prov.build_fingerprint(src, now_cmd, comp, cc, REPO_ROOT)
            recompile, reason = prov.decide_recompile(buildinfo, new_fp, cfile, exe)
            self.assertTrue(recompile, f"stale --int32 artifact was reused: {reason}")
            self.assertEqual("compile command changed", reason)

    def test_matching_signature_is_reused(self):
        """Control: without a configuration change the artifact IS reused, so
        the test above is detecting the change and not just always rebuilding."""
        import gibbon_benchmark as gb
        import bench_provenance as prov
        with tempfile.TemporaryDirectory() as td:
            td = Path(td)
            src, exe, cfile = td / "P.hs", td / "P.exe", td / "P.c"
            src.write_text("gibbon_main = 1\n")
            cfile.write_text("/* c */\n")
            exe.write_text("#!/bin/true\n")
            buildinfo = td / "P.buildinfo.json"
            comp = prov.CompilerResolution(td / "gibbon", "GIBBON_EXE", "h")
            cc = {"cc": "gcc", "path": "/usr/bin/gcc", "version": "v"}
            cmd = gb.build_gibbon_command(src, "soa", cfile, exe, "gcc",
                                          gibbon_exe=str(td / "gibbon"))
            fp = prov.build_fingerprint(src, cmd, comp, cc, REPO_ROOT)
            prov.write_buildinfo_atomic(buildinfo, fp, cfile, exe, REPO_ROOT)
            recompile, reason = prov.decide_recompile(buildinfo, fp, cfile, exe)
            self.assertFalse(recompile, reason)


class TestSmokeFixtureIsExplicitWidth(unittest.TestCase):
    def test_paired_fixture_exists_with_matching_names(self):
        for layout in ("AOS", "SOA"):
            self.assertTrue((HERE / "programs" / layout / "MixedWidthSmoke.hs").exists())

    def test_fixture_declares_all_four_widths(self):
        for layout in ("AOS", "SOA"):
            text = (HERE / "programs" / layout / "MixedWidthSmoke.hs").read_text()
            for w in ("Int8", "Int16", "Int32", "Int64"):
                self.assertIn(w, text, f"{layout} fixture must declare {w}")

    def test_fixture_layout_annotations_are_canonical(self):
        aos = (HERE / "programs" / "AOS" / "MixedWidthSmoke.hs").read_text()
        soa = (HERE / "programs" / "SOA" / "MixedWidthSmoke.hs").read_text()
        self.assertIn('{-# ANN type Rec "Linear" #-}', aos)
        self.assertIn('{-# ANN type Rec "Factored" #-}', soa)

    def test_width_profile_is_read_from_source_not_filename(self):
        import check_intensity_codegen as c
        prof = c.declared_width_profile(HERE / "programs" / "SOA" / "MixedWidthSmoke.hs")
        self.assertIn("mixed", prof)
        # A bare-Int program must not be described as explicit-width.
        prof2 = c.declared_width_profile(HERE / "programs" / "SOA" / "MapIntensityV2.hs")
        self.assertEqual("bare Int / Int64 default", prof2)


class TestProgramSelection(unittest.TestCase):
    """--programs picks the candidate set, --exclude-programs subtracts from
    it (see resolve_program_selection). The exclusion path is what lets a
    full evaluation skip one broken/slow benchmark without retyping the
    other 21 names, so a typo there must fail fast rather than silently
    leave the unwanted benchmark in a multi-hour run."""

    def test_no_flags_runs_the_default_list(self):
        import gibbon_benchmark as gb
        self.assertEqual(gb.resolve_program_selection(None, None),
                         gb.DEFAULT_PROGRAMS)
        self.assertEqual(gb.resolve_program_selection(None, []),
                         gb.DEFAULT_PROGRAMS)

    def test_exclusion_subtracts_from_the_default_list(self):
        import gibbon_benchmark as gb
        kept = gb.resolve_program_selection(None, ["Trie.hs", "List.hs"])
        self.assertNotIn("Trie.hs", kept)
        self.assertNotIn("List.hs", kept)
        self.assertEqual(len(kept), len(gb.DEFAULT_PROGRAMS) - 2)
        # Order of the survivors is the canonical DEFAULT_PROGRAMS order.
        self.assertEqual(kept, [p for p in gb.DEFAULT_PROGRAMS
                                if p not in ("Trie.hs", "List.hs")])

    def test_exclusion_subtracts_from_an_explicit_programs_list(self):
        import gibbon_benchmark as gb
        kept = gb.resolve_program_selection(["Trie.hs", "List.hs", "DomTree.hs"],
                                            ["List.hs"])
        self.assertEqual(kept, ["Trie.hs", "DomTree.hs"])

    def test_names_accepted_with_or_without_extension_or_path(self):
        import gibbon_benchmark as gb
        self.assertEqual(gb.resolve_program_selection(None, ["Trie"]),
                         gb.resolve_program_selection(None, ["Trie.hs"]))
        self.assertEqual(gb.resolve_program_selection(None, ["programs/AOS/Trie.hs"]),
                         gb.resolve_program_selection(None, ["Trie.hs"]))
        self.assertEqual(gb.normalize_program_name("Trie"), "Trie.hs")
        self.assertEqual(gb.normalize_program_name("programs/SOA/Trie.hs"), "Trie.hs")

    def test_unknown_exclusion_is_an_error_not_a_silent_no_op(self):
        import gibbon_benchmark as gb
        with self.assertRaises(gb.ProgramSelectionError) as cm:
            gb.resolve_program_selection(None, ["Tri.hs"])
        self.assertIn("Tri.hs", str(cm.exception))

    def test_glob_pattern_drops_a_whole_family_at_once(self):
        import gibbon_benchmark as gb
        # The eight OctTree_*.hs benchmarks are the motivating case: one
        # pattern instead of eight names.
        kept = gb.resolve_program_selection(None, ["OctTree*"])
        self.assertFalse([p for p in kept if p.startswith("OctTree")])
        self.assertEqual(len(kept), len(gb.DEFAULT_PROGRAMS) - 8)
        # Anchored, so ColorOctree.hs (which does not START with OctTree)
        # survives this pattern -- "*octree*" is what takes all nine.
        self.assertIn("ColorOctree.hs", kept)

    def test_glob_matching_is_anchored_to_the_whole_name(self):
        import gibbon_benchmark as gb
        # No implicit substring match, so a bare "OctTree" (which normalizes
        # to OctTree.hs, not a real benchmark) is an error rather than a
        # silent family-wide drop.
        with self.assertRaises(gb.ProgramSelectionError):
            gb.resolve_program_selection(None, ["OctTree"])

    def test_glob_matching_is_case_insensitive(self):
        import gibbon_benchmark as gb
        kept = gb.resolve_program_selection(None, ["*colorOCTREE*"])
        self.assertNotIn("ColorOctree.hs", kept)

    def test_the_octree_family_is_spelled_two_ways(self):
        import gibbon_benchmark as gb
        # OctTree_*.hs is Oct+Tree (doubled t); ColorOctree.hs is
        # Color+Octree. They differ by more than case, so "*octree*" reaches
        # only the second -- this is a property of the benchmark names, and
        # the test pins it so the documented recipe below stays honest.
        kept = gb.resolve_program_selection(None, ["*octree*"])
        self.assertNotIn("ColorOctree.hs", kept)
        self.assertIn("OctTree_sumMass.hs", kept)

    def test_two_documented_recipes_drop_all_nine_octree_benchmarks(self):
        import gibbon_benchmark as gb
        expected = [p for p in gb.DEFAULT_PROGRAMS
                    if not p.startswith("OctTree") and p != "ColorOctree.hs"]
        self.assertEqual(len(gb.DEFAULT_PROGRAMS) - len(expected), 9)
        # Two patterns, or one that spans both spellings.
        self.assertEqual(
            gb.resolve_program_selection(None, ["OctTree*", "ColorOctree.hs"]), expected)
        self.assertEqual(
            gb.resolve_program_selection(None, ["*oct*ree*"]), expected)

    def test_case_insensitive_matching_reaches_exact_names_too(self):
        import gibbon_benchmark as gb
        self.assertEqual(gb.resolve_program_selection(None, ["trie.hs"]),
                         gb.resolve_program_selection(None, ["Trie.hs"]))

    def test_literal_name_still_matches_only_itself(self):
        import gibbon_benchmark as gb
        kept = gb.resolve_program_selection(None, ["List.hs"])
        self.assertNotIn("List.hs", kept)
        # A literal must not behave like a prefix: LinearListReduction.hs
        # and reduceNestedList.hs both contain "List" and must survive.
        self.assertIn("LinearListReduction.hs", kept)
        self.assertIn("reduceNestedList.hs", kept)

    def test_overlapping_patterns_are_harmless(self):
        import gibbon_benchmark as gb
        kept = gb.resolve_program_selection(None, ["OctTree*", "OctTree_sumMass.hs"])
        self.assertEqual(len(kept), len(gb.DEFAULT_PROGRAMS) - 8)

    def test_a_glob_matching_everything_is_the_empty_run_error(self):
        import gibbon_benchmark as gb
        with self.assertRaises(gb.ProgramSelectionError) as cm:
            gb.resolve_program_selection(None, ["*"])
        self.assertIn("nothing left", str(cm.exception))

    def test_excluding_something_outside_an_explicit_programs_list_is_an_error(self):
        # "Trie.hs" is a real benchmark, but it is not in THIS run's list --
        # excluding it almost certainly means the user mistyped one of the
        # names they did select.
        import gibbon_benchmark as gb
        with self.assertRaises(gb.ProgramSelectionError):
            gb.resolve_program_selection(["List.hs"], ["Trie.hs"])

    def test_excluding_everything_is_an_error(self):
        import gibbon_benchmark as gb
        with self.assertRaises(gb.ProgramSelectionError) as cm:
            gb.resolve_program_selection(["List.hs"], ["List.hs"])
        self.assertIn("nothing left", str(cm.exception))

    def test_duplicate_exclusions_are_harmless(self):
        import gibbon_benchmark as gb
        self.assertEqual(gb.resolve_program_selection(None, ["Trie.hs", "Trie"]),
                         [p for p in gb.DEFAULT_PROGRAMS if p != "Trie.hs"])


class TestSimdIsaIsUniformAcrossConfigurations(unittest.TestCase):
    """Every configuration in a comparison must target the same SIMD ISA.

    This is a real defect this suite did not previously catch.  Gibbon defaults
    ``--simd-isa`` to avx2 when ``--opt-vectorization`` is given and to sse2
    otherwise, so a driver that left the flag implicit compiled the
    Gibbon-vectorized column for a 256-bit target and every column it was
    compared against for the x86-64 baseline -- where the C compiler's own
    auto-vectorizer can only reach SSE2.  Measured on one ArithmeticIntensity
    program: the SAME non-vectorized binary held 0 ``ymm`` references without
    the flag and 528 with it.  The whole difference landed in Gibbon's favour.
    """

    def _isa_of(self, **kw):
        import gibbon_benchmark as gb
        cmd = gb.build_gibbon_command("p.hs", "o.c", "e", "soa", cc="gcc", **kw)
        found = [a for a in cmd if a.startswith("--simd-isa=")]
        self.assertEqual(len(found), 1, f"expected exactly one --simd-isa in {cmd}")
        return found[0]

    def test_flag_is_always_passed_explicitly(self):
        # Never left to Gibbon's own default, which is context-dependent.
        self.assertEqual(self._isa_of(), "--simd-isa=avx2")

    def test_default_is_avx2(self):
        import gibbon_benchmark as gb
        self.assertEqual(gb.DEFAULT_SIMD_ISA, "avx2")
        self.assertEqual(self._isa_of(), f"--simd-isa={gb.DEFAULT_SIMD_ISA}")

    def test_vectorized_and_scalar_configs_agree(self):
        scalar = self._isa_of(enable_loopification=True)
        vector = self._isa_of(enable_loopification=True, enable_vectorization=True)
        self.assertEqual(scalar, vector,
                         "a vectorized column and the column it is compared "
                         "against must target the same ISA")

    def test_every_pldi_config_agrees(self):
        import gibbon_benchmark as gb
        seen = {}
        for table in (gb.PLDI_FOLD_CONFIGS, gb.PLDI_MAP_CONFIGS):
            for layout, configs in table.items():
                for name, kwargs in configs.items():
                    seen[(layout, name)] = self._isa_of(**kwargs)
        self.assertTrue(seen, "no PLDI configurations found")
        self.assertEqual(
            set(seen.values()), {f"--simd-isa={gb.DEFAULT_SIMD_ISA}"},
            "PLDI configurations do not all target one ISA: "
            + repr(sorted(set(seen.values()))))

    def test_override_reaches_the_command(self):
        self.assertEqual(self._isa_of(simd_isa="sse2"), "--simd-isa=sse2")

    def test_caption_names_the_isa(self):
        import gibbon_benchmark as gb
        try:
            for isa, needle in (("sse2", "SSE2"), ("avx2", "AVX2"),
                                ("native", "march=native")):
                gb.set_report_simd_isa(isa)
                self.assertIn(needle, gb.simd_isa_caption_note())
        finally:
            gb.set_report_simd_isa(gb.DEFAULT_SIMD_ISA)


class TestUnknownProgramNamesAreRejected(unittest.TestCase):
    """A --programs entry naming a nonexistent program must fail immediately.

    This cost a real run: `--programs Add1Tree8.hs` (the program is
    Add1TreeInt8.hs) was accepted, every configuration then failed "source not
    found", and the campaign produced a report of nothing but failures and a
    PDF with no per-program tables -- with the typo only discoverable
    afterwards. An unmatched --exclude-programs pattern was already an error
    for exactly this reason.
    """

    def setUp(self):
        import gibbon_benchmark as gb
        self.gb = gb
        self.dir = Path(__file__).resolve().parent / "programs"

    def test_the_real_typo_is_rejected_with_a_suggestion(self):
        with self.assertRaises(self.gb.ProgramSelectionError) as cm:
            self.gb.resolve_program_selection(
                ["Add1Tree8.hs"], None,
                default_programs=self.gb.DEFAULT_PROGRAMS + self.gb.PLDI_EXTRA_PROGRAMS,
                programs_dir=self.dir)
        self.assertIn("Add1TreeInt8.hs", str(cm.exception))

    def test_an_unrelated_unknown_name_is_rejected(self):
        with self.assertRaises(self.gb.ProgramSelectionError):
            self.gb.resolve_program_selection(
                ["NoSuchProgram.hs"], None, programs_dir=self.dir)

    def test_real_programs_are_accepted(self):
        for name in ("List.hs", "Add1TreeInt8.hs"):
            self.assertEqual(
                self.gb.resolve_program_selection(
                    [name], None,
                    default_programs=self.gb.DEFAULT_PROGRAMS + self.gb.PLDI_EXTRA_PROGRAMS,
                    programs_dir=self.dir),
                [name])

    def test_without_a_programs_dir_nothing_is_checked(self):
        # The check needs the filesystem; callers that cannot supply a
        # directory (unit tests constructing selections) keep working.
        self.assertEqual(
            self.gb.resolve_program_selection(["Whatever.hs"], None), ["Whatever.hs"])


class TestRanIsEnabledOnlyWhereRequalified(unittest.TestCase):
    """--no-ran stays campaign-wide; RAN is a named, justified exception.

    The policy's objection is to RAN being enabled SILENTLY -- a result so
    compiled is not admissible evidence. An exception is therefore admissible
    only when it is named, justified, re-qualified against the oracle, and
    reported as such in the tables. These tests pin all four properties.
    """

    def setUp(self):
        import gibbon_benchmark as gb
        self.gb = gb

    def test_only_decisiontreeclassify_is_exempt(self):
        self.assertEqual(set(self.gb.RAN_ENABLED_PROGRAMS),
                         {"DecisionTreeClassify.hs"})

    def test_the_exception_carries_its_justification(self):
        why = self.gb.RAN_ENABLED_PROGRAMS["DecisionTreeClassify.hs"]
        # Must record both why it is needed and that it was re-qualified.
        self.assertIn("_traverse_DTree", why)
        self.assertIn("oracle", why.lower())

    def test_exempt_program_omits_no_ran_and_others_keep_it(self):
        self.assertFalse(self.gb.program_uses_no_ran("DecisionTreeClassify.hs"))
        for other in ("DecisionTree.hs", "List.hs", "Trie.hs"):
            self.assertTrue(self.gb.program_uses_no_ran(other), other)

    def test_the_flag_reaches_the_compile_command(self):
        exempt = self.gb.build_gibbon_command(
            "p.hs", "o.c", "e", "soa", cc="gcc",
            use_no_ran=self.gb.program_uses_no_ran("DecisionTreeClassify.hs"))
        other = self.gb.build_gibbon_command(
            "p.hs", "o.c", "e", "soa", cc="gcc",
            use_no_ran=self.gb.program_uses_no_ran("List.hs"))
        self.assertNotIn("--no-ran", exempt)
        self.assertIn("--no-ran", other)

    def test_a_global_use_ran_still_overrides_everything(self):
        self.assertFalse(self.gb.program_uses_no_ran("List.hs", use_ran=True))

    def test_tables_label_the_exception_and_only_the_exception(self):
        self.assertIn("random-access nodes enabled",
                      self.gb.ran_caption_note("DecisionTreeClassify.hs"))
        for other in ("DecisionTree.hs", "List.hs"):
            self.assertEqual(self.gb.ran_caption_note(other), "")

    def test_an_unlisted_override_is_still_rejected(self):
        with self.assertRaises(RuntimeError) as cm:
            self.gb._validate_no_ran_overrides(
                {"List.hs": {"soa": {"use_no_ran": False}}})
        self.assertIn("List.hs", str(cm.exception))

    def test_the_decision_is_layout_independent(self):
        """AoS and SoA of the same program must agree on RAN.

        Comparing an AoS column built with random-access nodes against a SoA
        column built without them (or the reverse) would make the layout
        comparison meaningless -- it is the same class of error as compiling
        the two for different SIMD targets. The decision takes only the
        program name, with no layout or configuration parameter, so it cannot
        differ; this asserts it over the whole configuration matrix rather
        than trusting the signature.
        """
        for program in ("DecisionTreeClassify.hs", "DecisionTree.hs", "List.hs"):
            no_ran = self.gb.program_uses_no_ran(program)
            seen = set()
            for layout in ("aos", "soa"):
                for cfg_kwargs in self.gb.PLDI_MAP_CONFIGS[layout].values():
                    cmd = self.gb.build_gibbon_command(
                        program, "o.c", "e", layout, cc="gcc",
                        use_no_ran=no_ran, **cfg_kwargs)
                    seen.add("--no-ran" in cmd)
            self.assertEqual(len(seen), 1,
                             f"{program}: AoS and SoA disagree about RAN")
            self.assertEqual(seen.pop(), no_ran, program)

    def test_a_listed_program_may_override(self):
        # No exception: it is on the allowlist.
        self.gb._validate_no_ran_overrides(
            {"DecisionTreeClassify.hs": {"soa": {"use_no_ran": False}}})


class TestTimedRunsArePinnedToOneCore(unittest.TestCase):
    """Timed runs are pinned so a measurement cannot straddle core types.

    Measured on this project's hybrid i7-12700K (8 P-cores + 4 E-cores): an
    UNPINNED run retired 25-42% of its instructions on E-cores, and the split
    varied by ~17 percentage points run to run. Pinned, it is 0% -- every
    instruction on the P-core. That is what makes a perf-counter measurement
    attributable at all: perf reports the two core types as separate
    `cpu_core/` and `cpu_atom/` counter sets, and a run spread across both
    yields counts belonging to neither.
    """

    def setUp(self):
        import gibbon_benchmark as gb
        self.gb = gb

    def test_cpu_list_parsing(self):
        self.assertEqual(self.gb._parse_cpu_list("0-3"), [0, 1, 2, 3])
        self.assertEqual(self.gb._parse_cpu_list("0,2,4-6"), [0, 2, 4, 5, 6])
        self.assertEqual(self.gb._parse_cpu_list(""), [])
        self.assertEqual(self.gb._parse_cpu_list("junk"), [])

    def test_default_avoids_cpu0_and_its_smt_siblings(self):
        from pathlib import Path
        cpu = self.gb.default_pin_cpu()
        if cpu is None:
            self.skipTest("taskset unavailable")
        try:
            siblings = set(self.gb._parse_cpu_list(
                Path("/sys/devices/system/cpu/cpu0/topology/thread_siblings_list").read_text()))
        except OSError:
            self.skipTest("no CPU topology exposed")
        # CPU 0 carries most interrupt work; its SMT sibling shares that
        # core's execution resources, so neither is a quiet place to measure.
        self.assertNotIn(cpu, siblings)

    def test_default_is_a_performance_core_where_the_machine_has_them(self):
        from pathlib import Path
        cpu = self.gb.default_pin_cpu()
        if cpu is None:
            self.skipTest("taskset unavailable")
        try:
            pcores = self.gb._parse_cpu_list(Path("/sys/devices/cpu_core/cpus").read_text())
        except OSError:
            self.skipTest("not a hybrid machine")
        self.assertIn(cpu, pcores)

    def test_run_exe_accepts_a_pin_and_the_campaign_threads_it(self):
        import inspect
        self.assertIn("pin_cpu", inspect.signature(self.gb.run_exe).parameters)
        for fn in (self.gb.benchmark_program, self.gb.benchmark_build_pass,
                   self.gb.collect_pldi_variant_results,
                   self.gb.collect_add1tree_width_results,
                   self.gb.collect_arithintensity_width_results):
            self.assertIn("pin_cpu", inspect.signature(fn).parameters, fn.__name__)

    def test_every_run_in_the_campaign_shares_the_pinned_core(self):
        """Warmup, timed run and build pass all get the same core.

        A warmup on a different core warms the wrong caches and leaves the
        timed run paying the cost the warmup was meant to absorb; a build
        pass elsewhere is a timed measurement too.
        """
        import inspect, re
        src = inspect.getsource(self.gb.benchmark_program)
        # Two run_exe calls (warmup, timed) plus the benchmark_build_pass call.
        self.assertEqual(src.count("pin_cpu=pin_cpu"), 3, src.count("pin_cpu=pin_cpu"))
        # And no run_exe call inside it is left unpinned.
        for call in re.findall(r"run_exe\(.*?\)", src, re.S):
            self.assertIn("pin_cpu", call, call)

    def test_recorded_argv_excludes_the_launcher_prefix(self):
        # Provenance records what the BENCHMARK was given, not how it was
        # launched; tests and reports assert on the program's own arguments.
        import inspect
        src = inspect.getsource(self.gb.run_exe)
        self.assertLess(src.index("record_argv.append"), src.index('"taskset"'))



class TestDeadFieldScatterDegenerateInput(unittest.TestCase):
    """The trend line must not take the figure phase down.

    A one-program campaign contributes several passes at the same
    dead-field ratio. Fitting a line through a single x value raises
    LinAlgError, which used to abort every remaining figure -- including
    the stage heatmaps -- after the campaign had already been measured.
    """

    def test_one_program_still_draws(self):
        import gibbon_benchmark as gb
        if not gb.HAS_PLOT_LIBS:
            self.skipTest("matplotlib/numpy not installed")
        import tempfile
        res = {}
        for variant in ("aos", "soa"):
            r = gb.BenchmarkResult("P.hs", variant)
            r.compile_success = r.run_success = True
            r.adt_fields = 8
            # Every pass of one program shares a dead-field ratio, and a
            # program that uses every field shares the ratio 0.0 -- which is
            # what makes the fit's scaling divide by zero. Speedups differ,
            # as they do in a real run.
            times = (("a", 0.10), ("b", 0.20), ("c", 0.30)) if variant == "aos" \
                else (("a", 0.11), ("b", 0.17), ("c", 0.26))
            r.passes = {n: {"median_time": t, "pass_type": "fold", "uses": 8,
                            "dead_ratio": 0.0}
                        for n, t in times}
            import bench_provenance as prov
            st = prov.QualificationStatus(variant, "P.hs")
            st.compile_status = prov.COMPILE_OK
            st.exec_status = prov.EXEC_OK
            st.oracle_status = prov.ORACLE_PASS
            st.semantic_output = "42"
            r.qualification = st
            res[variant] = r
        with tempfile.TemporaryDirectory() as d:
            # Must not raise: every pass shares one dead-field ratio.
            gb._fig_dead_vs_speedup([(res["aos"], res["soa"])],
                                    Path(d) / "dead_vs_speedup")

if __name__ == "__main__":
    unittest.main(verbosity=2)
