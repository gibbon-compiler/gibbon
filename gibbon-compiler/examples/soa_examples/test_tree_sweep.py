#!/usr/bin/env python3
"""Regression tests for --tree-sweep (and its --sumtree-size-sweep subset).

  - TestDepthsAndLists: the depth spec forms and the traversal/language
    selections, with bad ones rejected.
  - TestConfigs: fold configurations for buildTree and sumTree, map ones for
    add1Tree, and the pointer build in each even when --pldi-config did not
    name it.
  - TestPrograms: every sweep program reads its depth from --size-param and
    times one pass; the models give the answers the programs compute.
  - TestLanguages: every language's source exists and prints the same
    timing and answer lines; the launcher passes the pass name first and
    stops a run over its memory limit.
  - TestFigure: one panel per traversal, a legend entry for every drawn line
    (including one only some panels have), unverified points named, and a
    replot that refuses another report.
"""
import importlib
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import gibbon_benchmark as gb  # noqa: E402

TRAVERSAL_KEYS = tuple(t[0] for t in gb.TREE_SWEEP_TRAVERSALS)


class TestDepthsAndLists(unittest.TestCase):
    def test_depth_forms(self):
        self.assertEqual(gb.parse_tree_sweep_depths("10:13"), [10, 11, 12, 13])
        self.assertEqual(gb.parse_tree_sweep_depths("10:16:3"), [10, 13, 16])
        self.assertEqual(gb.parse_tree_sweep_depths("20, 12,16"), [12, 16, 20])
        self.assertEqual(gb.parse_tree_sweep_depths(gb.TREE_SWEEP_DEFAULT_DEPTHS),
                         list(range(10, 27)))

    def test_bad_depths_are_rejected(self):
        for spec in ("", "a:b", "10:", "0:4", "10:50", "1:2:3:4"):
            with self.assertRaises(ValueError, msg=spec):
                gb.parse_tree_sweep_depths(spec)

    def test_selections_keep_the_canonical_order(self):
        self.assertEqual(gb.parse_tree_sweep_list("sum,build", TRAVERSAL_KEYS, "t"),
                         ["build", "sum"])
        self.assertEqual(gb.parse_tree_sweep_list("all", gb.TREE_SWEEP_LANGUAGES, "l"),
                         list(gb.TREE_SWEEP_LANGUAGES))
        self.assertEqual(gb.parse_tree_sweep_list("none", gb.TREE_SWEEP_LANGUAGES, "l"), [])
        with self.assertRaises(ValueError):
            gb.parse_tree_sweep_list("cobol", gb.TREE_SWEEP_LANGUAGES, "l")


class TestConfigs(unittest.TestCase):
    def setUp(self):
        self.addCleanup(importlib.reload, gb)

    def _names(self, registry):
        return [c for cfgs in gb.tree_sweep_configs(registry).values() for c in cfgs]

    def test_fold_and_map_registries_plus_pointer(self):
        fold, mapped = self._names("fold"), self._names("map")
        self.assertEqual(fold[-1], "ptr")
        self.assertEqual(mapped[-1], "ptr")
        self.assertFalse([n for n in fold if "loop" in n])
        self.assertTrue([n for n in mapped if "loop" in n])

    def test_pointer_is_added_once(self):
        gb.apply_config_selection(["aos_imm", "soa_mut"])
        self.assertEqual(self._names("fold"), ["aos_imm", "soa_mut", "ptr"])
        gb.apply_config_selection(["aos_mut", "ptr"])
        self.assertEqual(self._names("fold"), ["aos_mut", "ptr"])

    def test_units_count_every_configuration_and_language(self):
        per = sum(sum(len(c) for c in gb.tree_sweep_configs(reg).values()) + 7
                  for _k, _p, _prog, reg, _m in gb.TREE_SWEEP_TRAVERSALS)
        self.assertEqual(gb.tree_sweep_units([10, 11], list(TRAVERSAL_KEYS),
                                             list(gb.TREE_SWEEP_LANGUAGES)), 2 * per)


class TestPrograms(unittest.TestCase):
    def test_each_program_reads_its_depth_and_times_one_pass(self):
        for key, pass_name, program, _reg, _model in gb.TREE_SWEEP_TRAVERSALS:
            for layout in ("AOS", "SOA"):
                text = (gb.TREE_SWEEP_PROGRAMS_DIR / layout / program).read_text()
                self.assertIn("mkTree sizeParam 0", text, (program, layout))
                self.assertEqual(text.count("iterate ("), 1, (program, layout))
                self.assertIn("Running pass %s " % pass_name, text, (program, layout))

    def test_models_match_the_tree(self):
        def leaves(d, acc=0):
            return [acc] if d == 0 else leaves(d - 1, d + acc) * 2
        for d in (1, 3, 10):
            self.assertEqual(gb.tree_sweep_expected("mono_tree_sumtree_only", d),
                             str(sum(leaves(d))))
            self.assertEqual(gb.tree_sweep_expected("mono_tree_add1_only", d),
                             str(sum(x + 1 for x in leaves(d))))
        self.assertEqual(gb.tree_sweep_expected("mono_tree_add1_only", 3), "56")


class TestLanguages(unittest.TestCase):
    SOURCES = {"ghc": "treebench.hs", "mlton": "treebench.sml", "ocaml": "treebench.ml",
               "rust": "treebench.rs", "racket": "treebench.rkt",
               "java": "TreeBench.java", "chez": "treebench.ss"}

    def test_every_language_has_a_source_printing_the_shared_format(self):
        self.assertEqual(set(self.SOURCES), set(gb.TREE_SWEEP_LANGUAGES))
        for lang, name in self.SOURCES.items():
            text = (gb.TREE_SWEEP_LANGS_DIR / name).read_text()
            for marker in ("buildTree (build)", "add1Tree (map)", "sumTree (fold)",
                           "ITER TIMES: [", "End", "--size-param", "--iterate"):
                self.assertIn(marker, text, (lang, marker))

    def test_launcher_passes_the_pass_name_first_and_enforces_memory(self):
        with tempfile.TemporaryDirectory() as d:
            ok = gb._launcher(Path(d) / "ok.sh", ["echo"], "sum", 10 * 1048576)
            out = subprocess.run([str(ok), "--size-param", "3"], capture_output=True,
                                 text=True).stdout
            self.assertEqual(out.strip(), "sum --size-param 3")
            hog = gb._launcher(Path(d) / "hog.sh",
                               [sys.executable, "-c",
                                "import time; x = bytearray(300 << 20); time.sleep(5)"],
                               "sum", 50 * 1024)
            r = subprocess.run([str(hog)], capture_output=True, text=True, timeout=30)
            self.assertEqual(r.returncode, 137)
            self.assertIn("exceeded the", r.stderr)

    def test_chez_installed_as_scheme_is_found_and_mit_scheme_is_not(self):
        import os
        from unittest import mock

        def fake(version_line):
            d = tempfile.mkdtemp()
            exe = Path(d) / "scheme"
            exe.write_text("#!/bin/sh\necho '%s' >&2\n" % version_line)
            exe.chmod(0o755)
            return d
        for version, found in (("9.5.9", True), ("MIT/GNU Scheme running under GNU/Linux", False)):
            d = fake(version)
            with mock.patch.dict(os.environ, {"PATH": d}):
                got = gb._chez_command()
            self.assertEqual(got is not None, found, version)

    def test_a_language_point_is_verified_by_its_answer(self):
        out = ("Running pass sumTree (fold): \nITER TIMES: [0.000001000, 0.000002000]\n"
               "End\n48\n")
        good = gb._language_point([(True, 0.1, out, "", 0)], "sumTree", "48")
        self.assertTrue(good["verified"])
        self.assertAlmostEqual(good["median_s"], 1.5e-6)
        bad = gb._language_point([(True, 0.1, out, "", 0)], "sumTree", "49")
        self.assertFalse(bad["verified"])
        self.assertIn("expected 49", bad["error"])
        died = gb._language_point([(False, 0.1, "", "tree sweep: exceeded the 1.0 GB "
                                    "memory limit", 137)], "sumTree", "48")
        self.assertIn("memory limit", died["error"])


class TestFigure(unittest.TestCase):
    def _report(self):
        pt = lambda s, ok=True: {"median_s": s if ok else None, "verified": ok,
                                 "n": 3, "error": None if ok else "boom"}
        return {"kind": gb.TREE_SWEEP_JSON_KIND, "traversals": ["add1", "sum"],
                "pass_names": {"add1": "add1Tree", "sum": "sumTree"},
                "depths": [10, 11], "languages": ["ocaml"],
                "language_versions": {"ocaml": "OCaml 5"}, "languages_missing": {},
                "symbols": {"aos_imm": "$A$", "soa_loop_sbs_gibvec": "$S_v$", "ptr": "$P$"},
                "labels": {"aos_imm": "AoS, recursive traversal, immutable cursors",
                           "soa_loop_sbs_gibvec": "SoA, loopified", "ptr": "pointer"},
                "machine": {"cpu": "Test CPU"}, "cc": "gcc", "iterations": 5,
                "pass_rounds": 1, "pointer_iterations": {"add1": {"11": 2}},
                "language_memory_limit_gb": 9.6,
                "points": {
                    "add1": {"aos_imm": {"10": pt(1e-5), "11": pt(2e-5)},
                             "soa_loop_sbs_gibvec": {"10": pt(1e-6), "11": pt(2e-6)},
                             "ptr": {"10": pt(3e-5), "11": pt(0, ok=False)},
                             "lang:ocaml": {"10": pt(4e-5), "11": pt(8e-5)}},
                    "sum": {"aos_imm": {"10": pt(5e-6), "11": pt(1e-5)},
                            "ptr": {"10": pt(1e-6), "11": pt(2e-6)},
                            "lang:ocaml": {"10": pt(2e-6), "11": pt(4e-6)}}}}

    def test_one_panel_per_traversal_and_a_full_legend(self):
        tex = gb.tree_sweep_tex(self._report())
        self.assertEqual(tex.count("\\begin{axis}"), 2)
        self.assertIn("title={add1Tree}", tex)
        # aos_imm, soa_loop_sbs_gibvec, ptr, OCaml: the loopified line is in
        # the add1Tree panel only, and still gets its legend entry.
        self.assertEqual(tex.count("\\addlegendentry"), 4)
        self.assertIn("SoA, loopified", tex)
        self.assertIn("OCaml", tex)

    def test_unverified_points_caps_and_limits_are_in_the_caption(self):
        tex = gb.tree_sweep_tex(self._report())
        self.assertNotIn("(11,0)", tex)
        self.assertIn("add1Tree $P$ pointer-based (one heap object per node) at depth 11", tex)
        self.assertIn("depth 11: 2", tex)
        self.assertIn("9.6 GB", tex)

    def test_replot_refuses_another_report(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "x.json"
            p.write_text(json.dumps({"results": {}}))
            self.assertEqual(gb.replot_tree_sweep(p, Path(d)), 2)


if __name__ == "__main__":
    unittest.main()
