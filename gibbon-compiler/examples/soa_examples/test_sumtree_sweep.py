#!/usr/bin/env python3
"""Regression tests for --sumtree-size-sweep.

  - TestDepths: the depth spec forms, and out-of-range specs rejected.
  - TestConfigs: every fold configuration plus the pointer build, even when
    --pldi-config did not name ptr; no loopified configuration.
  - TestProgram: the sweep's sources read the depth from --size-param, and
    the model gives the answer the program prints.
  - TestGraph: one line per measured configuration, unverified points left
    out and named, and a replot refuses another report.
"""
import importlib
import json
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import gibbon_benchmark as gb  # noqa: E402


class TestDepths(unittest.TestCase):
    def test_range_step_and_list(self):
        self.assertEqual(gb.parse_sumtree_depths("10:13"), [10, 11, 12, 13])
        self.assertEqual(gb.parse_sumtree_depths("10:16:3"), [10, 13, 16])
        self.assertEqual(gb.parse_sumtree_depths("20, 12,16"), [12, 16, 20])

    def test_the_default_is_ten_to_twenty_six(self):
        self.assertEqual(gb.parse_sumtree_depths(gb.SUMTREE_SWEEP_DEFAULT_DEPTHS),
                         list(range(10, 27)))

    def test_bad_specs_are_rejected(self):
        for spec in ("", "a:b", "10:", "0:4", "10:50", "1:2:3:4"):
            with self.assertRaises(ValueError, msg=spec):
                gb.parse_sumtree_depths(spec)


class TestConfigs(unittest.TestCase):
    def setUp(self):
        self.addCleanup(importlib.reload, gb)

    def _names(self):
        return [c for cfgs in gb.sumtree_sweep_configs().values() for c in cfgs]

    def test_fold_configs_and_pointer(self):
        names = self._names()
        self.assertEqual(names[:-1], [c for cfgs in gb.PLDI_FOLD_CONFIGS.values()
                                      for c in cfgs])
        self.assertEqual(names[-1], "ptr")
        self.assertFalse([n for n in names if "loop" in n])

    def test_pointer_is_added_to_a_selection_without_it(self):
        gb.apply_config_selection(["aos_imm", "soa_mut"])
        self.assertEqual(self._names(), ["aos_imm", "soa_mut", "ptr"])

    def test_pointer_is_not_doubled_when_selected(self):
        gb.apply_config_selection(["aos_mut", "ptr"])
        self.assertEqual(self._names(), ["aos_mut", "ptr"])


class TestProgram(unittest.TestCase):
    def test_both_layouts_read_the_depth_at_run_time(self):
        for layout in ("AOS", "SOA"):
            text = (gb.SUMTREE_SWEEP_PROGRAMS_DIR / layout / gb.SUMTREE_SWEEP_PROGRAM).read_text()
            self.assertIn("tree = (mkTree sizeParam 0)", text, layout)

    def test_the_model_matches_what_the_program_computes(self):
        # mkTree d 0: every one of the 2^d leaves holds d(d+1)/2. Depth 3
        # printed 48 when compiled; check the formula by brute force too.
        def tree_sum(d, acc=0):
            return acc if d == 0 else 2 * tree_sum(d - 1, d + acc)
        for d in (1, 3, 10, 20):
            self.assertEqual(gb.sumtree_sweep_expected(d), str(tree_sum(d)), d)
        self.assertEqual(gb.sumtree_sweep_expected(3), "48")


class TestGraph(unittest.TestCase):
    def _report(self):
        pt = lambda s, ok=True: {"median_s": s if ok else None, "verified": ok,
                                 "n": 3, "error": None if ok else "boom"}
        return {"kind": gb.SUMTREE_SWEEP_JSON_KIND, "depths": [10, 11],
                "configurations": ["aos_imm", "soa_mut", "ptr"],
                "symbols": {"aos_imm": "$A$", "soa_mut": "$S$", "ptr": "$P$"},
                "labels": {"aos_imm": "AoS, recursive traversal, immutable cursors",
                           "soa_mut": "SoA", "ptr": "pointer"},
                "machine": {"cpu": "Test CPU"}, "cc": "gcc", "iterations": 5,
                "pass_rounds": 1,
                "points": {"aos_imm": {"10": pt(1e-5), "11": pt(2e-5)},
                           "soa_mut": {"10": pt(5e-6), "11": pt(0, ok=False)},
                           "ptr": {"10": pt(1e-6), "11": pt(2e-6)}}}

    def test_one_line_per_configuration_in_each_panel(self):
        tex = gb.sumtree_sweep_tex(self._report())
        self.assertEqual(tex.count("\\addplot["), 6)
        self.assertEqual(tex.count("\\addlegendentry"), 3)
        self.assertIn("AoS, immutable", tex)
        self.assertIn("dashed", tex)  # the pointer line

    def test_unverified_points_are_left_out_and_named(self):
        tex = gb.sumtree_sweep_tex(self._report())
        self.assertIn("(10,5e-06)", tex)
        self.assertNotIn("(11,0)", tex)
        self.assertIn("soa\\_mut at depth 11", tex)

    def test_time_per_leaf_divides_by_two_to_the_depth(self):
        tex = gb.sumtree_sweep_tex(self._report())
        self.assertIn("(11,0.976562)", tex)  # 2e-6 s / 2048 leaves, in ns

    def test_replot_refuses_another_report(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "x.json"
            p.write_text(json.dumps({"results": {}}))
            self.assertEqual(gb.replot_sumtree_sweep(p, Path(d)), 2)


if __name__ == "__main__":
    unittest.main()
