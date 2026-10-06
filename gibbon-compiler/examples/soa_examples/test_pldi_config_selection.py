#!/usr/bin/env python3
"""Regression tests for --pldi-config (choosing which --pldi-submission
configurations run) and the opt-in pointer-based configuration `ptr'.

  - TestConfigFile: the TOML loader accepts exactly one shape and rejects
    everything else with a message naming the problem; the shipped example
    names every known configuration.
  - TestSelection: no file leaves the default matrix untouched; a selection
    keeps column order, brings `ptr' in as its own layout, and drops every
    delta column that would compare against a configuration that did not
    run -- including after --av-variants.
  - TestPointerConfig: `ptr' compiles the AoS source with --pointer instead
    of --packed, is held to the AoS layout annotation, renders as its own
    Pointer column group, and takes no part in the AoS-vs-SoA best-of column.
"""
import importlib
import io
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import gibbon_benchmark as gb  # noqa: E402
import bench_provenance as prov  # noqa: E402

DEFAULT_NAMES = [n for lay in ("aos", "soa") for n in gb.PLDI_MAP_CONFIGS[lay]]


def _write(text: str) -> Path:
    f = tempfile.NamedTemporaryFile("w", suffix=".toml", delete=False)
    f.write(text)
    f.close()
    return Path(f.name)


def _verified(program, variant, seconds, pass_type="fold"):
    res = gb.BenchmarkResult(program, variant)
    st = prov.QualificationStatus(variant, program)
    st.compile_status = prov.COMPILE_OK
    st.exec_status = prov.EXEC_OK
    st.oracle_status = prov.ORACLE_PASS
    st.semantic_output = "42"
    res.compile_success = res.run_success = True
    res.passes = {"p": {"median_time": seconds, "pass_type": pass_type}}
    res.qualification = st
    return res


class TestConfigFile(unittest.TestCase):
    def test_reads_the_configs_list(self):
        p = _write('[pldi]\nconfigs = ["aos_imm", "ptr"]\n')
        self.assertEqual(gb.load_pldi_config_file(p), ["aos_imm", "ptr"])

    def test_rejects_a_file_without_a_pldi_table(self):
        p = _write('configs = ["aos_imm"]\n')
        with self.assertRaisesRegex(ValueError, r"no \[pldi\] table"):
            gb.load_pldi_config_file(p)

    def test_rejects_unknown_keys(self):
        # A misspelt key would otherwise be ignored and the default matrix
        # would run in its place.
        p = _write('[pldi]\nconfig = ["aos_imm"]\n')
        with self.assertRaisesRegex(ValueError, "unknown key"):
            gb.load_pldi_config_file(p)

    def test_rejects_a_non_list(self):
        p = _write('[pldi]\nconfigs = "aos_imm"\n')
        with self.assertRaisesRegex(ValueError, "must be a list"):
            gb.load_pldi_config_file(p)

    def test_rejects_duplicates(self):
        p = _write('[pldi]\nconfigs = ["aos_imm", "aos_imm"]\n')
        with self.assertRaisesRegex(ValueError, "listed twice: aos_imm"):
            gb.load_pldi_config_file(p)

    def test_rejects_invalid_toml(self):
        p = _write('[pldi\nconfigs = [\n')
        with self.assertRaisesRegex(ValueError, "not valid TOML"):
            gb.load_pldi_config_file(p)

    def test_the_example_names_every_known_configuration(self):
        names = gb.load_pldi_config_file(HERE / "pldi_configs.example.toml")
        self.assertEqual(sorted(names), sorted(gb.pldi_known_configs()))


class TestSelection(unittest.TestCase):
    def setUp(self):
        self.addCleanup(importlib.reload, gb)

    def test_no_selection_leaves_the_default_matrix_alone(self):
        before = (gb.PLDI_FOLD_CONFIGS, gb.PLDI_MAP_CONFIGS,
                  gb.PLDI_DELTA_COLUMNS_FOLD, gb.PLDI_DELTA_COLUMNS_MAP)
        gb.apply_config_selection(None)
        gb.prune_pldi_delta_columns()
        self.assertEqual(before, (gb.PLDI_FOLD_CONFIGS, gb.PLDI_MAP_CONFIGS,
                                  gb.PLDI_DELTA_COLUMNS_FOLD,
                                  gb.PLDI_DELTA_COLUMNS_MAP))

    def test_pointer_is_opt_in(self):
        self.assertNotIn("ptr", gb.PLDI_MAP_CONFIGS)
        self.assertNotIn("$\\Delta^{P}_{pk}$",
                         [c[1] for c in gb.PLDI_DELTA_COLUMNS_MAP])

    def test_selecting_everything_is_the_default_plus_pointer(self):
        gb.apply_config_selection(gb.pldi_known_configs())
        self.assertEqual([n for lay in ("aos", "soa")
                          for n in gb.PLDI_MAP_CONFIGS[lay]], DEFAULT_NAMES)
        self.assertEqual(list(gb.PLDI_FOLD_CONFIGS["ptr"]), ["ptr"])
        self.assertEqual(list(gb.PLDI_MAP_CONFIGS["ptr"]), ["ptr"])
        for cols in (gb.PLDI_DELTA_COLUMNS_FOLD, gb.PLDI_DELTA_COLUMNS_MAP):
            self.assertEqual(cols[-1][1], "$\\Delta^{P}_{pk}$")

    def test_order_follows_the_registry_not_the_file(self):
        gb.apply_config_selection(["aos_mut", "aos_imm"])
        self.assertEqual(list(gb.PLDI_MAP_CONFIGS["aos"]), ["aos_imm", "aos_mut"])

    def test_map_only_configurations_stay_out_of_the_fold_table(self):
        gb.apply_config_selection(["aos_mut", "aos_loop"])
        self.assertEqual(list(gb.PLDI_FOLD_CONFIGS["aos"]), ["aos_mut"])
        self.assertEqual(list(gb.PLDI_MAP_CONFIGS["aos"]), ["aos_mut", "aos_loop"])

    def test_an_unselected_layout_keeps_an_empty_group(self):
        gb.apply_config_selection(["aos_imm"])
        self.assertEqual(gb.PLDI_MAP_CONFIGS["soa"], {})
        self.assertEqual(gb._pldi_col_groups(gb.PLDI_MAP_CONFIGS),
                         [("AoS", ["aos_imm"])])

    def test_delta_columns_need_both_sides(self):
        # ptr without aos_imm has nothing to be compared against.
        gb.apply_config_selection(["aos_mut", "ptr"])
        syms = [c[1] for c in gb.PLDI_DELTA_COLUMNS_MAP]
        self.assertNotIn("$\\Delta^{P}_{pk}$", syms)
        self.assertNotIn("$\\Delta^{A}_{t}$", syms)  # needs aos_mut_notco
        for _l, _s, base, feat, _d in gb.PLDI_DELTA_COLUMNS_MAP:
            self.assertIn(base, gb.PLDI_MAP_CONFIGS.get("aos", {}))

    def test_av_twins_only_for_selected_bases(self):
        gb.apply_config_selection(["aos_imm", "aos_mut", "ptr"])
        gb.apply_av_variants(("fold", "loopified"))
        gb.prune_pldi_delta_columns()
        names = [n for cfgs in gb.PLDI_MAP_CONFIGS.values() for n in cfgs]
        self.assertEqual(names, ["aos_imm_navec", "aos_imm", "aos_mut_navec",
                                 "aos_mut", "ptr"])
        present = set(names)
        for cols in (gb.PLDI_DELTA_COLUMNS_FOLD, gb.PLDI_DELTA_COLUMNS_MAP):
            for _l, _s, base, feat, _d in cols:
                self.assertIn(base, present)
                self.assertIn(feat, present)

    def test_unknown_names_are_an_error_that_lists_the_known_ones(self):
        with self.assertRaisesRegex(ValueError, "unknown PLDI configuration.*'aos_im'.*aos_imm"):
            gb.apply_config_selection(["aos_im"])

    def test_naming_a_twin_explains_av_variants(self):
        with self.assertRaisesRegex(ValueError, "--av-variants"):
            gb.apply_config_selection(["aos_mut_navec"])

    def test_an_empty_list_is_an_error(self):
        with self.assertRaisesRegex(ValueError, "empty"):
            gb.apply_config_selection([])


class TestPointerConfig(unittest.TestCase):
    def setUp(self):
        self.addCleanup(importlib.reload, gb)

    def _cmd(self, **kw):
        return gb.build_gibbon_command(Path("P.hs"), "ptr", Path("P.c"),
                                       Path("P.exe"), "gcc", **kw)

    def test_pointer_replaces_packed(self):
        cmd = self._cmd(**gb.PLDI_OPTIONAL_FOLD_CONFIGS["ptr"]["ptr"])
        self.assertIn("--pointer", cmd)
        self.assertNotIn("--packed", cmd)
        self.assertNotIn("--use-mutable-cursors", cmd)

    def test_packed_is_still_the_default(self):
        cmd = self._cmd()
        self.assertIn("--packed", cmd)
        self.assertNotIn("--pointer", cmd)

    def test_reads_the_aos_source(self):
        self.assertEqual(gb.PLDI_LAYOUT_SOURCE_DIRS["ptr"], "AOS")

    def test_held_to_the_aos_layout_annotation(self):
        ok, detail = gb._source_layout_evidence(
            HERE / "programs" / "AOS" / "MonoTree.hs", "ptr")
        self.assertTrue(ok, detail)
        ok, _detail = gb._source_layout_evidence(
            HERE / "programs" / "SOA" / "MonoTree.hs", "ptr")
        self.assertFalse(ok)

    def _results(self, ptr_seconds):
        return {"aos_imm": _verified("P.hs", "aos_imm", 0.4),
                "soa_imm": _verified("P.hs", "soa_imm", 0.2),
                "ptr": _verified("P.hs", "ptr", ptr_seconds)}

    def _table(self, results):
        gb.apply_config_selection(["aos_imm", "soa_imm", "ptr"])
        buf = io.StringIO()
        gb._pldi_reading_notes(buf)
        gb._table_pldi_fold(buf, "P.hs", results)
        return buf.getvalue()

    def test_renders_as_its_own_column_group(self):
        tex = self._table(self._results(0.8))
        self.assertIn("\\multicolumn{1}{c}{\\textbf{Pointer}}", tex)
        self.assertIn(" & $P$", tex)
        self.assertIn("not part of $A^{\\min}$/$S^{\\min}$", tex)

    def test_best_of_layout_ignores_the_pointer_group(self):
        # The pointer build is fastest overall; A^min/S^min must still be
        # aos_imm / soa_imm = 2x, not ptr / soa_imm.
        cells = [("x", 0.4), ("x", 0.2), ("x", 0.01)]
        groups = [("AoS", ["aos_imm"]), ("SoA", ["soa_imm"]), ("Pointer", ["ptr"])]
        self.assertEqual(gb._pldi_best_of_layout_speedup(cells, groups),
                         gb._spd_cell(2.0))

    def test_best_of_layout_needs_both_packed_layouts(self):
        cells = [("x", 0.4), ("x", 0.01)]
        groups = [("AoS", ["aos_imm"]), ("Pointer", ["ptr"])]
        self.assertEqual(gb._pldi_best_of_layout_speedup(cells, groups), "--")

    def test_pointer_delta_is_positive_when_packed_is_faster(self):
        results = self._results(0.8)   # pointer 2x slower than aos_imm
        self.assertEqual(gb._pldi_delta_cell(results, "ptr", "aos_imm", "p"),
                         gb._signed_percent(0.8, 0.4))
        self.assertTrue(gb._signed_percent(0.8, 0.4).startswith("+"))

    def test_legend_lists_the_pointer_configuration(self):
        gb.apply_config_selection(["aos_imm", "ptr"])
        buf = io.StringIO()
        gb._table_pldi_legend(buf)
        self.assertIn("$P$ & Pointer-based representation (pointer mode", buf.getvalue())


class TestSummaryTables(unittest.TestCase):
    def setUp(self):
        self.addCleanup(importlib.reload, gb)

    def test_unselected_summary_says_so_instead_of_rendering_empty(self):
        gb.apply_config_selection(["aos_imm", "ptr"])
        buf = io.StringIO()
        gb._table_summary(buf, [], pldi_variant_results={
            "P.hs": {"aos_imm": _verified("P.hs", "aos_imm", 0.1)}})
        tex = buf.getvalue()
        self.assertIn("Pass-sum summary not produced", tex)
        self.assertIn("\\label{tab:summary}", tex)
        self.assertNotIn("tabular", tex)


class TestCommandLine(unittest.TestCase):
    def _run(self, *argv):
        return subprocess.run([sys.executable, str(HERE / "gibbon_benchmark.py"),
                               *argv], capture_output=True, text=True, cwd=HERE)

    def test_config_without_pldi_submission_is_an_error(self):
        p = _write('[pldi]\nconfigs = ["ptr"]\n')
        r = self._run("--pldi-config", str(p))
        self.assertEqual(r.returncode, 2)
        self.assertIn("use it with --pldi-submission", r.stderr)

    def test_a_bad_config_stops_before_any_work(self):
        p = _write('[pldi]\nconfigs = ["nope"]\n')
        r = self._run("--pldi-submission", "--pldi-config", str(p))
        self.assertEqual(r.returncode, 2)
        self.assertIn("unknown PLDI configuration", r.stderr)


if __name__ == "__main__":
    unittest.main()
