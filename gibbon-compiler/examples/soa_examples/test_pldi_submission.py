#!/usr/bin/env python3
"""Permanent regression tests for the --pldi-submission fold/map variant
matrix and table renderers in gibbon_benchmark.py.

Three layers:
  - TestPldiConfigRegistries: static sanity checks over PLDI_FOLD_CONFIGS /
    PLDI_MAP_CONFIGS / PLDI_ROW_LABELS / PLDI_COL_SYMBOLS -- the fold
    configs are a strict subset of the map configs per layout, every
    loopified config passes --opt-loopification without --auto-loopification
    (the confirmed policy: every curated map function this driver times
    already carries an explicit OPT:MayVectorize annotation), every SoA
    loopified config sets store_scalar_field_counts (mandatory, and a hard
    compile error if omitted -- see BUGS.md), and every config key has both
    a prose label and a unique compact column symbol.
  - TestPldiTableRendering: _table_pldi_fold/_table_pldi_map/
    _table_pldi_legend/_sig4, exercised ONLY with synthetic
    BenchmarkResult/QualificationStatus fixtures (no real compiles) --
    columns=configuration orientation, fold/map pass-type filtering from the
    same compiled result, 4-significant-digit rounding, an unverified or
    missing variant renders `--' not a number, and a program with zero
    passes of a given type renders no table for that type at all (not an
    empty/broken one).
  - TestPldiQualificationWarnings: the driver still checks every cell's
    correctness -- since the Qual. column is gone, an unverified
    (program, configuration) must instead surface as a printed warning.
"""
import importlib
import io
import re
import sys
import tempfile
import unittest
from unittest import mock
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import gibbon_benchmark as gb  # noqa: E402
import bench_provenance as prov  # noqa: E402


class TestPldiConfigRegistries(unittest.TestCase):
    def test_fold_configs_are_a_subset_of_map_configs_per_layout(self):
        for layout in ("aos", "soa"):
            for name, kwargs in gb.PLDI_FOLD_CONFIGS[layout].items():
                self.assertIn(name, gb.PLDI_MAP_CONFIGS[layout],
                             "%s missing from PLDI_MAP_CONFIGS[%r]" % (name, layout))
                self.assertEqual(kwargs, gb.PLDI_MAP_CONFIGS[layout][name],
                                 "%s kwargs differ between fold and map registries" % name)

    def test_map_configs_are_exactly_fold_configs_plus_the_documented_extras(self):
        """Naming them rather than counting them: a count says a row moved
        but not which, and the loopified rows come in auto-vectorizer pairs
        that have to stay paired."""
        self.assertEqual(
            set(gb.PLDI_MAP_CONFIGS["aos"]) - set(gb.PLDI_FOLD_CONFIGS["aos"]),
            {"aos_loop"})
        self.assertEqual(
            set(gb.PLDI_MAP_CONFIGS["soa"]) - set(gb.PLDI_FOLD_CONFIGS["soa"]),
            {"soa_loop", "soa_loop_sbs", "soa_loop_sbs_gibvec"})

    def test_every_loopified_config_omits_auto_loopification(self):
        for layout in ("aos", "soa"):
            for name, kwargs in gb.PLDI_MAP_CONFIGS[layout].items():
                if kwargs.get("enable_loopification"):
                    self.assertEqual(
                        kwargs.get("auto_loopification"), False,
                        "%s enables loopification but does not explicitly disable "
                        "auto_loopification" % name)

    def test_every_soa_loopified_config_stores_scalar_field_counts(self):
        # Mandatory: --opt-loopification without --store-scalar-field-counts
        # is now a hard compile error whenever an SoA candidate exists.
        for name, kwargs in gb.PLDI_MAP_CONFIGS["soa"].items():
            if kwargs.get("enable_loopification"):
                self.assertTrue(
                    kwargs.get("store_scalar_field_counts"),
                    "%s loopifies SoA without --store-scalar-field-counts" % name)

    def test_every_soa_scalar_count_config_defers_them(self):
        for name, kwargs in gb.PLDI_MAP_CONFIGS["soa"].items():
            if kwargs.get("store_scalar_field_counts"):
                self.assertTrue(kwargs.get("defer_scalar_counts"),
                                "%s bumps scalar counts per element" % name)

    def test_every_config_key_has_a_row_label(self):
        for layout in ("aos", "soa"):
            for name in gb.PLDI_MAP_CONFIGS[layout]:
                self.assertIn(name, gb.PLDI_ROW_LABELS, "%s has no PLDI_ROW_LABELS entry" % name)

    def test_every_config_key_has_a_unique_column_symbol(self):
        # The compact symbols are what let 13 configurations fit across the
        # page; a missing one would silently fall back to the raw config key
        # (wide) and a duplicate would make two columns indistinguishable.
        symbols = []
        for layout in ("aos", "soa"):
            for name in gb.PLDI_MAP_CONFIGS[layout]:
                self.assertIn(name, gb.PLDI_COL_SYMBOLS,
                              "%s has no PLDI_COL_SYMBOLS entry" % name)
                symbols.append(gb.PLDI_COL_SYMBOLS[name])
        self.assertEqual(len(symbols), len(set(symbols)), "duplicate column symbol")

    def test_auto_vectorization_superscript_is_av_and_set_smaller(self):
        """No default column mentions the vectorizer at all -- it is on, and
        a marker for a default is noise. The opt-in twin carries $-av$, set
        at \\scriptscriptstyle so it reads as a modifier rather than part of
        the name."""
        for sym in gb.PLDI_COL_SYMBOLS.values():
            self.assertNotIn("av", sym)
        gb.apply_av_variants(("fold",))
        self.addCleanup(importlib.reload, gb)
        twin = gb.PLDI_COL_SYMBOLS["aos_mut_navec"]
        self.assertIn("-av", twin)
        self.assertIn("\\scriptscriptstyle", twin)
    def test_every_superscript_is_set_at_the_same_smaller_size(self):
        for name, sym in gb.PLDI_COL_SYMBOLS.items():
            if "^" in sym:
                self.assertIn("\\scriptscriptstyle", sym,
                              "%s superscript is not size-matched" % name)

    def test_column_symbols_are_math_mode(self):
        for name, sym in gb.PLDI_COL_SYMBOLS.items():
            self.assertTrue(sym.startswith("$") and sym.endswith("$"),
                            "%s symbol %r is not math mode" % (name, sym))

    def test_gibbon_vectorization_configs_also_enable_selective_buffer_sharing(self):
        for name, kwargs in gb.PLDI_MAP_CONFIGS["soa"].items():
            if kwargs.get("enable_vectorization"):
                self.assertTrue(kwargs.get("enable_selective_buffer_sharing"),
                                "%s enables Gibbon vectorization without SBS" % name)

    def test_extra_programs_are_both_full_width_sweeps(self):
        # The width sweeps are reported by --pldi-submission but are not
        # part of the main AoS/SoA campaign, so they live outside
        # DEFAULT_PROGRAMS. Derived from the family constants, so adding a
        # width to either family cannot silently miss the tables.
        self.assertEqual(
            gb.PLDI_EXTRA_PROGRAMS,
            list(gb.ADD1TREE_WIDTH_PROGRAMS) + list(gb.ARITHINTENSITY_WIDTH_PROGRAMS))
        self.assertEqual(len(gb.PLDI_EXTRA_PROGRAMS), 8)

    def test_arithmetic_intensity_family_is_reported(self):
        for width in (8, 16, 32, 64):
            name = "ArithmeticIntensityInt%d.hs" % width
            self.assertIn(name, gb.PLDI_EXTRA_PROGRAMS)
            for layout in ("AOS", "SOA"):
                self.assertTrue((HERE / "programs" / layout / name).exists(),
                                "%s/%s missing" % (layout, name))

    def test_both_sweeps_have_registered_oracles(self):
        import json
        manifest = json.loads(
            (HERE / "oracles" / "manifest.json").read_text())["oracles"]
        for program in gb.PLDI_EXTRA_PROGRAMS:
            self.assertIn(program.replace(".hs", ""), manifest,
                          "%s has no registered oracle" % program)
        for p in gb.PLDI_EXTRA_PROGRAMS:
            self.assertNotIn(p, gb.DEFAULT_PROGRAMS,
                             "%s would join the main campaign, not just the "
                             "PLDI matrix" % p)
            for layout in ("AOS", "SOA"):
                self.assertTrue((HERE / "programs" / layout / p).exists(),
                                "%s/%s missing" % (layout, p))

    def test_int64_is_included_and_does_not_duplicate_monotree(self):
        # Int64 completes the sweep. It is NOT a duplicate of MonoTree.hs:
        # only the map passes are comparable, the tree shapes differ, and
        # Add1Tree's fold is `checksumTree`, which no table reports.
        self.assertIn("Add1TreeInt64.hs", gb.PLDI_EXTRA_PROGRAMS)
        self.assertIn("MonoTree.hs", gb.DEFAULT_PROGRAMS)
        self.assertNotIn("Add1TreeInt64.hs", gb.DEFAULT_PROGRAMS)
        self.assertTrue(gb.is_verification_pass("checksumTree"))

    def test_each_sweep_covers_every_integer_width_once(self):
        for prefix, family in (("Add1TreeInt", gb.ADD1TREE_WIDTH_PROGRAMS),
                               ("ArithmeticIntensityInt",
                                gb.ARITHINTENSITY_WIDTH_PROGRAMS)):
            widths = sorted(int(p.replace(prefix, "").replace(".hs", ""))
                            for p in family)
            self.assertEqual(widths, [8, 16, 32, 64],
                             "%s* is not a complete width sweep" % prefix)

    def test_extra_programs_participate_in_program_selection(self):
        candidates = gb.DEFAULT_PROGRAMS + gb.PLDI_EXTRA_PROGRAMS
        kept = gb.resolve_program_selection(None, None, default_programs=candidates)
        self.assertEqual(len(kept), len(gb.DEFAULT_PROGRAMS) + 8)
        # ... and can be excluded like anything else.
        narrowed = gb.resolve_program_selection(
            None, ["Add1Tree*", "ArithmeticIntensity*"],
            default_programs=candidates)
        self.assertEqual(narrowed, gb.DEFAULT_PROGRAMS)

    def test_no_tco_configs_disable_gcc_tail_calls_not_loopification(self):
        for layout in ("aos", "soa"):
            key = "%s_mut_notco" % layout
            kwargs = gb.PLDI_FOLD_CONFIGS[layout][key]
            self.assertTrue(kwargs.get("use_no_gcc_tail_calls"))
            self.assertFalse(kwargs.get("enable_loopification", False))



def _pldi_document(kind, results, program="P.hs"):
    """The shared reading notes plus one per-pass table, as the document
    emits them: the notes are written once for the whole run, so an
    explanation belongs in the document, not in every caption."""
    buf = io.StringIO()
    gb._pldi_reading_notes(buf)
    (gb._table_pldi_fold if kind == "fold" else gb._table_pldi_map)(
        buf, program, results)
    return buf.getvalue()


def _make_result(program, variant, pass_data, verified=True, oracle_status=None):
    res = gb.BenchmarkResult(program, variant)
    st = prov.QualificationStatus(variant, program)
    st.compile_status = prov.COMPILE_OK
    st.exec_status = prov.EXEC_OK
    if verified:
        st.oracle_status = prov.ORACLE_PASS
        st.semantic_output = "42"
    else:
        st.oracle_status = oracle_status or prov.ORACLE_FAIL
        st.oracle_detail = "synthetic test fixture: deliberately unverified"
        st.semantic_output = "42" if oracle_status != prov.ORACLE_MISSING else None
    res.compile_success = True
    res.run_success = True
    res.passes = pass_data
    res.qualification = st
    return res


class TestMatrixJsonRoundTrip(unittest.TestCase):
    """--figures-from-json redraws the heatmaps from the stored matrix, so the
    loader must hand the figure code the same rows the live run did."""

    def _matrix(self):
        matrix = {}
        for name, t in (("A.hs", 0.5), ("B.hs", 0.25)):
            by_cfg = {}
            for cfg in ("aos_imm", "aos_mut", "soa_mut"):
                res = _make_result(name, cfg, {
                    "f": {"median_time": t if cfg != "aos_imm" else 1.0,
                          "pass_type": "fold", "uses": 2}})
                res.build_time = 0.1
                by_cfg[cfg] = res
            by_cfg["soa_imm"] = _make_result(name, "soa_imm", {}, verified=False)
            by_cfg["soa_imm"].run_success = False
            matrix[name] = by_cfg
        return matrix

    def test_loaded_matrix_matches_the_written_one(self):
        import tempfile
        matrix = self._matrix()
        path = Path(tempfile.mkdtemp()) / "m.json"
        with mock.patch("builtins.print"):
            gb.write_pldi_matrix_json(matrix, path)
        loaded = gb.load_pldi_matrix_json(path)
        self.assertEqual(set(loaded), set(matrix))
        for program, by_cfg in matrix.items():
            for cfg, res in by_cfg.items():
                back = loaded[program][cfg]
                self.assertEqual(prov.verified_result(back),
                                 prov.verified_result(res), (program, cfg))
                if prov.verified_result(res):
                    self.assertEqual(back.passes["f"]["median_time"],
                                     res.passes["f"]["median_time"])
                    self.assertEqual(back.build_time, res.build_time)
        self.assertEqual(gb.total_pass_time(loaded["A.hs"]["soa_mut"]), 0.5)
        self.assertIsNone(gb.total_pass_time(loaded["A.hs"]["soa_imm"]))

    def test_campaign_report_round_trips_into_figure_pairs(self):
        import tempfile
        aos = _make_result("A.hs", "aos", {
            "f": {"median_time": 1.0, "pass_type": "fold", "stdev": 0.25,
                  "iter_times": [0.75, 1.0, 1.25]}})
        soa = _make_result("A.hs", "soa", {
            "f": {"median_time": 0.5, "pass_type": "fold", "stdev": 0.1,
                  "iter_times": [0.4, 0.5, 0.6]}})
        path = Path(tempfile.mkdtemp()) / "r.json"
        with mock.patch("builtins.print"):
            gb.write_json_results([(aos, soa)], path)
        pairs = gb.load_results_json(path)
        self.assertEqual(len(pairs), 1)
        back_a, back_s = pairs[0]
        self.assertEqual(back_a.program, "A.hs")
        self.assertEqual(back_a.passes["f"]["median_time"], 1.0)
        self.assertEqual(back_s.passes["f"]["median_time"], 0.5)
        self.assertTrue(prov.verified_result(back_a))

    def test_error_bars_survive_a_round_trip_through_json(self):
        # write_json_results drops iter_times, so a figure that recomputed the
        # deviation from them would draw a replotted run as having none.
        import tempfile
        aos = _make_result("A.hs", "aos", {
            "f": {"median_time": 1.0, "pass_type": "fold", "stdev": 0.25,
                  "iter_times": [0.75, 1.0, 1.25]}})
        path = Path(tempfile.mkdtemp()) / "r.json"
        with mock.patch("builtins.print"):
            gb.write_json_results([(aos, aos)], path)
        back = gb.load_results_json(path)[0][0]
        self.assertNotIn("iter_times", back.passes["f"])
        self.assertAlmostEqual(gb._pass_stdev(aos.passes["f"]), 0.25)
        self.assertAlmostEqual(gb._pass_stdev(back.passes["f"]), 0.25)

    def test_report_kind_is_detected_from_the_file(self):
        import tempfile
        d = Path(tempfile.mkdtemp())
        matrix_path, campaign_path = d / "m.json", d / "c.json"
        res = _make_result("A.hs", "aos_mut",
                           {"f": {"median_time": 1.0, "pass_type": "fold"}})
        with mock.patch("builtins.print"):
            gb.write_pldi_matrix_json({"A.hs": {"aos_mut": res}}, matrix_path)
            gb.write_json_results([(res, res)], campaign_path)
        self.assertEqual(gb.json_report_kind(matrix_path), "matrix")
        self.assertEqual(gb.json_report_kind(campaign_path), "campaign")

    def test_qualification_round_trips_and_rederives_verified(self):
        st = prov.QualificationStatus("v", "p")
        st.compile_status, st.exec_status = prov.COMPILE_OK, prov.EXEC_OK
        st.oracle_status, st.semantic_output = prov.ORACLE_PASS, "1"
        back = prov.QualificationStatus.from_dict(st.as_dict())
        self.assertTrue(back.verified)
        d = st.as_dict(); d["oracle_status"] = prov.ORACLE_FAIL
        d["verified"] = True            # a stored flag must not be trusted
        self.assertFalse(prov.QualificationStatus.from_dict(d).verified)


class TestPldiTableRendering(unittest.TestCase):
    def _render(self, program, results, kind):
        buf = io.StringIO()
        (gb._table_pldi_fold if kind == "fold" else gb._table_pldi_map)(buf, program, results)
        return buf.getvalue()

    def test_sig4_rounds_to_four_significant_digits(self):
        self.assertEqual(gb._sig4(0.024612345), "0.02461")
        self.assertEqual(gb._sig4(1.23456), "1.235")
        self.assertEqual(gb._sig4(123.456), "123.5")
        self.assertEqual(gb._sig4(None), "--")

    def test_sig4_renders_tiny_values_as_latex_math_not_e_notation(self):
        # %.4g would emit "1.235e-05", which reads badly in a table.
        out = gb._sig4(1.23456e-05)
        self.assertNotIn("e-", out)
        self.assertEqual(out, "$1.235 \\times 10^{-5}$")

    def test_configurations_are_columns_not_rows(self):
        results = {"aos_mut": _make_result("P.hs", "aos_mut", {
            "f": {"median_time": 0.01, "pass_type": "fold"}})}
        out = self._render("P.hs", results, "fold")
        header = [l for l in out.splitlines()
                  if gb.PLDI_COL_SYMBOLS["aos_mut"] in l][0]
        # Every fold configuration shares one header line ...
        for layout in ("aos", "soa"):
            for key in gb.PLDI_FOLD_CONFIGS[layout]:
                self.assertIn(gb.PLDI_COL_SYMBOLS[key], header)
        # ... and the pass is a row, not a column.
        self.assertTrue(any(l.startswith("f &") for l in out.splitlines()))

    def test_fold_and_map_passes_split_from_the_same_compiled_result(self):
        # One BenchmarkResult reports BOTH a fold pass and a map pass (the
        # same shape as a real "aos_mut" compile of a program with both) --
        # the fold table must show only the fold pass, the map table only
        # the map pass, both reading from the SAME underlying result.
        # NB: a real fold pass name, not `checksumTree` -- that one is a
        # verification pass and is filtered out of every table by design
        # (TestVerificationPassExclusion covers it).
        results = {
            "aos_mut": _make_result("P.hs", "aos_mut", {
                "sumTree": {"median_time": 0.01, "pass_type": "fold"},
                "add1Tree": {"median_time": 0.02, "pass_type": "map"},
            }),
        }
        fold_out = self._render("P.hs", results, "fold")
        map_out = self._render("P.hs", results, "map")
        self.assertIn("sumTree", fold_out)
        self.assertNotIn("add1Tree", fold_out)
        self.assertIn("add1Tree", map_out)
        self.assertNotIn("sumTree", map_out)
        self.assertIn("0.01", fold_out)
        self.assertIn("0.02", map_out)

    def test_map_table_carries_the_loopified_columns_the_fold_table_omits(self):
        results = {"aos_mut": _make_result("P.hs", "aos_mut", {
            "m": {"median_time": 0.01, "pass_type": "map"},
            "g": {"median_time": 0.02, "pass_type": "fold"},
        })}
        fold_out = self._render("P.hs", results, "fold")
        map_out = self._render("P.hs", results, "map")
        loop_sym = gb.PLDI_COL_SYMBOLS["soa_loop_sbs_gibvec"]
        self.assertIn(loop_sym, map_out)
        self.assertNotIn(loop_sym, fold_out)

    def test_group_headers_span_the_right_column_counts(self):
        results = {"aos_mut": _make_result("P.hs", "aos_mut", {
            "m": {"median_time": 0.01, "pass_type": "map"}})}
        out = self._render("P.hs", results, "map")
        # Derived from the configuration tables rather than hard-coded, so
        # adding a configuration updates the expectation with it.
        n_aos = len(gb.PLDI_MAP_CONFIGS["aos"])
        n_soa = len(gb.PLDI_MAP_CONFIGS["soa"])
        self.assertIn("\\multicolumn{%d}{c}{\\textbf{AoS}}" % n_aos, out)
        self.assertIn("\\multicolumn{%d}{c}{\\textbf{SoA}}" % n_soa, out)
        # Pass + Uses + Dead%, then one column per configuration, then the
        # best-of-layout ratio.
        self.assertIn("\\begin{tabular}{l c c" + " r" * (n_aos + n_soa) + " r}", out)
        # Uses and Dead% sit between the label and the groups, so the group
        # rules start at column 4; the ratio column belongs to neither group
        # and gets no rule.
        self.assertIn("\\cmidrule(lr){4-%d}\\cmidrule(lr){%d-%d}"
                      % (3 + n_aos, 4 + n_aos, 3 + n_aos + n_soa), out)

    def test_no_qual_column_is_emitted(self):
        results = {"aos_mut": _make_result("P.hs", "aos_mut", {
            "f": {"median_time": 0.01, "pass_type": "fold"}})}
        out = self._render("P.hs", results, "fold")
        self.assertNotIn("Qual", out)
        self.assertNotIn("VERIFIED", out)

    def test_unverified_variant_renders_its_failure_symbol_not_a_number(self):
        results = {
            "aos_mut": _make_result("P.hs", "aos_mut", {
                "f": {"median_time": 0.01, "pass_type": "fold"}}, verified=True),
            "soa_mut": _make_result("P.hs", "soa_mut", {
                "f": {"median_time": 999.0, "pass_type": "fold"}}, verified=False),
        }
        out = self._render("P.hs", results, "fold")
        row = [l for l in out.splitlines() if l.startswith("f &")][0]
        cells = [c.strip() for c in row.rstrip(" \\").split("&")]
        keys = (list(gb.PLDI_FOLD_CONFIGS["aos"]) + list(gb.PLDI_FOLD_CONFIGS["soa"]))
        # Three leading columns now: the pass name, Uses and Dead%.
        lead = 3
        self.assertEqual(cells[lead + keys.index("aos_mut")], "0.01")
        # ORACLE_FAIL -> "ran, output did not match the oracle".
        self.assertEqual(cells[lead + keys.index("soa_mut")], gb.PLDI_SYM_WRONG_OUTPUT)
        self.assertNotIn("999", row)

    def test_missing_variant_renders_its_symbol_not_a_crash(self):
        # A config the caller never populated (e.g. a compile that never
        # ran) must still produce a column cell, not a KeyError.
        results = {"aos_mut": _make_result("P.hs", "aos_mut", {
            "f": {"median_time": 0.01, "pass_type": "fold"}})}
        out = self._render("P.hs", results, "fold")
        row = [l for l in out.splitlines() if l.startswith("f &")][0]
        cells = [c.strip() for c in row.rstrip(" \\").split("&")]
        keys = (list(gb.PLDI_FOLD_CONFIGS["aos"]) + list(gb.PLDI_FOLD_CONFIGS["soa"]))
        self.assertEqual(cells[3 + keys.index("soa_imm")], gb.PLDI_SYM_NOT_MEASURED)

    def test_program_with_no_passes_of_a_type_renders_no_table(self):
        # Mirrors DomTree.hs-style programs that are fold-only or map-only
        # in a given layout's timed output -- the OTHER table must simply
        # not be emitted for that program, not emitted empty/broken.
        results = {"aos_mut": _make_result("P.hs", "aos_mut", {
            "onlyFold": {"median_time": 0.01, "pass_type": "fold"}})}
        map_out = self._render("P.hs", results, "map")
        self.assertEqual(map_out, "")

    def test_structurally_ineligible_loopified_variant_still_renders(self):
        # DomTree.hs's computeWidths case: a MayVectorize-annotated function
        # the compiler correctly declines to loopify (genuine parent-child
        # dependency) still compiles, runs, and verifies -- its loopified
        # column must carry the (unchanged) timing, not `--'.
        results = {
            "aos_mut": _make_result("DomTree.hs", "aos_mut", {
                "computeWidths": {"median_time": 0.03, "pass_type": "map"}}),
            "aos_loop": _make_result("DomTree.hs", "aos_loop", {
                "computeWidths": {"median_time": 0.03, "pass_type": "map"}}),
        }
        out = self._render("DomTree.hs", results, "map")
        row = [l for l in out.splitlines() if l.startswith("computeWidths &")][0]
        cells = [c.strip() for c in row.rstrip(" \\").split("&")]
        keys = (list(gb.PLDI_MAP_CONFIGS["aos"]) + list(gb.PLDI_MAP_CONFIGS["soa"]))
        # Pass, Uses and Dead% occupy cells 0-2, so the configurations start
        # at 3. Indexing from 1 happened to land on another 0.03 cell.
        self.assertEqual(cells[3 + keys.index("aos_loop")], "0.03")

    def test_multiple_passes_get_their_own_rows(self):
        results = {"aos_mut": _make_result("DomTree.hs", "aos_mut", {
            "computeWidths": {"median_time": 0.01, "pass_type": "map"},
            "scaleLayout": {"median_time": 0.02, "pass_type": "map"},
        })}
        out = self._render("DomTree.hs", results, "map")
        rows = [l.split(" &")[0] for l in out.splitlines()]
        self.assertIn("computeWidths", rows)
        self.assertIn("scaleLayout", rows)

    def test_fold_like_pass_type_is_treated_as_fold(self):
        # parse_passes classifies "fold_like" as "fold" via substring match
        # (KDTree.hs/OctTree.hs/OctTree_barnesHutPotential.hs/
        # OctTree_fmmPotential.hs print this). Confirm the table split
        # agrees, using the same pass_type string parse_passes would set.
        results = {"aos_mut": _make_result("KDTree.hs", "aos_mut", {
            "sumMassInRange": {"median_time": 0.01, "pass_type": "fold"}})}
        # Simulate what parse_passes actually assigns for a "(fold_like, ...)"
        # header: "fold" in "fold_like".lower() is True.
        self.assertIn("fold", "fold_like")
        out = self._render("KDTree.hs", results, "fold")
        self.assertIn("sumMassInRange", out)

    def test_legend_documents_every_configuration_symbol(self):
        buf = io.StringIO()
        gb._table_pldi_legend(buf)
        out = buf.getvalue()
        self.assertIn("\\label{tab:pldi-legend}", out)
        for layout in ("aos", "soa"):
            for key in gb.PLDI_MAP_CONFIGS[layout]:
                self.assertIn(gb.PLDI_COL_SYMBOLS[key], out)
                self.assertIn(gb._tex_escape(gb.PLDI_ROW_LABELS[key]), out)

    def test_legend_introduces_no_undefined_abbreviation(self):
        # The legend is where a reader decodes the column symbols, so it
        # must not itself lean on jargon the paper never expands: "SBS" and
        # "TCO" in particular were undefined in an earlier draft.
        buf = io.StringIO()
        gb._table_pldi_legend(buf)
        out = buf.getvalue()
        for abbrev in ("SBS", "TCO", "gcc-vec", "Gibbon-vec"):
            self.assertNotIn(abbrev, out, "legend uses undefined %r" % abbrev)
        self.assertIn("selective buffer sharing", out)
        self.assertIn("C tail-call optimization", out)
        self.assertIn("C auto-vectorizer", out)

    def test_tables_reference_the_legend(self):
        results = {"aos_mut": _make_result("P.hs", "aos_mut", {
            "f": {"median_time": 0.01, "pass_type": "fold"}})}
        out = self._render("P.hs", results, "fold")
        self.assertIn("\\ref{tab:pldi-legend}", out)

    def test_uses_the_booktabs_style_of_the_other_tables(self):
        results = {"aos_mut": _make_result("P.hs", "aos_mut", {
            "f": {"median_time": 0.01, "pass_type": "fold"}})}
        out = self._render("P.hs", results, "fold")
        for token in ("\\begin{table}[t]", "\\centering", "\\caption{",
                      "\\gibbonnumfont", "\\toprule", "\\midrule",
                      "\\bottomrule", "\\cmidrule(lr)"):
            self.assertIn(token, out)
        # The shabby draft leaned on \resizebox to fit; the compact column
        # symbols replace it, so the font stays consistent with Table 1.
        self.assertNotIn("resizebox", out)

    def test_a_wide_table_steps_the_font_down_rather_than_resizing(self):
        """The font steps down as columns are added so the table stays in
        the paper's own type; \\gibbonfit scales only what is still too wide
        after that, and a scaled table no longer matches the body type."""
        results = {"aos_mut": _make_result("P.hs", "aos_mut", {
            "m": {"median_time": 0.01, "pass_type": "map"},
            "g": {"median_time": 0.02, "pass_type": "fold"},
        })}
        order = ["\\small", "\\footnotesize", "\\scriptsize", "\\tiny"]
        for kind, registry in (("map", gb.PLDI_MAP_CONFIGS),
                               ("fold", gb.PLDI_FOLD_CONFIGS)):
            out = self._render("P.hs", results, kind)
            columns = sum(len(layout) for layout in registry.values()) + 4
            expected = gb._table_size_directive(columns).split("\\gibbon")[0].strip()
            self.assertIn(expected, out, kind)
            # Never a size LARGER than the one chosen.
            for bigger in order[:order.index(expected)]:
                self.assertNotIn(bigger + "\\gibbonnumfont", out, kind)
            self.assertNotIn("resizebox{\\textwidth}", out, kind)
            self.assertIn("\\gibbonfit{", out, kind)

class TestPldiQualificationWarnings(unittest.TestCase):
    def test_verified_run_produces_no_warnings(self):
        results = {"P.hs": {
            "aos_mut": _make_result("P.hs", "aos_mut", {
                "f": {"median_time": 0.01, "pass_type": "fold"}})}}
        self.assertEqual(gb.pldi_qualification_warnings(results), [])

    def test_unverified_configuration_is_named_in_a_warning(self):
        results = {"P.hs": {
            "aos_mut": _make_result("P.hs", "aos_mut", {
                "f": {"median_time": 0.01, "pass_type": "fold"}}),
            "soa_mut": _make_result("P.hs", "soa_mut", {
                "f": {"median_time": 9.0, "pass_type": "fold"}}, verified=False),
        }}
        lines = gb.pldi_qualification_warnings(results)
        self.assertEqual(len(lines), 1)
        self.assertIn("P.hs", lines[0])
        self.assertIn(gb.PLDI_ROW_LABELS["soa_mut"], lines[0])
        self.assertIn("deliberately unverified", lines[0])

    def test_report_prints_each_warning(self):
        results = {"P.hs": {
            "soa_mut": _make_result("P.hs", "soa_mut", {
                "f": {"median_time": 9.0, "pass_type": "fold"}}, verified=False)}}
        buf = io.StringIO()
        stdout, sys.stdout = sys.stdout, buf
        try:
            lines = gb.report_pldi_qualification_warnings(results)
        finally:
            sys.stdout = stdout
        self.assertEqual(len(lines), 1)
        self.assertIn(gb.PLDI_ROW_LABELS["soa_mut"], buf.getvalue())


class TestImmutableNoTcoBaseline(unittest.TestCase):
    """The immutable, tail-call-disabled configuration and what it is for.

    Measuring what mutable cursors bought against $A_{ri}$ -- immutable but
    with tail calls ENABLED -- reports mutability plus whatever tail calls
    contributed, and the two are not separable that way: mutability is
    precisely what puts the traversal in tail position for the C compiler to
    optimize. The baseline therefore has tail calls disabled on BOTH sides.
    """

    def test_configuration_exists_for_both_layouts(self):
        for layout, name in (("aos", "aos_imm_notco"), ("soa", "soa_imm_notco")):
            for table in (gb.PLDI_FOLD_CONFIGS, gb.PLDI_MAP_CONFIGS):
                self.assertIn(name, table[layout])

    def test_it_is_immutable_and_tail_calls_are_off(self):
        for name in ("aos_imm_notco", "soa_imm_notco"):
            layout = name[:3]
            kw = gb.PLDI_FOLD_CONFIGS[layout][name]
            self.assertFalse(kw.get("use_mutable_cursors", False), name)
            self.assertTrue(kw.get("use_no_gcc_tail_calls", False), name)

    def test_every_configuration_has_a_symbol_and_a_label(self):
        for layout in ("aos", "soa"):
            for name in gb.PLDI_MAP_CONFIGS[layout]:
                self.assertIn(name, gb.PLDI_COL_SYMBOLS, name)
                self.assertIn(name, gb.PLDI_ROW_LABELS, name)

    def test_mutability_delta_compares_like_for_like(self):
        found = [c for c in gb.PLDI_DELTA_COLUMNS_FOLD if c[1].endswith("_{m}$")]
        self.assertEqual(len(found), 2, "expected one mutability delta per layout")
        for _layout, _sym, baseline, feature, _legend in found:
            # Both sides must have tail calls disabled, or the column reports
            # mutability confounded with the tail-call optimization.
            for cfg in (baseline, feature):
                layout = cfg[:3]
                kw = gb.PLDI_FOLD_CONFIGS[layout][cfg]
                self.assertTrue(kw.get("use_no_gcc_tail_calls", False),
                                f"{cfg} must have tail calls disabled")
            self.assertFalse(
                gb.PLDI_FOLD_CONFIGS[baseline[:3]][baseline]
                  .get("use_mutable_cursors", False))
            self.assertTrue(
                gb.PLDI_FOLD_CONFIGS[feature[:3]][feature]
                  .get("use_mutable_cursors", False))


class TestStackExhaustionIsDistinguished(unittest.TestCase):
    """A configuration that recurses per element dies on the C stack, and the
    table must say so rather than report a generic run failure.

    This is not a defect being hidden: List.hs builds 100,000,000 elements, so
    an immutable-cursor or tail-call-disabled traversal needs a stack no
    setting can provide (the RTS already raises RLIMIT_STACK to 4GB
    successfully, and that is not close). It is the effect these columns exist
    to demonstrate.
    """

    def _crashed(self, returncode):
        res = gb.BenchmarkResult("P.hs", "aos_imm")
        st = prov.QualificationStatus("aos_imm", "P.hs")
        st.compile_status = prov.COMPILE_OK
        st.exec_status = prov.EXEC_FAIL
        res.compile_success = True
        res.run_success = False
        res.run_returncode = returncode
        res.qualification = st
        return res

    def test_segfault_gets_its_own_symbol(self):
        self.assertEqual(gb._pldi_failure_symbol(self._crashed(-11)),
                         gb.PLDI_SYM_STACK_EXHAUSTED)
        self.assertEqual(gb._pldi_failure_symbol(self._crashed(139)),
                         gb.PLDI_SYM_STACK_EXHAUSTED)

    def test_other_run_failures_keep_the_generic_symbol(self):
        self.assertEqual(gb._pldi_failure_symbol(self._crashed(1)),
                         gb.PLDI_SYM_RUN_FAIL)

    def test_the_symbol_is_distinct_from_every_other(self):
        syms = [gb.PLDI_SYM_COMPILE_FAIL, gb.PLDI_SYM_RUN_FAIL,
                gb.PLDI_SYM_WRONG_OUTPUT, gb.PLDI_SYM_NOT_MEASURED,
                gb.PLDI_SYM_STACK_EXHAUSTED]
        self.assertEqual(len(syms), len(set(syms)))


class TestFieldUsageColumns(unittest.TestCase):
    """Uses and Dead% come back to the per-program tables.

    Dead% is the fraction of the ADT a pass never touches -- the quantity a
    struct-of-arrays layout exists to exploit -- so a table of layout
    comparisons without it omits the independent variable.
    """

    def test_usage_is_read_from_whichever_config_recorded_it(self):
        r = _make_result("P.hs", "aos_mut",
                         {"f": {"median_time": 0.01, "pass_type": "fold",
                                "uses": 1, "dead_ratio": 0.5}})
        r.adt_fields = 2
        uses_s, dead_s = gb._pldi_field_usage({"aos_mut": r}, "f")
        self.assertEqual(uses_s, "1/2")
        self.assertEqual(dead_s, "50\\%")

    def test_total_is_recovered_when_the_annotation_is_absent(self):
        r = _make_result("P.hs", "aos_mut",
                         {"f": {"median_time": 0.01, "pass_type": "fold",
                                "uses": 2, "dead_ratio": 0.5}})
        r.adt_fields = None
        uses_s, _ = gb._pldi_field_usage({"aos_mut": r}, "f")
        self.assertEqual(uses_s, "2/4")

    def test_missing_data_renders_a_dash_not_a_crash(self):
        r = _make_result("P.hs", "aos_mut",
                         {"f": {"median_time": 0.01, "pass_type": "fold"}})
        r.adt_fields = None
        self.assertEqual(gb._pldi_field_usage({"aos_mut": r}, "f"), ("--", "--"))


class TestDeltaIsNormalisedToTheFeature(unittest.TestCase):
    """Deltas are (baseline - feature) / FEATURE == (speedup - 1) x 100.

    Against the BASELINE the scale saturates: 5x reads 80%, 8x reads 87.5%,
    100x reads 99%. Large wins compress into a narrow band and stop being
    distinguishable, which is what made a real speedup look unimpressive in
    the tables. Against the feature the scale is unbounded.
    """

    def test_speedups_map_to_speedup_minus_one(self):
        for speedup, expected in ((2.0, 100.0), (5.0, 400.0), (8.0, 700.0)):
            cell = gb._signed_percent(1.0, 1.0 / speedup)
            got = float(cell.replace("\\%", "").replace("$-$", "-").lstrip("+"))
            self.assertAlmostEqual(got, expected, delta=0.5,
                                   msg=f"{speedup}x -> {cell}")

    def test_a_slowdown_is_negative(self):
        cell = gb._signed_percent(1.0, 2.0)          # feature twice as slow
        self.assertIn("-", cell)

    def test_no_measurement_renders_a_dash(self):
        self.assertEqual(gb._signed_percent(None, 1.0), "--")
        self.assertEqual(gb._signed_percent(1.0, None), "--")
        # a zero FEATURE time is the degenerate denominator now, not baseline
        self.assertEqual(gb._signed_percent(1.0, 0.0), "--")
        self.assertNotEqual(gb._signed_percent(0.0, 1.0), "--")

    def test_legend_formulas_are_derived_not_hand_written(self):
        """Every column's stated formula must divide by its OWN feature.

        The formulas used to be twelve hand-written copies of the arithmetic.
        They are now generated from the (baseline, feature) pair the
        arithmetic itself uses, so they cannot contradict the numbers above
        them.
        """
        import io, re
        buf = io.StringIO()
        gb._table_pldi_delta_legend(buf)
        out = buf.getvalue()
        pairs = {c[1]: (c[2], c[3])
                 for c in (gb.PLDI_DELTA_COLUMNS_FOLD + gb.PLDI_DELTA_COLUMNS_MAP)}
        for sym, (base, feat) in pairs.items():
            b = gb.PLDI_COL_SYMBOLS[base].strip("$")
            f = gb.PLDI_COL_SYMBOLS[feat].strip("$")
            self.assertIn(f"$({b} - {f}) / {f}$", out, sym)

    def test_no_stale_baseline_denominated_formula_survives(self):
        import io
        buf = io.StringIO()
        gb._table_pldi_delta_legend(buf)
        out = buf.getvalue()
        for _lay, sym, base, feat, _d in (gb.PLDI_DELTA_COLUMNS_FOLD
                                          + gb.PLDI_DELTA_COLUMNS_MAP):
            b = gb.PLDI_COL_SYMBOLS[base].strip("$")
            f = gb.PLDI_COL_SYMBOLS[feat].strip("$")
            self.assertNotIn(f"$({b} - {f}) / {b}$", out,
                             f"{sym} still states the old baseline denominator")


class TestMapTablesReportSharedBuffers(unittest.TestCase):
    """Map tables report shared BUFFERS; fold tables keep Uses/Dead%.

    A map copies every field into the output region, so "fields used" is
    vacuously all of them and distinguishes nothing. What separates one map
    from another is how much of the data it merely COPIES -- and the unit
    that is shared is a BUFFER, not a field: a factored value is one buffer
    per scalar field PLUS the constructor stream, and a dependence-free map
    shares that stream too because it rebuilds the same shape.

    Confirmed against generated C for PiecewiseFunctions: with sharing on,
    buf0 (the constructor stream) and buf2..buf6 are shared -- six of seven
    -- while buf1, the coefficient the map rewrites, is not.
    """

    def _res(self, pass_type, shared=None, uses=None, slots=6, adt=8):
        pd = {"median_time": 0.01, "pass_type": pass_type}
        if shared is not None:
            pd["shared"] = shared; pd["shared_slots"] = slots
        if uses is not None:
            pd["uses"] = uses; pd["dead_ratio"] = (adt - uses) / adt
        r = _make_result("P.hs", "aos_mut", {"p": pd})
        r.adt_fields = adt
        r.adt_info = {"scalar_field_slots": slots,
                      "soa_total_buffers": slots + 1}
        return {"aos_mut": r}

    def test_the_constructor_stream_counts_as_a_shared_buffer(self):
        # 5 unmodified scalar fields -> 6 shared buffers of 7. Counting only
        # fields reported 5/6 and understated every map by one buffer.
        got = gb._pldi_shared_buffers(self._res("map", shared=5, slots=6), "p")
        self.assertEqual(got[0], "6/7")
        self.assertEqual(got[1], "86\\%")

    def test_a_map_that_modifies_its_only_field_still_shares_the_stream(self):
        # Add1Tree: one scalar field, rewritten. Field-counting said 0/1 (0%),
        # but the constructor stream IS shared, so half the buffers are.
        got = gb._pldi_shared_buffers(self._res("map", shared=0, slots=1), "p")
        self.assertEqual(got[0], "1/2")
        self.assertEqual(got[1], "50\\%")

    def test_recursive_fields_are_in_neither_count(self):
        # adt=8 includes 2 recursive children; the denominator is 6 scalar
        # buffers + 1 constructor stream, never 8 or 9.
        got = gb._pldi_shared_buffers(self._res("map", shared=5, slots=6, adt=8), "p")
        self.assertEqual(got[0].split("/")[1], "7")

    def test_missing_annotation_renders_a_dash(self):
        self.assertEqual(gb._pldi_shared_buffers(self._res("map"), "p"), ("--", "--"))

    def test_map_table_header_is_the_sharing_symbol(self):
        import io
        buf = io.StringIO()
        gb._table_pldi_map(buf, "P.hs", self._res("map", shared=5))
        out = buf.getvalue()
        self.assertIn("$\\Sigma_b$", out)
        self.assertNotIn("\\textbf{Uses}", out)

    def test_fold_table_still_reports_field_usage(self):
        import io
        buf = io.StringIO()
        gb._table_pldi_fold(buf, "P.hs", self._res("fold", uses=3))
        out = buf.getvalue()
        self.assertIn("\\textbf{Uses}", out)
        self.assertNotIn("$\\Sigma_b$", out)

    def test_every_map_pass_in_the_suite_is_annotated(self):
        """No map banner may be left without `shared=`.

        An un-annotated pass renders `--`, which is indistinguishable from a
        pass that genuinely shares nothing.
        """
        import re
        from pathlib import Path
        root = Path(__file__).resolve().parent / "programs"
        missing = []
        for layout in ("AOS", "SOA"):
            for src in sorted((root / layout).glob("*.hs")):
                for m in re.finditer(r'Running pass\s+([^("]+?)\s*\(\s*map\b([^)]*)\)',
                                     src.read_text()):
                    if "shared=" not in m.group(2):
                        missing.append(f"{layout}/{src.name}: {m.group(1).strip()}")
        self.assertEqual(missing, [], "map passes without shared=: %r" % missing)


class TestTableFontSize(unittest.TestCase):
    """Table figures are set one point larger than they were.

    \\gibbonnumfont is applied on top of whatever size the surrounding table
    selected (\\small or \\footnotesize), so the bump is relative and the two
    table sizes stay in proportion. The leading tracks it, or larger digits
    would collide between rows.
    """

    def _preamble(self):
        import io, tempfile
        from pathlib import Path
        with tempfile.TemporaryDirectory() as d:
            out = Path(d) / "t.tex"
            gb.write_latex_tables([], out)
            return out.read_text()

    def test_font_bump_is_one_point_larger_than_before(self):
        src = (HERE / "gibbon_benchmark.py").read_text()
        self.assertIn("\\\\f@size pt+1.5pt", src)
        self.assertNotIn("\\\\f@size pt+0.5pt", src)

    def test_leading_grew_with_the_size(self):
        src = (HERE / "gibbon_benchmark.py").read_text()
        self.assertIn("\\\\f@size pt+3.9pt", src)
        self.assertNotIn("\\\\f@size pt+2.9pt", src)


class TestVerificationPassExclusion(unittest.TestCase):
    """`checksumTree` folds the mapped tree into the single value the oracle
    compares -- correctness apparatus, not a benchmark kernel. Its OUTPUT is
    still what qualifies a run; only its TIMING is kept out of the tables and
    out of every pass-sum aggregate."""

    def _res(self):
        return _make_result("Add1TreeInt8.hs", "aos_mut", {
            "add1Tree":     {"median_time": 0.01, "pass_type": "map"},
            "sumTree":      {"median_time": 0.02, "pass_type": "fold"},
            "checksumTree": {"median_time": 99.0, "pass_type": "fold"},
        })

    def test_registry_names_checksumtree(self):
        self.assertIn("checksumTree", gb.VERIFICATION_PASSES)
        self.assertTrue(gb.is_verification_pass("checksumTree"))
        self.assertFalse(gb.is_verification_pass("sumTree"))
        self.assertFalse(gb.is_verification_pass("add1Tree"))

    def test_excluded_from_the_per_program_fold_table(self):
        results = {"aos_mut": self._res()}
        out = self._fold(results)
        self.assertNotIn("checksumTree", out)
        self.assertIn("sumTree", out)

    def _fold(self, results):
        buf = io.StringIO()
        gb._table_pldi_fold(buf, "Add1TreeInt8.hs", results)
        return buf.getvalue()

    def test_excluded_from_pass_name_discovery(self):
        names = gb._pldi_pass_names({"aos_mut": self._res()}, "fold")
        self.assertEqual(names, ["sumTree"])

    def test_excluded_from_every_pass_sum_aggregate(self):
        res = self._res()
        # 0.01 + 0.02, NOT 99.02 -- a single verification pass would
        # otherwise dominate and invert every speedup in the table.
        self.assertAlmostEqual(gb.total_pass_time(res), 0.03)
        self.assertAlmostEqual(gb.total_pass_time(res, "fold"), 0.02)
        self.assertAlmostEqual(gb.total_pass_time(res, "map"), 0.01)

    def test_a_program_whose_only_fold_is_verification_gets_no_fold_table(self):
        results = {"aos_mut": _make_result("P.hs", "aos_mut", {
            "add1Tree":     {"median_time": 0.01, "pass_type": "map"},
            "checksumTree": {"median_time": 0.02, "pass_type": "fold"}})}
        self.assertEqual(self._fold(results), "")

    # -- the aggregates that do NOT go through total_pass_time --------------

    def _pair(self, counter="PAPI_TOT_CYC"):
        """AoS 2x faster than SoA on the kernel, identical on the checksum."""
        def side(variant, kernel_t, kernel_c, fold_t, fold_c):
            return _make_result("P.hs", variant, {
                "add1Tree": {"median_time": kernel_t, "pass_type": "map",
                             "dead_ratio": 0.8,
                             "papi_counters": {counter: {"median": kernel_c}}},
                "checksumTree": {"median_time": fold_t, "pass_type": "fold",
                                 "dead_ratio": 0.0,
                                 "papi_counters": {counter: {"median": fold_c}}}})
        return (side("aos", 1.0, 100.0, 9.0, 900.0),
                side("soa", 0.5, 50.0, 9.0, 900.0))

    def test_excluded_from_the_papi_totals(self):
        aos, soa = self._pair()
        c = "PAPI_TOT_CYC"
        # 100/50 == 2x. Counting the checksum's identical 900 on both sides
        # gave 1000/950 == 1.05x, pulling every counter ratio towards 1.
        self.assertEqual(gb._papi_total_for_result(aos, c), 100.0)
        self.assertEqual(gb._papi_total_for_result(soa, c), 50.0)

    def test_excluded_from_the_fold_vs_map_figure(self):
        aos, soa = self._pair()
        # The checksum is this program's only fold, so its fold bar has no
        # data at all; it used to be drawn as a 1.05x "fold speedup".
        self.assertEqual(gb.total_pass_time(aos, "fold"), 0.0)
        self.assertAlmostEqual(gb.total_pass_time(aos, "map") /
                               gb.total_pass_time(soa, "map"), 2.0)

    def test_excluded_from_the_ghc_table_and_its_total(self):
        aos, soa = self._pair()
        ghc = _make_result("P.hs", "ghc", {
            "add1Tree": {"median_time": 2.0, "pass_type": "map"},
            "checksumTree": {"median_time": 9.0, "pass_type": "fold"}})
        buf = io.StringIO()
        gb._table_per_program_ghc(buf, [(aos, soa)],
                                  [{"program": "P.hs", "aos": aos,
                                    "soa": soa, "ghc": ghc}])
        out = buf.getvalue()
        self.assertNotIn("checksumTree", out)
        # Total GHC/Am is 2.0/1.0, matching the one row above it; summing the
        # raw passes made it 11.0/10.0.
        self.assertIn("\\textbf{Total}", out)
        total_row = [l for l in out.splitlines() if "\\textbf{Total}" in l][0]
        self.assertIn("2.00$\\times$", total_row)
        self.assertIn("4.00$\\times$", total_row)

    def test_excluded_from_the_dead_ratio_scatter(self):
        aos, soa = self._pair()
        captured = {}
        with mock.patch.object(gb, "_save"), \
             mock.patch.object(gb.plt, "subplots") as subplots:
            ax = mock.MagicMock()
            subplots.return_value = (mock.MagicMock(), ax)
            ax.scatter.side_effect = lambda x, y, **kw: captured.setdefault(
                kw.get("label", ""), (list(x), list(y)))
            gb._fig_dead_vs_speedup([(aos, soa)], Path("/dev/null"))
        # Only the map kernel is plotted; the checksum reads every field, so
        # it would sit at dead_ratio 0 and anchor the trend line.
        self.assertNotIn(0.0, [x for xs, _ys in captured.values() for x in xs])

    def test_excluded_from_the_per_pass_heatmap_and_the_stacked_breakdown(self):
        aos, soa = self._pair()
        for fn, arg in ((gb._fig_heatmaps, Path(tempfile.mkdtemp())),
                        (gb._fig_breakdown, Path("/dev/null"))):
            ticks, legends = [], []
            with mock.patch.object(gb, "_save"), \
                 mock.patch.object(gb.plt, "colorbar"), \
                 mock.patch.object(gb.plt, "subplots") as subplots:
                ax = mock.MagicMock()
                fig = mock.MagicMock()
                subplots.return_value = (fig, (ax, ax) if fn is gb._fig_breakdown
                                         else ax)
                ax.set_xticklabels.side_effect = lambda ls, **kw: ticks.extend(ls)
                fig.legend.side_effect = lambda h, ls, **kw: legends.extend(ls)
                fn([(aos, soa)], arg)
            shown = " ".join(ticks + legends)
            self.assertNotIn("checksumTree", shown)
            self.assertIn("add1Tree", shown)


class TestGeomeanRowsCompareTheSameSet(unittest.TestCase):
    """A geomean row is read column against column, so every column's mean
    must be over the same programs (or the same passes)."""

    def _timed(self, program, variant, seconds):
        return _make_result(program, variant,
                            {"m": {"median_time": seconds, "pass_type": "map"}})

    def test_a_compiler_that_skipped_the_slow_program_is_not_the_fastest(self):
        entries = [
            {"program": "A.hs",
             "aos": self._timed("A.hs", "aos", 1.0),
             "soa": self._timed("A.hs", "soa", 1.0),
             "ghc": self._timed("A.hs", "ghc", 4.0)},
            {"program": "B.hs",
             "aos": self._timed("B.hs", "aos", 100.0),
             "soa": self._timed("B.hs", "soa", 100.0),
             "ghc": None},
        ]
        buf = io.StringIO()
        gb._table_comparison_ghc_mlton(buf, entries)
        out = buf.getvalue()
        gm = [l for l in out.splitlines() if "\\textbf{Geomean}" in l][0]
        # GHC is 4x SLOWER on the only program it ran; it must not be bolded
        # as the fastest merely for skipping the expensive one.
        self.assertIn("\\textbf{1.000}", gm)
        self.assertNotIn("\\textbf{4.000}", gm)
        self.assertIn("covers the 1 program(s)", out)

    def test_both_ghc_speedup_columns_cover_one_program_set(self):
        entries = [
            {"program": "A.hs",
             "aos": self._timed("A.hs", "aos", 1.0),
             "soa": self._timed("A.hs", "soa", 0.5),
             "ghc": self._timed("A.hs", "ghc", 2.0)},
            # SoA never verified here, so this program can move neither column.
            {"program": "B.hs",
             "aos": self._timed("B.hs", "aos", 1.0),
             "soa": _make_result("B.hs", "soa", {}, verified=False),
             "ghc": self._timed("B.hs", "ghc", 100.0)},
        ]
        buf = io.StringIO()
        gb._table_speedup_vs_ghc(buf, entries)
        out = buf.getvalue()
        gm = [l for l in out.splitlines() if "\\textbf{Geomean}" in l][0]
        self.assertIn("2.00$\\times$", gm)      # GHC/AoS over A.hs alone
        self.assertIn("4.00$\\times$", gm)      # GHC/SoA over A.hs alone
        self.assertIn("covers the 1 program(s)", out)

    def test_per_program_geomean_bars_use_the_passes_both_sides_measured(self):
        aos = _make_result("P.hs", "aos", {
            "m1": {"median_time": 1.0, "pass_type": "map"},
            "m2": {"median_time": 4.0, "pass_type": "map"}})
        soa = _make_result("P.hs", "soa", {
            "m1": {"median_time": 0.5, "pass_type": "map"}})
        bars = []
        with mock.patch.object(gb, "_save"), \
             mock.patch.object(gb.plt, "subplots") as subplots:
            ax = mock.MagicMock()
            subplots.return_value = (mock.MagicMock(), ax)
            ax.bar.side_effect = lambda x, h, w, **kw: bars.append(
                (kw.get("label"), list(h))) or mock.MagicMock()
            gb._fig_per_program([(aos, soa)],
                                Path(tempfile.mkdtemp()))
        heights = dict(bars)
        # Last bar of each series is the geomean: over m1 only, 1.0 vs 0.5.
        self.assertAlmostEqual(heights["AOS"][-1], 1.0)
        self.assertAlmostEqual(heights["SOA"][-1], 0.5)


class TestEndToEndTimeIsComplete(unittest.TestCase):
    """The end-to-end figure divides one configuration's total by another's,
    so both must cover the same passes."""

    def _matrix(self, missing_in=None):
        matrix = {}
        for cfg, t in (("aos_imm", 1.0), ("aos_mut", 0.5)):
            passes = {"m": {"median_time": t, "pass_type": "map"},
                      "n": {"median_time": t, "pass_type": "map"}}
            if cfg == missing_in:
                del passes["n"]
            res = _make_result("P.hs", cfg, passes)
            res.build_time = 0.1
            matrix[cfg] = res
        return matrix

    def test_a_complete_configuration_totals_build_plus_every_pass(self):
        m = self._matrix()
        self.assertAlmostEqual(gb._pldi_end_to_end_time(m, "aos_mut"), 1.1)

    def test_a_configuration_missing_a_pass_carries_no_total(self):
        m = self._matrix(missing_in="aos_mut")
        # 0.1 + 0.5 against the other's 0.1 + 2.0 would read as a 3.5x
        # speedup built from one pass against two.
        self.assertIsNone(gb._pldi_end_to_end_time(m, "aos_mut"))


class TestRowExtremeHighlighting(unittest.TestCase):
    def test_fastest_is_green_and_slowest_is_red(self):
        cells = [("0.05", 0.05), ("0.01", 0.01), ("0.09", 0.09)]
        out = gb._highlight_row_extremes(cells)
        self.assertEqual(out[1], "\\textcolor{%s}{0.01}" % gb.COLOR_FASTEST)
        self.assertEqual(out[2], "\\textcolor{%s}{0.09}" % gb.COLOR_SLOWEST)
        self.assertEqual(out[0], "0.05")

    def test_unmeasured_cells_are_never_ranked(self):
        # `--` must not read as "fastest" (0) -- that would award the green
        # to whichever configuration failed hardest.
        out = gb._highlight_row_extremes([("--", None), ("0.05", 0.05), ("0.09", 0.09)])
        self.assertEqual(out[0], "--")
        self.assertIn(gb.COLOR_FASTEST, out[1])
        self.assertIn(gb.COLOR_SLOWEST, out[2])

    def test_nothing_is_coloured_when_there_is_nothing_to_compare(self):
        for cells in ([("0.02", 0.02)],                      # one value
                      [("0.02", 0.02), ("0.02", 0.02)],      # all equal
                      [("0.02", 0.02), ("--", None)],        # one measured
                      [("--", None), ("--", None)]):         # none measured
            for cell in gb._highlight_row_extremes(cells):
                self.assertNotIn("textcolor", cell,
                                 "coloured a row with no comparison: %r" % (cells,))

    def test_ties_at_an_extreme_are_all_marked(self):
        out = gb._highlight_row_extremes([("0.01", 0.01), ("0.01", 0.01), ("0.09", 0.09)])
        self.assertIn(gb.COLOR_FASTEST, out[0])
        self.assertIn(gb.COLOR_FASTEST, out[1])
        self.assertIn(gb.COLOR_SLOWEST, out[2])

    def test_tables_declare_the_colours_and_require_xcolor(self):
        import tempfile
        results = {"aos_mut": _make_result("P.hs", "aos_mut", {
            "f": {"median_time": 0.01, "pass_type": "fold"}})}
        with tempfile.TemporaryDirectory() as d:
            out = Path(d) / "t.tex"
            gb.write_latex_tables([], out, None, pldi_variant_results={"P.hs": results})
            text = out.read_text()
        self.assertIn("\\definecolor{%s}{RGB}{0,100,0}" % gb.COLOR_FASTEST, text)
        self.assertIn("\\definecolor{%s}{RGB}{204,0,0}" % gb.COLOR_SLOWEST, text)
        self.assertIn("xcolor", text)

    def test_tables_bump_the_font_half_a_point(self):
        import tempfile
        results = {"aos_mut": _make_result("P.hs", "aos_mut", {
            "f": {"median_time": 0.01, "pass_type": "fold"},
            "m": {"median_time": 0.01, "pass_type": "map"}})}
        with tempfile.TemporaryDirectory() as d:
            out = Path(d) / "t.tex"
            gb.write_latex_tables([], out, None,
                                  pldi_variant_results={"P.hs": results})
            text = out.read_text()
        # Defined once, relative to whatever size each table selected, so
        # \small and \footnotesize tables keep their relative sizing.
        self.assertIn("\\f@size pt+1.5pt", text)
        self.assertEqual(text.count("\\renewcommand{\\gibbonnumfont}"), 1)
        # ... and actually applied, at both sizes.
        self.assertIn("\\small\\gibbonnumfont", text)
        self.assertIn("\\footnotesize\\gibbonnumfont", text)


class TestSummaryLoopifiedColumns(unittest.TestCase):
    """Table 1 keeps its three groups (end-to-end / fold / map). What
    changes under --pldi-submission is WHICH configurations fill them: each
    layout's most-optimized one, replacing the plain mutable-cursor Am/Sm
    pair -- not an extra group beside them."""

    def _summary(self, all_results, pldi=None):
        buf = io.StringIO()
        gb._table_summary(buf, all_results, None, pldi_variant_results=pldi)
        return buf.getvalue()

    def _prog_result(self, prog, variant, fold_t, map_t=None):
        map_t = fold_t if map_t is None else map_t
        res = _make_result(prog, variant, {
            "g": {"median_time": fold_t, "pass_type": "fold"},
            "m": {"median_time": map_t, "pass_type": "map"}})
        res.adt_fields = 4
        res.adt_info = {"soa_total_buffers": 5, "type_name": "T"}
        return res

    def _pldi(self, prog, aos_fold, aos_map, soa_fold, soa_map):
        return {prog: {
            gb.SUMMARY_LOOPIFIED_AOS: self._prog_result(
                prog, gb.SUMMARY_LOOPIFIED_AOS, aos_fold, aos_map),
            gb.SUMMARY_LOOPIFIED_SOA: self._prog_result(
                prog, gb.SUMMARY_LOOPIFIED_SOA, soa_fold, soa_map)}}

    def _pair(self, prog="P.hs"):
        return (self._prog_result(prog, "aos", 9.0),
                self._prog_result(prog, "soa", 9.0))

    def test_configs_reported_are_the_two_most_optimized_ones(self):
        self.assertEqual(gb.SUMMARY_LOOPIFIED_AOS, "aos_loop")
        self.assertEqual(gb.SUMMARY_LOOPIFIED_SOA,
                         "soa_loop_sbs_gibvec")
        aos_cfg = gb.PLDI_MAP_CONFIGS["aos"][gb.SUMMARY_LOOPIFIED_AOS]
        soa_cfg = gb.PLDI_MAP_CONFIGS["soa"][gb.SUMMARY_LOOPIFIED_SOA]
        self.assertTrue(aos_cfg["enable_loopification"])
        self.assertTrue(aos_cfg["use_mutable_cursors"])
        self.assertNotIn("use_no_gcc_vec", aos_cfg)  # C auto-vec left ON
        self.assertTrue(soa_cfg["enable_loopification"])
        self.assertTrue(soa_cfg["use_mutable_cursors"])
        self.assertTrue(soa_cfg["enable_selective_buffer_sharing"])
        self.assertTrue(soa_cfg["enable_vectorization"])
        self.assertNotIn("use_no_gcc_vec", soa_cfg)  # C auto-vec left ON

    def test_there_is_no_extra_group_beside_the_usual_three(self):
        out = self._summary([self._pair()], self._pldi("P.hs", .3, .7, .1, .4))
        self.assertNotIn("Loopified", out)
        for group in ("End-to-end", "Fold passes", "Map passes"):
            self.assertIn("\\multicolumn{3}{c}{\\textbf{%s}}" % group, out)
        self.assertEqual(out.count("\\multicolumn{3}{c}"), 3)
        # 1 label + 2 ADT + 3 groups x 3 = 12 columns, no more.
        self.assertIn("\\begin{tabular}{l c c r r r r r r r r r}", out)

    def test_loopified_pair_replaces_am_sm_in_every_group(self):
        out = self._summary([self._pair()], self._pldi("P.hs", .3, .7, .1, .4))
        self.assertNotIn("Am (s)", out)
        self.assertNotIn("Sm (s)", out)
        self.assertNotIn("Am/Sm", out)
        self.assertNotIn("Ai (s)", out)   # immutable columns drop out too
        # One (AoS, SoA, ratio) triple per group -- three of each.
        self.assertEqual(out.count("$A_{\\ell}$ (s)"), 3)
        self.assertEqual(out.count("$S_{\\ell bv}$ (s)"), 3)

    def test_each_group_reports_its_own_pass_type(self):
        # AoS folds 0.30 / maps 0.70; SoA folds 0.10 / maps 0.40.
        out = self._summary([self._pair()], self._pldi("P.hs", .3, .7, .1, .4))
        row = [l for l in out.splitlines() if l.startswith("P &")][0]
        cells = [c.strip() for c in row.rstrip(" \\").split("&")]
        # program, fields, bufs, then 3 x (AoS, SoA, ratio)
        self.assertEqual(cells[3], "1.000")   # end-to-end AoS = .3 + .7
        self.assertEqual(cells[4], "0.5000")  # end-to-end SoA = .1 + .4
        self.assertIn("2.00$\\times$", cells[5])
        self.assertEqual(cells[6], "0.3000")  # fold AoS
        self.assertEqual(cells[7], "0.1000")  # fold SoA
        self.assertIn("3.00$\\times$", cells[8])
        self.assertEqual(cells[9], "0.7000")  # map AoS
        self.assertEqual(cells[10], "0.4000") # map SoA
        self.assertIn("1.75$\\times$", cells[11])

    def test_legacy_columns_survive_without_pldi_results(self):
        out = self._summary([self._pair()])
        self.assertIn("Am (s)", out)
        self.assertIn("Am/Sm", out)
        self.assertNotIn("+av", out)

    def test_missing_or_unverified_config_renders_dashes_in_every_group(self):
        out = self._summary([self._pair()], {"P.hs": {}})
        row = [l for l in out.splitlines() if l.startswith("P &")][0]
        cells = [c.strip() for c in row.rstrip(" \\").split("&")]
        self.assertEqual(cells[3:], ["--"] * 9)

    def test_octree_row_needs_every_member_verified(self):
        # A partial sum would understate the merged row; it must be `--`.
        members = ["OctTree_sumMass.hs", "OctTree_sumEnergy.hs"]
        pldi = {members[0]: {gb.SUMMARY_LOOPIFIED_AOS: self._prog_result(
            members[0], gb.SUMMARY_LOOPIFIED_AOS, 0.25, 0.25)}}
        self.assertIsNone(gb._summary_loopified_total(
            pldi, "OctTreeCombined.hs", gb.SUMMARY_LOOPIFIED_AOS, members))
        pldi[members[1]] = {gb.SUMMARY_LOOPIFIED_AOS: self._prog_result(
            members[1], gb.SUMMARY_LOOPIFIED_AOS, 0.125, 0.125)}
        self.assertAlmostEqual(gb._summary_loopified_total(
            pldi, "OctTreeCombined.hs", gb.SUMMARY_LOOPIFIED_AOS, members), 0.75)
        # ... and the pass_type filter applies through the member sum too.
        self.assertAlmostEqual(gb._summary_loopified_total(
            pldi, "OctTreeCombined.hs", gb.SUMMARY_LOOPIFIED_AOS, members,
            "fold"), 0.375)


    def test_caption_names_where_the_per_program_tables_can_disagree(self):
        """Table 1's fold group is measured on binaries the per-program
        fold tables never show, so the two can differ in magnitude and --
        where the layouts are close -- in direction. The caption has to
        name that, and has to say a group here is a pass-sum."""
        out = self._summary([self._pair()], self._pldi("P.hs", 2.0, 2.0, 1.0, 1.0))
        cap = out.split("\\label{")[0]
        self.assertIn("NOT among the columns", cap)
        self.assertIn("per-program FOLD tables", cap)
        self.assertIn("in direction", cap)
        self.assertIn("pass-SUM", cap)
        # The old claim covered only the AoS side; folds gain nothing from
        # loopification on either.
        self.assertIn("neither layout's fold", cap)


class TestFailureSymbols(unittest.TestCase):
    """A no-number cell says WHICH failure it was. "Did not compile" and
    "compiled, ran, and computed the wrong answer" are very different
    claims about a configuration and must not share a symbol."""

    def _status(self, **kw):
        res = gb.BenchmarkResult("P.hs", "v")
        st = prov.QualificationStatus("v", "P.hs")
        st.compile_status = kw.get("compile", prov.COMPILE_OK)
        st.exec_status = kw.get("exec", prov.EXEC_OK)
        st.oracle_status = kw.get("oracle", prov.ORACLE_PASS)
        st.semantic_output = kw.get("output", "42")
        res.qualification = st
        return res

    def test_the_four_symbols_are_distinct(self):
        syms = [gb.PLDI_SYM_COMPILE_FAIL, gb.PLDI_SYM_RUN_FAIL,
                gb.PLDI_SYM_WRONG_OUTPUT, gb.PLDI_SYM_NOT_MEASURED]
        self.assertEqual(len(syms), len(set(syms)))
        self.assertEqual(gb.PLDI_SYM_COMPILE_FAIL, "*")
        self.assertEqual(gb.PLDI_SYM_RUN_FAIL, "-")
        self.assertEqual(gb.PLDI_SYM_WRONG_OUTPUT, "**")

    def test_each_failure_mode_maps_to_its_own_symbol(self):
        self.assertEqual(gb._pldi_failure_symbol(
            self._status(compile=prov.COMPILE_FAIL)), gb.PLDI_SYM_COMPILE_FAIL)
        self.assertEqual(gb._pldi_failure_symbol(
            self._status(exec=prov.EXEC_FAIL)), gb.PLDI_SYM_RUN_FAIL)
        self.assertEqual(gb._pldi_failure_symbol(
            self._status(oracle=prov.ORACLE_FAIL)), gb.PLDI_SYM_WRONG_OUTPUT)
        # Printing nothing is one way for the output not to match, not a
        # separate kind of event.
        self.assertEqual(gb._pldi_failure_symbol(
            self._status(output=None)), gb.PLDI_SYM_WRONG_OUTPUT)
        self.assertEqual(gb._pldi_failure_symbol(
            self._status(oracle=prov.ORACLE_MISSING)), gb.PLDI_SYM_NOT_MEASURED)
        self.assertEqual(gb._pldi_failure_symbol(None), gb.PLDI_SYM_NOT_MEASURED)

    def test_symbols_are_read_off_the_qualification_label(self):
        # The table must not re-derive "what happened" independently of the
        # driver's own decision, or it can disagree with the warning list.
        for kwargs, label in ((dict(compile=prov.COMPILE_FAIL), "COMPILE-FAIL"),
                              (dict(exec=prov.EXEC_FAIL), "RUN-FAIL"),
                              (dict(oracle=prov.ORACLE_FAIL), "WRONG"),
                              (dict(output=None), "EMPTY-OUTPUT")):
            self.assertEqual(self._status(**kwargs).qualification.label, label)

    def test_caption_defines_every_symbol_it_can_emit(self):
        results = {"aos_mut": _make_result("P.hs", "aos_mut", {
            "f": {"median_time": 0.01, "pass_type": "fold"}})}
        caption = _pldi_document("fold", results)
        for sym in (gb.PLDI_SYM_COMPILE_FAIL, gb.PLDI_SYM_RUN_FAIL,
                    gb.PLDI_SYM_WRONG_OUTPUT, gb.PLDI_SYM_NOT_MEASURED):
            self.assertIn("`%s'" % sym, caption,
                          "caption does not define the %r symbol" % sym)

    def test_a_failure_symbol_is_never_ranked_as_fastest(self):
        out = gb._highlight_row_extremes(
            [(gb.PLDI_SYM_COMPILE_FAIL, None), ("0.05", 0.05), ("0.09", 0.09)])
        self.assertEqual(out[0], gb.PLDI_SYM_COMPILE_FAIL)
        self.assertIn(gb.COLOR_FASTEST, out[1])


class TestBestOfLayoutSpeedup(unittest.TestCase):
    """Each per-program row ends with fastest-AoS / fastest-SoA. Best-vs-best
    rather than a fixed pair, so neither layout is judged by a configuration
    that happened to suit this particular kernel badly."""

    GROUPS = [("AoS", ["a1", "a2", "a3"]), ("SoA", ["s1", "s2"])]

    def test_ratio_uses_each_layouts_row_minimum(self):
        cells = [("0.20", 0.20), ("0.10", 0.10), ("0.30", 0.30),
                 ("0.05", 0.05), ("0.08", 0.08)]
        # min AoS 0.10 / min SoA 0.05 = 2.00x -- NOT first/first (4.00x)
        # and not last/last (3.75x).
        out = gb._pldi_best_of_layout_speedup(cells, self.GROUPS)
        self.assertIn("2.00$\\times$", out)

    def test_failed_configurations_cannot_win_their_layout(self):
        # The `*` cell carries no value, so the AoS best is 0.10, not "0".
        cells = [(gb.PLDI_SYM_COMPILE_FAIL, None), ("0.10", 0.10),
                 (gb.PLDI_SYM_RUN_FAIL, None), ("0.20", 0.20),
                 (gb.PLDI_SYM_NOT_MEASURED, None)]
        self.assertIn("0.50$\\times$",
                      gb._pldi_best_of_layout_speedup(cells, self.GROUPS))

    def test_dash_when_either_layout_has_nothing_measured(self):
        no_aos = [("*", None), ("*", None), ("*", None), ("0.05", 0.05), ("0.08", 0.08)]
        no_soa = [("0.20", 0.20), ("0.10", 0.10), ("0.30", 0.30), ("**", None), ("?", None)]
        self.assertEqual(gb._pldi_best_of_layout_speedup(no_aos, self.GROUPS), "--")
        self.assertEqual(gb._pldi_best_of_layout_speedup(no_soa, self.GROUPS), "--")

    def test_bolded_like_every_other_speedup_in_the_paper(self):
        big = [("1.00", 1.0), ("1.00", 1.0), ("1.00", 1.0), ("0.50", 0.5), ("0.50", 0.5)]
        small = [("1.00", 1.0), ("1.00", 1.0), ("1.00", 1.0), ("0.99", 0.99), ("0.99", 0.99)]
        self.assertIn("\\textbf{", gb._pldi_best_of_layout_speedup(big, self.GROUPS))
        self.assertNotIn("\\textbf{", gb._pldi_best_of_layout_speedup(small, self.GROUPS))

    def test_column_is_present_in_both_table_kinds(self):
        results = {"aos_mut": _make_result("P.hs", "aos_mut", {
            "g": {"median_time": 0.02, "pass_type": "fold"},
            "m": {"median_time": 0.01, "pass_type": "map"}}),
            "soa_mut": _make_result("P.hs", "soa_mut", {
            "g": {"median_time": 0.01, "pass_type": "fold"},
            "m": {"median_time": 0.005, "pass_type": "map"}})}
        # Derived from the registries rather than written out: this
        # assertion went stale once already when the immutable-no-TCO
        # configurations were added, and a hardcoded count tests the
        # constant, not the renderer.
        for kind in ("fold", "map"):
            n_cfg = sum(len(gb.PLDI_FOLD_CONFIGS[lay] if kind == "fold"
                            else gb.PLDI_MAP_CONFIGS[lay])
                        for lay in ("aos", "soa"))
            buf = io.StringIO()
            (gb._table_pldi_fold if kind == "fold" else gb._table_pldi_map)(
                buf, "P.hs", results)
            out = buf.getvalue()
            self.assertIn("$A^{\\min}$/$S^{\\min}$", out,
                          "%s table has no best-of-layout column" % kind)
            # One label column, the two ADT-characterization columns, the
            # configurations, then the ratio column.
            self.assertIn(
                "\\begin{tabular}{l c c" + " r" * (n_cfg + 1) + "}", out)
            row = [l for l in out.splitlines() if l.startswith(("g &", "m &"))][0]
            self.assertIn("2.00$\\times$", row)

    def test_caption_explains_the_column(self):
        results = {"aos_mut": _make_result("P.hs", "aos_mut", {
            "g": {"median_time": 0.02, "pass_type": "fold"}})}
        caption = _pldi_document("fold", results)
        self.assertIn("$A^{\\min}$/$S^{\\min}$", caption)
        self.assertIn("fastest AoS configuration", caption)

    def test_a_row_of_all_failures_yields_a_dash_not_a_crash(self):
        cells = [("*", None)] * 5
        self.assertEqual(gb._pldi_best_of_layout_speedup(cells, self.GROUPS), "--")

    def test_minimum_is_taken_only_over_the_displayed_columns(self):
        """A^min/S^min must be checkable against the row printed above it.

        The loopified configurations DO time every fold pass -- the fold
        table simply does not display their columns -- so minimising over
        them would produce a ratio a reader could not derive from the
        table, and would silently import the summary table's comparison
        into a table that is not making it."""
        passes = {"g": {"median_time": 0.02, "pass_type": "fold"}}
        fast = {"g": {"median_time": 0.001, "pass_type": "fold"}}
        results = {"aos_mut": _make_result("P.hs", "aos_mut", passes),
                   "soa_mut": _make_result("P.hs", "soa_mut", passes),
                   # Not a fold-table column; must not reach the ratio.
                   gb.SUMMARY_LOOPIFIED_SOA: _make_result(
                       "P.hs", gb.SUMMARY_LOOPIFIED_SOA, fast)}
        buf = io.StringIO()
        gb._table_pldi_fold(buf, "P.hs", results)
        row = [l for l in buf.getvalue().splitlines() if l.startswith("g &")][0]
        self.assertIn("1.00$\\times$", row)
        self.assertNotIn("20.00$\\times$", row)

    def test_fold_caption_says_the_summarys_pair_is_not_a_column_here(self):
        """The two tables can disagree about which layout leads, because
        they are reading different binaries. A reader has no way to see
        that from the columns, so the caption has to say it."""
        results = {"aos_mut": _make_result("P.hs", "aos_mut", {
            "g": {"median_time": 0.02, "pass_type": "fold"}})}
        cap = _pldi_document("fold", results)
        self.assertIn("columns that table shows and no others", cap)
        self.assertIn("recursive configurations only", cap)
        self.assertIn("tab:summary", cap)
        self.assertIn("reverse which one leads", cap)

    def test_map_caption_does_not_present_an_annotation_as_an_achievement(self):
        """$\\Sigma_b$ is read from a `shared=N` string literal in the
        benchmark source. It says what the pass writes, not what the
        optimization did.

        DomTree's `computeWidths` renders 13/14 = 93% and its
        $\\Delta^{S}_{b}$ is +0.10%: enabling selective buffer sharing
        produces a gensym-identical function, because sharing is
        implemented on the loopified form and that pass declines
        loopification. A caption calling 93% "the buffers sharing shares
        rather than rewrites" states the opposite of what happened."""
        results = {"aos_mut": _make_result("P.hs", "aos_mut", {
            "m": {"median_time": 0.02, "pass_type": "map"}})}
        cap = _pldi_document("map", results)
        self.assertIn("leaves unmodified", cap)
        self.assertIn("upper bound", cap)
        self.assertIn("NOT a measurement", cap)
        self.assertIn("\\Delta^{S}_{b}", cap)
        # The old wording asserted the optimization had done it.
        self.assertNotIn("sharing ($b$) shares rather than rewrites", cap)

    def test_map_caption_says_the_summary_is_a_pass_sum(self):
        """The map table DOES show the summary's pair, so the remaining way
        the two can disagree is aggregation: one row here against a sum
        over every map pass there."""
        results = {"aos_mut": _make_result("P.hs", "aos_mut", {
            "m": {"median_time": 0.02, "pass_type": "map"}})}
        cap = _pldi_document("map", results)
        self.assertIn("columns that table shows and no others", cap)
        self.assertIn("pass-SUM", cap)
        self.assertIn("lead here and trail there", cap)


class TestSplitFamilyMerging(unittest.TestCase):
    """A family that ships as one executable per timed pass must still be
    REPORTED as one program -- one table, one row per pass, in the original
    order -- exactly as when it was a single executable."""

    MEMBERS = ["PiecewiseFunctions_norm2Estimate.hs",
               "PiecewiseFunctions_truncateTolViolations.hs",
               "PiecewiseFunctions_addConstPW.hs"]
    PASSES = {"PiecewiseFunctions_norm2Estimate.hs": ("norm2Estimate", "fold"),
              "PiecewiseFunctions_truncateTolViolations.hs": ("truncateTolViolations", "fold"),
              "PiecewiseFunctions_addConstPW.hs": ("addConstPW", "map")}

    def _pldi(self, failing_in=None, t=0.01):
        """failing_in: {member: [configs it failed in]}."""
        failing_in = failing_in or {}
        out = {}
        for i, member in enumerate(self.MEMBERS):
            pname, ptype = self.PASSES[member]
            out[member] = {}
            for cfg in ["aos_mut", "soa_mut"]:
                if cfg in failing_in.get(member, []):
                    res = _make_result(member, cfg, {}, verified=False)
                    res.run_success = False
                    res.qualification.compile_status = prov.COMPILE_FAIL
                else:
                    res = _make_result(member, cfg, {
                        pname: {"median_time": t * (i + 1), "pass_type": ptype}})
                out[member][cfg] = res
        return out

    def test_group_registry_names_the_family(self):
        self.assertIn("PiecewiseFunctions.hs", gb.PROGRAM_MERGE_GROUPS)
        self.assertEqual(gb.PROGRAM_MERGE_GROUPS["PiecewiseFunctions.hs"],
                         "PiecewiseFunctions_")

    def test_members_collapse_into_one_program(self):
        merged = gb.merge_pldi_program_groups(self._pldi())
        self.assertIn("PiecewiseFunctions.hs", merged)
        for member in self.MEMBERS:
            self.assertNotIn(member, merged,
                             "%s still reported separately" % member)

    def test_every_members_pass_becomes_a_row(self):
        merged = gb.merge_pldi_program_groups(self._pldi())
        entry = merged["PiecewiseFunctions.hs"]
        self.assertEqual(sorted(entry["aos_mut"].passes),
                         sorted(p for p, _ in self.PASSES.values()))

    def test_row_order_follows_default_programs_not_the_alphabet(self):
        # DEFAULT_PROGRAMS lists the members in the order the original
        # combined program computed them; alphabetical order would put
        # addConstPW first and scramble the table against the old one.
        members = gb.merge_group_members(
            "PiecewiseFunctions.hs", "PiecewiseFunctions_", gb.DEFAULT_PROGRAMS)
        self.assertEqual(members[0], "PiecewiseFunctions_norm2Estimate.hs")
        self.assertEqual(members[-1], "PiecewiseFunctions_diffPW.hs")
        self.assertNotEqual(members, sorted(members))

    def test_fold_and_map_members_land_in_their_own_tables(self):
        merged = gb.merge_pldi_program_groups(self._pldi())
        entry = merged["PiecewiseFunctions.hs"]
        self.assertEqual(gb._pldi_pass_names(entry, "fold"),
                         ["norm2Estimate", "truncateTolViolations"])
        self.assertEqual(gb._pldi_pass_names(entry, "map"), ["addConstPW"])

    def test_one_members_failure_blanks_only_its_own_cell(self):
        # The whole point of per-pass provenance: a member that failed in
        # ONE configuration must not take the rest of the family's column
        # down with it, and must report its OWN failure mode.
        failing = "PiecewiseFunctions_truncateTolViolations.hs"
        merged = gb.merge_pldi_program_groups(
            self._pldi(failing_in={failing: ["aos_mut"]}))
        entry = merged["PiecewiseFunctions.hs"]
        _good, good_val = gb._pldi_cell(entry["aos_mut"], "norm2Estimate")
        bad_text, bad_val = gb._pldi_cell(entry["aos_mut"], "truncateTolViolations")
        self.assertIsNotNone(good_val, "a healthy member lost its number")
        self.assertIsNone(bad_val)
        self.assertEqual(bad_text, gb.PLDI_SYM_COMPILE_FAIL)
        # The same pass still reports its number in the configuration where
        # that member did succeed.
        _ok, ok_val = gb._pldi_cell(entry["soa_mut"], "truncateTolViolations")
        self.assertIsNotNone(ok_val)

    def test_a_member_failing_everywhere_drops_its_row_but_is_still_reported(self):
        # Known and accepted: a pass name is only learned from a run that
        # produced it, so a member that failed in EVERY configuration
        # contributes no row. It is not lost, though -- the warning list is
        # computed BEFORE merging, so it still names that member by file.
        failing = "PiecewiseFunctions_truncateTolViolations.hs"
        unmerged = self._pldi(failing_in={failing: ["aos_mut", "soa_mut"]})
        merged = gb.merge_pldi_program_groups(unmerged)
        entry = merged["PiecewiseFunctions.hs"]
        self.assertNotIn("truncateTolViolations", entry["aos_mut"].passes)
        warnings = gb.pldi_qualification_warnings(unmerged)
        self.assertTrue(any(failing in w for w in warnings),
                        "a member failing everywhere vanished from the warnings")

    def test_nothing_happens_when_the_family_is_absent(self):
        other = {"Trie.hs": {"aos_mut": _make_result("Trie.hs", "aos_mut", {
            "f": {"median_time": 0.01, "pass_type": "fold"}})}}
        self.assertEqual(gb.merge_pldi_program_groups(other), other)
        self.assertIsNone(gb.merge_pldi_program_groups(None))

    def test_summary_pairs_collapse_to_one_row(self):
        pairs = []
        for i, member in enumerate(self.MEMBERS):
            pname, ptype = self.PASSES[member]
            pairs.append((_make_result(member, "aos", {
                pname: {"median_time": 0.01 * (i + 1), "pass_type": ptype}}),
                          _make_result(member, "soa", {
                pname: {"median_time": 0.02 * (i + 1), "pass_type": ptype}})))
        merged = gb.merge_program_groups_in_pairs(pairs)
        self.assertEqual(len(merged), 1)
        aos, soa = merged[0]
        self.assertEqual(aos.program, "PiecewiseFunctions.hs")
        # Pass-sums add up across the members, so Table 1's row is the same
        # total the single executable would have reported.
        self.assertAlmostEqual(gb.total_pass_time(aos), 0.01 + 0.02 + 0.03)
        self.assertAlmostEqual(gb.total_pass_time(soa), 0.02 + 0.04 + 0.06)
        self.assertAlmostEqual(gb.total_pass_time(aos, "map"), 0.03)


class TestDeltaTables(unittest.TestCase):
    """Per-pass delta tables: what each optimization actually bought, in
    seconds. Every column is baseline - feature, so positive always means
    the feature made the pass faster."""

    TIMES = {"aos_imm": 0.10, "aos_imm_notco": 0.13,
             "aos_mut_notco": 0.08, "aos_mut": 0.05,
             "aos_loop": 0.03,
             "soa_imm": 0.20, "soa_imm_notco": 0.24,
             "soa_mut_notco": 0.16, "soa_mut": 0.12,
             "soa_loop": 0.10, "soa_loop_sbs": 0.06,
             # Deliberately SLOWER than soa_loop_sbs: Gibbon vectorization
             # hurting is the case an absolute value would hide.
             "soa_loop_sbs_gibvec": 0.07}

    def _results(self, times=None):
        times = times or self.TIMES
        return {cfg: _make_result("P.hs", cfg, {
            "g": {"median_time": t, "pass_type": "fold"},
            "m": {"median_time": t, "pass_type": "map"}})
            for cfg, t in times.items()}

    def _row(self, kind):
        buf = io.StringIO()
        (gb._table_pldi_fold_deltas if kind == "fold"
         else gb._table_pldi_map_deltas)(buf, "P.hs", self._results())
        out = buf.getvalue()
        prefix = "g &" if kind == "fold" else "m &"
        row = [l for l in out.splitlines() if l.startswith(prefix)][0]
        return out, [c.strip() for c in row.rstrip(" \\").split("&")][1:]

    def test_fold_table_has_the_four_requested_columns(self):
        """No auto-vectorizer column by default: the vectorizer is on
        everywhere and unmarked, and its ablations are opt-in."""
        self.assertEqual([c[1] for c in gb.PLDI_DELTA_COLUMNS_FOLD],
                         ["$\\Delta^{A}_{m}$", "$\\Delta^{A}_{t}$",
                          "$\\Delta^{S}_{m}$", "$\\Delta^{S}_{t}$"])
        _out, cells = self._row("fold")
        # Percent of the FEATURE, i.e. (speedup - 1) x 100:
        #   0.13->0.08 = +62.5%   0.08->0.05 = +60%
        #   0.24->0.16 = +50%     0.16->0.12 = +33.33%
        # The mutability columns must subtract from the no-TCO immutable
        # configs, which the fixture gives times of their own: reading
        # aos_imm/soa_imm instead would report +25% and +66.67%.
        self.assertEqual(cells,
                         ["+62.5\\%", "+60\\%", "+50\\%", "+33.33\\%"])

    def test_map_table_carries_forward_every_fold_column(self):
        # Both layouts' cursor/TCO deltas carry forward, each at the head of
        # its own layout group.
        for col in gb.PLDI_DELTA_COLUMNS_FOLD:
            self.assertIn(col, gb.PLDI_DELTA_COLUMNS_MAP,
                          "fold column %s did not carry forward" % col[1])
        # Each layout's fold columns head that layout's group in the map
        # table, so a reader moving between the two tables meets them in
        # the same order.
        for layout in ("AoS", "SoA"):
            fold = [c[1] for c in gb.PLDI_DELTA_COLUMNS_FOLD if c[0] == layout]
            mapped = [c[1] for c in gb.PLDI_DELTA_COLUMNS_MAP if c[0] == layout]
            self.assertEqual(mapped[:len(fold)], fold)

    def test_map_table_has_the_eight_requested_columns(self):
        """The default carries no auto-vectorizer column at all."""
        self.assertEqual(
            [c[1] for c in gb.PLDI_DELTA_COLUMNS_MAP],
            ["$\\Delta^{A}_{m}$", "$\\Delta^{A}_{t}$", "$\\Delta^{A}_{\\ell}$",
             "$\\Delta^{S}_{m}$", "$\\Delta^{S}_{t}$", "$\\Delta^{S}_{\\ell}$",
             "$\\Delta^{S}_{b}$", "$\\Delta^{S}_{v}$"])
        _out, cells = self._row("map")
        self.assertEqual(len(cells), 8)

    def test_delta_subscripts_reuse_the_runtime_symbol_vocabulary(self):
        # A delta column must not invent a letter for a feature the
        # configuration symbols already name -- a reader who has learned
        # Table 2 should be able to read a delta column unaided.
        import re
        # Longest first, so `av' is one atom rather than `a' + `v' and
        # `\ell' is not mistaken for `e'.
        atoms = ["\\ell", "av", "b", "i", "m", "r", "t", "v"]

        def decomposes(token):
            # A token may carry the same +/- state marker the configuration
            # symbols use, so $\\Delta^{A}_{\\ell|+av}$ says "loopification,
            # measured where the auto-vectorizer is on".
            token = token.lstrip("+-")
            """A token may NAME one feature or COMBINE several, the way the
            configuration symbols do: $A_{rm}$ is recursive + mutable, so
            $\\Delta^{A}_{av|rm}$ says the auto-vectorizer on top of it."""
            rest = token.replace(" ", "")
            while rest:
                for atom in atoms:
                    if rest.startswith(atom):
                        rest = rest[len(atom):]
                        break
                else:
                    return False
            return True

        for _l, sym, _b, _f, _d in (gb.PLDI_DELTA_COLUMNS_FOLD
                                    + gb.PLDI_DELTA_COLUMNS_MAP):
            subscript = re.search(r"_\{([^}]*)\}", sym).group(1)
            for token in subscript.split("|"):
                self.assertTrue(decomposes(token),
                                "%s uses %r, which names no configuration "
                                "feature" % (sym, token))

    def test_c_auto_vectorization_is_spelled_av_everywhere(self):
        """The default has no auto-vectorizer column at all; the opt-in ones
        spell the knob `av' and say what it was added on top of, never `c'."""
        self.assertNotIn("av", " ".join(c[1] for c in gb.PLDI_DELTA_COLUMNS_MAP))
        gb.apply_av_variants(("fold", "loopified"))
        self.addCleanup(importlib.reload, gb)
        syms = [c[1] for c in gb.PLDI_DELTA_COLUMNS_MAP]
        for want in ("$\\Delta^{A}_{av|rm}$", "$\\Delta^{A}_{av|\\ell}$",
                     "$\\Delta^{S}_{av|rm}$", "$\\Delta^{S}_{av|\\ell}$"):
            self.assertIn(want, syms)
        for sym in syms:
            self.assertNotIn("_{c}", sym)
            self.assertNotIn("c|", sym)
            self.assertNotIn("|c}", sym)
    def test_each_layout_group_is_contiguous(self):
        # The renderer builds \cmidrule spans by scanning for layout
        # changes, so a group split in two would silently produce three
        # spanning headers instead of two.
        layouts = [c[0] for c in gb.PLDI_DELTA_COLUMNS_MAP]
        self.assertEqual(layouts, sorted(layouts, key=["AoS", "SoA"].index))

    def test_every_column_subtracts_the_configurations_it_claims_to(self):
        for _layout, sym, base, feat, _desc in gb.PLDI_DELTA_COLUMNS_MAP:
            for cfg in (base, feat):
                self.assertIn(cfg, self.TIMES, "%s names unknown config %r" % (sym, cfg))
            self.assertNotEqual(base, feat, "%s subtracts a config from itself" % sym)

    def test_positive_always_means_the_feature_helped(self):
        _out, cells = self._row("map")
        by_sym = dict(zip([c[1] for c in gb.PLDI_DELTA_COLUMNS_MAP], cells))
        # Every feature in the fixture helps except Gibbon vectorization,
        # which is 0.06 -> 0.07.
        self.assertEqual(by_sym["$\\Delta^{S}_{\\ell}$"], "+20\\%")     # (.12-.10)/.10
        self.assertEqual(by_sym["$\\Delta^{S}_{b}$"], "+66.67\\%")   # (.10-.06)/.06
        self.assertEqual(by_sym["$\\Delta^{S}_{v}$"], "$-$14.29\\%") # (.06-.07)/.07

    def test_a_hindering_feature_is_visible_as_a_negative_not_a_magnitude(self):
        # The reason these are signed: |0.06 - 0.07| = 0.01 is
        # indistinguishable from a 0.01 improvement.
        _out, cells = self._row("map")
        self.assertIn("$-$", "".join(cells),
                      "a feature that cost time did not render as negative")

    def test_missing_either_operand_renders_dash(self):
        times = dict(self.TIMES)
        del times["aos_imm"]
        results = self._results(times)
        self.assertEqual(
            gb._pldi_delta_cell(results, "aos_imm", "aos_mut_notco", "g"), "--")
        # ... and the rest of the row still computes.
        self.assertEqual(
            gb._pldi_delta_cell(results, "aos_mut_notco", "aos_mut", "g"), "+60\\%")

    def test_unverified_operand_never_contributes_a_number(self):
        results = self._results()
        results["aos_imm"] = _make_result("P.hs", "aos_imm", {
            "g": {"median_time": 999.0, "pass_type": "fold"}}, verified=False)
        self.assertEqual(
            gb._pldi_delta_cell(results, "aos_imm", "aos_mut_notco", "g"), "--")

    def test_signed_formatter(self):
        self.assertEqual(gb._signed_sig4(0.0246123), "+0.02461")
        self.assertEqual(gb._signed_sig4(-0.0246123), "$-$0.02461")
        self.assertEqual(gb._signed_sig4(None), "--")

    def test_percentages_are_of_the_feature_not_the_baseline(self):
        # (baseline - feature) / FEATURE, which is identically
        # (speedup - 1) x 100.
        self.assertEqual(gb._signed_percent(0.10, 0.08), "+25\\%")
        self.assertEqual(gb._signed_percent(0.08, 0.10), "$-$20\\%")
        self.assertEqual(gb._signed_percent(0.05, 0.05), "+0\\%")
        # A feature that doubles the runtime reads -50%, not -100%: with the
        # feature in the denominator it is SLOWDOWNS that saturate.
        self.assertEqual(gb._signed_percent(0.05, 0.10), "$-$50\\%")

    def test_the_scale_does_not_saturate_on_large_wins(self):
        # The whole reason for the feature denominator. Against the baseline
        # an 8x win reads 87.5% and a 100x win 99%, so the two are nearly
        # indistinguishable; against the feature they are far apart.
        self.assertEqual(gb._signed_percent(0.80, 0.10), "+700\\%")
        self.assertEqual(gb._signed_percent(10.0, 0.10), "+9900\\%")

    def test_percentage_needs_a_usable_denominator(self):
        # The denominator is the FEATURE, so that is what has to be
        # positive; must not raise ZeroDivisionError.
        self.assertEqual(gb._signed_percent(0.05, 0.0), "--")
        self.assertEqual(gb._signed_percent(None, 0.05), "--")
        self.assertEqual(gb._signed_percent(0.05, None), "--")
        # A zero BASELINE still divides -- it is the numerator now.
        self.assertEqual(gb._signed_percent(0.0, 0.05), "$-$100\\%")

    def test_percentages_are_scale_free(self):
        # The point of normalizing: two passes 1000x apart in absolute time
        # that gained the same fraction report the SAME number, which raw
        # seconds could never show.
        self.assertEqual(gb._signed_percent(1.0, 0.75),
                         gb._signed_percent(0.001, 0.00075))

    def test_legend_defines_every_delta_column(self):
        buf = io.StringIO()
        gb._table_pldi_delta_legend(buf)
        out = buf.getvalue()
        self.assertIn("\\label{tab:pldi-delta-legend}", out)
        for _l, sym, _b, _f, _d in (gb.PLDI_DELTA_COLUMNS_FOLD
                                    + gb.PLDI_DELTA_COLUMNS_MAP):
            self.assertIn(sym, out, "legend does not define %s" % sym)

    def test_delta_tables_reference_their_legend_and_their_timing_table(self):
        for kind in ("fold", "map"):
            out, _cells = self._row(kind)
            self.assertIn("\\ref{tab:pldi-delta-legend}", out)
            self.assertIn("\\ref{tab:pldi-%s-P}" % kind, out)
            self.assertIn("\\label{tab:pldi-%s-delta-P}" % kind, out)

    def test_no_delta_table_when_the_program_has_no_passes_of_that_type(self):
        results = {"aos_mut": _make_result("P.hs", "aos_mut", {
            "g": {"median_time": 0.01, "pass_type": "fold"}})}
        buf = io.StringIO()
        gb._table_pldi_map_deltas(buf, "P.hs", results)
        self.assertEqual(buf.getvalue(), "")


class TestVanillaSummaryTable(unittest.TestCase):
    """A second copy of Table 1 whose AoS side is stock Gibbon (immutable
    cursors, nothing enabled) instead of AoS's own best configuration, so
    the speedups read as "what SoA buys over the compiler as it ships"."""

    def _mk(self, cfg, fold, mp):
        res = _make_result("P.hs", cfg, {
            "g": {"median_time": fold, "pass_type": "fold"},
            "m": {"median_time": mp, "pass_type": "map"}})
        res.adt_fields = 4
        res.adt_info = {"soa_total_buffers": 5, "type_name": "T"}
        return res

    def _tex(self):
        import tempfile
        pldi = {"P.hs": {
            "aos_imm": self._mk("aos_imm", 0.40, 0.60),                      # 1.00
            gb.SUMMARY_LOOPIFIED_AOS: self._mk(gb.SUMMARY_LOOPIFIED_AOS, 0.20, 0.30),  # 0.50
            gb.SUMMARY_LOOPIFIED_SOA: self._mk(gb.SUMMARY_LOOPIFIED_SOA, 0.10, 0.15),  # 0.25
        }}
        with tempfile.TemporaryDirectory() as d:
            out = Path(d) / "t.tex"
            gb.write_latex_tables([(self._mk("aos", 9, 9), self._mk("soa", 9, 9))],
                                  out, None, pldi_variant_results=pldi)
            return out.read_text()

    def _block(self, tex, label):
        return tex[tex.index("\\label{%s}" % label):]

    def test_vanilla_config_has_no_gibbon_optimization(self):
        """No Gibbon optimization at all -- and, like every column that does
        not carry $+av$, the C auto-vectorizer off. The vectorizer is held
        off on both sides of every comparison except the $+av$ columns, so
        that it cannot be credited to whichever Gibbon optimization is being
        measured beside it."""
        self.assertEqual(gb.SUMMARY_VANILLA_AOS, "aos_imm")
        cfg = gb.PLDI_MAP_CONFIGS["aos"][gb.SUMMARY_VANILLA_AOS]
        self.assertFalse(cfg.get("use_mutable_cursors", False))
        self.assertFalse(cfg.get("enable_loopification", False))
        self.assertFalse(cfg.get("enable_vectorization", False))
        # The C auto-vectorizer is on, as in every default configuration:
        # a disabled backend would make this a handicapped baseline.
        self.assertNotIn("use_no_gcc_vec", cfg)

    def test_both_summary_tables_are_emitted(self):
        tex = self._tex()
        self.assertIn("\\label{tab:summary}", tex)
        self.assertIn("\\label{tab:summary-vs-vanilla}", tex)

    def test_only_the_aos_side_differs(self):
        tex = self._tex()
        vanilla = self._block(tex, "tab:summary-vs-vanilla")
        header = [l for l in vanilla.splitlines() if "(s)" in l][0]
        self.assertIn(gb.PLDI_COL_SYMBOLS["aos_imm"], header)
        self.assertNotIn(gb.PLDI_COL_SYMBOLS[gb.SUMMARY_LOOPIFIED_AOS], header)
        # SoA side is unchanged.
        self.assertIn(gb.PLDI_COL_SYMBOLS[gb.SUMMARY_LOOPIFIED_SOA], header)

    def test_it_reads_the_vanilla_numbers_not_the_loopified_ones(self):
        tex = self._tex()
        loop_row = [l for l in self._block(tex, "tab:summary").splitlines()
                    if l.startswith("P &")][0]
        vanilla_row = [l for l in self._block(tex, "tab:summary-vs-vanilla").splitlines()
                       if l.startswith("P &")][0]
        # loopified AoS end-to-end 0.50 vs SoA 0.25 -> 2.00x
        self.assertIn("0.5000", loop_row)
        self.assertIn("2.00$\\times$", loop_row)
        # vanilla AoS end-to-end 1.00 vs the SAME SoA 0.25 -> 4.00x
        self.assertIn("1.000", vanilla_row)
        self.assertIn("4.00$\\times$", vanilla_row)

    def test_same_three_groups_and_shape_as_table_one(self):
        tex = self._tex()
        vanilla = self._block(tex, "tab:summary-vs-vanilla")
        for group in ("End-to-end", "Fold passes", "Map passes"):
            self.assertIn("\\multicolumn{3}{c}{\\textbf{%s}}" % group, vanilla)
        self.assertIn("\\begin{tabular}{l c c r r r r r r r r r}", vanilla)

    def test_caption_names_both_configurations_and_the_baseline_framing(self):
        vanilla = self._block(self._tex(), "tab:summary-vs-vanilla")
        caption = vanilla[:vanilla.index("\\label")] if "\\label" in vanilla[:1] else \
            self._tex()[:self._tex().index("\\label{tab:summary-vs-vanilla}")]
        caption = caption[caption.rindex("\\caption{"):]
        self.assertIn(gb.PLDI_ROW_LABELS["aos_imm"], caption)
        self.assertIn(gb.PLDI_ROW_LABELS[gb.SUMMARY_LOOPIFIED_SOA], caption)
        self.assertIn("vanilla Gibbon", caption)
        # The loopification caveat belongs only to the loopified table.
        self.assertNotIn("Nothing in a fold is loopifiable", caption)

    def test_loopified_table_keeps_its_fold_caveat(self):
        tex = self._tex()
        caption = tex[:tex.index("\\label{tab:summary}")]
        caption = caption[caption.rindex("\\caption{"):]
        self.assertIn("Nothing in a fold is loopifiable", caption)

    def test_no_vanilla_table_without_pldi_results(self):
        import tempfile
        with tempfile.TemporaryDirectory() as d:
            out = Path(d) / "t.tex"
            gb.write_latex_tables([(self._mk("aos", 9, 9), self._mk("soa", 9, 9))],
                                  out, None)
            self.assertNotIn("tab:summary-vs-vanilla", out.read_text())


class TestPldiMatrixSerialisation(unittest.TestCase):
    """A configuration that compiled and then failed must leave enough behind
    to diagnose it after the run is over."""

    @staticmethod
    def _res(program, cfg, compiled, ran, rc=None, out=None):
        r = gb.BenchmarkResult(program, cfg)
        r.compile_success, r.run_success = compiled, ran
        r.run_returncode, r.output = rc, out
        return r

    def _matrix(self):
        return {"List.hs": {
            "aos_mut": self._res("List.hs", "aos_mut", True, False, rc=1, out="tag error\n"),
            "aos_imm": self._res("List.hs", "aos_imm", True, False, rc=-11, out=""),
            "soa_mut": self._res("List.hs", "soa_mut", True, True, rc=0, out="fine"),
        }}

    def _write(self):
        import json, tempfile, pathlib
        d = tempfile.mkdtemp()
        out = pathlib.Path(d) / "m.json"
        gb.write_pldi_matrix_json(self._matrix(), out, {"repo": {"head": "abc"}})
        return json.loads(out.read_text())

    def test_a_failed_run_records_its_return_code(self):
        r = self._write()["results"]["List.hs"]
        self.assertEqual(r["aos_mut"]["run_returncode"], 1)

    def test_a_signal_is_distinguishable_from_a_nonzero_exit(self):
        r = self._write()["results"]["List.hs"]
        self.assertEqual(r["aos_imm"]["run_returncode"], -11)
        self.assertNotEqual(r["aos_mut"]["run_returncode"],
                            r["aos_imm"]["run_returncode"])

    def test_a_failed_run_keeps_what_it_printed(self):
        r = self._write()["results"]["List.hs"]
        self.assertIn("tag error", r["aos_mut"]["failure_output_tail"])

    def test_a_successful_run_carries_no_output_tail(self):
        r = self._write()["results"]["List.hs"]
        self.assertNotIn("failure_output_tail", r["soa_mut"])

    def test_failures_are_listed_by_program_and_configuration(self):
        self.assertEqual(self._write()["run_failures"],
                         ["List.hs:aos_imm", "List.hs:aos_mut"])

    def test_every_configuration_is_serialised_not_just_failures(self):
        self.assertEqual(sorted(self._write()["results"]["List.hs"]), 
                         ["aos_imm", "aos_mut", "soa_mut"])


# ---------------------------------------------------------------------------
# Waterfall figures: the per-program speedup decomposition.
#
# The figures themselves need matplotlib, but everything that can be WRONG
# about them is in the data layer -- whether the chain is contiguous, whether
# the segments sum to the bar, and whether an unmeasured link is dropped
# rather than quietly producing a partial bar. That is all tested here
# without drawing anything.
# ---------------------------------------------------------------------------
class TestRoundAggregation(unittest.TestCase):

    @staticmethod
    def _rounds(times):
        return [{"median_time": t, "mean_time": t + 1, "n": 21,
                 "pass_type": "fold"} for t in times]

    def test_the_reported_time_is_the_median_across_rounds(self):
        agg = gb.aggregate_rounds(self._rounds([0.10, 0.30, 0.20]))
        self.assertAlmostEqual(agg["median_time"], 0.20)
        self.assertEqual(agg["rounds"], 3)
        self.assertEqual(sorted(agg["round_medians"]), [0.10, 0.20, 0.30])

    def test_the_other_fields_come_from_one_real_round(self):
        """Not a blend: a row mixing the median of one round with the mean
        of another describes a run that never happened."""
        agg = gb.aggregate_rounds(self._rounds([0.10, 0.30, 0.20]))
        self.assertAlmostEqual(agg["mean_time"], 1.20)

    def test_a_between_round_interval_is_reported(self):
        agg = gb.aggregate_rounds(self._rounds([0.10, 0.11, 0.12]))
        self.assertIn("between_round_ci95_pct", agg)
        self.assertGreater(agg["between_round_spread_pct"], 0.0)

    def test_two_rounds_do_not_fabricate_a_confidence_interval(self):
        agg = gb.aggregate_rounds(self._rounds([0.10, 0.12]))
        self.assertNotIn("between_round_ci95_pct", agg)
        self.assertIn("between_round_spread_pct", agg)

    def test_one_round_reports_no_spread_at_all(self):
        agg = gb.aggregate_rounds(self._rounds([0.10]))
        self.assertAlmostEqual(agg["median_time"], 0.10)
        self.assertNotIn("between_round_spread_pct", agg)

    def test_rounds_that_did_not_report_the_pass_are_ignored(self):
        """A pass missing from one round must not be averaged in as zero."""
        agg = gb.aggregate_rounds([None] + self._rounds([0.20, 0.20]))
        self.assertEqual(agg["rounds"], 2)
        self.assertAlmostEqual(agg["median_time"], 0.20)

    def test_a_pass_no_round_measured_stays_unmeasured(self):
        self.assertEqual(gb.aggregate_rounds([None, None]), {})

    def test_whole_program_rounds_default_to_one(self):
        """A pass timing is already the median of --iterations within a run,
        and the whole-program wall time no longer feeds the end-to-end
        figure, so repeating the whole executable buys little."""
        import inspect
        sig = inspect.signature(gb.collect_pldi_variant_results)
        self.assertEqual(sig.parameters["pass_rounds"].default, 1)
        self.assertNotIn("measure_rounds", sig.parameters)

    def test_three_rounds_reject_a_single_bad_sample(self):
        """One anomalous round put a 0.63x buffer-sharing cell in the
        end-to-end figure where the true value is 1.04x."""
        agg = gb.aggregate_rounds([{"median_time": t, "pass_type": "map"}
                                   for t in (0.55, 0.98, 0.55)])
        self.assertAlmostEqual(agg["median_time"], 0.55)

    def test_two_rounds_would_not_have(self):
        """With two the median sits between the good and the bad sample, so
        the outlier still moves the reported number."""
        agg = gb.aggregate_rounds([{"median_time": t, "pass_type": "map"}
                                   for t in (0.55, 0.98)])
        self.assertGreater(agg["median_time"], 0.7)

    def test_the_collector_compiles_before_it_runs(self):
        """Interleaving is only possible if every configuration is built
        first; compiling and running each in turn fixes the order."""
        import inspect
        src = inspect.getsource(gb.collect_pldi_variant_results)
        self.assertIn("run_rounds(jobs", src)
        self.assertLess(src.index("compile_one("), src.index("run_rounds(jobs"))


# ---------------------------------------------------------------------------
# --use-width: selecting narrowed payload variants.
# ---------------------------------------------------------------------------
class TestWidthSelection(unittest.TestCase):

    def setUp(self):
        import tempfile
        self._tmp = tempfile.TemporaryDirectory()
        self.dir = Path(self._tmp.name)
        (self.dir / "SOA").mkdir()
        self.addCleanup(self._tmp.cleanup)

    def _write(self, name, body):
        (self.dir / "SOA" / name).write_text(body)

    WIDE = "data T = Leaf Int64\n       | Node T T\n\nf :: T -> Int\n"
    NARROW = "data T = Leaf Int32\n       | Node T T\n\nf :: T -> Int\n"
    # A 64-bit LOOP COUNTER, no 64-bit field: costs no buffer width.
    COUNTER_ONLY = "data T = Leaf Int8\n       | Node T T\n\nmk :: Int -> Int -> T\n"

    def test_the_name_mapping(self):
        self.assertEqual(gb.width_program_name("Compiler.hs", 32), "Compiler_i32.hs")
        self.assertEqual(gb.width_program_name("Compiler.hs", 8), "Compiler_i8.hs")

    def test_64_is_the_unsuffixed_source(self):
        """The default width must name the files that exist today, so an
        unflagged run is byte-for-byte the run it was before."""
        self.assertEqual(gb.width_suffix(64), "")
        self.assertEqual(gb.width_program_name("Compiler.hs", 64), "Compiler.hs")

    def test_64_selects_everything_unchanged(self):
        self._write("P.hs", self.WIDE)
        sel, skipped = gb.apply_width_selection(["P.hs"], self.dir, 64)
        self.assertEqual((sel, skipped), (["P.hs"], []))

    def test_a_program_with_a_variant_is_swapped(self):
        self._write("P.hs", self.WIDE)
        self._write("P_i32.hs", self.NARROW)
        self.assertEqual(gb.apply_width_selection(["P.hs"], self.dir, 32),
                         (["P_i32.hs"], []))

    def test_a_program_that_cannot_represent_is_skipped_not_substituted(self):
        """Its fields cannot hold their values that narrow. Falling back to
        the wide source would put two widths in one report."""
        self._write("P.hs", self.WIDE)
        self._write("P_i32.hs", self.NARROW)
        sel, skipped = gb.apply_width_selection(["P.hs"], self.dir, 8)
        self.assertEqual(sel, [])
        self.assertEqual(skipped, ["P.hs"])

    def test_the_deliberately_wide_benchmarks_are_left_alone(self):
        for name in gb.NARROW_EXEMPT:
            self._write(name, self.WIDE)
        sel, skipped = gb.apply_width_selection(list(gb.NARROW_EXEMPT), self.dir, 32)
        self.assertEqual(sel, list(gb.NARROW_EXEMPT))
        self.assertEqual(skipped, [])

    def test_a_program_with_no_wide_field_passes_through(self):
        self._write("P.hs", self.COUNTER_ONLY)
        self.assertEqual(gb.apply_width_selection(["P.hs"], self.dir, 16),
                         (["P.hs"], []))

    def test_a_loop_counter_is_not_a_payload_field(self):
        self._write("P.hs", self.COUNTER_ONLY)
        self.assertFalse(gb.program_has_wide_payload(self.dir, "P.hs"))

    def test_a_declared_field_is(self):
        self._write("P.hs", self.WIDE)
        self.assertTrue(gb.program_has_wide_payload(self.dir, "P.hs"))

    def test_every_width_output_path_is_distinct(self):
        """Four campaigns writing one performance_table.tex would leave only
        the last width's tables on disk."""
        paths = {gb._width_tagged(Path("performance_table.tex"), w)
                 for w in gb.PAYLOAD_WIDTHS}
        self.assertEqual(len(paths), len(gb.PAYLOAD_WIDTHS))

    def test_the_sweep_covers_every_width(self):
        self.assertEqual(tuple(gb.PAYLOAD_WIDTHS), (64, 32, 16, 8))
        self.assertIn(gb.DEFAULT_PAYLOAD_WIDTH, gb.PAYLOAD_WIDTHS)

    def test_real_campaign_programs_are_classified_as_expected(self):
        """Guards the classifier against the actual sources, so a future
        edit that moves a field type cannot silently change which programs
        a width sweep demands variants for."""
        real = Path(__file__).resolve().parent / "programs"
        if not (real / "SOA" / "Compiler.hs").exists():
            self.skipTest("benchmark sources not present")
        for name, expected in (("Compiler.hs", True), ("KDTree.hs", True),
                               ("Add1TreeInt8.hs", False),
                               ("OctTree_clearFlags.hs", False)):
            self.assertEqual(gb.program_has_wide_payload(real, name), expected, name)



class TestSymbolConventions(unittest.TestCase):
    """One marker for OFF and one for ON, everywhere.

    The table mixed $\\neg t$ for a disabled tail-call optimization with
    $-av$ for a disabled auto-vectorizer, so a reader had to learn that two
    different glyphs meant the same thing."""

    def test_no_symbol_uses_neg(self):
        for cfg, sym in gb.PLDI_COL_SYMBOLS.items():
            self.assertNotIn("\\neg", sym, cfg)

    def test_disabled_is_minus_and_enabled_is_plus(self):
        import re
        for cfg, sym in gb.PLDI_COL_SYMBOLS.items():
            sup = re.search(r"\^\{\\scriptscriptstyle ([^}]*)\}", sym)
            if not sup:
                continue
            for mark in sup.group(1).split(","):
                self.assertRegex(mark.strip(), r"^[-+](t|av)$", cfg)

    def test_the_legend_does_not_teach_a_glyph_it_no_longer_uses(self):
        buf = io.StringIO()
        gb._table_pldi_legend(buf)
        self.assertNotIn("\\neg", buf.getvalue())


class TestColumnOrder(unittest.TestCase):

    def test_columns_follow_the_delta_chain(self):
        """Left to right crosses the same steps the delta table measures,
        so the two tables can be read against each other."""
        for layout, prefix in (("aos", "aos"), ("soa", "soa")):
            self.assertEqual(
                list(gb.PLDI_FOLD_CONFIGS[layout]),
                ["%s_imm_notco" % prefix, "%s_imm" % prefix,
                 "%s_mut_notco" % prefix, "%s_mut" % prefix])

    def test_mutable_sits_after_mutable_without_tail_calls(self):
        for layout in ("aos", "soa"):
            keys = list(gb.PLDI_FOLD_CONFIGS[layout])
            mut = [k for k in keys if k.endswith("_mut")][0]
            notco = [k for k in keys if k.endswith("_mut_notco")][0]
            self.assertGreater(keys.index(mut), keys.index(notco), layout)

    def test_the_delta_chain_walks_the_columns_in_order(self):
        """Each fold delta column's baseline and feature are adjacent
        columns, in that order -- which is what makes the ordering
        meaningful rather than decorative."""
        for layout, cols in (("aos", [c for c in gb.PLDI_DELTA_COLUMNS_FOLD
                                      if c[0] == "AoS"]),
                             ("soa", [c for c in gb.PLDI_DELTA_COLUMNS_FOLD
                                      if c[0] == "SoA"])):
            keys = list(gb.PLDI_FOLD_CONFIGS[layout])
            for _l, sym, base, feat, _d in cols:
                self.assertLess(keys.index(base), keys.index(feat), sym)


class TestAvVariantsDefault(unittest.TestCase):
    """With no --av-variants the C auto-vectorizer is on everywhere and
    mentioned nowhere. That is what an ordinary build does, and it means no
    delta in a default run can confuse the vectorizer with the optimization
    it is measuring -- the defect that reported loopification at 0.40x on
    ArithmeticIntensityInt16 when it is worth 1.07x."""

    def test_no_configuration_disables_it(self):
        for layout in gb.PLDI_MAP_CONFIGS.values():
            for cfg, kwargs in layout.items():
                self.assertNotIn("use_no_gcc_vec", kwargs, cfg)

    def test_no_symbol_or_label_mentions_it(self):
        for cfg, sym in gb.PLDI_COL_SYMBOLS.items():
            self.assertNotIn("av", sym, cfg)
        for cfg, label in gb.PLDI_ROW_LABELS.items():
            self.assertNotIn("auto-vector", label, cfg)

    def test_no_delta_column_measures_it(self):
        for _l, sym, _b, _f, _d in (gb.PLDI_DELTA_COLUMNS_FOLD
                                    + gb.PLDI_DELTA_COLUMNS_MAP):
            self.assertNotIn("av", sym, sym)

    def test_every_delta_holds_it_constant_trivially(self):
        """Vacuously true while nothing disables it -- asserted so that
        adding a -av configuration to the default set fails here rather than
        silently reintroducing the defect."""
        def off(cfg):
            return any(lay[cfg].get("use_no_gcc_vec")
                       for lay in gb.PLDI_MAP_CONFIGS.values() if cfg in lay)
        for _l, sym, base, feat, _d in (gb.PLDI_DELTA_COLUMNS_FOLD
                                        + gb.PLDI_DELTA_COLUMNS_MAP):
            self.assertEqual(off(base), off(feat), sym)


class TestPldiSubmissionBuildsAvTwins(unittest.TestCase):
    """The compact stage heatmaps need every -av twin."""

    def test_pldi_submission_defaults_to_all(self):
        args = gb.build_parser().parse_args(["--generate-paper", "--pldi-submission"])
        self.assertEqual(gb.default_av_variants(args.av_variants,
                                                args.pldi_submission), "all")

    def test_an_explicit_choice_wins(self):
        for choice in ("fold", "none"):
            args = gb.build_parser().parse_args(
                ["--generate-paper", "--pldi-submission", "--av-variants", choice])
            self.assertEqual(gb.default_av_variants(args.av_variants,
                                                    args.pldi_submission), choice)
        self.assertEqual(gb.resolve_av_variants("none"), ())

    def test_other_runs_stay_without_twins(self):
        args = gb.build_parser().parse_args([])
        self.assertIsNone(gb.default_av_variants(args.av_variants,
                                                 args.pldi_submission))


class TestAvVariants(unittest.TestCase):
    """--av-variants adds the ablations, each with the column that contrasts
    it against its unmarked default."""

    def setUp(self):
        self.addCleanup(importlib.reload, gb)

    @staticmethod
    def _off(cfg):
        return any(lay[cfg].get("use_no_gcc_vec")
                   for lay in gb.PLDI_MAP_CONFIGS.values() if cfg in lay)

    def _syms(self):
        return [c[1] for c in gb.PLDI_DELTA_COLUMNS_MAP]

    def test_all_expands_to_both(self):
        self.assertEqual(gb.resolve_av_variants("all"), ("fold", "loopified"))
        self.assertEqual(gb.resolve_av_variants(None), ())
        self.assertEqual(gb.resolve_av_variants("fold"), ("fold",))

    def test_fold_twins_only_the_recursive_configuration(self):
        gb.apply_av_variants(("fold",))
        self.assertTrue(self._off("aos_mut_navec"))
        self.assertIn("aos_mut_navec", gb.PLDI_FOLD_CONFIGS["aos"])
        self.assertNotIn("aos_loop_navec", gb.PLDI_MAP_CONFIGS["aos"])
        self.assertIn("$\\Delta^{A}_{av|rm}$",
                      [c[1] for c in gb.PLDI_DELTA_COLUMNS_FOLD])

    def test_loopified_gives_the_map_table_its_av_columns(self):
        """The choices name a TABLE: `loopified' twins everything the map
        table shows, the recursive baseline included -- without it,
        loopification could not be measured with the vectorizer off."""
        gb.apply_av_variants(("loopified",))
        self.assertTrue(self._off("aos_loop_navec"))
        self.assertTrue(self._off("aos_mut_navec"))
        self.assertIn("aos_mut_navec", gb.PLDI_MAP_CONFIGS["aos"])
        # The FOLD table is left alone: that is what `fold' is for.
        self.assertNotIn("aos_mut_navec", gb.PLDI_FOLD_CONFIGS["aos"])
        self.assertNotIn("av", " ".join(c[1] for c in gb.PLDI_DELTA_COLUMNS_FOLD))

    def test_each_twin_brings_its_contrast_column(self):
        gb.apply_av_variants(("fold", "loopified"))
        for want in ("$\\Delta^{A}_{av|rm}$", "$\\Delta^{S}_{av|rm}$",
                     "$\\Delta^{A}_{av|\\ell}$", "$\\Delta^{S}_{av|\\ell}$",
                     "$\\Delta^{S}_{av|\\ell b}$",
                     "$\\Delta^{S}_{av|\\ell bv}$"):
            self.assertIn(want, self._syms())

    def test_only_the_av_columns_move_the_vectorizer(self):
        gb.apply_av_variants(("fold", "loopified"))
        for _l, sym, base, feat, _d in (gb.PLDI_DELTA_COLUMNS_FOLD
                                        + gb.PLDI_DELTA_COLUMNS_MAP):
            moves = self._off(base) != self._off(feat)
            self.assertEqual(moves, "av|" in sym, sym)

    def test_every_gibbon_optimization_is_isolated_from_the_vectorizer(self):
        """Each keeps its name and moves to the vectorizer-off pair.

        Measuring Gibbon's SIMD vectorization on top of gcc's reports only
        what is left after the backend has already vectorized the loop:
        geomean 0.993x, helping 0 of 10 passes, against 1.823x and up to
        8.05x for the same optimization measured without it. The whole
        chain moves together so that it still telescopes."""
        gb.apply_av_variants(("loopified",))
        by = {c[1]: c for c in gb.PLDI_DELTA_COLUMNS_MAP}
        for sym in ("$\\Delta^{A}_{\\ell}$", "$\\Delta^{S}_{\\ell}$",
                    "$\\Delta^{S}_{b}$", "$\\Delta^{S}_{v}$"):
            self.assertIn(sym, by)
            for cfg in by[sym][2:4]:
                self.assertTrue(self._off(cfg), "%s / %s" % (sym, cfg))

    def test_the_soa_chain_telescopes(self):
        """Each Gibbon-side column starts where the previous one ended, so
        the columns compose. A chain measured half in one vectorizer world
        and half in the other would not."""
        gb.apply_av_variants(("loopified",))
        by = {c[1]: c for c in gb.PLDI_DELTA_COLUMNS_MAP}
        chain = ["$\\Delta^{S}_{\\ell}$", "$\\Delta^{S}_{b}$",
                 "$\\Delta^{S}_{v}$"]
        for earlier, later in zip(chain, chain[1:]):
            self.assertEqual(by[earlier][3], by[later][2],
                             "%s ends at %s but %s starts at %s"
                             % (earlier, by[earlier][3], later, by[later][2]))

    def test_the_backend_gets_its_own_column_at_each_stage(self):
        """What the auto-vectorizer adds is reported, not discarded -- it
        moves out of the Gibbon columns and into the av ones."""
        gb.apply_av_variants(("loopified",))
        by = {c[1]: c for c in gb.PLDI_DELTA_COLUMNS_MAP}
        for sym, stage in (("$\\Delta^{S}_{av|\\ell}$", "soa_loop"),
                           ("$\\Delta^{S}_{av|\\ell b}$", "soa_loop_sbs"),
                           ("$\\Delta^{S}_{av|\\ell bv}$", "soa_loop_sbs_gibvec")):
            base, feat = by[sym][2], by[sym][3]
            self.assertEqual(feat, stage)
            self.assertEqual(base, gb.av_variant_name(stage))
            self.assertTrue(self._off(base))
            self.assertFalse(self._off(feat))

    def test_no_column_qualifies_a_feature_with_a_vectorizer_world(self):
        """`|' means "on top of" in every column -- $\\Delta_{av|\\ell}$ is the
        vectorizer applied to loopified code. A $\\Delta_{\\ell|-av}$ would
        silently switch it to mean "in the world where", and read as
        loopification applied on top of $-av$."""
        gb.apply_av_variants(("fold", "loopified"))
        for _l, sym, _b, _f, _d in (gb.PLDI_DELTA_COLUMNS_FOLD
                                    + gb.PLDI_DELTA_COLUMNS_MAP):
            if "|" in sym:
                self.assertTrue(sym.split("_{", 1)[1].startswith("av|"), sym)

    def test_fold_alone_leaves_one_loopification_column(self):
        """`fold' twins no loopified configuration, so there is only one
        vectorizer world for loopification to be measured in."""
        gb.apply_av_variants(("fold",))
        syms = [c[1] for c in gb.PLDI_DELTA_COLUMNS_MAP]
        self.assertIn("$\\Delta^{A}_{\\ell}$", syms)
        self.assertNotIn("$\\Delta^{A}_{\\ell|-av}$", syms)

    def test_the_layouts_gain_comparable_vectorizer_columns(self):
        """Both loopified, neither shared, vectorizer off then on -- so the
        AoS and SoA columns answer 'does the backend favour one layout' on
        the same terms. The sharing-on SoA column cannot, since AoS has no
        sharing to match it."""
        gb.apply_av_variants(("loopified",))
        by = {c[1]: c for c in gb.PLDI_DELTA_COLUMNS_MAP}
        for sym, layout in (("$\\Delta^{A}_{av|\\ell}$", "aos"),
                            ("$\\Delta^{S}_{av|\\ell}$", "soa")):
            for cfg in by[sym][2:4]:
                kwargs = gb.PLDI_MAP_CONFIGS[layout][cfg]
                self.assertTrue(kwargs["enable_loopification"], cfg)
                self.assertNotIn("enable_selective_buffer_sharing", kwargs, cfg)

    def test_a_marker_keeps_any_marker_already_there(self):
        self.assertEqual(
            gb._with_av_marker("$A_{rm}^{\\scriptscriptstyle -t}$", "-av"),
            "$A_{rm}^{\\scriptscriptstyle -t,-av}$")
        self.assertEqual(gb._with_av_marker("$A_{rm}$", "+av"),
                         "$A_{rm}^{\\scriptscriptstyle +av}$")

    def test_a_marker_replaces_rather_than_stacks(self):
        """Applied twice a symbol must not end up reading `-av,+av'."""
        once = gb._with_av_marker("$A_{rm}$", "-av")
        self.assertEqual(gb._with_av_marker(once, "+av"),
                         "$A_{rm}^{\\scriptscriptstyle +av}$")

    def test_both_halves_of_a_pair_are_marked(self):
        """Once a pair is on the page, leaving the enabled half unmarked
        would make the reader infer it from a neighbour's absence."""
        gb.apply_av_variants(("loopified",))
        self.assertEqual(gb.PLDI_COL_SYMBOLS["soa_loop"],
                         "$S_{\\ell}^{\\scriptscriptstyle +av}$")
        self.assertEqual(gb.PLDI_COL_SYMBOLS["soa_loop_navec"],
                         "$S_{\\ell}^{\\scriptscriptstyle -av}$")

    def test_a_twin_sits_next_to_the_column_it_is_read_against(self):
        """Appended at the end it would sit pages away from its partner."""
        gb.apply_av_variants(("loopified",))
        order = list(gb.PLDI_MAP_CONFIGS["soa"])
        self.assertEqual(
            order,
            ["soa_imm_notco", "soa_imm", "soa_mut_notco",
             "soa_mut_navec", "soa_mut",
             "soa_loop_navec", "soa_loop",
             "soa_loop_sbs_navec", "soa_loop_sbs",
             "soa_loop_sbs_gibvec_navec", "soa_loop_sbs_gibvec"])

    def test_delta_columns_follow_the_same_progression(self):
        """Each contrast column sits beside the step it measures, rather
        than being appended after the columns it belongs among."""
        gb.apply_av_variants(("loopified",))
        soa = [c[1] for c in gb.PLDI_DELTA_COLUMNS_MAP if c[0] == "SoA"]
        self.assertEqual(soa, [
            "$\\Delta^{S}_{m}$", "$\\Delta^{S}_{t}$", "$\\Delta^{S}_{av|rm}$",
            "$\\Delta^{S}_{\\ell}$", "$\\Delta^{S}_{av|\\ell}$",
            "$\\Delta^{S}_{b}$", "$\\Delta^{S}_{av|\\ell b}$",
            "$\\Delta^{S}_{v}$", "$\\Delta^{S}_{av|\\ell bv}$"])

    def test_every_column_varies_one_thing(self):
        """An audit, run as a test: a column whose two configurations differ
        in two compile flags reports both as whatever its subscript names.
        SoA loopification is the one allowed exception -- it cannot run
        without scalar-count footers, which it takes in deferred form."""
        gb.apply_av_variants(("fold", "loopified"))
        def kwargs(cfg):
            for layout in gb.PLDI_MAP_CONFIGS.values():
                if cfg in layout:
                    return layout[cfg]
            raise KeyError(cfg)
        for _l, sym, base, feat, _d in gb.PLDI_DELTA_COLUMNS_MAP:
            kb, kf = kwargs(base), kwargs(feat)
            differ = {k for k in set(kb) | set(kf)
                      if kb.get(k, False) != kf.get(k, False)}
            if sym == "$\\Delta^{S}_{\\ell}$":
                self.assertEqual(differ, {"enable_loopification",
                                          "store_scalar_field_counts",
                                          "defer_scalar_counts"})
            else:
                self.assertEqual(len(differ), 1, "%s varies %s" % (sym, differ))

    def test_layout_groups_stay_contiguous(self):
        """The renderer builds \\cmidrule spans by scanning for layout
        changes, so an interleaved column would produce three spanning
        headers instead of two."""
        gb.apply_av_variants(("fold", "loopified"))
        for cols in (gb.PLDI_DELTA_COLUMNS_FOLD, gb.PLDI_DELTA_COLUMNS_MAP):
            layouts = [c[0] for c in cols]
            self.assertEqual(layouts, sorted(layouts, key=["AoS", "SoA"].index))

    def test_every_added_configuration_has_a_symbol_and_a_label(self):
        gb.apply_av_variants(("fold", "loopified"))
        for layout in gb.PLDI_MAP_CONFIGS.values():
            for cfg in layout:
                self.assertIn(cfg, gb.PLDI_COL_SYMBOLS, cfg)
                self.assertIn(cfg, gb.PLDI_ROW_LABELS, cfg)
        self.assertEqual(len(set(gb.PLDI_COL_SYMBOLS.values())),
                         len(gb.PLDI_COL_SYMBOLS))

    def test_the_label_says_disabled_exactly_when_the_flags_do(self):
        gb.apply_av_variants(("fold", "loopified"))
        for layout in gb.PLDI_MAP_CONFIGS.values():
            for cfg, kwargs in layout.items():
                self.assertEqual(bool(kwargs.get("use_no_gcc_vec")),
                                 "auto-vectorization disabled"
                                 in gb.PLDI_ROW_LABELS[cfg], cfg)


class TestQuickRun(unittest.TestCase):
    """--quick-run: a small representative subset, so a presentational
    change can be checked in minutes rather than hours."""

    class _Args:
        pass

    def _args(self, **kw):
        a = self._Args()
        a.quick_run = True
        a.programs = None
        a.exclude_programs = None
        for attr, _flag in gb.QUICK_RUN_DISABLED:
            setattr(a, attr, False)
        for k, v in kw.items():
            setattr(a, k, v)
        return a

    def _resolve(self, args, default):
        return gb.resolve_program_selection(
            args.programs, args.exclude_programs,
            default_programs=(gb.QUICK_RUN_PROGRAMS if args.quick_run
                              else default),
            programs_dir=Path(__file__).resolve().parent / "programs")

    def test_the_subset_is_the_requested_ten(self):
        self.assertEqual(
            gb.QUICK_RUN_PROGRAMS,
            ["KDTree.hs", "Compiler.hs",
             "Add1TreeInt8.hs", "Add1TreeInt16.hs", "Add1TreeInt32.hs",
             "Add1TreeInt64.hs",
             "ArithmeticIntensityInt8.hs", "ArithmeticIntensityInt16.hs",
             "ArithmeticIntensityInt32.hs", "ArithmeticIntensityInt64.hs"])

    def test_every_subset_program_is_a_real_campaign_program(self):
        """A name that is not in the campaign list would be reported as a
        column of failures rather than as a mistake."""
        full = set(gb.DEFAULT_PROGRAMS) | set(gb.PLDI_EXTRA_PROGRAMS)
        for program in gb.QUICK_RUN_PROGRAMS:
            self.assertIn(program, full, program)

    def test_both_layouts_of_every_subset_program_exist(self):
        root = Path(__file__).resolve().parent / "programs"
        if not (root / "SOA" / "Compiler.hs").exists():
            self.skipTest("benchmark sources not present")
        for program in gb.QUICK_RUN_PROGRAMS:
            for layout in ("AOS", "SOA"):
                self.assertTrue((root / layout / program).exists(),
                                "%s/%s" % (layout, program))

    def test_it_narrows_the_campaign_as_well_as_the_matrix(self):
        """The campaign phase is most of the wall clock, so narrowing only
        the matrix would leave a quick run slow -- and would pair a full
        Table 1 with a partial matrix."""
        args = self._args()
        campaign = self._resolve(args, None)
        matrix = self._resolve(args, gb.DEFAULT_PROGRAMS + gb.PLDI_EXTRA_PROGRAMS)
        self.assertEqual(campaign, gb.QUICK_RUN_PROGRAMS)
        self.assertEqual(matrix, gb.QUICK_RUN_PROGRAMS)

    def test_without_it_nothing_is_narrowed(self):
        args = self._args(quick_run=False)
        self.assertEqual(
            len(self._resolve(args, gb.DEFAULT_PROGRAMS + gb.PLDI_EXTRA_PROGRAMS)),
            len(gb.DEFAULT_PROGRAMS + gb.PLDI_EXTRA_PROGRAMS))

    def test_an_explicit_program_list_still_wins(self):
        args = self._args(programs=["Compiler.hs"])
        self.assertEqual(self._resolve(args, None), ["Compiler.hs"])

    def test_exclusions_still_apply_to_the_subset(self):
        args = self._args(exclude_programs=["Add1Tree*"])
        left = self._resolve(args, None)
        self.assertNotIn("Add1TreeInt8.hs", left)
        self.assertIn("KDTree.hs", left)

    def test_the_extra_phases_are_switched_off(self):
        """Each compiles its own configuration set on top of the matrix, so
        leaving one on would undo the point of the mode."""
        args = self._args(**{attr: True for attr, _f in gb.QUICK_RUN_DISABLED})
        overridden = gb.apply_quick_run(args)
        for attr, flag in gb.QUICK_RUN_DISABLED:
            self.assertFalse(getattr(args, attr), flag)
        self.assertEqual(len(overridden), len(gb.QUICK_RUN_DISABLED))

    def test_it_reports_only_what_it_actually_overrode(self):
        args = self._args(roofline=True)
        self.assertEqual(gb.apply_quick_run(args), ["--roofline"])

    def test_iterations_are_untouched(self):
        """A table that looks like a result should be one. Quick runs have
        fewer numbers, not noisier ones."""
        import inspect
        src = inspect.getsource(gb.apply_quick_run)
        self.assertNotIn("iterations", src)

    def test_the_subset_covers_both_table_shapes_and_every_width(self):
        """A layout problem only shows up if the subset renders the same
        shapes the full report does: a fold-heavy program, a map-heavy one,
        and both width families across all four widths."""
        for width in (8, 16, 32, 64):
            self.assertIn("Add1TreeInt%d.hs" % width, gb.QUICK_RUN_PROGRAMS)
            self.assertIn("ArithmeticIntensityInt%d.hs" % width,
                          gb.QUICK_RUN_PROGRAMS)
        self.assertIn("KDTree.hs", gb.QUICK_RUN_PROGRAMS)
        self.assertIn("Compiler.hs", gb.QUICK_RUN_PROGRAMS)


class TestCompileFailureIsDiagnosable(unittest.TestCase):

    def test_a_failed_compile_records_the_reason(self):
        """A blank table cell is only actionable if the report says why.
        The collector had been passing the compiler's message to the
        qualification but not onto the result, so the JSON's `error' field
        came out empty and a failure could not be diagnosed after the run."""
        import inspect
        src = inspect.getsource(gb.collect_pldi_variant_results)
        head = src[:src.index("qualify_variant(\n                        program, "
                              "cfg_name, source, False, err")]
        self.assertIn("res.error_message = err", head)

    def test_the_serializer_carries_it(self):
        res = _make_result("P.hs", "soa_loop", {})
        res.compile_success = False
        res.error_message = "loopifyTraversals: ... --store-scalar-field-counts"
        rec = gb._ser_result(res)
        self.assertIn("store-scalar-field-counts", rec["error"])


class TestStageFigures(unittest.TestCase):
    """The per-optimization heatmaps: programs down, optimizations across.
    These describe the extended chain (--extended-stages)."""

    MAP_CFGS = ["aos_imm", "aos_mut", "aos_imm_notco", "aos_mut_notco",
                "soa_mut", "soa_mut_notco", "soa_loop", "soa_loop_sbs",
                "soa_loop_sbs_gibvec"]
    ISOLATED = MAP_CFGS + ["soa_mut_navec", "soa_loop_navec",
                           "soa_loop_sbs_navec", "soa_loop_sbs_gibvec_navec"]

    def _matrix(self, times, pass_type="map", pass_name="m"):
        return {"P.hs": {cfg: _make_result(
            "P.hs", cfg, {pass_name: {"median_time": t,
                                      "pass_type": pass_type}})
            for cfg, t in times.items()}}

    def test_every_step_changes_exactly_one_thing(self):
        """The fold chain used to open with aos_imm -> soa_imm_notco, which
        switched layout AND disabled tail calls, and so read 0.47x for
        KDTree where the honest SoA number is 1.62x."""
        def kwargs(cfg):
            for layout in gb.PLDI_MAP_CONFIGS.values():
                if cfg in layout:
                    return layout[cfg]
            # a -av twin the registry does not carry in this process
            base = cfg[:-len(gb.AV_VARIANT_SUFFIX)]
            for layout in gb.PLDI_MAP_CONFIGS.values():
                if base in layout:
                    return dict(layout[base], use_no_gcc_vec=True)
            raise KeyError(cfg)
        for kind in ("fold", "map"):
            for label, source, target in gb._pldi_stage_chain(kind, set(self.ISOLATED), extended=True):
                ks, kt = kwargs(source), kwargs(target)
                differ = {k for k in set(ks) | set(kt)
                          if ks.get(k, False) != kt.get(k, False)}
                # The layout is not a compile flag -- it is which source
                # directory the program was taken from -- so it does not
                # show up in the kwargs and has to be counted separately.
                if source[:3] != target[:3]:
                    differ.add("layout")
                if label == "Loopification" and source.startswith("soa"):
                    # SoA loopification cannot run without scalar-count
                    # footers, which it takes in deferred form.
                    self.assertEqual(differ, {"enable_loopification",
                                              "store_scalar_field_counts",
                                              "defer_scalar_counts"})
                else:
                    self.assertEqual(len(differ), 1,
                                     "%s/%s varies %s" % (kind, label, differ))

    def test_the_fold_chain_ends_at_soa_mutable(self):
        stages = gb._pldi_stage_chain("fold", set(self.ISOLATED), extended=True)
        self.assertEqual(stages[0][1], "aos_imm")
        self.assertEqual(stages[-1][2], "soa_mut")
        self.assertEqual([s[0] for s in stages],
                         ["C tail calls off", "Mutable cursors", "SoA layout",
                          "C tail calls on"])

    def test_the_fold_chain_is_a_strict_prefix_of_the_map_chain(self):
        """One opening to learn, and the two figures line up column for
        column at the left: a fold simply stops where loopification would
        begin, since nothing in a fold is loopifiable."""
        fold = gb._pldi_stage_chain("fold", set(self.ISOLATED), extended=True)
        maps = gb._pldi_stage_chain("map", set(self.ISOLATED), extended=True)
        self.assertEqual(maps[:len(fold)], fold)
        self.assertLess(len(fold), len(maps))

    def test_mutable_cursors_are_separated_from_the_tail_calls_they_unlock(self):
        """Mutable cursors put the traversal in tail position, so a single
        A_ri -> A_rm column collects everything the tail-call optimization
        then does -- 2.618x on Compiler's map passes, for a step that is
        1.136x of cursors and 2.271x of tail calls."""
        for kind in ("fold", "map", "endtoend"):
            labels = [st[0] for st in gb._pldi_stage_chain(kind, set(self.ISOLATED), extended=True)]
            self.assertEqual(labels[:4], ["C tail calls off", "Mutable cursors",
                                          "SoA layout", "C tail calls on"], kind)

    def test_the_map_chain_does_not_detour_through_aos_loopified(self):
        """Walking AoS to its best and then dropping back to SoA recursive
        would put a large slowdown in the middle of the chain. What AoS
        loopification achieves is reported by its own delta column."""
        stages = gb._pldi_stage_chain("map", set(self.ISOLATED), extended=True)
        touched = {cfg for _l, a, b in stages for cfg in (a, b)}
        self.assertNotIn("aos_loop", touched)
        self.assertNotIn(gb.av_variant_name("aos_loop"), touched)

    def test_the_chain_reads_the_data_not_the_registry(self):
        """A report is drawn from measurements, and the process drawing them
        may be configured differently from the run that produced them."""
        plain = gb._pldi_stage_chain("map", set(self.MAP_CFGS), extended=True)
        isolated = gb._pldi_stage_chain("map", set(self.ISOLATED), extended=True)
        self.assertNotIn("C auto-vec. off", [st[0] for st in plain])
        self.assertIn("C auto-vec. off", [st[0] for st in isolated])

    def test_gibbon_simd_is_measured_without_the_backend(self):
        """Measured on top of gcc's vectorizer it reports what is left after
        the backend has already vectorized the loop, which is nothing."""
        stages = gb._pldi_stage_chain("map", set(self.ISOLATED), extended=True)
        simd = [s for s in stages if s[0] == "Gibbon SIMD"][0]
        self.assertEqual(simd[1], "soa_loop_sbs_navec")
        self.assertEqual(simd[2], "soa_loop_sbs_gibvec_navec")

    def test_turning_the_backend_off_is_its_own_column(self):
        """Folded into loopification it would read 0.40x on
        ArithmeticIntensityInt16, where loopification alone is 1.07x."""
        labels = [st[0] for st in gb._pldi_stage_chain("map", set(self.ISOLATED), extended=True)]
        self.assertEqual(labels.index("C auto-vec. off") + 1,
                         labels.index("Loopification"))

    def test_the_stages_telescope(self):
        for kind, available in (("map", set(self.ISOLATED)),
                                ("map", set(self.MAP_CFGS)),
                                ("fold", set(self.MAP_CFGS))):
            stages = gb._pldi_stage_chain(kind, available, extended=True)
            for earlier, later in zip(stages, stages[1:]):
                self.assertEqual(earlier[2], later[1],
                                 "%s ends at %s, %s starts at %s"
                                 % (earlier[0], earlier[2], later[0], later[1]))

    def test_every_cell_is_relative_to_vanilla(self):
        """Each cell is Vanilla Gibbon's time over the stage's own, and the
        last stage is the total."""
        times = {"aos_imm": 8.0, "aos_imm_notco": 8.0, "aos_mut_notco": 6.0,
                 "soa_mut_notco": 5.0, "aos_mut": 6.0, "soa_mut": 4.0,
                 "soa_mut_navec": 4.4, "soa_loop_navec": 2.2,
                 "soa_loop_sbs_navec": 1.1, "soa_loop_sbs_gibvec_navec": 0.55,
                 "soa_loop": 2.0, "soa_loop_sbs": 1.0,
                 "soa_loop_sbs_gibvec": 0.5}
        rows, _labels, dropped = gb._pldi_stage_rows(self._matrix(times), "map", extended=True)
        self.assertEqual(dropped, [])
        row = rows[0]
        stages = gb._pldi_stage_chain("map", set(times), extended=True)
        self.assertEqual(len(row["factors"]), len(stages) + 1)
        for factor, (_label, _source, target) in zip(row["factors"][1:], stages):
            self.assertAlmostEqual(factor, times["aos_imm"] / times[target])
        self.assertAlmostEqual(row["factors"][-1], row["total"])
        self.assertAlmostEqual(row["total"], 16.0)

    def test_a_program_missing_a_link_is_dropped(self):
        times = {c: 1.0 for c in self.ISOLATED}
        del times["soa_loop_sbs_navec"]
        rows, _labels, dropped = gb._pldi_stage_rows(self._matrix(times), "map", extended=True)
        self.assertEqual(rows, [])
        self.assertEqual(dropped, ["P.hs"])

    def test_rows_are_ordered_by_name_not_total(self):
        matrix = {}
        for name, best in (("B.hs", 0.5), ("A.hs", 0.1), ("C.hs", 0.9)):
            times = {c: 1.0 for c in self.ISOLATED}
            times["soa_loop_sbs_gibvec"] = best
            matrix.update(self._matrix(times)["P.hs"] and
                          {name: self._matrix(times)["P.hs"]})
        rows, _labels, _d = gb._pldi_stage_rows(matrix, "map", extended=True)
        self.assertEqual([r["program"] for r in rows], ["A", "B", "C"])

    def test_arithmetic_intensity_is_a_subgroup_after_the_other_synthetics(self):
        names = ["ArithmeticIntensityInt8.hs", "TernaryTree.hs",
                 "Add1TreeInt8.hs", "Compiler.hs"]
        ordered = sorted(names, key=lambda p: gb.pldi_stage_sort_key(
            p, gb.pldi_stage_group(p)))
        self.assertEqual(ordered, ["Compiler.hs", "Add1TreeInt8.hs",
                                   "TernaryTree.hs",
                                   "ArithmeticIntensityInt8.hs"])
        self.assertEqual(gb.pldi_stage_group("ArithmeticIntensityInt8.hs"),
                         "synthetic")
        self.assertEqual(gb.pldi_stage_subgroup("ArithmeticIntensityInt8.hs"),
                         "arithintensity")
        self.assertIsNone(gb.pldi_stage_subgroup("Add1TreeInt8.hs"))

    def test_aos_columns_carry_a_layout_note(self):
        self.assertEqual(gb.PLDI_STAGE_COLUMN_NOTES,
                         {"Vanilla Gibbon": "AoS", "Mutable cursors": "AoS"})

    def test_a_width_family_sits_together_in_width_order(self):
        names = ["ArithmeticIntensityInt64.hs", "List.hs",
                 "ArithmeticIntensityInt8.hs", "Add1TreeInt16.hs",
                 "ArithmeticIntensityInt16.hs", "Add1TreeInt8.hs"]
        ordered = sorted(names, key=lambda p: gb.pldi_stage_sort_key(
            p, gb.pldi_stage_group(p)))
        self.assertEqual(ordered, [
            "Add1TreeInt8.hs", "Add1TreeInt16.hs", "List.hs",
            "ArithmeticIntensityInt8.hs", "ArithmeticIntensityInt16.hs",
            "ArithmeticIntensityInt64.hs"])


class TestCompactStageChain(unittest.TestCase):
    """The default heatmaps: one column per Gibbon optimization, with the C
    auto-vectorizer off in every column, Vanilla included, when its twins
    were measured."""

    PLAIN = ["aos_imm", "aos_mut", "aos_imm_notco", "aos_mut_notco",
             "soa_mut", "soa_mut_notco", "soa_loop", "soa_loop_sbs",
             "soa_loop_sbs_gibvec"]
    FULL = PLAIN + [gb.av_variant_name(c) for c in (
        "aos_imm", "aos_mut", "soa_mut", "soa_loop", "soa_loop_sbs",
        "soa_loop_sbs_gibvec")]

    def test_the_columns(self):
        labels = lambda kind: [st[0] for st in gb._pldi_stage_chain(kind, set(self.FULL))]
        self.assertEqual(labels("fold"), ["Mutable cursors", "SoA layout"])
        self.assertEqual(labels("map"), ["Mutable cursors", "SoA layout",
                                         "Loopification", "Buffer sharing",
                                         "Gibbon SIMD"])

    def test_every_configuration_is_av_off_when_measured(self):
        """Left on in Vanilla alone, the auto-vectorizer would credit it
        with vectorized kernels no later column is measured with."""
        for kind in ("fold", "map", "endtoend"):
            stages = gb._pldi_stage_chain(kind, set(self.FULL))
            self.assertEqual(stages[0][1], gb.av_variant_name("aos_imm"))
            for _label, source, target in stages:
                self.assertTrue(source.endswith(gb.AV_VARIANT_SUFFIX), source)
                self.assertTrue(target.endswith(gb.AV_VARIANT_SUFFIX), target)

    def test_without_every_twin_it_stays_av_on(self):
        """Mixing worlds would put the auto-vectorizer switch inside a
        column; a partial set of twins falls back to av-on throughout."""
        partial = self.FULL[:-1]
        self.assertTrue(gb._pldi_compact_isolated("fold", set(partial)))
        for kind in ("map", "endtoend"):
            for _label, source, target in gb._pldi_stage_chain(kind, set(partial)):
                self.assertFalse(source.endswith(gb.AV_VARIANT_SUFFIX), source)
                self.assertFalse(target.endswith(gb.AV_VARIANT_SUFFIX), target)

    def test_it_telescopes(self):
        for available in (set(self.FULL), set(self.PLAIN)):
            stages = gb._pldi_stage_chain("map", available)
            for earlier, later in zip(stages, stages[1:]):
                self.assertEqual(earlier[2], later[1])

    def _one(self, program, times):
        return {program: {cfg: _make_result(
            program, cfg, {"m": {"median_time": v, "pass_type": "map"}})
            for cfg, v in times.items()}}

    def test_vanilla_is_ordinary_for_most_programs(self):
        times = {c: 1.0 for c in self.FULL}
        times["aos_imm"] = 8.0
        times[gb.av_variant_name("aos_imm")] = 100.0   # not this row's anchor
        times[gb.av_variant_name("soa_loop_sbs_gibvec")] = 0.5
        rows, labels, _d = gb._pldi_stage_rows(self._one("KDTree.hs", times), "map")
        row = rows[0]
        self.assertEqual(labels[0], "Vanilla Gibbon")
        self.assertEqual(len(labels), 6)
        self.assertFalse(row["vanilla_av_off"])
        self.assertAlmostEqual(row["factors"][0], 1.0)
        self.assertAlmostEqual(row["total"], 16.0)
        self.assertIsNone(row["av_on"][0])

    def test_vanilla_is_av_off_for_the_arithmetic_intensity_kernels(self):
        """Their kernels are what gcc vectorizes, so an ordinary Vanilla
        would be credited with a speedup no later column is measured with."""
        for program in gb.PLDI_AV_OFF_VANILLA_PROGRAMS:
            times = {c: 1.0 for c in self.FULL}
            times["aos_imm"] = 2.0                     # Vanilla, auto-vec on
            times[gb.av_variant_name("aos_imm")] = 8.0
            times[gb.av_variant_name("soa_loop_sbs_gibvec")] = 0.5
            rows, _labels, _d = gb._pldi_stage_rows(self._one(program, times), "map")
            row = rows[0]
            self.assertTrue(row["vanilla_av_off"], program)
            self.assertAlmostEqual(row["total"], 16.0)
            self.assertAlmostEqual(row["av_on"][0], 4.0)   # its corner

    def test_the_chain_after_vanilla_is_av_off_either_way(self):
        for program in ("KDTree.hs", "ArithmeticIntensityInt8.hs"):
            times = {c: 1.0 for c in self.FULL}
            times["aos_imm"] = 4.0
            times[gb.av_variant_name("aos_imm")] = 4.0
            times[gb.av_variant_name("soa_mut")] = 2.0
            times["soa_mut"] = 1.0
            rows, labels, _d = gb._pldi_stage_rows(self._one(program, times), "map")
            self.assertAlmostEqual(rows[0]["factors"][labels.index("SoA layout")], 2.0)

    def test_each_cell_carries_its_auto_vectorized_counterpart(self):
        times = {c: 1.0 for c in self.FULL}
        times["aos_imm"] = 8.0
        times["soa_loop"] = 2.0                        # S_l with auto-vec on
        times["soa_loop_sbs_gibvec"] = 0.5             # the ordinary best
        rows, labels, _d = gb._pldi_stage_rows(self._one("P.hs", times), "map")
        row = rows[0]
        self.assertAlmostEqual(row["av_on"][labels.index("Loopification")], 4.0)
        self.assertAlmostEqual(row["total_av_on"], 16.0)
        self.assertEqual(len(row["av_on"]), len(row["factors"]))

    def test_a_missing_counterpart_leaves_the_corner_empty(self):
        times = {c: 1.0 for c in self.FULL}
        del times["soa_loop_sbs"]
        matrix = {"P.hs": {cfg: _make_result(
            "P.hs", cfg, {"m": {"median_time": t, "pass_type": "map"}})
            for cfg, t in times.items()}}
        rows, labels, dropped = gb._pldi_stage_rows(matrix, "map")
        self.assertEqual(dropped, [])
        self.assertIsNone(rows[0]["av_on"][labels.index("Buffer sharing")])

    def test_the_extended_chain_has_no_corners(self):
        times = {c: 1.0 for c in self.FULL}
        matrix = {"P.hs": {cfg: _make_result(
            "P.hs", cfg, {"m": {"median_time": t, "pass_type": "map"}})
            for cfg, t in times.items()}}
        rows, _labels, _d = gb._pldi_stage_rows(matrix, "map", extended=True)
        self.assertTrue(all(v is None for v in rows[0]["av_on"]))

    def test_vanilla_is_twinned_without_a_contrast_column(self):
        self.addCleanup(importlib.reload, gb)
        gb.apply_av_variants(("fold", "loopified"))
        self.assertIn(gb.av_variant_name("aos_imm"), gb.PLDI_MAP_CONFIGS["aos"])
        for _l, _sym, base, feat, _d in (gb.PLDI_DELTA_COLUMNS_FOLD
                                         + gb.PLDI_DELTA_COLUMNS_MAP):
            self.assertNotIn("aos_imm", (base, feat))



class TestVanillaAnchorColumn(unittest.TestCase):
    """The figure is a progression, so where it starts is a column of its
    own rather than something inferred from the first step's label."""

    ISOLATED = ["aos_imm", "aos_mut", "aos_imm_notco", "aos_mut_notco",
                "soa_mut", "soa_mut_notco", "soa_loop", "soa_loop_sbs",
                "soa_loop_sbs_gibvec", "soa_mut_navec", "soa_loop_navec",
                "soa_loop_sbs_navec", "soa_loop_sbs_gibvec_navec"]

    def _matrix(self, times):
        return {"P.hs": {cfg: _make_result(
            "P.hs", cfg, {"m": {"median_time": t, "pass_type": "map"}})
            for cfg, t in times.items()}}

    def test_the_first_column_is_vanilla_and_always_one(self):
        times = {c: 1.0 for c in self.ISOLATED}
        times["aos_imm"] = 4.0
        rows, labels, _d = gb._pldi_stage_rows(self._matrix(times), "map")
        self.assertEqual(labels[0], "Vanilla Gibbon")
        self.assertAlmostEqual(rows[0]["factors"][0], 1.0)

    def test_it_does_not_disturb_the_total(self):
        """The last stage is still the total."""
        times = {c: 1.0 for c in self.ISOLATED}
        times["aos_imm"] = 8.0
        times["soa_loop_sbs_gibvec"] = 0.5
        rows, _labels, _d = gb._pldi_stage_rows(self._matrix(times), "map")
        row = rows[0]
        self.assertAlmostEqual(row["factors"][-1], row["total"])
        self.assertAlmostEqual(row["total"], 16.0)

    def test_both_kinds_get_one(self):
        for kind in ("fold", "map", "endtoend"):
            times = {c: 1.0 for c in self.ISOLATED}
            matrix = self._matrix(times)
            for res in matrix["P.hs"].values():
                res.build_time = 1.0
            rows, labels, _d = gb._pldi_stage_rows(matrix, kind)
            self.assertEqual(labels[0], "Vanilla Gibbon", kind)
            if kind != "fold":   # the fixture's only pass is a map
                self.assertEqual(len(rows), 1, kind)


class TestTablesAlwaysFit(unittest.TestCase):
    """A table is \\input into a document whose text width this generator
    cannot know, so it must be measured and scaled where it is used."""

    def _tex(self, pldi=None):
        import tempfile
        with tempfile.TemporaryDirectory() as d:
            out = Path(d) / "t.tex"
            res = _make_result("P.hs", "aos_mut", {
                "m": {"median_time": 0.01, "pass_type": "map"},
                "g": {"median_time": 0.02, "pass_type": "fold"}})
            res.adt_fields = 4
            res.adt_info = {"soa_total_buffers": 5, "type_name": "T"}
            gb.write_latex_tables([(res, res)], out, None,
                                  pldi_variant_results=pldi)
            return out.read_text()

    def test_every_tabular_is_wrapped_in_the_fit_macro(self):
        """An unwrapped one would run into the margin instead of scaling."""
        tex = self._tex()
        self.assertEqual(tex.count("\\gibbonfit{"),
                         tex.count("\\end{tabular}}"))
        self.assertEqual(tex.count("\\begin{tabular}"),
                         tex.count("\\end{tabular}}"))

    def test_no_tabular_closes_without_its_brace(self):
        for line in self._tex().splitlines():
            if "\\end{tabular}" in line:
                self.assertIn("\\end{tabular}}", line, line)

    def test_the_macro_only_scales_when_it_has_to(self):
        """A table that already fits keeps the surrounding text's size; an
        unconditional \\resizebox would rescale every table, including ones
        that fit, and blow small ones up past the body type."""
        tex = self._tex()
        self.assertIn("\\ifdim\\wd\\gibbon@fitbox>\\linewidth", tex)
        self.assertIn("\\resizebox{\\linewidth}{!}", tex)
        self.assertNotIn("\\resizebox{\\textwidth}{!}", tex)

    def test_a_scaled_table_is_recorded_in_the_log(self):
        self.assertIn("GIBBON-TABLE-SCALED", self._tex())

    def test_the_required_packages_are_all_declared(self):
        """amsmath was missing, so a document that did not already load it
        failed on \\text inside a delta-table caption."""
        header = self._tex().splitlines()[1]
        for package in ("booktabs", "graphicx", "amsmath", "xcolor"):
            self.assertIn(package, header)

    def test_the_font_steps_down_before_scaling_is_needed(self):
        """Stepping the font keeps the table in the paper's own type;
        scaling does not, so it is the last resort rather than the first."""
        sizes = [gb._table_size_directive(n).split()[0]
                 for n in (6, 10, 16, 22)]
        self.assertEqual(sizes, ["\\small\\gibbonnumfont",
                                 "\\footnotesize\\gibbonnumfont",
                                 "\\scriptsize\\gibbonnumfont",
                                 "\\tiny\\gibbonnumfont"])

    def test_wider_tables_never_get_a_larger_font(self):
        order = ["\\small", "\\footnotesize", "\\scriptsize", "\\tiny"]
        ranks = [order.index(gb._table_size_directive(n).split("\\gibbon")[0].strip())
                 for n in range(1, 40)]
        self.assertEqual(ranks, sorted(ranks))


class TestHeatmapColorScale(unittest.TestCase):
    """Colour encodes magnitude, so the ramp has to be spent on the range
    the data occupies rather than on one outlier."""

    def test_the_arms_saturate_at_32x_and_half(self):
        self.assertEqual(gb.pldi_stage_shade(32.0), (1.0, False))
        self.assertEqual(gb.pldi_stage_shade(0.5), (-1.0, False))
        self.assertTrue(gb.pldi_stage_shade(40.0)[1])
        self.assertTrue(gb.pldi_stage_shade(0.4)[1])
        self.assertEqual(gb.pldi_stage_shade(1.0), (0.0, False))

    def test_a_small_dip_is_visibly_red(self):
        """0.976x must not read as white."""
        pos, _clipped = gb.pldi_stage_shade(0.976)
        self.assertLess(pos, -0.15)

    def test_the_common_range_stays_legible(self):
        """1.3x and 3.4x apart; 10x and 20x apart; 20x not saturated."""
        shade = lambda v: gb.pldi_stage_shade(v)[0]
        self.assertGreater(shade(1.3), 0.15)
        self.assertGreater(shade(3.4) - shade(1.3), 0.25)
        self.assertGreater(shade(20.0) - shade(10.0), 0.08)
        self.assertLess(shade(20.0), 1.0)

    def test_it_is_a_diverging_map_with_a_neutral_midpoint(self):
        """Polarity about 1.0x: two hues, neutral middle, never a rainbow
        and never a hue at the midpoint."""
        self.assertEqual(gb.PLDI_STAGE_CMAP, "RdBu")

    def test_a_step_that_loses_speed_is_marked(self):
        self.assertEqual(gb.pldi_stage_dips([1.0, 1.26, 1.12, 2.4, 2.18, 20.3]),
                         [False, False, True, False, True, False])

    def test_a_dip_invisible_in_the_label_is_not_marked(self):
        self.assertEqual(gb.pldi_stage_dips([1.0, 2.301, 2.2995]),
                         [False, False, False])


class TestBenchmarkCharacteristicsTable(unittest.TestCase):
    """A speedup is not interpretable without the shape of the data behind
    it: node width, buffer count and how much of a node a pass ignores."""

    def _render(self, pairs):
        buf = io.StringIO()
        gb._table_benchmark_characteristics(buf, pairs)
        return buf.getvalue()

    def _pair(self, program="A.hs", dead=0.5, uses=3, fields=6, buffers=5):
        aos = _make_result(program, "aos", {
            "f": {"median_time": 1.0, "pass_type": "fold", "uses": uses,
                  "dead_ratio": dead},
            "m": {"median_time": 2.0, "pass_type": "map", "uses": uses + 1,
                  "dead_ratio": dead / 2}})
        soa = _make_result(program, "soa", dict(aos.passes))
        aos.adt_fields = soa.adt_fields = fields
        soa.adt_info = {"type_name": "T", "soa_total_buffers": buffers,
                        "nonrec_field_slots": None}
        return (aos, soa)

    def test_it_reports_width_buffers_pass_counts_and_dead_headroom(self):
        tex = self._render([self._pair()])
        self.assertIn("\\label{tab:benchmark-characteristics}", tex)
        row = [l for l in tex.splitlines() if l.startswith("\\texttt{A}")][0]
        self.assertIn("& 6 &", row)      # fields
        self.assertIn("& 5 &", row)      # buffers
        self.assertIn("& 1 & 1 &", row)  # one fold, one map
        self.assertIn("3--4", row)       # uses range
        self.assertIn("50\\%", row)      # largest dead fraction

    def test_the_verification_pass_is_not_a_benchmark_kernel(self):
        aos, soa = self._pair()
        for res in (aos, soa):
            res.passes["checksumTree"] = {"median_time": 9.0,
                                          "pass_type": "fold", "uses": 1,
                                          "dead_ratio": 0.0}
        row = [l for l in self._render([(aos, soa)]).splitlines()
               if l.startswith("\\texttt{A}")][0]
        self.assertIn("& 1 & 1 &", row)
        self.assertIn("50\\%", row)

    def test_an_unverified_program_is_not_described(self):
        aos, soa = self._pair()
        soa.qualification.oracle_status = prov.ORACLE_FAIL
        self.assertEqual(self._render([(aos, soa)]), "")

    def test_the_caption_does_not_claim_a_working_set(self):
        tex = self._render([self._pair()])
        self.assertIn("working-set sizes are not measured here", tex)


class TestTablesFromStoredResults(unittest.TestCase):
    def test_tables_need_the_campaign_report(self):
        import tempfile
        d = Path(tempfile.mkdtemp())
        res = _make_result("A.hs", "aos_mut",
                           {"f": {"median_time": 1.0, "pass_type": "fold"}})
        with mock.patch("builtins.print"):
            gb.write_pldi_matrix_json({"A.hs": {"aos_mut": res}}, d / "m.json")
            rc = gb.replot_figures_from_json([d / "m.json"], d / "figs",
                                             latex_table=d / "t.tex")
        self.assertEqual(rc, 1)
        self.assertFalse((d / "t.tex").exists())

    def test_the_stored_runs_provenance_is_what_is_recorded(self):
        import tempfile
        d = Path(tempfile.mkdtemp())
        res = _make_result("A.hs", "aos",
                           {"f": {"median_time": 1.0, "pass_type": "fold"}})
        with mock.patch("builtins.print"):
            gb.write_json_results([(res, res)], d / "c.json",
                                  campaign_extra={"codegen": {"simd_isa": "sse2"},
                                                  "driver_argv": ["original-run"]})
            gb.replot_figures_from_json([d / "c.json"], d / "figs",
                                        latex_table=d / "t.tex")
        tex = (d / "t.tex").read_text()
        self.assertIn("original-run", tex)
        self.assertIn("sse2", tex)


class TestMeasurementEnvironment(unittest.TestCase):
    def test_a_pinned_core_reserves_its_smt_siblings(self):
        with mock.patch.object(gb.Path, "read_text", lambda self: "2-3"):
            self.assertEqual(gb.smt_siblings(2), {2, 3})

    def test_a_core_with_no_topology_file_is_its_own_sibling(self):
        def boom(self):
            raise OSError("no such file")
        with mock.patch.object(gb.Path, "read_text", boom):
            self.assertEqual(gb.smt_siblings(5), {5})

    def test_reservation_keeps_the_driver_off_the_whole_core(self):
        applied = {}
        with mock.patch.object(gb.os, "sched_getaffinity", lambda _p: set(range(8))), \
             mock.patch.object(gb.os, "sched_setaffinity",
                               lambda _p, cpus: applied.update(cpus=set(cpus))), \
             mock.patch.object(gb, "smt_siblings", lambda c: {c, c + 1}):
            self.assertTrue(gb.reserve_pin_cpu(2))
        self.assertNotIn(2, applied["cpus"])
        self.assertNotIn(3, applied["cpus"])

    def test_the_sibling_is_kept_when_reserving_both_leaves_nothing(self):
        applied = {}
        with mock.patch.object(gb.os, "sched_getaffinity", lambda _p: {0, 1}), \
             mock.patch.object(gb.os, "sched_setaffinity",
                               lambda _p, cpus: applied.update(cpus=set(cpus))), \
             mock.patch.object(gb, "smt_siblings", lambda c: {0, 1}):
            self.assertTrue(gb.reserve_pin_cpu(0))
        self.assertEqual(applied["cpus"], {1})

    def test_frequency_policy_is_recorded(self):
        info = gb._machine_description()
        # Present on this Linux machine; a kernel without them records neither.
        for key in ("cpu_governor", "turbo"):
            if key in info:
                self.assertTrue(info[key])


class TestBuildPassIsNotComparedAcrossCompilers(unittest.TestCase):
    def test_the_combination_is_refused(self):
        src = Path(gb.__file__).read_text()
        main_src = src[src.index("\ndef main("):]
        self.assertIn("--include-build-pass cannot be combined with", main_src)
        i = main_src.index("args.include_build_pass and (args.benchmark_ghc")
        # Refused before anything is compiled or measured.
        self.assertLess(i, main_src.index("for prog in programs_to_run:"))


class TestErrorBarIsTheRightSpread(unittest.TestCase):
    """A comparison between two configurations compares two processes, so the
    within-process standard error is not its uncertainty."""

    def test_between_round_ci_is_preferred_when_present(self):
        pd = {"stderr": 0.0001, "between_round_ci95_abs": 0.02}
        self.assertEqual(gb.pass_error_bar(pd), (0.02, "between-round"))

    def test_within_process_stderr_is_the_fallback(self):
        self.assertEqual(gb.pass_error_bar({"stderr": 0.0001}),
                         (0.0001, "within-process"))

    def test_absent_statistics_give_no_bar(self):
        self.assertEqual(gb.pass_error_bar({}), (0.0, "within-process"))

    def test_caption_names_whichever_spread_the_tables_show(self):
        one = _make_result("A.hs", "aos", {
            "f": {"median_time": 1.0, "pass_type": "fold", "stderr": 0.001}})
        many = _make_result("A.hs", "aos", {
            "f": {"median_time": 1.0, "pass_type": "fold", "stderr": 0.001,
                  "between_round_ci95_abs": 0.05}})
        self.assertIn("WITHIN one process", gb.error_bar_caption_note([one]))
        self.assertIn("measured once", gb.error_bar_caption_note([one]))
        self.assertIn("pass-rounds", gb.error_bar_caption_note([many]))
        self.assertNotIn("measured once", gb.error_bar_caption_note([many]))

    def test_a_missing_result_does_not_break_the_caption(self):
        self.assertIn("WITHIN one process", gb.error_bar_caption_note([None]))


class TestSubmissionDefaults(unittest.TestCase):
    """--pldi-submission implies the measurement discipline a submission
    needs, rather than relying on the operator to remember the flags."""

    def test_pass_rounds_default_to_repetition_for_a_submission(self):
        self.assertEqual(gb.default_pass_rounds(None, True),
                         gb.PLDI_DEFAULT_PASS_ROUNDS)
        self.assertGreaterEqual(gb.PLDI_DEFAULT_PASS_ROUNDS, 3)

    def test_an_ordinary_run_still_measures_once(self):
        self.assertEqual(gb.default_pass_rounds(None, False), 1)

    def test_an_explicit_count_wins(self):
        self.assertEqual(gb.default_pass_rounds(2, True), 2)
        self.assertEqual(gb.default_pass_rounds(7, False), 7)

    def test_a_nonsense_count_is_floored_at_one(self):
        self.assertEqual(gb.default_pass_rounds(0, True), 1)

    def test_main_resolves_it_before_the_matrix_uses_it(self):
        src = Path(gb.__file__).read_text()
        main_src = src[src.index("\ndef main("):]
        self.assertLess(main_src.index("default_pass_rounds("),
                        main_src.index("pass_rounds=args.pass_rounds"))


class TestProvenanceDescribesWhatRan(unittest.TestCase):
    """The recorded block travels into the paper; it must not credit the
    numbers with a discipline the path that produced them did not apply."""

    def _block(self):
        args = gb.build_parser().parse_args(["--pldi-submission"])
        args.pass_rounds = gb.default_pass_rounds(args.pass_rounds, True)
        return gb.campaign_provenance(args)["timing"]

    def test_each_measuring_path_records_its_own_warmup(self):
        t = self._block()
        self.assertIn("campaign_phase", t)
        self.assertIn("variant_matrix_phase", t)
        self.assertEqual(t["variant_matrix_phase"]["warmup_runs"],
                         gb.MATRIX_WARMUP_RUNS)
        self.assertEqual(t["variant_matrix_phase"]["cooldown_seconds"], 0.0)

    def test_no_bare_warmup_field_that_could_be_read_as_global(self):
        t = self._block()
        for key in ("warmup_runs", "warmup_iterations", "cooldown_seconds"):
            self.assertNotIn(key, t)

    def test_the_round_count_is_recorded(self):
        t = self._block()
        self.assertEqual(t["pass_rounds"], gb.PLDI_DEFAULT_PASS_ROUNDS)
        self.assertEqual(t["variant_matrix_phase"]["rounds"],
                         gb.PLDI_DEFAULT_PASS_ROUNDS)

    def test_codegen_says_its_flags_are_whole_run_only(self):
        args = gb.build_parser().parse_args(["--pldi-submission"])
        codegen = gb.campaign_provenance(args)["codegen"]
        self.assertIn("per_configuration_flags", codegen)


class TestRunRounds(unittest.TestCase):
    """Interleaving itself. Every delta subtracts one configuration from
    another measured in a separate process, so what matters is that neither
    is systematically measured before the other."""

    def _fake(self):
        calls = []
        def run_exe(exe, iterations, use_iterate_flag=True, pin_cpu=None, **kw):
            calls.append(Path(exe).name)
            return (True, 1.0, "out", "", 0)
        return run_exe, calls

    def test_every_job_runs_once_per_round(self):
        run_exe, calls = self._fake()
        jobs = [(c, Path(c)) for c in "abc"]
        with mock.patch.object(gb, "run_exe", run_exe):
            out = gb.run_rounds(jobs, 5, 4, warmup_runs=0)
        self.assertEqual([len(v) for v in out.values()], [4, 4, 4])
        self.assertEqual(calls.count("a"), 4)

    def test_as_many_rounds_as_jobs_puts_each_in_every_slot(self):
        run_exe, calls = self._fake()
        jobs = [(c, Path(c)) for c in "abc"]
        with mock.patch.object(gb, "run_exe", run_exe):
            gb.run_rounds(jobs, 5, 3, warmup_runs=0)
        rounds = [calls[i * 3:(i + 1) * 3] for i in range(3)]
        for slot in range(3):
            self.assertEqual(sorted(r[slot] for r in rounds), ["a", "b", "c"])

    def test_few_rounds_still_spread_each_job_across_the_order(self):
        """Rotating by one would leave every job in effectively the part of
        the order it started in, which is what rotation exists to avoid.
        Three rounds over eighteen jobs must start far apart."""
        run_exe, calls = self._fake()
        jobs = [("%02d" % i, Path("%02d" % i)) for i in range(18)]
        with mock.patch.object(gb, "run_exe", run_exe):
            gb.run_rounds(jobs, 5, 3, warmup_runs=0)
        starts = [calls[i * 18] for i in range(3)]
        self.assertEqual(len(set(starts)), 3)
        ordered = sorted(int(x) for x in starts)
        self.assertGreaterEqual(min(b - a for a, b in zip(ordered, ordered[1:])), 4)

    def test_a_single_round_keeps_the_original_order(self):
        run_exe, calls = self._fake()
        jobs = [(c, Path(c)) for c in "abc"]
        with mock.patch.object(gb, "run_exe", run_exe):
            gb.run_rounds(jobs, 5, 1, warmup_runs=0)
        self.assertEqual(calls, ["a", "b", "c"])

    def test_zero_rounds_still_runs_once(self):
        """A caller passing 0 must not get a result with no measurement
        behind it."""
        run_exe, calls = self._fake()
        with mock.patch.object(gb, "run_exe", run_exe):
            out = gb.run_rounds([("a", Path("a"))], 5, 0, warmup_runs=0)
        self.assertEqual(len(out["a"]), 1)

    def test_every_round_uses_the_top_level_iteration_count(self):
        """A round is a repetition of the whole measurement, not a different
        one: each still runs --iterate with the campaign's --iterations."""
        seen = []
        def run_exe(exe, iterations, use_iterate_flag=True, pin_cpu=None, **kw):
            seen.append(iterations)
            return (True, 1.0, "out", "", 0)
        with mock.patch.object(gb, "run_exe", run_exe):
            gb.run_rounds([("a", Path("a")), ("b", Path("b"))], 21, 3,
                          warmup_runs=0)
        self.assertEqual(set(seen), {21})
        self.assertEqual(len(seen), 6)

    def test_every_job_is_warmed_up_before_the_first_timed_round(self):
        """A first run pays cold caches and first-touch of the output region;
        the driver measured 6.3% between a first and a second run of one
        binary, larger than many effects the matrix reports."""
        seen = []
        def run_exe(exe, iterations, use_iterate_flag=True, pin_cpu=None, **kw):
            seen.append((Path(exe).name, iterations))
            return (True, 1.0, "out", "", 0)
        jobs = [(c, Path(c)) for c in "abc"]
        with mock.patch.object(gb, "run_exe", run_exe):
            out = gb.run_rounds(jobs, 20, 2)
        warm = seen[:3]
        self.assertEqual([n for n, _i in warm], ["a", "b", "c"])
        self.assertTrue(all(i == gb.MATRIX_WARMUP_ITERATIONS for _n, i in warm))
        # Warm-ups are discarded: only the timed rounds are collected.
        self.assertEqual([len(v) for v in out.values()], [2, 2, 2])
        self.assertTrue(all(i == 20 for _n, i in seen[3:]))

    def test_the_warm_up_precedes_every_timed_run_not_just_its_own_job(self):
        # Warming a job immediately before timing it would leave the LAST
        # job's timed run adjacent to the first job's warm-up instead.
        order = []
        def run_exe(exe, iterations, use_iterate_flag=True, pin_cpu=None, **kw):
            order.append((Path(exe).name, iterations))
            return (True, 1.0, "out", "", 0)
        jobs = [(c, Path(c)) for c in "ab"]
        with mock.patch.object(gb, "run_exe", run_exe):
            gb.run_rounds(jobs, 20, 1)
        self.assertEqual(order, [("a", 1), ("b", 1), ("a", 20), ("b", 20)])

    def test_warm_up_can_be_turned_off(self):
        run_exe, calls = self._fake()
        with mock.patch.object(gb, "run_exe", run_exe):
            gb.run_rounds([("a", Path("a"))], 5, 1, warmup_runs=0)
        self.assertEqual(calls, ["a"])


class TestBuildTimedSources(unittest.TestCase):
    """The build is timed by generating a copy of the program with `iterate`
    moved onto the construction, so the timed build cannot drift from the
    build the measured program runs."""

    PROGRAMS_DIR = Path(__file__).resolve().parent / "programs"

    def _sources(self):
        for layout in ("AOS", "SOA"):
            for program in gb.DEFAULT_PROGRAMS:
                src = self.PROGRAMS_DIR / layout / program
                if src.exists():
                    yield layout, program, src

    def test_every_curated_program_has_a_construction_to_time(self):
        """A program with no construction binding would silently have no
        build term, and its end-to-end row would be dropped."""
        for layout, program, src in self._sources():
            _text, builds = gb.build_timed_source(src.read_text())
            self.assertTrue(builds, "%s/%s" % (layout, program))

    def test_the_passes_are_no_longer_iterated(self):
        """One iterated expression per marked block is all the parser keeps,
        and a pass left iterated would both be timed and cost nine runs of
        work the cached per-pass medians already cover."""
        for layout, program, src in self._sources():
            text, builds = gb.build_timed_source(src.read_text())
            iterated = [line.strip() for line in text.splitlines()
                        if re.search(r"=\s*iterate\s*\(", line)]
            self.assertEqual(len(iterated), len(builds),
                             "%s/%s: %s" % (layout, program, iterated))

    def test_the_construction_line_is_carried_over_verbatim(self):
        """The generated copy times the same construction the real program
        runs -- the hand-written copies under programs/*_BUILD build
        DecisionTree at depth 35 where the real program builds 32."""
        for layout, program, src in self._sources():
            text, _builds = gb.build_timed_source(src.read_text())
            self.assertEqual(gb._construction_lines(text),
                             gb._construction_lines(src.read_text()),
                             "%s/%s" % (layout, program))

    def test_a_program_that_builds_twice_pays_for_both(self):
        """DomTree builds a full tree for its folds and a smaller one for its
        maps; its end-to-end time includes both."""
        src = self.PROGRAMS_DIR / "SOA" / "DomTree.hs"
        _text, builds = gb.build_timed_source(src.read_text())
        self.assertEqual(builds, ["build_tree", "build_tree_smaller"])

    def test_each_construction_gets_its_own_marked_block(self):
        """Two ITER TIMES lines inside one block leave only the second: the
        parser replaces rather than accumulates."""
        src = self.PROGRAMS_DIR / "SOA" / "DomTree.hs"
        text, builds = gb.build_timed_source(src.read_text())
        for name in builds:
            self.assertIn('Running pass %s (build): ' % name, text)

    def test_the_marker_is_parsed_as_a_build_pass(self):
        """`build` has to be a pass type of its own: the tables select fold
        and map by type, so a build typed `unknown` would be invisible and a
        build typed `fold` would be counted as one."""
        parsed = gb.parse_passes(
            'Running pass build_tree (build): \n'
            'ITER TIMES: [0.10, 0.20, 0.30]\n'
            'End\n')
        self.assertEqual(list(parsed), ["build_tree"])
        self.assertEqual(parsed["build_tree"]["pass_type"], "build")
        self.assertAlmostEqual(parsed["build_tree"]["median_time"], 0.20)

    def test_an_unwrapped_pass_block_reports_nothing(self):
        """The pass blocks stay in the generated source so the program still
        prints its own result; with nothing iterated they must not appear as
        passes with no time."""
        parsed = gb.parse_passes(
            'Running pass build_tree (build): \n'
            'ITER TIMES: [0.10]\n'
            'End\n'
            'Running pass sumArea (fold, uses=6): \n'
            'End\n')
        self.assertEqual(list(parsed), ["build_tree"])

    def test_an_inserted_marker_matches_the_markers_already_there(self):
        """The suite writes main two ways -- one `let` block of bindings, and
        a chain of `let ... in` -- so an inserted line has to carry the same
        `let`/`in` shape as the bindings around it or the program will not
        compile."""
        shape = re.compile(r"^(\s*)(let\s+)?_ = printsym \(quote "
                           r"\"Running pass ([^\"]*)\"\)(\s+in)?\s*$")
        for layout, program, src in self._sources():
            text, builds = gb.build_timed_source(src.read_text())
            shapes = {}
            for line in text.splitlines():
                m = shape.match(line)
                if not m:
                    continue
                inserted = m.group(3).startswith(tuple(builds))
                shapes.setdefault(inserted, set()).add(
                    (m.group(1), bool(m.group(2)), bool(m.group(4))))
            self.assertIn(True, shapes, "%s/%s" % (layout, program))
            if False in shapes:
                self.assertEqual(shapes[True], shapes[False],
                                 "%s/%s" % (layout, program))


class TestBuildTimingScope(unittest.TestCase):
    def test_a_split_family_times_one_build(self):
        """The members were split from one program that built the structure
        once and ran every pass on it."""
        for member in ("OctTree_clearFlags.hs", "OctTree_sumMass.hs",
                       "PiecewiseFunctions_diffPW.hs"):
            owner = gb.build_timing_program(member)
            self.assertEqual(owner, gb.build_timing_program(
                "OctTree_sumMass.hs" if member.startswith("OctTree")
                else "PiecewiseFunctions_norm2Estimate.hs"))

    def test_the_owner_is_a_real_member(self):
        owner = gb.build_timing_program("OctTree_clearFlags.hs")
        self.assertIn(owner, gb.DEFAULT_PROGRAMS)
        self.assertTrue(owner.startswith("OctTree_"))

    def test_an_ordinary_program_owns_its_own_build(self):
        self.assertEqual(gb.build_timing_program("KDTree.hs"), "KDTree.hs")

    def test_a_family_whose_members_disagree_is_reported(self):
        """The shared build is the family's build only while every member
        builds the same thing. OctTree's two map members build a fixed depth
        where its six folds build sizeParam + 8."""
        warnings = gb.build_family_disagreements(
            TestBuildTimedSources.PROGRAMS_DIR, list(gb.DEFAULT_PROGRAMS))
        self.assertTrue(any("OctTree_clearFlags.hs" in w for w in warnings),
                        warnings)
        self.assertFalse(any("PiecewiseFunctions" in w for w in warnings),
                         warnings)

    def test_an_override_lowers_the_count_but_never_raises_it(self):
        """An override exists to keep an already-large build from dominating
        the campaign, not to measure something more than was asked for."""
        self.assertEqual(gb.build_iterations_for("List.hs", 9), 3)
        self.assertEqual(gb.build_iterations_for("List.hs", 2), 2)
        self.assertEqual(gb.build_iterations_for("KDTree.hs", 9), 9)
        self.assertEqual(gb.build_iterations_for("KDTree.hs", 0), 1)

    def test_the_requested_count_defaults_to_nine(self):
        import inspect
        sig = inspect.signature(gb.collect_pldi_variant_results)
        self.assertEqual(sig.parameters["build_iterations"].default, 9)


class TestEndToEndTime(unittest.TestCase):
    """End to end is the build plus every timed pass, not the executable's
    wall time."""

    def _res(self, build=None, passes=None):
        res = _make_result("P.hs", "soa_mut", passes if passes is not None else {
            "f": {"median_time": 0.25, "pass_type": "fold"},
            "m": {"median_time": 0.75, "pass_type": "map"}})
        res.build_time = build
        res.exec_time_per_iter = 99.0
        return res

    def test_it_is_the_build_plus_the_passes(self):
        t = gb._pldi_end_to_end_time({"soa_mut": self._res(build=2.0)}, "soa_mut")
        self.assertAlmostEqual(t, 3.0)

    def test_it_does_not_read_the_executables_wall_time(self):
        """Wall time is one sample per run and, for a family split into one
        executable per pass, charges every member the build they share."""
        t = gb._pldi_end_to_end_time({"soa_mut": self._res(build=2.0)}, "soa_mut")
        self.assertNotAlmostEqual(t, 99.0)

    def test_a_missing_build_is_not_silently_dropped(self):
        """Reporting the pass sum alone would hide the build a layout has to
        pay, and would read as a complete end-to-end number."""
        self.assertIsNone(
            gb._pldi_end_to_end_time({"soa_mut": self._res(build=None)}, "soa_mut"))

    def test_a_program_with_no_timed_pass_has_no_end_to_end_number(self):
        self.assertIsNone(gb._pldi_end_to_end_time(
            {"soa_mut": self._res(build=2.0, passes={})}, "soa_mut"))

    def test_the_verification_pass_is_left_out(self):
        res = self._res(build=1.0, passes={
            "m": {"median_time": 0.5, "pass_type": "map"},
            "checksumTree": {"median_time": 4.0, "pass_type": "fold"}})
        self.assertAlmostEqual(
            gb._pldi_end_to_end_time({"soa_mut": res}, "soa_mut"), 1.5)

    def test_the_build_stays_out_of_every_pass_sum(self):
        """Nothing that sums passes may pick the build up: the pass-sum
        tables report the passes, and the build is the other term."""
        res = self._res(build=5.0)
        self.assertAlmostEqual(gb.total_pass_time(res), 1.0)
        self.assertNotIn("build_tree", res.passes)


class TestMergedFamilyBuild(unittest.TestCase):
    def _member(self, name, pass_name, build):
        res = _make_result(name, "soa_mut",
                           {pass_name: {"median_time": 0.5, "pass_type": "fold"}})
        res.build_time = build
        res.build_passes = {"build_pfTree": {"median_time": build,
                                             "pass_type": "build"}}
        return res

    def test_the_family_pays_its_shared_build_once(self):
        """Eight members of one split family each measured the same
        construction; the merged program is the single program they came
        from, which built it once."""
        matrix = {
            "PiecewiseFunctions_norm2Estimate.hs": {
                "soa_mut": self._member("PiecewiseFunctions_norm2Estimate.hs",
                                        "norm2Estimate", 2.0)},
            "PiecewiseFunctions_diffPW.hs": {
                "soa_mut": self._member("PiecewiseFunctions_diffPW.hs",
                                        "diffPW", 2.0)},
        }
        merged = gb.merge_pldi_program_groups(matrix)
        res = merged["PiecewiseFunctions.hs"]["soa_mut"]
        self.assertAlmostEqual(res.build_time, 2.0)
        self.assertAlmostEqual(gb.total_pass_time(res), 1.0)
        self.assertAlmostEqual(
            gb._pldi_end_to_end_time(merged["PiecewiseFunctions.hs"], "soa_mut"),
            3.0)


class TestSplitFamiliesRenderAsOneProgram(unittest.TestCase):
    """A family split into one executable per timed pass is one program
    everywhere it is reported, not eight."""

    def _family(self, prefix, members):
        out = {}
        for name, pass_name in members:
            res = _make_result(name, "soa_mut",
                               {pass_name: {"median_time": 0.5,
                                            "pass_type": "fold"}})
            res.build_time = 2.0
            out[name] = {"soa_mut": res}
        return out

    def test_both_split_families_are_registered(self):
        """OctTree was split the same way PiecewiseFunctions was but was
        never registered, so it rendered as eight programs."""
        self.assertEqual(set(gb.PROGRAM_MERGE_GROUPS),
                         {"OctTree.hs", "PiecewiseFunctions.hs"})

    def test_octtree_members_fold_into_one_program(self):
        matrix = self._family("OctTree_", [
            ("OctTree_sumMass.hs", "sumMass"),
            ("OctTree_clearFlags.hs", "clearFlags")])
        merged = gb.merge_pldi_program_groups(matrix)
        self.assertEqual(sorted(merged), ["OctTree.hs"])
        self.assertEqual(sorted(merged["OctTree.hs"]["soa_mut"].passes),
                         ["clearFlags", "sumMass"])

    def test_the_merged_family_pays_one_build_for_every_pass(self):
        """Eight members reporting eight builds of one structure is what
        made the split visible in the end-to-end numbers."""
        matrix = self._family("OctTree_", [
            ("OctTree_sumMass.hs", "sumMass"),
            ("OctTree_clearFlags.hs", "clearFlags")])
        merged = gb.merge_pldi_program_groups(matrix)
        self.assertAlmostEqual(
            gb._pldi_end_to_end_time(merged["OctTree.hs"], "soa_mut"), 3.0)
        split = sum(gb._pldi_end_to_end_time(matrix[m], "soa_mut")
                    for m in matrix)
        self.assertAlmostEqual(split, 5.0)   # the same build, charged twice

    def test_the_figures_see_what_the_tables_see(self):
        """The tables merged their own copy while the figures were handed the
        unmerged matrix, so one report showed the same family both ways."""
        matrix = self._family("OctTree_", [
            ("OctTree_sumMass.hs", "sumMass"),
            ("OctTree_clearFlags.hs", "clearFlags")])
        seen = []

        def capture(results, out, kind, title, extended=False):
            seen.append(sorted(results))
            return []

        import tempfile
        with mock.patch.object(gb, "_fig_pldi_stages", capture), \
                mock.patch.object(gb, "_pub_rc", lambda: None):
            with tempfile.TemporaryDirectory() as d:
                gb.generate_pldi_stage_figures(matrix, Path(d))
        self.assertTrue(seen)
        for programs in seen:
            self.assertEqual(programs, ["OctTree.hs"])

    def test_merging_twice_changes_nothing(self):
        """The figures merge their input, and a caller that already merged
        must not have its family taken apart or doubled."""
        matrix = self._family("OctTree_", [("OctTree_sumMass.hs", "sumMass")])
        once = gb.merge_pldi_program_groups(matrix)
        twice = gb.merge_pldi_program_groups(once)
        self.assertEqual(sorted(once), sorted(twice))
        self.assertEqual(sorted(once["OctTree.hs"]["soa_mut"].passes),
                         sorted(twice["OctTree.hs"]["soa_mut"].passes))

    def test_coloroctree_is_not_swept_into_the_octree_family(self):
        """The name is spelled two ways -- OctTree_*.hs is Oct+Tree and
        ColorOctree.hs is Color+Octree -- and they are separate programs."""
        matrix = self._family("OctTree_", [("OctTree_sumMass.hs", "sumMass")])
        matrix.update(self._family("", [("ColorOctree.hs", "quantize")]))
        merged = gb.merge_pldi_program_groups(matrix)
        self.assertEqual(sorted(merged), ["ColorOctree.hs", "OctTree.hs"])


class TestScalarCountsFollowLoopification(unittest.TestCase):
    """Scalar-count footers only serve loopified SoA traversals, so a
    program where nothing is loopified compiles without them."""

    REPORT = (
        "loopification report (AoS pass):\n"
        "  add1Tree: declined: a caller passes an end cursor that is not the value's own end\n"
        "  mkTree: declined: not a candidate (no OPT:MayVectorize, not inferred, or a generated packed helper)\n"
        "loopification report (SoA pass):\n"
        "  add1Tree: loopified\n"
        "  mkTree: declined: not a candidate (no OPT:MayVectorize, not inferred, or not a fully factored single-type map)\n")

    def test_report_parse_reads_only_the_soa_section(self):
        self.assertEqual(gb.parse_soa_loopified(self.REPORT), ["add1Tree"])
        aos_only = self.REPORT.split("loopification report (SoA pass)")[0]
        aos_only = aos_only.replace("declined: a caller passes an end cursor "
                                    "that is not the value's own end", "loopified")
        self.assertEqual(gb.parse_soa_loopified(aos_only), [])

    def test_nothing_loopified_drops_counts_and_deferral(self):
        kw = gb.PLDI_MAP_CONFIGS["soa"]["soa_loop"]
        gated = gb.pldi_unloopified_kwargs(kw, [])
        self.assertFalse(gated["store_scalar_field_counts"])
        self.assertFalse(gated["defer_scalar_counts"])
        self.assertTrue(gated["enable_loopification"])
        self.assertIsNone(gb.scalar_count_mode(gated))

    def test_nothing_loopified_drops_buffer_sharing(self):
        """With nothing to share the pass still rewrites every call site."""
        for cfg in ("soa_loop_sbs", "soa_loop_sbs_gibvec"):
            kw = gb.PLDI_MAP_CONFIGS["soa"][cfg]
            gated = gb.pldi_unloopified_kwargs(kw, [])
            self.assertFalse(gated["enable_selective_buffer_sharing"], cfg)
            self.assertTrue(gated["enable_loopification"], cfg)
            self.assertEqual(gated.get("enable_vectorization", False),
                             kw.get("enable_vectorization", False), cfg)
            self.assertIs(gb.pldi_unloopified_kwargs(kw, ["add1Tree"]), kw)

    def test_loopified_or_unknown_keeps_counts(self):
        kw = gb.PLDI_MAP_CONFIGS["soa"]["soa_loop"]
        for loopified in (["add1Tree"], None):
            gated = gb.pldi_unloopified_kwargs(kw, loopified)
            self.assertIs(gated, kw)
            self.assertEqual(gb.scalar_count_mode(gated), "deferred")

    def test_the_report_runs_with_a_relative_output_dir(self):
        """`main` hands the report a scratch directory under --output-dir,
        a relative path by default, while the compiler runs from the repo
        root. The report must still be produced, for a program with nothing
        to loopify and for one with something."""
        import os
        import tempfile
        if gb.resolve_gibbon().path is None:
            self.skipTest("gibbon executable not available")
        here = Path(gb.__file__).resolve().parent
        scratch = gb.build_parser().parse_args([]).output_dir / "loopify_report"
        self.assertFalse(scratch.is_absolute())
        kw = gb.PLDI_MAP_CONFIGS["soa"]["soa_loop"]
        cwd = os.getcwd()
        with tempfile.TemporaryDirectory() as d:
            os.chdir(d)
            try:
                for program, expected in (("KDTree.hs", []),
                                          ("Add1TreeInt8.hs", ["add1Tree"])):
                    got = gb.soa_loopified_functions(
                        here / "programs" / "SOA" / program, kw, scratch,
                        use_no_ran=gb.program_uses_no_ran(program))
                    self.assertEqual(got, expected, program)
            finally:
                os.chdir(cwd)

    def _collect_with_reports(self, programs, report):
        import tempfile
        with tempfile.TemporaryDirectory() as d:
            (Path(d) / "SOA").mkdir()
            for program in programs:
                (Path(d) / "SOA" / program).write_text("gibbon_main = 0\n")
            with mock.patch.object(gb, "soa_loopification_report", report), \
                    mock.patch.object(gb, "compile_one",
                                      lambda *a, **k: (False, 0.0, "stub")), \
                    mock.patch.object(gb, "qualify_variant",
                                      lambda *a, **k: None):
                return gb.collect_pldi_variant_results(
                    Path(d), Path(d) / "out", "gcc", False, None,
                    programs=list(programs))

    def test_every_report_failing_stops_the_phase(self):
        """A report that fails everywhere is a broken command, not a
        property of the programs."""
        with self.assertRaises(RuntimeError) as ctx:
            self._collect_with_reports(
                ["KDTree.hs", "MonoTree.hs"],
                lambda *a, **k: (None, "exit 1: cannot open C file"))
        self.assertIn("cannot open C file", str(ctx.exception))

    def test_one_failing_report_keeps_that_programs_counts(self):
        def report(source, *a, **k):
            if source.name == "MonoTree.hs":
                return None, "exit 1: boom"
            return [], None
        out = io.StringIO()
        with mock.patch("sys.stdout", out):
            results = self._collect_with_reports(["KDTree.hs", "MonoTree.hs"],
                                                 report)
        self.assertIsNone(results["KDTree.hs"]["soa_loop"].scalar_counts)
        self.assertEqual(results["MonoTree.hs"]["soa_loop"].scalar_counts,
                         "deferred")
        self.assertIn("FAILED for 1 program(s): MonoTree", out.getvalue())
        self.assertIn("exit 1: boom", out.getvalue())

    def test_split_family_decides_together(self):
        family = gb.build_family("OctTree_sumMass.hs")
        self.assertIn("OctTree_scaleEnergy.hs", family)
        self.assertEqual(gb.build_family("KDTree.hs"), ["KDTree.hs"])

    def test_counts_are_serialised(self):
        r = gb.BenchmarkResult("KDTree.hs", "soa_loop")
        r.scalar_counts, r.soa_loopified = None, []
        ser = gb._ser_result(r)
        self.assertIn("scalar_counts", ser)
        self.assertIn("selective_buffer_sharing", ser)
        self.assertEqual(ser["soa_loopified"], [])

class TestStageFigureGroups(unittest.TestCase):
    """Each stage heatmap lists the real-world benchmarks first and the
    synthetic ones below a rule."""

    def _merged_names(self):
        names = set()
        for program in gb.DEFAULT_PROGRAMS + gb.PLDI_EXTRA_PROGRAMS:
            for family, prefix in gb.PROGRAM_MERGE_GROUPS.items():
                if program.startswith(prefix):
                    program = family
            names.add(program)
        return names

    def test_every_real_world_name_is_a_program(self):
        """A misspelt name would silently move a benchmark to synthetic."""
        self.assertLessEqual(set(gb.PLDI_REAL_WORLD_PROGRAMS), self._merged_names())

    def test_the_split(self):
        for program in ("Compiler.hs", "OctTree.hs", "PiecewiseFunctions.hs",
                        "ColorOctree.hs", "DecisionTreeClassify.hs"):
            self.assertEqual(gb.pldi_stage_group(program), "realworld", program)
        for program in ("ArithmeticIntensityInt8.hs", "Add1TreeInt64.hs",
                        "LinearListReduction.hs", "MonoTree.hs", "List.hs"):
            self.assertEqual(gb.pldi_stage_group(program), "synthetic", program)

    def test_real_world_rows_come_first(self):
        matrix = {}
        for name, best in (("MonoTree.hs", 0.1), ("KDTree.hs", 0.5),
                           ("Add1TreeInt8.hs", 0.2), ("Compiler.hs", 0.9)):
            times = {c: 1.0 for c in TestCompactStageChain.FULL}
            times[gb.av_variant_name("soa_loop_sbs_gibvec")] = best
            matrix[name] = {cfg: _make_result(
                name, cfg, {"m": {"median_time": v, "pass_type": "map"}})
                for cfg, v in times.items()}
        rows, _labels, _d = gb._pldi_stage_rows(matrix, "map")
        self.assertEqual([r["program"] for r in rows],
                         ["Compiler", "KDTree", "Add1TreeInt8", "MonoTree"])
        self.assertEqual([r["group"] for r in rows],
                         ["realworld", "realworld", "synthetic", "synthetic"])

    def test_one_figure_per_kind_holds_both_groups(self):
        drawn = []

        def capture(results, out, kind, title, extended=False):
            drawn.append((out.name, sorted(results)))
            return []

        matrix = {name: {"aos_imm": _make_result(name, "aos_imm", {})}
                  for name in ("KDTree.hs", "MonoTree.hs")}
        import tempfile
        with mock.patch.object(gb, "_fig_pldi_stages", capture), \
                mock.patch.object(gb, "_pub_rc", lambda: None):
            with tempfile.TemporaryDirectory() as d:
                gb.generate_pldi_stage_figures(matrix, Path(d))
        self.assertEqual(sorted(name for name, _p in drawn),
                         ["pldi_stages_endtoend", "pldi_stages_fold",
                          "pldi_stages_map"])
        for _name, programs in drawn:
            self.assertEqual(programs, ["KDTree.hs", "MonoTree.hs"])


if __name__ == "__main__":
    unittest.main()
