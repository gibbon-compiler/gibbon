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
import io
import sys
import unittest
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
        aos_extra = set(gb.PLDI_MAP_CONFIGS["aos"]) - set(gb.PLDI_FOLD_CONFIGS["aos"])
        soa_extra = set(gb.PLDI_MAP_CONFIGS["soa"]) - set(gb.PLDI_FOLD_CONFIGS["soa"])
        self.assertEqual(len(aos_extra), 2, "AoS maps should add exactly 2 rows beyond folds")
        self.assertEqual(len(soa_extra), 5, "SoA maps should add exactly 5 rows beyond folds")

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
        # "+c" was ambiguous (C compiler? C auto-vec?) and, at plain
        # superscript size, the binary + is set as large as the subscript
        # letters and reads as part of the name rather than as a modifier.
        for key in ("aos_loop_gccvec_on", "soa_loop_gccvec_on_sbs_on",
                    "soa_loop_gccvec_on_sbs_on_gibvec_on"):
            sym = gb.PLDI_COL_SYMBOLS[key]
            self.assertIn("+av", sym)
            self.assertNotIn("+c", sym)
            self.assertIn("\\scriptscriptstyle", sym)

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
        loop_sym = gb.PLDI_COL_SYMBOLS["soa_loop_gccvec_on_sbs_on_gibvec_on"]
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
        self.assertEqual(cells[1 + keys.index("soa_imm")], gb.PLDI_SYM_NOT_MEASURED)

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
            "aos_loop_gccvec_off": _make_result("DomTree.hs", "aos_loop_gccvec_off", {
                "computeWidths": {"median_time": 0.03, "pass_type": "map"}}),
        }
        out = self._render("DomTree.hs", results, "map")
        row = [l for l in out.splitlines() if l.startswith("computeWidths &")][0]
        cells = [c.strip() for c in row.rstrip(" \\").split("&")]
        keys = (list(gb.PLDI_MAP_CONFIGS["aos"]) + list(gb.PLDI_MAP_CONFIGS["soa"]))
        self.assertEqual(cells[1 + keys.index("aos_loop_gccvec_off")], "0.03")

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
        self.assertIn("C auto-vectorization", out)

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
                      "\\small", "\\toprule", "\\midrule", "\\bottomrule",
                      "\\cmidrule(lr)"):
            self.assertIn(token, out)
        # The shabby draft leaned on \resizebox to fit; the compact column
        # symbols replace it, so the font stays consistent with Table 1.
        self.assertNotIn("resizebox", out)

    def test_wide_map_table_steps_down_one_font_size_instead_of_resizing(self):
        # 13 configuration columns do not fit the text width at \small, so
        # the map tables use \footnotesize plus a tighter \tabcolsep (both
        # local to the table environment) rather than a \resizebox, which
        # would rescale the font out of step with the rest of the paper.
        results = {"aos_mut": _make_result("P.hs", "aos_mut", {
            "m": {"median_time": 0.01, "pass_type": "map"},
            "g": {"median_time": 0.02, "pass_type": "fold"},
        })}
        map_out = self._render("P.hs", results, "map")
        fold_out = self._render("P.hs", results, "fold")
        self.assertIn("\\footnotesize", map_out)
        self.assertIn("\\setlength{\\tabcolsep}{4pt}", map_out)
        self.assertNotIn("resizebox", map_out)
        # The 6-column fold table keeps the surrounding tables' \small.
        self.assertIn("\\small", fold_out)
        self.assertNotIn("\\footnotesize", fold_out)


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


if __name__ == "__main__":
    unittest.main()


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
        self.assertEqual(gb.SUMMARY_LOOPIFIED_AOS, "aos_loop_gccvec_on")
        self.assertEqual(gb.SUMMARY_LOOPIFIED_SOA,
                         "soa_loop_gccvec_on_sbs_on_gibvec_on")
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
        self.assertEqual(out.count("$A_{\\ell}^{\\scriptscriptstyle +av}$ (s)"), 3)
        self.assertEqual(out.count("$S_{\\ell bv}^{\\scriptscriptstyle +av}$ (s)"), 3)

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
        buf = io.StringIO()
        gb._table_pldi_fold(buf, "P.hs", results)
        caption = buf.getvalue()
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
        buf = io.StringIO()
        gb._table_pldi_fold(buf, "P.hs", results)
        caption = buf.getvalue()
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
        buf = io.StringIO()
        gb._table_pldi_fold(buf, "P.hs", results)
        cap = buf.getvalue()
        self.assertIn("columns THIS table", cap)
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
        buf = io.StringIO()
        gb._table_pldi_map(buf, "P.hs", results)
        cap = buf.getvalue()
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
        buf = io.StringIO()
        gb._table_pldi_map(buf, "P.hs", results)
        cap = buf.getvalue()
        self.assertIn("columns THIS table", cap)
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
             "aos_loop_gccvec_off": 0.04, "aos_loop_gccvec_on": 0.03,
             "soa_imm": 0.20, "soa_imm_notco": 0.24,
             "soa_mut_notco": 0.16, "soa_mut": 0.12,
             "soa_loop_gccvec_off_sbs_off": 0.10,
             "soa_loop_gccvec_off_sbs_on": 0.06,
             "soa_loop_gccvec_on_sbs_on": 0.05,
             # Deliberately SLOWER than sbs_on: Gibbon vectorization hurting
             # is the case an absolute value would hide.
             "soa_loop_gccvec_off_sbs_on_gibvec_on": 0.07,
             "soa_loop_gccvec_on_sbs_on_gibvec_on": 0.045}

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
        syms = [c[1] for c in gb.PLDI_DELTA_COLUMNS_MAP]
        self.assertEqual(syms[:2], [c[1] for c in gb.PLDI_DELTA_COLUMNS_FOLD[:2]])
        aos_count = sum(1 for c in gb.PLDI_DELTA_COLUMNS_MAP if c[0] == "AoS")
        self.assertEqual(syms[aos_count:aos_count + 2],
                         [c[1] for c in gb.PLDI_DELTA_COLUMNS_FOLD[2:]])

    def test_map_table_has_the_twelve_requested_columns(self):
        self.assertEqual(
            [c[1] for c in gb.PLDI_DELTA_COLUMNS_MAP],
            ["$\\Delta^{A}_{m}$", "$\\Delta^{A}_{t}$", "$\\Delta^{A}_{\\ell}$",
             "$\\Delta^{A}_{av}$",
             "$\\Delta^{S}_{m}$", "$\\Delta^{S}_{t}$", "$\\Delta^{S}_{\\ell}$",
             "$\\Delta^{S}_{b}$", "$\\Delta^{S}_{av}$", "$\\Delta^{S}_{v}$",
             "$\\Delta^{S}_{av|v}$", "$\\Delta^{S}_{v|av}$"])
        _out, cells = self._row("map")
        self.assertEqual(len(cells), 12)

    def test_delta_subscripts_reuse_the_runtime_symbol_vocabulary(self):
        # A delta column must not invent a letter for a feature the
        # configuration symbols already name -- a reader who has learned
        # Table 2 should be able to read a delta column unaided.
        import re
        vocabulary = {"m", "i", "r", "\\ell", "b", "v", "av", "t"}
        for _l, sym, _b, _f, _d in gb.PLDI_DELTA_COLUMNS_MAP:
            subscript = re.search(r"_\{([^}]*)\}", sym).group(1)
            for token in subscript.split("|"):
                self.assertIn(token, vocabulary,
                              "%s uses %r, which names no configuration "
                              "feature" % (sym, token))

    def test_c_auto_vectorization_is_spelled_av_everywhere(self):
        # The configuration symbols spell it `+av`; the delta columns must
        # not call the same knob `c`.
        syms = [c[1] for c in gb.PLDI_DELTA_COLUMNS_MAP]
        self.assertIn("$\\Delta^{S}_{av}$", syms)
        self.assertIn("$\\Delta^{A}_{av}$", syms)
        for sym in syms:
            self.assertNotIn("_{c}", sym)
            self.assertNotIn("c|", sym)
            self.assertNotIn("|c}", sym)
        self.assertTrue(any("+av" in s for s in gb.PLDI_COL_SYMBOLS.values()))

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
        self.assertEqual(by_sym["$\\Delta^{S}_{b}$"], "+66.67\\%")     # (.10-.06)/.06
        self.assertEqual(by_sym["$\\Delta^{S}_{v}$"], "$-$14.29\\%")   # (.06-.07)/.07
        self.assertEqual(by_sym["$\\Delta^{S}_{av|v}$"], "+55.56\\%")  # (.07-.045)/.045
        self.assertEqual(by_sym["$\\Delta^{S}_{v|av}$"], "+11.11\\%")  # (.05-.045)/.045

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

    def test_vanilla_config_is_stock_gibbon(self):
        self.assertEqual(gb.SUMMARY_VANILLA_AOS, "aos_imm")
        cfg = gb.PLDI_MAP_CONFIGS["aos"][gb.SUMMARY_VANILLA_AOS]
        self.assertFalse(cfg.get("use_mutable_cursors", False))
        self.assertFalse(cfg.get("enable_loopification", False))
        self.assertFalse(cfg.get("enable_vectorization", False))
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
