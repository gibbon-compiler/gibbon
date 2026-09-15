#!/usr/bin/env python3
"""Permanent regression tests: ArithmeticIntensityIntN.hs source policy, the
independent modular oracle's design verification, and the 'Integer-width
high-arithmetic-intensity vectorization' table's eligibility gating --
INCLUDING the width-64 SIMD exclusion (the one structural difference from
the Add1Tree table: W64 must never render a number in its Gibbon-SIMD
column, because the only existing packed W64 multiply helper is a legacy
scalar-spill, not real SIMD).

Four layers:
  - TestArithIntensityOracleModel: the Python oracle
    (oracles/arithintensity_model.py) is internally sound --
    verify_design() proves all eight failure classes are distinguished at
    every width -- and its committed-size values are pinned.
  - TestArithIntensitySourceWidths: static source checks over the eight
    ArithmeticIntensityIntN.hs files (AoS+SoA) -- payload width
    correctness, no bare Int in a semantic signature, AoS/SoA algorithm
    equivalence, no avoidable toInt* inside arithKernel, the kernel's four
    stages are all present exactly once, program/oracle registration.
  - TestArithIntensityWidthTable: the gibbon_benchmark.py table renderer,
    exercised ONLY with synthetic BenchmarkResult/QualificationStatus
    fixtures -- proves an unverified/missing/unsupported variant can never
    reach a numeric cell, and specifically that width 64's SIMD cell is
    ALWAYS N/A even when a (deliberately wrong) synthetic "verified"
    soa_simd result is supplied for it.
  - TestArithIntensityMutations: representative kernel/lane/spill/
    eligibility mutations, applied to real files with restore-and-reverify
    where applicable.
"""
import inspect
import re
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROGRAMS_AOS = HERE / "programs" / "AOS"
PROGRAMS_SOA = HERE / "programs" / "SOA"
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE / "oracles"))

import arithintensity_model as model  # noqa: E402
import gibbon_benchmark as gb  # noqa: E402
import bench_provenance as prov  # noqa: E402
from test_width_migration import parse_data_decl, parse_function_signatures  # noqa: E402

WIDTHS = (8, 16, 32, 64)
LANES = {8: 16, 16: 8, 32: 4, 64: 2}


class TestArithIntensityOracleModel(unittest.TestCase):
    def test_design_verification_passes_at_every_width(self):
        problems = model.verify_design()
        self.assertEqual(problems, [],
                         "arithintensity_model design no longer distinguishes: %s" % problems)

    def test_committed_size_values_are_pinned(self):
        # Regression pin: independently re-derived, then compared against
        # the value recorded from that derivation (oracles/manifest.json) --
        # never copied from Gibbon.
        # Depth 35 values (the layouts were unified there on 2026-09-06,
        # after SoA had drifted to 35 while AoS stayed at 20); the
        # superseded depth-20 values were
        # {8: -101, 16: -12133, 32: -1129983845, 64: -8688910714306965349}.
        # High-intensity kernel (431 ops/element) as of 2026-09-07; the
        # superseded 8-op values were
        # {8: 115, 16: -15757, 32: 803521139, 64: 378431239996359283}.
        expected = {8: 8, 16: -3832, 32: 701296904,
                    64: -8550431977486094072}
        for width, exp in expected.items():
            self.assertEqual(model.expected(width), exp,
                             "width %d oracle value drifted" % width)

    def test_oracle_wraps_after_every_operation_not_at_the_end(self):
        """The oracle must not compute in arbitrary precision and truncate
        only at the end -- verified by checking that `kernel` calls `w`
        (the per-op wrap) after each of the five arithmetic expressions,
        not once on the final result alone."""
        src = Path(model.__file__).read_text()
        m = re.search(r"def kernel\(x, w\):(.*?)\n\n\n", src, re.DOTALL)
        self.assertIsNotNone(m)
        body = m.group(1)
        # Each of a/b/c/d/return applies w(...) to its own multiply/add/sub,
        # not just once at the very end.
        self.assertGreaterEqual(body.count("w("), 8,
                                "expected per-operation wrapping, found too few w() calls")

    def test_leaf_count_matches_documented_fibonacci_shape(self):
        # Read from the closed form, not by building the tree -- at depth 35
        # an explicit tree is 24.2M nodes.
        self.assertEqual(model.leaf_count(), 24157817)

    def test_closed_form_agrees_with_the_literal_build_map_fold(self):
        for depth in (0, 1, 5, 12, 20):
            for width in WIDTHS:
                self.assertEqual(
                    model.expected(width, depth, model.SEED0),
                    model.expected_explicit(width, depth, model.SEED0),
                    "closed form differs from explicit fold at depth %d, "
                    "width %d" % (depth, width))

    def test_model_depth_matches_every_source_file(self):
        # The drift this catches actually happened: the SoA sources were
        # raised to 35 while AoS stayed at 20, so every SoA configuration
        # scored WRONG while benchmarking a 24x larger tree.
        depths = model.source_depths()
        self.assertEqual(len(depths), 8,
                         "expected 8 ArithmeticIntensityIntN.hs sources, "
                         "found %d" % len(depths))
        for path, (depth, seed) in depths.items():
            self.assertEqual((depth, seed), (model.DEPTH0, model.SEED0),
                             "%s builds mkTree %d %d but the oracle models "
                             "mkTree %d %d" % (path, depth, seed,
                                               model.DEPTH0, model.SEED0))

    def test_manifest_matches_the_model(self):
        import json
        manifest = json.loads(
            (HERE / "oracles" / "manifest.json").read_text())["oracles"]
        for width in WIDTHS:
            self.assertEqual(
                manifest["ArithmeticIntensityInt%d" % width]["expected"],
                str(model.expected(width)),
                "manifest ArithmeticIntensityInt%d is stale" % width)



class TestArithIntensitySourceWidths(unittest.TestCase):
    def _path(self, variant_dir, width):
        return variant_dir / ("ArithmeticIntensityInt%d.hs" % width)

    def test_every_file_exists_both_layouts(self):
        for width in WIDTHS:
            for d in (PROGRAMS_AOS, PROGRAMS_SOA):
                self.assertTrue(self._path(d, width).exists(), "%s missing" % self._path(d, width))

    def test_tree_payload_field_matches_declared_width(self):
        for width in WIDTHS:
            for d in (PROGRAMS_AOS, PROGRAMS_SOA):
                text = self._path(d, width).read_text()
                ctors = parse_data_decl(text, "Tree")
                self.assertEqual(ctors["Leaf"], ["Int%d" % width],
                                 "%s: Leaf field is %r, want Int%d" %
                                 (self._path(d, width), ctors["Leaf"], width))

    def test_no_bare_int_in_semantic_signatures(self):
        bare_int = re.compile(r"\bInt\b")
        sig_re = re.compile(r"^([A-Za-z_][A-Za-z0-9_']*)\s*::\s*(.+)$", re.MULTILINE)
        failures = []
        for width in WIDTHS:
            for d in (PROGRAMS_AOS, PROGRAMS_SOA):
                text = self._path(d, width).read_text()
                for m in sig_re.finditer(text):
                    name, rhs = m.group(1), m.group(2)
                    if name not in ("arithKernel", "checksumTree"):
                        continue
                    if bare_int.search(rhs):
                        failures.append("%s %s :: %s" % (self._path(d, width).name, name, rhs.strip()))
        self.assertEqual(failures, [], "\n".join(failures))

    def _kernel_body(self, text):
        m = re.search(r"^arithKernel ::.*?\n(?:arithKernel .*\n(?:  .*\n)*)+", text, re.MULTILINE)
        self.assertIsNotNone(m, "could not isolate arithKernel body")
        return m.group(0)

    def test_kernel_body_has_no_avoidable_conversion(self):
        for width in WIDTHS:
            for d in (PROGRAMS_AOS, PROGRAMS_SOA):
                body = self._kernel_body(self._path(d, width).read_text())
                self.assertNotIn("toInt", body,
                                 "%s: avoidable conversion inside arithKernel" % self._path(d, width))

    def test_kernel_op_count_matches_the_declared_constant(self):
        """The kernel's actual operation count must equal
        gibbon_benchmark.ARITH_OPS_PER_ELEMENT, in every source.

        That constant is the NUMERATOR of the roofline overlay's
        arithmetic-intensity axis, so a source edit that changes the op
        count without updating it silently mis-places every point on the
        plot. Counted from the source rather than asserted as a literal,
        so the two cannot drift.

        (Supersedes a check for exactly 4 multiplies -- the kernel was
        raised from 8 to 431 ops on 2026-09-07 to make it compute-bound.)"""
        import gibbon_benchmark as gb
        for width in WIDTHS:
            for d in (PROGRAMS_AOS, PROGRAMS_SOA):
                body = self._kernel_body(self._path(d, width).read_text())
                # Strip `->` first: the case arrow in `Leaf x ->` would
                # otherwise be counted as a subtraction.
                arith = body.replace("->", " ")
                ops = arith.count("*") + arith.count("+") + arith.count("-")
                self.assertEqual(
                    ops, gb.ARITH_OPS_PER_ELEMENT,
                    "%s: kernel performs %d operations but "
                    "ARITH_OPS_PER_ELEMENT says %d"
                    % (self._path(d, width), ops, gb.ARITH_OPS_PER_ELEMENT))

    def test_kernel_chains_are_independent_and_data_dependent(self):
        """The two properties that make this kernel measure what it claims.

        Independence: a single dependent chain is latency-bound, measured
        at 7.08 vs 50.10 Gop/s for the same op count, so it would raise
        arithmetic intensity without exercising the vector units.

        Data-dependent, odd multiplier: `a*m + c` with CONSTANT m is
        linear, so the rounds fold into one multiply-add and the compiler
        deletes the work (observed: 163.5 Gop/s against a 59.6 ceiling).
        Odd keeps each step a bijection mod 2^k, where squaring collapsed
        64 leaf values to 2 at Int8."""
        for width in WIDTHS:
            for d in (PROGRAMS_AOS, PROGRAMS_SOA):
                body = self._kernel_body(self._path(d, width).read_text())
                self.assertGreaterEqual(
                    len(re.findall(r"\ba\d+_\d+ =", body)), 4,
                    "%s: fewer than 4 independent chains" % self._path(d, width))
                self.assertTrue(
                    re.search(r"\* +ta\d+_\d+|\* +tb\d+_\d+", body),
                    "%s: multiplier is not data-dependent" % self._path(d, width))
                self.assertTrue(
                    re.search(r"t[ab]\d+_\d+ = [ab]\d+_\d+ \+ [ab]\d+_\d+ \+ 1", body),
                    "%s: multiplier is not forced odd (2x+1)" % self._path(d, width))

    def test_no_ordered_comparison_or_division_in_kernel(self):
        """Requirements 9/10: avoid division/modulus/exponentiation and
        ordered comparisons inside the hot kernel (packed W64 ordered
        comparison is unavailable under baseline SSE2)."""
        forbidden = re.compile(r"`div`|`mod`|<=|>=|[<>]|\*\*")
        for width in WIDTHS:
            for d in (PROGRAMS_AOS, PROGRAMS_SOA):
                body = self._kernel_body(self._path(d, width).read_text())
                # Strip every Haskell `->` (function-type AND case-arm
                # arrow -- both use this exact token) before scanning, so
                # its `>` is never mistaken for an ordered-comparison
                # operator; a real `<`/`>` comparison cannot occur adjacent
                # to a `-` this way, since Gibbon has no `-<`/`->`-shaped
                # comparison operator.
                body = body.replace("->", "")
                self.assertIsNone(forbidden.search(body),
                                  "%s: forbidden operator in arithKernel" % self._path(d, width))

    def test_aos_and_soa_agree_on_every_function_signature(self):
        mismatches = []
        for width in WIDTHS:
            aos_sigs = parse_function_signatures(self._path(PROGRAMS_AOS, width).read_text())
            soa_sigs = parse_function_signatures(self._path(PROGRAMS_SOA, width).read_text())
            for name in sorted(set(aos_sigs) & set(soa_sigs)):
                if aos_sigs[name] != soa_sigs[name]:
                    mismatches.append("Int%d.%s: AOS=%r SOA=%r" %
                                      (width, name, aos_sigs[name], soa_sigs[name]))
        self.assertEqual(mismatches, [])

    def test_soa_declares_factored_and_aos_declares_linear(self):
        for width in WIDTHS:
            aos_text = self._path(PROGRAMS_AOS, width).read_text()
            soa_text = self._path(PROGRAMS_SOA, width).read_text()
            self.assertIn('{-# ANN type Tree "Linear" #-}', aos_text)
            self.assertIn('{-# ANN type Tree "Factored" #-}', soa_text)

    def test_arithkernel_is_mayvectorize_annotated_both_layouts(self):
        for width in WIDTHS:
            for d in (PROGRAMS_AOS, PROGRAMS_SOA):
                text = self._path(d, width).read_text()
                self.assertIn('{-# ANN arithKernel "OPT:MayVectorize" #-}', text,
                             "%s missing MayVectorize annotation" % self._path(d, width))

    def test_no_toint64_toint32_round_trip(self):
        pattern = re.compile(r"toInt\d+\s*\(\s*toInt\d+")
        for width in WIDTHS:
            for d in (PROGRAMS_AOS, PROGRAMS_SOA):
                text = self._path(d, width).read_text()
                self.assertIsNone(pattern.search(text),
                                  "%s: width round trip found" % self._path(d, width))

    def test_registered_in_gibbon_benchmark(self):
        for width in WIDTHS:
            self.assertIn("ArithmeticIntensityInt%d.hs" % width, gb.ARITHINTENSITY_WIDTH_PROGRAMS)
            self.assertNotIn("ArithmeticIntensityInt%d.hs" % width, gb.DEFAULT_PROGRAMS)

    def test_registered_in_oracle_manifest(self):
        import json
        manifest = json.loads((HERE / "oracles" / "manifest.json").read_text())["oracles"]
        for width in WIDTHS:
            key = "ArithmeticIntensityInt%d" % width
            self.assertIn(key, manifest, "%s missing from oracles/manifest.json" % key)
            entry = manifest[key]
            self.assertIn(entry.get("provenance"), prov.ORACLE_PROVENANCES)
            self.assertEqual(entry["expected"], str(model.expected(width)))

    def test_every_width_has_a_soa_simd_config(self):
        for width in (8, 16, 32, 64):
            self.assertIn("soa_simd", gb.ARITHINTENSITY_WIDTH_CONFIGS[width])

    def test_w64_simd_enables_the_emulated_multiply(self):
        """The replacement for BW-02's guard.

        W64's SIMD column is only a measurement if the compiler was actually
        permitted to emit the emulated multiply. Without the flag the
        vectorizer declines every W64 multiply, the loop stays scalar, and the
        column would silently duplicate soa_loopify while claiming to be SIMD --
        which is the fabricated-number failure BW-02 existed to prevent."""
        self.assertTrue(
            gb.ARITHINTENSITY_WIDTH_CONFIGS[64]["soa_simd"].get("simd_w64_multiply"))

    def test_only_w64_enables_the_emulated_multiply(self):
        """8/16/32 have native packed multiplies; asking for the emulation
        there would measure something no default build ever emits."""
        for width in (8, 16, 32):
            self.assertFalse(
                gb.ARITHINTENSITY_WIDTH_CONFIGS[width]["soa_simd"].get(
                    "simd_w64_multiply", False))

    def test_c_autovectorizer_off_in_every_column_of_both_width_tables(self):
        """Every column of both integer-width tables must disable the C
        compiler's auto-vectorizer, so the tables measure GIBBON's SIMD pass
        and nothing else.

        This is a REGRESSION guard, not a style preference. The flag used to
        sit only on the Gibbon-side columns while the two raw columns kept
        GCC's vectorizer, which inverted the headline result: measured on
        Int16, the table showed raw 0.1875s against loopified 0.4663s and so
        reported loopification as a 2.5x REGRESSION. Compared with the C
        vectorizer in the same state on both sides, loopification is faster
        either way -- 1.36x with it on, 1.11x with it off. GCC's SLP
        (basic-block) vectorizer reaches the recursive form too, so leaving
        it on anywhere in these tables re-creates that false comparison."""
        tables = [("ADD1TREE_WIDTH_CONFIGS", gb.ADD1TREE_WIDTH_CONFIGS)]
        for width, cfgs in gb.ARITHINTENSITY_WIDTH_CONFIGS.items():
            tables.append(("ARITHINTENSITY_WIDTH_CONFIGS[%d]" % width, cfgs))
        for table_name, cfgs in tables:
            self.assertTrue(cfgs, "%s is empty" % table_name)
            for col, opts in cfgs.items():
                self.assertTrue(
                    opts.get("use_no_gcc_vec", False),
                    "%s column %r does not set use_no_gcc_vec; a column "
                    "compiled with GCC's vectorizer cannot be compared "
                    "against one compiled without it" % (table_name, col))

    def test_width_sweeps_run_at_the_drivers_iteration_count(self):
        """Both width sweeps must be handed --iterations, not left at the
        collector's 1 default.

        At one iteration a cell is a single cold sample with no median
        behind it, and these kernels are not reliable at one sample: the
        campaign's own Int8 SIMD binary measures 0.0916 s as a 21-iteration
        median, and one single-shot run in twelve of that same binary reads
        0.21 s -- 2.3x, enough to rank the width last when it is second
        fastest. The rest of the report is medians over --iterations, so a
        single-shot table is also not comparable with any other table
        here."""
        src = inspect.getsource(gb.main)
        for fn in ("collect_add1tree_width_results",
                   "collect_arithintensity_width_results"):
            call = re.search(re.escape(fn) + r"\((.*?)\)\n", src, re.S)
            self.assertIsNotNone(call, "%s is not called in main()" % fn)
            self.assertIn("iterations=args.iterations", call.group(1),
                          "%s is called without the driver's iteration "
                          "count" % fn)

    def test_collector_forwards_its_iteration_count_to_the_executable(self):
        """The parameter has to reach --iterate, not merely be accepted."""
        seen = []
        real_compile, real_run = gb.compile_one, gb.run_exe
        gb.compile_one = lambda *a, **k: (False, 0.0, "stubbed")
        gb.run_exe = lambda exe, iterations, **k: (
            seen.append(iterations) or (False, 0.0, None, "stubbed", -1))
        try:
            gb.collect_arithintensity_width_results(
                PROGRAMS_AOS.parent, Path("/nonexistent-out"), "gcc",
                False, None, iterations=7)
        finally:
            gb.compile_one, gb.run_exe = real_compile, real_run
        # compile_one is stubbed to fail, so run_exe is never reached; the
        # point of the stub is that the call SHAPE is exercised. Re-run with
        # a succeeding compile stub to see the iteration count itself.
        gb.compile_one = lambda *a, **k: (True, 0.0, None)
        gb.run_exe = lambda exe, iterations, **k: (
            seen.append(iterations) or (False, 0.0, None, "stubbed", -1))
        try:
            gb.collect_arithintensity_width_results(
                PROGRAMS_AOS.parent, Path("/nonexistent-out"), "gcc",
                False, None, iterations=7)
        finally:
            gb.compile_one, gb.run_exe = real_compile, real_run
        self.assertTrue(seen, "run_exe was never called")
        self.assertEqual(set(seen), {7})

    def test_no_gcc_vec_caption_note_states_the_flag_and_its_cost(self):
        """The caption has to say the C vectorizer is off in every column.
        Without that, a reader takes these as ordinary builds and the
        absolute times look inexplicably slow beside the per-program tables,
        which do leave it on."""
        note = gb.no_gcc_vec_caption_note()
        self.assertIn("--no-gcc-vectorize", note)
        self.assertIn("Every column", note)
        # SLP specifically: it is why merely disabling LOOP vectorization
        # would not have been enough for a recursive traversal.
        self.assertIn("SLP", note)
        self.assertIn("higher than a default build", note)

    def test_ops_per_byte_excludes_construction_and_verification(self):
        """arith_intensity_metrics must derive from the KERNEL alone
        (ARITH_OPS_PER_ELEMENT operations, 1 load + 1 store), never from
        mkTree/checksumTree or loop/cursor overhead."""
        for width in WIDTHS:
            m = gb.arith_intensity_metrics(width)
            self.assertEqual(m["ops_per_element"], gb.ARITH_OPS_PER_ELEMENT)
            wb = width // 8
            self.assertEqual(m["bytes_loaded_per_element"], wb)
            self.assertEqual(m["bytes_stored_per_element"], wb)
            self.assertAlmostEqual(m["ops_per_byte"],
                                   gb.ARITH_OPS_PER_ELEMENT / (2 * wb))


def _make_result(program, variant, verified, median_time=None, oracle_status=None):
    t = median_time if median_time is not None else 1.0
    res = gb.BenchmarkResult(program, variant)
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
        st.semantic_output = "42" if oracle_status != prov.ORACLE_MISSING else None
    res.passes = {"arithKernel": {"median_time": t, "pass_type": "map"}}
    res.compile_success = True
    res.run_success = True
    res.qualification = st
    return res


class TestArithIntensityWidthTable(unittest.TestCase):
    def _render(self, results_by_width):
        import io
        buf = io.StringIO()
        gb._table_arith_intensity(buf, results_by_width)
        return buf.getvalue()

    def test_all_verified_renders_numeric_cells_and_speedups(self):
        results = {32: {
            "aos_mut": _make_result("ArithmeticIntensityInt32.hs", "aos_mut", True, median_time=4.0),
            "soa_mut": _make_result("ArithmeticIntensityInt32.hs", "soa_mut", True, median_time=2.0),
            "soa_loopify": _make_result("ArithmeticIntensityInt32.hs", "soa_loopify", True, median_time=2.0),
            "soa_simd": _make_result("ArithmeticIntensityInt32.hs", "soa_simd", True, median_time=0.5),
        }}
        out = self._render(results)
        self.assertIn("Int32", out)
        self.assertIn("4.000000", out)
        self.assertIn("2.000000", out)
        self.assertIn("0.500000", out)
        self.assertIn(r"$\times$", out)

    def test_w64_simd_column_reports_its_measurement(self):
        """W64's SIMD cell used to be hardcoded N/A. It is now a measurement
        like any other, and the row says the multiply is emulated so a reader
        does not mistake it for a native one."""
        results = {64: {
            "aos_mut": _make_result("ArithmeticIntensityInt64.hs", "aos_mut", True, median_time=4.0),
            "soa_loopify_shared": _make_result("ArithmeticIntensityInt64.hs",
                                               "soa_loopify_shared", True, median_time=2.0),
            "soa_simd": _make_result("ArithmeticIntensityInt64.hs", "soa_simd", True, median_time=8.0),
        }}
        out = self._render(results)
        self.assertIn("8.000000", out)
        self.assertIn("emulated multiply", out)

    def test_w64_row_renders_even_with_no_config_present_at_all(self):
        results = {64: {
            "aos_mut": _make_result("ArithmeticIntensityInt64.hs", "aos_mut", True, median_time=1.0),
        }}
        out = self._render(results)
        row = [l for l in out.splitlines() if l.startswith("Int64")][0]
        self.assertIn("N/A", row)

    def test_unverified_variant_renders_na_not_a_number(self):
        results = {8: {
            "aos_mut": _make_result("ArithmeticIntensityInt8.hs", "aos_mut", True, median_time=1.0),
            "soa_mut": _make_result("ArithmeticIntensityInt8.hs", "soa_mut", False),
            "soa_loopify": _make_result("ArithmeticIntensityInt8.hs", "soa_loopify", True, median_time=1.0),
            "soa_simd": _make_result("ArithmeticIntensityInt8.hs", "soa_simd", True, median_time=0.5),
        }}
        out = self._render(results)
        row = [l for l in out.splitlines() if l.startswith("Int8")][0]
        cells = [c.strip() for c in row.split("&")]
        self.assertEqual(cells[6], "N/A")  # SoA raw

    def test_speedup_never_computed_from_non_positive_denominator(self):
        results = {16: {
            "soa_loopify": _make_result("ArithmeticIntensityInt16.hs", "soa_loopify", True, median_time=1.0),
            "soa_simd": _make_result("ArithmeticIntensityInt16.hs", "soa_simd", True, median_time=0.0),
        }}
        spd, reason = prov.safe_speedup(
            results[16]["soa_loopify"], results[16]["soa_simd"], gb.total_pass_time)
        self.assertIsNone(spd)
        self.assertIn("not positive", reason)

    def test_ops_per_byte_columns_are_always_numeric_and_static(self):
        """The structural intensity columns (ops/elem, bytes ld/st,
        ops/byte) are not gated on qualification at all -- they are
        compile-time constants of the kernel, present even for a row with
        zero verified variants."""
        results = {8: {}}
        out = self._render(results)
        row = [l for l in out.splitlines() if l.startswith("Int8")][0]
        cells = [c.strip() for c in row.split("&")]
        self.assertEqual(cells[1], str(gb.ARITH_OPS_PER_ELEMENT))   # ops/elem
        self.assertEqual(cells[2], "1")   # bytes loaded/elem
        self.assertEqual(cells[3], "1")   # bytes stored/elem
        # ops/byte = ARITH_OPS_PER_ELEMENT / (load + store bytes);
        # width 8 is 1 byte each way.
        self.assertEqual(cells[4], "%.2f" % (gb.ARITH_OPS_PER_ELEMENT / 2.0))


class TestArithIntensityMutations(unittest.TestCase):
    def test_wrong_payload_width_is_caught(self):
        path = PROGRAMS_AOS / "ArithmeticIntensityInt32.hs"
        backup = path.read_text()
        try:
            mutated = backup.replace("data Tree = Leaf Int32", "data Tree = Leaf Int64", 1)
            path.write_text(mutated)
            ctors = parse_data_decl(path.read_text(), "Tree")
            self.assertNotEqual(ctors["Leaf"], ["Int32"])
        finally:
            path.write_text(backup)
        self.assertEqual(path.read_text(), backup)

    def test_aos_soa_disagreement_is_caught(self):
        path = PROGRAMS_AOS / "ArithmeticIntensityInt16.hs"
        backup = path.read_text()
        try:
            mutated = backup.replace(
                "checksumTree :: Tree -> Int16 -> Int16",
                "checksumTree :: Tree -> Int16 -> Int", 1)
            path.write_text(mutated)
            aos_sigs = parse_function_signatures(path.read_text())
            soa_sigs = parse_function_signatures((PROGRAMS_SOA / "ArithmeticIntensityInt16.hs").read_text())
            self.assertNotEqual(aos_sigs.get("checksumTree"), soa_sigs.get("checksumTree"))
        finally:
            path.write_text(backup)
        self.assertEqual(path.read_text(), backup)

    def test_dropped_kernel_stage_is_caught_by_oracle(self):
        """A stage-omitted kernel (matching model._kernel_stage_omitted)
        must diverge from the correct value.

        Run at VERIFY_DEPTH, not DEPTH0: this asserts a property of the
        KERNEL (a corrupted one is detectable), which does not depend on the
        committed depth, and DEPTH0's 24.2M-leaf tree cannot be built."""
        depth = model.VERIFY_DEPTH
        corrupted = model.checksum(
            model.apply_kernel(model.build(depth, model.SEED0),
                               model._kernel_stage_omitted, model.wrap(32)),
            0, model.wrap(32))
        self.assertNotEqual(corrupted, model.expected(32, depth, model.SEED0))

    def test_a_w64_simd_row_is_marked_emulated_however_fast_it_claims_to_be(self):
        """The mutation framing of the same guarantee: a fast W64 SIMD number
        is reported, but never as an ordinary native-SIMD result."""
        results = {64: {"soa_simd": _make_result(
            "ArithmeticIntensityInt64.hs", "soa_simd", True, median_time=0.01)}}
        import io
        buf = io.StringIO()
        gb._table_arith_intensity(buf, results)
        out = buf.getvalue()
        self.assertIn("emulated multiply", out)


if __name__ == "__main__":
    unittest.main()
