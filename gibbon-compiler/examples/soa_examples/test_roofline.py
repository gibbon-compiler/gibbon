#!/usr/bin/env python3
"""Permanent regression tests for the --roofline mode.

The measurement itself is a real compile-and-run and is NOT re-run here
(it takes ~20s); these tests cover the parts that can silently produce a
wrong number: the embedded probe source's anti-optimization guards, the
ridge-point arithmetic, the overlay's op accounting, and the fact that the
probe never touches Gibbon's shared RTS build directory.
"""
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import gibbon_benchmark as gb  # noqa: E402
import bench_provenance as prov  # noqa: E402


class TestProbeSourceGuards(unittest.TestCase):
    """The probe measures a ceiling by counting ops it assumes executed.
    Every way the compiler can delete that work is a way to report a
    fabricated number, so each defence is pinned here."""

    def test_multiply_operands_are_opaque(self):
        # With a literal 1, `a*x+y` folds to `a+y`: half the counted work
        # disappears and the reported ceiling roughly doubles. An earlier
        # revision did exactly this and reported integer ceilings that were
        # suspiciously exactly proportional to lane count.
        self.assertIn("OPAQUE_SEED", gb.ROOFLINE_SOURCE)
        self.assertIn("volatile", gb.ROOFLINE_SOURCE)
        self.assertIn("opaque_one()", gb.ROOFLINE_SOURCE)

    def test_accumulators_are_register_resident_vectors(self):
        # Plain arrays made the loop store-bound and measured ~5.5 GFLOPS
        # instead of ~76. Vector extensions keep each accumulator in a
        # register.
        self.assertIn("vector_size", gb.ROOFLINE_SOURCE)
        self.assertIn("__asm__ __volatile__", gb.ROOFLINE_SOURCE)

    def test_results_are_consumed_so_the_loops_cannot_be_deleted(self):
        self.assertIn("defeat DCE", gb.ROOFLINE_SOURCE)

    def test_probe_is_single_threaded(self):
        # No OpenMP: the Gibbon benchmarks this bounds are single-threaded.
        self.assertNotIn("omp.h", gb.ROOFLINE_SOURCE)
        self.assertNotIn("#pragma omp", gb.ROOFLINE_SOURCE)

    def test_stream_array_is_far_larger_than_any_llc(self):
        # A triad that fits in cache measures cache bandwidth, not DRAM.
        self.assertIn("STREAM_N", gb.ROOFLINE_SOURCE)
        self.assertIn("32u * 1000u * 1000u", gb.ROOFLINE_SOURCE)

    def test_probe_is_plain_c_and_needs_no_extra_toolchain(self):
        self.assertNotIn("#include <iostream>", gb.ROOFLINE_SOURCE)
        self.assertIn("#include <stdio.h>", gb.ROOFLINE_SOURCE)

    def test_probe_never_invokes_gibbon(self):
        # It must not be able to disturb (or be disturbed by) a campaign:
        # every `gibbon` invocation rebuilds the RTS into one shared
        # directory, so two concurrent ones race on the same object files.
        # Checked structurally -- no call to any Gibbon-invoking helper --
        # rather than by grepping prose.
        import ast
        import inspect
        tree = ast.parse(inspect.getsource(gb.run_roofline_probe))
        called = {n.func.id for n in ast.walk(tree)
                  if isinstance(n, ast.Call) and isinstance(n.func, ast.Name)}
        for helper in ("build_gibbon_command", "compile_one", "run_exe"):
            self.assertNotIn(helper, called,
                             "the roofline probe calls %s, which can invoke "
                             "gibbon and race a running campaign" % helper)
        # ... and the only executable it runs is the probe it just built.
        src_lines = [l.split("#")[0] for l in
                     inspect.getsource(gb.run_roofline_probe).splitlines()]
        code = "\n".join(l for l in src_lines if not l.strip().startswith('"'))
        self.assertNotIn("gibbon_exe", code)


class TestRidgePoints(unittest.TestCase):
    def test_ridge_is_peak_over_bandwidth(self):
        results = {"BANDWIDTH_GB_S": 25.0, "INT16_GIOPS": 200.0,
                   "FP64_GFLOPS": 75.0}
        ridges = gb.roofline_ridge_points(results)
        self.assertAlmostEqual(ridges["INT16_GIOPS"], 8.0)
        self.assertAlmostEqual(ridges["FP64_GFLOPS"], 3.0)
        self.assertNotIn("BANDWIDTH_GB_S", ridges)

    def test_every_measured_ceiling_gets_a_ridge(self):
        results = {k: 10.0 for k in gb.ROOFLINE_KEYS}
        ridges = gb.roofline_ridge_points(results)
        self.assertEqual(len(ridges), len(gb.ROOFLINE_KEYS) - 1)


class TestOverlayPoints(unittest.TestCase):
    def _res(self, width, cfg, t, verified=True):
        res = gb.BenchmarkResult("ArithmeticIntensityInt%d.hs" % width, cfg)
        st = prov.QualificationStatus(cfg, res.program)
        st.compile_status = prov.COMPILE_OK
        st.exec_status = prov.EXEC_OK
        st.oracle_status = prov.ORACLE_PASS if verified else prov.ORACLE_FAIL
        st.semantic_output = "42"
        st.oracle_detail = "" if verified else "synthetic"
        res.compile_success = res.run_success = True
        res.passes = {"arithKernel": {"median_time": t, "pass_type": "map"},
                      "checksumTree": {"median_time": 9.0, "pass_type": "fold"}}
        res.qualification = st
        return res

    def test_x_is_the_suites_own_ops_per_byte(self):
        pts = gb.roofline_overlay_points({32: {"soa_mut": self._res(32, "soa_mut", 0.5)}},
                                         leaf_count=1000)
        self.assertEqual(len(pts), 1)
        self.assertAlmostEqual(pts[0]["ops_per_byte"],
                               gb.arith_intensity_metrics(32)["ops_per_byte"])

    def test_y_is_total_ops_over_measured_time(self):
        leaves = 1_000_000
        pts = gb.roofline_overlay_points({16: {"soa_mut": self._res(16, "soa_mut", 0.25)}},
                                         leaf_count=leaves)
        ops = leaves * gb.arith_intensity_metrics(16)["ops_per_element"]
        self.assertAlmostEqual(pts[0]["gops"], ops / 0.25 / 1e9)

    def test_verification_pass_is_not_plotted(self):
        # checksumTree is correctness apparatus; plotting it as a kernel
        # would put a meaningless point on the roofline.
        pts = gb.roofline_overlay_points({8: {"soa_mut": self._res(8, "soa_mut", 0.5)}},
                                         leaf_count=1000)
        self.assertEqual([p["pass"] for p in pts], ["arithKernel"])

    def test_unverified_result_contributes_no_point(self):
        pts = gb.roofline_overlay_points(
            {8: {"soa_mut": self._res(8, "soa_mut", 0.5, verified=False)}},
            leaf_count=1000)
        self.assertEqual(pts, [])

    def test_no_results_is_empty_not_an_error(self):
        self.assertEqual(gb.roofline_overlay_points(None), [])
        self.assertEqual(gb.roofline_overlay_points({}), [])

    def test_each_point_carries_its_own_iteration_count_and_timestamp(self):
        """Per-MEASUREMENT provenance, not just per-campaign.

        A single overlay entry is the only record of what produced it, and
        without the iteration count behind it a median and a single cold
        sample are indistinguishable after the fact -- which is exactly the
        question asked of a cell that reads several times its neighbours."""
        res = self._res(32, "soa_simd", 0.5)
        res.passes["arithKernel"]["n"] = 51
        res.run_finished_at = "2026-09-14T17:00:00"
        pts = gb.roofline_overlay_points({32: {"soa_simd": res}}, leaf_count=1000)
        self.assertEqual(pts[0]["iterations"], 51)
        self.assertEqual(pts[0]["measured_at"], "2026-09-14T17:00:00")

    def test_a_dram_reading_below_the_models_own_bound_is_rejected(self):
        """The model counts the Leaf field and nothing else, so real traffic
        can only exceed it. A counter that has stopped reporting yields a
        few MB against a gigabyte-per-iteration kernel, and the resulting
        x-coordinate -- which is the one that gets plotted -- lands three
        orders of magnitude out with nothing saying so."""
        res = self._res(32, "soa_simd", 0.5)
        pts = gb.roofline_overlay_points(
            {32: {"soa_simd": res}}, leaf_count=1_000_000,
            measured_bytes={(32, "soa_simd"): 1_000_000.0})
        model = gb.arith_intensity_metrics(32)["ops_per_byte"]
        self.assertAlmostEqual(pts[0]["ops_per_byte"], model)
        self.assertIsNone(pts[0]["ops_per_byte_measured"])
        self.assertIsNone(pts[0]["dram_bytes_per_iteration"])
        self.assertIn("rejected a DRAM reading", pts[0]["intensity_source"])

    def test_a_plausible_dram_reading_is_still_used(self):
        leaves = 1_000_000
        ops = leaves * gb.arith_intensity_metrics(32)["ops_per_element"]
        model = gb.arith_intensity_metrics(32)["ops_per_byte"]
        # Ten times the model's byte count, i.e. an ops/byte a tenth of it.
        big = ops / (model / 10.0)
        pts = gb.roofline_overlay_points(
            {32: {"soa_simd": self._res(32, "soa_simd", 0.5)}},
            leaf_count=leaves, measured_bytes={(32, "soa_simd"): big})
        self.assertAlmostEqual(pts[0]["ops_per_byte"], model / 10.0)
        self.assertEqual(pts[0]["dram_bytes_per_iteration"], big)
        self.assertIn("measured DRAM traffic", pts[0]["intensity_source"])

    def test_missing_per_measurement_provenance_is_null_not_absent(self):
        # A consumer must be able to tell "one iteration" from "unknown".
        pts = gb.roofline_overlay_points({32: {"soa_mut": self._res(32, "soa_mut", 0.5)}},
                                         leaf_count=1000)
        self.assertIn("iterations", pts[0])
        self.assertIn("measured_at", pts[0])
        self.assertIsNone(pts[0]["iterations"])
        self.assertIsNone(pts[0]["measured_at"])


class TestOutputs(unittest.TestCase):
    RESULTS = {"BANDWIDTH_GB_S": 28.11, "FP64_GFLOPS": 77.2,
               "INT8_GIOPS": 111.37, "INT16_GIOPS": 203.81,
               "INT32_GIOPS": 60.17, "INT64_GIOPS": 13.24}

    def test_json_carries_measurements_ridges_and_caveats(self):
        with tempfile.TemporaryDirectory() as d:
            out, figs = Path(d) / "o", Path(d) / "f"
            path = gb.write_roofline_outputs(self.RESULTS, out, figs,
                                             machine={"cpu": "test"})
            data = json.loads(path.read_text())
        self.assertEqual(data["measurements"], self.RESULTS)
        self.assertIn("ridge_points_ops_per_byte", data)
        # The caveats must travel WITH the numbers -- a bandwidth figure
        # whose byte-accounting convention is unstated is not reusable.
        self.assertIn("24 B/element", data["notes"]["bandwidth"])
        self.assertIn("single-threaded", data["notes"]["threading"])

    def test_plot_script_is_emitted_even_without_matplotlib(self):
        with tempfile.TemporaryDirectory() as d:
            out, figs = Path(d) / "o", Path(d) / "f"
            gb.write_roofline_outputs(self.RESULTS, out, figs)
            self.assertTrue((figs / "plot_roofline.py").exists())

    def test_plot_script_can_find_the_driver_from_any_figures_dir(self):
        # --figures-dir may be anywhere, so the script cannot locate
        # gibbon_benchmark.py by walking up from its own path; an earlier
        # version did and died with ModuleNotFoundError.
        with tempfile.TemporaryDirectory() as d:
            figs = Path(d) / "deeply" / "nested" / "elsewhere"
            gb.write_roofline_outputs(self.RESULTS, Path(d) / "o", figs)
            script = (figs / "plot_roofline.py").read_text()
        self.assertNotIn("@@DRIVER_DIR@@", script)
        self.assertIn(str(Path(gb.__file__).resolve().parent), script)

    def test_generated_plot_script_actually_runs(self):
        # End-to-end: generate data + script, then run the script exactly as
        # a user would and confirm it produces a PNG.
        import subprocess
        with tempfile.TemporaryDirectory() as d:
            out, figs = Path(d) / "o", Path(d) / "f"
            data = gb.write_roofline_outputs(self.RESULTS, out, figs)
            png = Path(d) / "redrawn.png"
            proc = subprocess.run(
                [sys.executable, str(figs / "plot_roofline.py"), str(data), str(png)],
                capture_output=True, text=True)
            # The plot needs numpy as well as matplotlib, so guard on
            # either being absent -- guarding on matplotlib alone turned a
            # missing numpy into a spurious failure of the RENDERER.
            for mod in ("matplotlib", "numpy"):
                if "No module named '%s'" % mod in proc.stderr:
                    self.skipTest("%s not importable in this interpreter" % mod)
            self.assertEqual(proc.returncode, 0, proc.stderr[-800:])
            self.assertTrue(png.exists() and png.stat().st_size > 0)

    def test_ceiling_table_covers_every_measured_key(self):
        keys = {k for k, _s, _l in gb.ROOFLINE_CEILINGS}
        self.assertEqual(keys, set(gb.ROOFLINE_KEYS) - {"BANDWIDTH_GB_S"})


if __name__ == "__main__":
    unittest.main()
