#!/usr/bin/env python3
"""Regression tests for what a hardware count means, on both backends.

  - TestSharedLabels: the shared counters carry the same labels in the
    driver, the PAPI path (Codegen.hs) and the kperf path (gibbon_rts.c), so
    an M1 table and an x86 table line up row for row.
  - TestUnavailable: a metric the CPU has no event for is reported as
    unavailable, never as a count, and the notes say so.
  - TestEvents: the notes name the event behind every counter and warn when
    one counter was read from more than one event.
  - TestNoiseFloor: rows of a handful of counts get no fastest/slowest marks,
    a counter that is all noise collapses to one line, and a ratio of noise
    is not printed.
  - TestWindow: the notes say what a count covers, and a stored report from
    before the counter reads moved inside the timed region says so.
"""
import importlib
import io
import json
import os
import re
import unittest.mock
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
REPO = HERE.parents[2]

import gibbon_benchmark as gb  # noqa: E402
from test_kperf_counters import _counted, _verified  # noqa: E402


def _tex(results):
    buf = io.StringIO()
    gb.write_pldi_counter_tables(buf, results)
    return buf.getvalue()


def _c_labels(text: str, array: str):
    body = re.search(array + r"\[[A-Z_]+\] = \{(.*?)\};", text, re.S).group(1)
    return re.findall(r'\\?"([A-Z0-9_]+)\\?"', body)


class TestSharedLabels(unittest.TestCase):
    def test_papi_labels_match_codegen(self):
        src = (REPO / "gibbon-compiler/src/Gibbon/Passes/Codegen.hs").read_text()
        self.assertEqual(_c_labels(src, "gibbon_native_papi_metric_labels"),
                         list(gb.PAPI_COUNTER_METRICS))

    def test_kperf_labels_match_the_runtime_as_a_set(self):
        src = (REPO / "gibbon-rts/rts-c/gibbon_rts.c").read_text()
        self.assertEqual(sorted(_c_labels(src, "gib_kperf_metric_labels")),
                         sorted(gb.KPERF_COUNTER_METRICS))

    def test_both_backends_report_every_shared_counter(self):
        for m in gb.SHARED_COUNTER_METRICS:
            self.assertIn(m, gb.PAPI_COUNTER_METRICS)
            self.assertIn(m, gb.KPERF_COUNTER_METRICS)
            for backend in ("papi", "kperf"):
                self.assertIn(m, gb.COUNTER_DEFINITIONS[backend], (backend, m))

    def test_l2_and_llc_are_x86_only(self):
        for m in ("L2_LOAD_MISSES_RETIRED", "LLC_LOAD_MISSES_RETIRED"):
            self.assertIn(m, gb.PAPI_COUNTER_METRICS)
            self.assertNotIn(m, gb.KPERF_COUNTER_METRICS)


class TestPapiGroups(unittest.TestCase):
    def setUp(self):
        self.addCleanup(importlib.reload, gb)

    def test_groups_match_codegen_and_cover_every_metric_once(self):
        src = (REPO / "gibbon-compiler/src/Gibbon/Passes/Codegen.hs").read_text()
        masks = [int(m) for m in re.search(
            r"gibbon_native_papi_metric_groups\[[A-Z_]+\] = \{\\n\\\s*\\\s*([0-9, ]+),",
            src).group(1).split(",")]
        for metric, mask in zip(gb.PAPI_COUNTER_METRICS, masks):
            groups = {g for g, ms in gb.PAPI_COUNTER_GROUPS.items() if metric in ms}
            self.assertEqual(groups, {g for g in gb.PAPI_COUNTER_GROUPS if mask & (1 << (g - 1))},
                             metric)

    def test_each_group_fits_four_programmable_counters(self):
        for g, ms in gb.PAPI_COUNTER_GROUPS.items():
            self.assertLessEqual(len([m for m in ms if m not in ("CPU_CYCLES", "INSTRUCTIONS")]),
                                 4, g)

    def test_groups_merge_into_one_result(self):
        def run(counters, unavailable=()):
            res = _counted("P.hs", "aos_mut", {"p": ("fold", counters)})
            if unavailable:
                res.passes["p"]["papi_unavailable"] = list(unavailable)
            return {"P.hs": {"aos_mut": res}}
        first = run({"CPU_CYCLES": 10.0, "L1D_LOAD_MISSES_RETIRED": 5.0})
        second = run({"CPU_CYCLES": 99.0, "L1I_MISSES": 7.0}, unavailable=["DTLB_MISSES"])
        merged = gb.merge_counter_groups([first, second])["P.hs"]["aos_mut"].passes["p"]
        self.assertEqual({m: v["median"] for m, v in merged["papi_counters"].items()},
                         {"CPU_CYCLES": 10.0, "L1D_LOAD_MISSES_RETIRED": 5.0, "L1I_MISSES": 7.0})
        self.assertEqual(merged["papi_native_events"]["L1I_MISSES"], "EV_L1I_MISSES")
        self.assertEqual(merged["papi_unavailable"], ["DTLB_MISSES"])

    def test_the_phase_runs_each_group_with_its_variable(self):
        seen = []

        def fake(*_a, **kw):
            seen.append((os.environ.get("GIBBON_PAPI_GROUP"), _a[3]))
            return {}
        with unittest.mock.patch.object(gb, "collect_pldi_variant_results", fake):
            gb.collect_pldi_counter_results(Path("p"), Path("o"), "gcc", True, 1, pin_cpu=2)
        self.assertEqual(seen, [("1", True), ("2", False)])
        self.assertNotIn("GIBBON_PAPI_GROUP", os.environ)


class TestUnavailable(unittest.TestCase):
    def setUp(self):
        self.addCleanup(importlib.reload, gb)

    def test_an_unavailable_metric_is_recorded_not_counted(self):
        res = _verified("P.hs", "aos_mut", {"p": {"median_time": 0.1, "pass_type": "fold"}})
        gb.attach_papi_native_to_passes(res, (
            "Running pass p (fold, uses=1):\n"
            "PAPI_NATIVE DTLB_MISSES[unavailable]\n"
            "PAPI_NATIVE CPU_CYCLES[perf::CYCLES]=500\n"
            "End\n"))
        pdata = res.passes["p"]
        self.assertEqual(pdata["papi_unavailable"], ["DTLB_MISSES"])
        self.assertNotIn("DTLB_MISSES", pdata["papi_counters"])
        self.assertEqual(pdata["papi_counters"]["CPU_CYCLES"]["median"], 500)

    def test_the_unavailable_line_is_not_program_output(self):
        import bench_provenance as prov
        self.assertEqual(prov.semantic_output("PAPI_NATIVE DTLB_MISSES[unavailable]\n42\n").strip(),
                         "42")

    def test_the_notes_name_what_was_not_counted(self):
        gb.apply_config_selection(["aos_mut", "ptr"])
        results = {"P.hs": {cfg: _counted("P.hs", cfg, {"p": ("fold", {"CPU_CYCLES": 5e6})})
                            for cfg in ("aos_mut", "ptr")}}
        for res in results["P.hs"].values():
            res.passes["p"]["papi_unavailable"] = ["DTLB_MISSES"]
        self.assertIn("\\textbf{Not counted}: this CPU has no event for Data TLB misses",
                      _tex(results))


class TestEvents(unittest.TestCase):
    def setUp(self):
        self.addCleanup(importlib.reload, gb)
        gb.apply_config_selection(["aos_mut", "ptr"])

    def _results(self, ptr_event):
        results = {"P.hs": {cfg: _counted("P.hs", cfg, {"p": ("fold", {"L1D_LOAD_MISSES_RETIRED": 5e6})})
                            for cfg in ("aos_mut", "ptr")}}
        results["P.hs"]["aos_mut"].passes["p"]["papi_native_events"] = {
            "L1D_LOAD_MISSES_RETIRED": "MEM_LOAD_RETIRED:L1_MISS"}
        results["P.hs"]["ptr"].passes["p"]["papi_native_events"] = {
            "L1D_LOAD_MISSES_RETIRED": ptr_event}
        return results

    def test_the_notes_name_the_event_and_its_definition(self):
        tex = _tex(self._results("MEM_LOAD_RETIRED:L1_MISS"))
        self.assertIn("retired loads that missed the L1D", tex)
        self.assertIn("MEM\\_LOAD\\_RETIRED:L1\\_MISS", tex)
        self.assertNotIn("\\textbf{Warning}", tex)

    def test_two_events_for_one_counter_are_flagged(self):
        tex = _tex(self._results("perf::L1-DCACHE-LOAD-MISSES"))
        self.assertIn("\\textbf{Warning}: L1D load misses (retired) was read from more than one event", tex)


class TestNoiseFloor(unittest.TestCase):
    def setUp(self):
        self.addCleanup(importlib.reload, gb)
        gb.apply_config_selection(["aos_mut", "soa_mut", "ptr"])

    def _results(self, counts):
        return {"P.hs": {cfg: _counted("P.hs", cfg, {"p": ("fold", {
                    "L1I_MISSES": v, "L1D_LOAD_MISSES_RETIRED": 1000 * v,
                    "INSTRUCTIONS": 1e9})})
                         for cfg, v in counts.items()}}

    def _per_config(self, tex):
        return tex[tex.index("per-configuration counters"):]

    def test_a_noise_counter_collapses_to_one_line(self):
        table = self._per_config(_tex(self._results({"aos_mut": 3, "soa_mut": 9, "ptr": 40})))
        l1i = table[table.index("\\textit{L1I misses}"):]
        self.assertIn("below %d per iteration (at most 4.0e+01): noise level"
                      % gb.COUNTER_NOISE_FLOOR, l1i.splitlines()[1])
        # The L1D block, above the floor, keeps its marks.
        self.assertIn("\\textcolor{%s}" % gb.COLOR_FASTEST, table)

    def test_a_noise_row_is_printed_unmarked(self):
        # One pass above the floor keeps the block; the other is noise.
        results = self._results({"aos_mut": 3, "soa_mut": 9, "ptr": 40})
        for cfg, res in results["P.hs"].items():
            res.passes["q"] = {"median_time": 0.1, "pass_type": "fold",
                               "papi_counters": {"L1I_MISSES": {"median": 5000.0 + len(cfg), "n": 3}},
                               "papi_native_events": {"L1I_MISSES": "EV"}}
        table = self._per_config(_tex(results))
        l1i = table[table.index("\\textit{L1I misses}"):table.index("\\textit{L1D load misses (retired)}")
                    if "\\textit{L1D load misses (retired)}" in table[table.index("\\textit{L1I misses}"):] else None]
        p_row = next(l for l in l1i.splitlines() if l.startswith("p &"))
        q_row = next(l for l in l1i.splitlines() if l.startswith("q &"))
        self.assertNotIn("textcolor", p_row)
        self.assertIn("textcolor", q_row)

    def test_a_ratio_of_noise_is_not_printed(self):
        gb.apply_config_selection(["aos_mut", "soa_mut"])
        results = {"P.hs": {cfg: _counted("P.hs", cfg, {"p": ("fold", {
                       "DTLB_MISSES": v, "INSTRUCTIONS": 1e9})})
                            for cfg, v in (("aos_mut", 200.0), ("soa_mut", 100.0))}}
        tex = _tex(results)
        per_prog = tex[tex.index("\\label{tab:P_pldi_counters}"):]
        row = next(l for l in per_prog.splitlines() if l.startswith("\\texttt{p}"))
        self.assertTrue(row.rstrip(" \\").endswith("--"), row)
        self.assertNotIn("2.00", tex[tex.index("pldi_counters_totals"):tex.index("pldi_counters_mpki")])


class TestWindow(unittest.TestCase):
    def setUp(self):
        self.addCleanup(importlib.reload, gb)
        gb.apply_config_selection(["aos_mut", "ptr"])
        self.results = {"P.hs": {cfg: _counted("P.hs", cfg, {"p": ("fold", {"CPU_CYCLES": 5e6})})
                                 for cfg in ("aos_mut", "ptr")}}

    def test_a_fresh_run_counts_the_timed_region(self):
        self.assertEqual(gb.COUNTER_WINDOW, "timed")
        self.assertIn("so a count covers exactly what that iteration's time covers",
                      _tex(self.results))

    def test_an_older_stored_report_says_it_counted_the_whole_iteration(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "r.json"
            path.write_text(json.dumps({"campaign": {"codegen": {"counter_backend": "kperf"}},
                                        "results": {}}))
            gb.adopt_stored_campaign_settings(path)
        self.assertEqual(gb.COUNTER_WINDOW, "iteration")
        self.assertIn("this report predates counting the timed region alone",
                      _tex(self.results))


if __name__ == "__main__":
    unittest.main()
