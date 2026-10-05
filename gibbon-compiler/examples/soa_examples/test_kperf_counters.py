#!/usr/bin/env python3
"""Regression tests for the opt-in kperf counter backend (--pldi-kperf-counters,
macOS) and the per-configuration counter tables.

  - TestOptIn: nothing changes without the flag -- no --enable-kperf in any
    command, no launcher prefix, PAPI stays the default backend.
  - TestKperfPlumbing: the flag reaches the compile command, the runs get the
    `sudo -n' prefix, KPERF_NATIVE lines are parsed like PAPI_NATIVE ones, and
    the counter phase uses its own directory without --pin-cpu.
  - TestPerConfigTable: every measured configuration (Pointer included) gets
    a column, grouped like the timing tables, with or without an AoS/SoA pair.
  - TestNotesAndReplot: the notes say which backend took the counts, and a
    replot restores it from the stored report.
"""
import importlib
import io
import json
import os
import stat
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import gibbon_benchmark as gb  # noqa: E402
import bench_provenance as prov  # noqa: E402


def _verified(program, cfg, passes):
    res = gb.BenchmarkResult(program, cfg)
    st = prov.QualificationStatus(cfg, program)
    st.compile_status = prov.COMPILE_OK
    st.exec_status = prov.EXEC_OK
    st.oracle_status = prov.ORACLE_PASS
    st.semantic_output = "42"
    res.compile_success = res.run_success = True
    res.passes = passes
    res.qualification = st
    return res


def _counted(program, cfg, per_pass):
    """per_pass: {pass: (pass_type, {counter: median})}"""
    data = {p: {"median_time": 0.1, "pass_type": t,
                "papi_counters": {c: {"median": v, "n": 3} for c, v in cs.items()},
                "papi_native_events": {c: "EV_" + c for c in cs}}
            for p, (t, cs) in per_pass.items()}
    return _verified(program, cfg, data)


class TestOptIn(unittest.TestCase):
    def setUp(self):
        self.addCleanup(importlib.reload, gb)

    def test_commands_carry_no_kperf_flag_by_default(self):
        cmd = gb.build_gibbon_command(Path("P.hs"), "aos_mut", Path("P.c"),
                                      Path("P.exe"), "gcc")
        self.assertNotIn("--enable-kperf", cmd)

    def test_defaults(self):
        self.assertEqual(gb.COUNTER_BACKEND, "papi")
        self.assertEqual(gb.KPERF_EXEC_PREFIX, [])

    def test_papi_lines_still_parse(self):
        res = _verified("P.hs", "aos_mut", {"p": {"median_time": 0.1, "pass_type": "fold"}})
        gb.attach_papi_native_to_passes(
            res, "Running pass p (fold, uses=1):\nPAPI_NATIVE L1D_LOAD_MISSES[perf::X]=7\nEnd\n")
        self.assertEqual(res.passes["p"]["papi_counters"]["L1D_LOAD_MISSES"]["median"], 7)


class TestKperfPlumbing(unittest.TestCase):
    def setUp(self):
        self.addCleanup(importlib.reload, gb)

    def test_flag_reaches_the_compile_command(self):
        cmd = gb.build_gibbon_command(Path("P.hs"), "ptr", Path("P.c"), Path("P.exe"),
                                      "gcc", use_pointer=True, enable_kperf=True)
        self.assertIn("--enable-kperf", cmd)
        self.assertIn("--pointer", cmd)

    def test_kperf_lines_parse_like_papi_lines(self):
        res = _verified("P.hs", "ptr", {"p": {"median_time": 0.1, "pass_type": "fold"}})
        out = ("Running pass p (fold, uses=1):\n"
               "KPERF_NATIVE L1D_LOAD_MISSES[L1D_CACHE_MISS_LD]=10\n"
               "KPERF_NATIVE L1D_LOAD_MISSES[L1D_CACHE_MISS_LD]=30\n"
               "KPERF_NATIVE CPU_CYCLES[FIXED_CYCLES]=500\n"
               "End\n")
        gb.attach_papi_native_to_passes(res, out)
        pdata = res.passes["p"]
        self.assertEqual(pdata["papi_counters"]["L1D_LOAD_MISSES"]["median"], 20)
        self.assertEqual(pdata["papi_native_events"]["L1D_LOAD_MISSES"], "L1D_CACHE_MISS_LD")
        self.assertEqual(pdata["papi_counters"]["CPU_CYCLES"]["median"], 500)

    def test_exec_prefix_launches_the_executable(self):
        with tempfile.TemporaryDirectory() as d:
            exe = Path(d) / "probe.exe"
            exe.write_text("#!/bin/sh\necho \"FOO=$FOO args=$*\"\n")
            exe.chmod(exe.stat().st_mode | stat.S_IEXEC)
            ok, _t, out, _err, rc = gb.run_exe(exe, 3, exec_prefix=["/usr/bin/env", "FOO=1"])
            self.assertTrue(ok, _err)
            self.assertIn("FOO=1 args=--size-param 0 --iterate 3", out)
            _ok, _t, out2, _e, _rc = gb.run_exe(exe, 3)
            self.assertIn("FOO= ", out2)

    def test_counter_phase_uses_kperf_without_pinning(self):
        seen = {}

        def fake(*args, **kwargs):
            seen["args"], seen["kwargs"] = args, kwargs
            return {}

        with mock.patch.object(gb, "collect_pldi_variant_results", side_effect=fake), \
             mock.patch.object(gb, "run_alignment_probe", return_value=None) as probe:
            gb.collect_pldi_counter_results(Path("programs"), Path("out"), "gcc", False,
                                            iterations=5, pin_cpu=None, backend="kperf")
        probe.assert_called_once()
        self.assertTrue(seen["kwargs"]["enable_kperf"])
        self.assertFalse(seen["kwargs"].get("enable_papi_native", False))
        self.assertIsNone(seen["kwargs"]["pin_cpu"])
        self.assertEqual(seen["args"][1], Path("out") / "counters_kperf")
        self.assertEqual(gb.COUNTER_BACKEND, "kperf")
        self.assertEqual(gb._PAPI_COUNTER_ORDER, list(gb.KPERF_COUNTER_METRICS))

    def test_papi_counter_phase_still_requires_pinning(self):
        with self.assertRaisesRegex(RuntimeError, "--pin-cpu"):
            gb.collect_pldi_counter_results(Path("programs"), Path("out"), "gcc", False,
                                            iterations=5, pin_cpu=None)

    def test_root_needs_no_sudo(self):
        with mock.patch.object(gb.os, "geteuid", return_value=0), \
             mock.patch.object(gb.subprocess, "run") as run:
            gb.prepare_kperf_privileges()
        run.assert_not_called()
        self.assertEqual(gb.KPERF_EXEC_PREFIX, [])

    def test_non_root_asks_sudo_once_then_uses_sudo_n(self):
        with mock.patch.object(gb.os, "geteuid", return_value=501), \
             mock.patch.object(gb.shutil, "which", return_value="/usr/bin/sudo"), \
             mock.patch.object(gb.subprocess, "run",
                               return_value=subprocess.CompletedProcess([], 0)) as run, \
             mock.patch("threading.Thread"):
            gb.prepare_kperf_privileges()
        # The password once, then a check that `sudo -n` reuses it.
        self.assertEqual([c.args[0] for c in run.call_args_list],
                         [["sudo", "-v"], ["sudo", "-n", "true"]])
        self.assertEqual(gb.KPERF_EXEC_PREFIX, ["sudo", "-n"])

    def test_failed_sudo_is_an_error(self):
        with mock.patch.object(gb.os, "geteuid", return_value=501), \
             mock.patch.object(gb.shutil, "which", return_value="/usr/bin/sudo"), \
             mock.patch.object(gb.subprocess, "run",
                               return_value=subprocess.CompletedProcess([], 1)):
            with self.assertRaisesRegex(RuntimeError, "sudo -v"):
                gb.prepare_kperf_privileges()


class TestSudoSession(unittest.TestCase):
    """macOS sudo keeps its password ticket per terminal session, so a
    `sudo -n` run must stay in the driver's session."""

    def setUp(self):
        self.addCleanup(importlib.reload, gb)

    def _sid_of_child(self, prefix):
        with tempfile.TemporaryDirectory() as d:
            exe = Path(d) / "sid.exe"
            exe.write_text("#!%s\nimport os; print(os.getsid(0))\n" % sys.executable)
            exe.chmod(exe.stat().st_mode | stat.S_IEXEC)
            ok, _t, out, err, _rc = gb.run_exe(exe, 1, exec_prefix=prefix)
            self.assertTrue(ok, err)
            return int(out.split()[-1])

    def test_prefixed_runs_stay_in_the_session(self):
        self.assertEqual(self._sid_of_child(["/usr/bin/env"]), os.getsid(0))

    def test_other_runs_still_get_their_own_session(self):
        self.assertNotEqual(self._sid_of_child(None), os.getsid(0))

    def test_a_sudo_that_cannot_be_reused_fails_up_front(self):
        results = [subprocess.CompletedProcess([], 0),
                   subprocess.CompletedProcess([], 1, "", "sudo: a password is required")]
        with mock.patch.object(gb.os, "geteuid", return_value=501), \
             mock.patch.object(gb.shutil, "which", return_value="/usr/bin/sudo"), \
             mock.patch.object(gb.subprocess, "run", side_effect=results):
            with self.assertRaisesRegex(RuntimeError, "a password is required"):
                gb.prepare_kperf_privileges()


class TestNoEmptyDeltaTables(unittest.TestCase):
    def setUp(self):
        self.addCleanup(importlib.reload, gb)

    def test_a_selection_without_pairs_emits_no_delta_tables(self):
        gb.apply_config_selection(["aos_mut", "soa_mut", "ptr"])
        gb.prune_pldi_delta_columns()
        self.assertEqual(gb.PLDI_DELTA_COLUMNS_FOLD, [])
        results = {cfg: _verified("P.hs", cfg, {"p": {"median_time": 0.1, "pass_type": "fold"}})
                   for cfg in ("aos_mut", "soa_mut", "ptr")}
        buf = io.StringIO()
        gb._table_pldi_delta_legend(buf)
        gb._table_pldi_fold_deltas(buf, "P.hs", results)
        self.assertEqual(buf.getvalue(), "")

    def test_a_pair_still_gets_its_table(self):
        gb.apply_config_selection(["aos_imm", "ptr"])
        gb.prune_pldi_delta_columns()
        results = {cfg: _verified("P.hs", cfg, {"p": {"median_time": t, "pass_type": "fold"}})
                   for cfg, t in (("aos_imm", 0.1), ("ptr", 0.2))}
        buf = io.StringIO()
        gb._table_pldi_delta_legend(buf)
        gb._table_pldi_fold_deltas(buf, "P.hs", results)
        self.assertIn("$\\Delta^{P}_{pk}$", buf.getvalue())


class TestPerConfigTable(unittest.TestCase):
    def setUp(self):
        self.addCleanup(importlib.reload, gb)
        gb.apply_config_selection(["aos_imm", "aos_mut", "soa_mut", "ptr"])
        # Above the noise floor, so the row's extremes are marked.
        counts = {"aos_imm": 30000, "aos_mut": 20000, "soa_mut": 10000, "ptr": 90000}
        self.by_cfg = {cfg: _counted("P.hs", cfg, {
            "sumTree": ("fold", {"L1D_LOAD_MISSES": v, "CPU_CYCLES": 10 * v}),
            "add1Tree": ("map", {"L1D_LOAD_MISSES": v + 1})})
            for cfg, v in counts.items()}

    def _tex(self, results):
        buf = io.StringIO()
        gb.write_pldi_counter_tables(buf, results)
        return buf.getvalue()

    def test_every_configuration_is_a_column_grouped_like_the_timing_tables(self):
        tex = self._tex({"P.hs": self.by_cfg})
        table = tex[tex.index("per-configuration counters"):]
        self.assertIn("\\multicolumn{2}{c}{\\textbf{AoS}} & "
                      "\\multicolumn{1}{c}{\\textbf{SoA}} & "
                      "\\multicolumn{1}{c}{\\textbf{Pointer}}", table)
        self.assertIn(" & $P$", table)
        self.assertIn("\\textit{L1D load misses}", table)
        # Fewest green (soa_mut), most red (ptr), in the sumTree row.
        l1d = table[table.index("\\textit{L1D load misses}"):]
        row = next(l for l in l1d.splitlines() if l.startswith("sumTree &"))
        self.assertIn("\\textcolor{%s}{%s}" % (gb.COLOR_FASTEST, gb._fmt_counter(10000)), row)
        self.assertIn("\\textcolor{%s}{%s}" % (gb.COLOR_SLOWEST, gb._fmt_counter(90000)), row)

    def test_rendered_without_an_aos_soa_pair(self):
        only = {k: v for k, v in self.by_cfg.items() if k in ("aos_imm", "ptr")}
        gb.apply_config_selection(["aos_imm", "ptr"])
        tex = self._tex({"P.hs": only})
        self.assertIn("per-configuration counters", tex)
        self.assertNotIn("counter totals, AoS vs SoA", tex)
        self.assertIn("\\paragraph{Hardware counters.}", tex)


class TestKperfMemoryRows(unittest.TestCase):
    """The M1 has no L2/LLC miss events. Its other memory events must appear
    under their own names, in a fixed order, and never as L2/LLC rows."""

    def setUp(self):
        self.addCleanup(importlib.reload, gb)

    def test_proxies_render_under_their_own_names(self):
        gb.apply_config_selection(["aos_mut", "ptr"])
        counts = {m: 10 for m in gb.KPERF_COUNTER_METRICS}
        results = {"P.hs": {cfg: _counted("P.hs", cfg, {"p": ("fold", counts)})
                            for cfg in ("aos_mut", "ptr")}}
        buf = io.StringIO()
        gb.write_pldi_counter_tables(buf, results)
        table = buf.getvalue()[buf.getvalue().index("per-configuration counters"):]
        rows = [l for l in table.splitlines() if l.startswith("\\multicolumn{3}{l}{\\textit{")]
        labels = [r.split("\\textit{")[1].split("}")[0] for r in rows]
        self.assertEqual(labels[-4:], ["L1D load misses (incl. speculative)",
                                       "Dispatch-stall cycles", "Data page walks",
                                       "64B-crossing loads/stores"])
        # The shared ones come first, under their own heading.
        self.assertEqual(labels[:5], [gb.counter_label(m) for m in gb.SHARED_COUNTER_METRICS])
        self.assertLess(table.index("Counted the same way on the M1 and x86"),
                        table.index("This machine only"))
        self.assertNotIn("L2 data misses", labels)
        self.assertNotIn("LLC misses", labels)

    def test_kperf_metric_list_names_no_l2_or_llc_cache_event(self):
        self.assertFalse({"L2D_MISSES", "LLC_LOAD_MISSES", "L2I_MISSES"}
                         & set(gb.KPERF_COUNTER_METRICS))
        self.assertEqual(len(gb.KPERF_COUNTER_METRICS), 9)


PROBE = {"aligned": {"latency_ns": 1.26, "throughput_ns": 0.2},
         "unaligned_in_64B": {"latency_ns": 1.255, "throughput_ns": 0.2},
         "cross_64B": {"latency_ns": 1.258, "throughput_ns": 0.2},
         "cross_128B_line": {"latency_ns": 1.33, "throughput_ns": 0.21}}


class TestAlignmentTables(unittest.TestCase):
    """The tables that let a reader check misalignment against measurements:
    the probe's per-class cost and, per pass, crossings and a time bound."""

    def setUp(self):
        self.addCleanup(importlib.reload, gb)

    def test_penalty_is_the_worst_extra_latency(self):
        self.assertAlmostEqual(gb.alignment_penalty_ns(PROBE), 0.07)
        self.assertIsNone(gb.alignment_penalty_ns(None))
        flat = {k: {"latency_ns": 1.0, "throughput_ns": 0.2} for k in PROBE}
        self.assertEqual(gb.alignment_penalty_ns(flat), 0.0)

    def test_the_probe_compiles_and_reports_every_class(self):
        with tempfile.TemporaryDirectory() as d:
            probe = gb.run_alignment_probe(Path(d), "cc")
        self.assertEqual(set(probe), {"aligned", "unaligned_in_64B", "cross_64B",
                                      "cross_128B_line"})
        for v in probe.values():
            self.assertGreater(v["latency_ns"], 0)

    def _tex(self):
        gb.apply_config_selection(["aos_mut", "ptr"])
        gb.COUNTER_BACKEND = "kperf"
        gb.ALIGNMENT_PROBE = PROBE
        counts = {"aos_mut": {"CROSS_64B_ACCESSES": 31000, "INSTRUCTIONS": 7500000},
                  "ptr": {"CROSS_64B_ACCESSES": 10, "INSTRUCTIONS": 4000000}}
        results = {"P.hs": {cfg: _counted("P.hs", cfg, {"sumTree": ("fold", c)})
                            for cfg, c in counts.items()}}
        buf = io.StringIO()
        gb.write_pldi_counter_tables(buf, results)
        return buf.getvalue()

    def test_tables_carry_the_measured_cost_and_the_bound(self):
        tex = self._tex()
        self.assertIn("crossing a 128 B block & 1.330 & 0.210", tex)
        table = tex[tex.index("misaligned accesses --"):]
        row = [l for l in table.splitlines() if l.startswith("sumTree &")]
        # 31000/7.5e6*1000 = 4.13; 31000 * 0.07 ns / 0.1 s = 0.00%(2e-3 %).
        self.assertEqual(row[0], "sumTree & 4.13 & 0.00 \\\\")
        self.assertEqual(row[1], "sumTree & 0.00\\% & 0.00\\% \\\\")

    def test_no_alignment_tables_for_papi_runs(self):
        tex = self._tex()
        self.assertIn("misaligned accesses", tex)
        gb.COUNTER_BACKEND = "papi"
        buf = io.StringIO()
        gb.write_pldi_alignment_tables(buf, {"P.hs": {}})
        self.assertEqual(buf.getvalue(), "")

    def test_replot_restores_the_probe(self):
        f = tempfile.NamedTemporaryFile("w", suffix=".json", delete=False)
        json.dump({"campaign": {"codegen": {"counter_backend": "kperf",
                                            "alignment_probe": PROBE}}}, f)
        f.close()
        gb.adopt_stored_campaign_settings(Path(f.name))
        self.assertEqual(gb.ALIGNMENT_PROBE, PROBE)


class TestNotesAndReplot(unittest.TestCase):
    def setUp(self):
        self.addCleanup(importlib.reload, gb)

    def _notes(self):
        buf = io.StringIO()
        results = {"P.hs": {"aos_mut": _counted("P.hs", "aos_mut",
                                                {"p": ("fold", {"L1D_LOAD_MISSES": 1})})}}
        gb._table_pldi_counter_notes(buf, results, None)
        return buf.getvalue()

    def test_notes_name_the_backend(self):
        self.assertIn("from PAPI", self._notes())
        gb.COUNTER_BACKEND = "kperf"
        notes = self._notes()
        self.assertIn("kperf", notes)
        self.assertIn("no L2 or last-level cache", notes)
        self.assertNotIn("libpapi", notes)

    def test_replot_restores_the_backend(self):
        f = tempfile.NamedTemporaryFile("w", suffix=".json", delete=False)
        json.dump({"campaign": {"codegen": {"counter_backend": "kperf"}}}, f)
        f.close()
        gb.adopt_stored_campaign_settings(Path(f.name))
        self.assertEqual(gb.COUNTER_BACKEND, "kperf")


class TestFailedCounterPhase(unittest.TestCase):
    def test_notes_say_no_counts_were_produced(self):
        res = _verified("P.hs", "aos_mut", {"p": {"median_time": 0.1, "pass_type": "fold"}})
        buf = io.StringIO()
        gb.write_pldi_counter_tables(buf, {"P.hs": {"aos_mut": res}})
        self.assertIn("No counter run produced counts", buf.getvalue())


class TestOracleIgnoresCounterLines(unittest.TestCase):
    """A counter run prints its counts between the program's own lines; the
    oracle must see only the program's answer, as it does for PAPI."""

    def test_kperf_lines_are_not_semantic_output(self):
        out = ("Running program MonoTree: \n"
               "Running pass sumTree (fold, uses=3): \n"
               "ITERS: 3\nSIZE: 1\nBATCHTIME: 1.0e-03\nSELFTIMED: 3.0e-04\n"
               "KPERF_NATIVE CPU_CYCLES[FIXED_CYCLES]=123\n"
               "KPERF_NATIVE L1D_LOAD_MISSES[L1D_CACHE_MISS_LD]=45\n"
               "End\n'#(45088768 45088768)\n")
        self.assertEqual(prov.semantic_tokens(out), ["'#(45088768", "45088768)"])
        entry = prov.OracleEntry("MonoTree", "'#(45088768 45088768)", "python-model")
        self.assertEqual(entry.check(out)[0], prov.ORACLE_PASS)


class TestCommandLine(unittest.TestCase):
    def _run(self, *argv):
        return subprocess.run([sys.executable, str(HERE / "gibbon_benchmark.py"), *argv],
                              capture_output=True, text=True, cwd=HERE)

    def test_needs_pldi_submission(self):
        r = self._run("--pldi-kperf-counters")
        self.assertEqual(r.returncode, 2)
        self.assertIn("pass --pldi-submission too", r.stderr)

    @unittest.skipUnless(sys.platform == "darwin", "macOS-only message")
    def test_papi_counters_on_macos_name_the_kperf_flag(self):
        r = self._run("--pldi-submission", "--pldi-cache-counters", "--pin-cpu", "auto")
        self.assertEqual(r.returncode, 2)
        self.assertIn("on macOS use --pldi-kperf-counters", r.stderr)

    def test_one_backend_at_a_time(self):
        r = self._run("--pldi-submission", "--pldi-kperf-counters", "--pldi-cache-counters")
        self.assertEqual(r.returncode, 2)
        self.assertIn("choose one counter backend", r.stderr)


if __name__ == "__main__":
    unittest.main()
