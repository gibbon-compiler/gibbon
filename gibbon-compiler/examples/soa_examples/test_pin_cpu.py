"""--pin-cpu is OPT-IN, and omitting it must restore the pre-pinning driver.

Pinning confines every timed run to one core's private L1/L2 and to one SMT
sibling's share of the shared units, which on this suite made some benchmarks
measurably worse rather than merely quieter. So it is off unless asked for,
and "off" has to mean the driver touches CPU affinity NOWHERE -- not merely
that it skips `taskset` on the run, since narrowing the driver's own mask
would change scheduling for the compiles too.
"""
import os
import unittest
from unittest import mock
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import gibbon_benchmark as gb


class TestPinCpuIsOptIn(unittest.TestCase):
    def _raw(self, argv):
        return gb.build_parser().parse_args(argv).pin_cpu

    def test_omitting_the_flag_disables_pinning(self):
        # THE regression this file exists for.
        self.assertIsNone(gb.resolve_pin_cpu_arg(self._raw([])))

    def test_bare_flag_selects_a_cpu_automatically(self):
        with mock.patch.object(gb, "default_pin_cpu", return_value=7):
            self.assertEqual(gb.resolve_pin_cpu_arg(self._raw(["--pin-cpu"])), 7)

    def test_explicit_cpu_number(self):
        self.assertEqual(gb.resolve_pin_cpu_arg(self._raw(["--pin-cpu", "5"])), 5)

    def test_explicit_none_matches_omitting_it(self):
        self.assertEqual(gb.resolve_pin_cpu_arg(self._raw(["--pin-cpu", "none"])),
                         gb.resolve_pin_cpu_arg(self._raw([])))

    def test_auto_is_still_spellable(self):
        with mock.patch.object(gb, "default_pin_cpu", return_value=3):
            self.assertEqual(gb.resolve_pin_cpu_arg(self._raw(["--pin-cpu", "auto"])), 3)

    def test_off_and_case_and_padding_all_mean_off(self):
        for raw in ("none", "NONE", "off", " None ", ""):
            self.assertIsNone(gb.resolve_pin_cpu_arg(raw), repr(raw))

    def test_the_flag_does_not_swallow_a_following_option(self):
        # nargs="?" is only safe because the parser has no positionals; if one
        # is ever added, a bare `--pin-cpu` would start eating it.
        args = gb.build_parser().parse_args(["--pin-cpu", "--iterations", "9"])
        self.assertEqual(gb.resolve_pin_cpu_arg(args.pin_cpu) is not None, True)
        self.assertEqual(args.iterations, 9)

    def test_parser_has_no_positionals(self):
        # The precondition for the test above, asserted directly.
        for action in gb.build_parser()._actions:
            self.assertTrue(action.option_strings,
                            "positional %r makes bare --pin-cpu ambiguous"
                            % action.dest)


class TestPinningOffTouchesNothing(unittest.TestCase):
    def test_no_affinity_call_when_pinning_is_off(self):
        with mock.patch.object(os, "sched_setaffinity") as setaff:
            self.assertFalse(gb.reserve_pin_cpu(None))
        setaff.assert_not_called()

    def test_affinity_call_when_pinning_is_on(self):
        # The contrast case: proves the assertion above is not vacuous.
        with mock.patch.object(os, "sched_getaffinity", return_value={0, 1, 2, 3}), \
             mock.patch.object(gb, "smt_siblings", lambda c: {c}), \
             mock.patch.object(os, "sched_setaffinity") as setaff:
            self.assertTrue(gb.reserve_pin_cpu(2))
        setaff.assert_called_once_with(0, {0, 1, 3})

    def test_the_pinned_cores_sibling_thread_is_reserved_too(self):
        # A sibling shares the physical core's front end and ports, so leaving
        # it schedulable for the driver does not reserve the core.
        with mock.patch.object(os, "sched_getaffinity", return_value={0, 1, 2, 3}), \
             mock.patch.object(gb, "smt_siblings", lambda c: {2, 3}), \
             mock.patch.object(os, "sched_setaffinity") as setaff:
            self.assertTrue(gb.reserve_pin_cpu(2))
        setaff.assert_called_once_with(0, {0, 1})

    def test_reservation_declines_rather_than_stranding_the_driver(self):
        with mock.patch.object(os, "sched_getaffinity", return_value={2}), \
             mock.patch.object(os, "sched_setaffinity") as setaff:
            self.assertFalse(gb.reserve_pin_cpu(2))
        setaff.assert_not_called()

    def _capture_argv(self, pin_cpu, taskset_present=True):
        """run_exe returns early for a missing exe, so this needs a real file
        on disk; subprocess.run is intercepted to capture the launch argv."""
        import tempfile
        seen = {}

        def fake_run(cmd, **kw):
            seen["cmd"] = list(cmd)
            raise RuntimeError("captured argv; no need to actually run")

        with tempfile.TemporaryDirectory() as d:
            exe = Path(d) / "x.exe"
            exe.write_text("#!/bin/sh\nexit 0\n")
            exe.chmod(0o755)
            which = "/usr/bin/taskset" if taskset_present else None
            with mock.patch.object(gb.subprocess, "Popen", side_effect=fake_run), \
                 mock.patch.object(gb.shutil, "which", return_value=which):
                try:
                    gb.run_exe(exe, 1, pin_cpu=pin_cpu)
                except Exception:
                    pass
        self.assertIn("cmd", seen, "run_exe never reached subprocess.Popen")
        return seen["cmd"]

    def test_run_exe_does_not_prepend_taskset_when_off(self):
        cmd = self._capture_argv(None)
        self.assertNotIn("taskset", " ".join(cmd))

    def test_run_exe_prepends_taskset_when_on(self):
        cmd = self._capture_argv(4)
        self.assertEqual(cmd[:3], ["taskset", "-c", "4"])

    def test_pinning_is_skipped_when_taskset_is_absent(self):
        # Asking for a pin on a machine without taskset must still run the
        # benchmark, unpinned, rather than failing to launch it.
        cmd = self._capture_argv(4, taskset_present=False)
        self.assertNotIn("taskset", " ".join(cmd))

class TestHelpTextWarnsAboutTheTradeoff(unittest.TestCase):
    def test_help_says_it_is_opt_in_and_why(self):
        help_text = gb.build_parser().format_help()
        self.assertIn("--pin-cpu", help_text)
        for phrase in ("OPT-IN", "OMIT"):
            self.assertIn(phrase, help_text)


if __name__ == "__main__":
    unittest.main()
