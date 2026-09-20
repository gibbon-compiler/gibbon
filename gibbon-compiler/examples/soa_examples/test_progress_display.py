#!/usr/bin/env python3
"""Tests for the pinned progress display (bench_progress.py)."""
import io
import re
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import bench_progress as bp
import gibbon_benchmark as gb


class TestDisabledWhenItCannotDraw(unittest.TestCase):
    """A display that cannot draw must be inert, not merely quiet.

    Redirecting a campaign to a log file is the normal way to run it, and a
    single stray escape sequence makes that log unreadable.
    """

    def test_disabled_for_a_non_tty(self):
        self.assertFalse(bp.ProgressDisplay(stream=io.StringIO()).enabled)

    def test_disabled_stream_receives_nothing_at_all(self):
        buf = io.StringIO()
        d = bp.ProgressDisplay(stream=buf)
        d.add_phase("p", "phase", 3)
        d.install(); d.start_phase("p"); d.item("x", "compiling")
        d.advance(); d.finish_phase(); d.close()
        self.assertEqual(buf.getvalue(), "")

    def test_explicitly_disabled_is_inert(self):
        n = bp.NullProgress()
        self.assertFalse(n.enabled)
        n.add_phase("p", "phase", 1); n.install(); n.item("a", "b")
        n.advance(); n.close()          # must not raise


class TestWorkAccounting(unittest.TestCase):
    def setUp(self):
        self.d = bp.ProgressDisplay(width=100)
        self.d.add_phase("a", "campaign", 10)
        self.d.add_phase("b", "variant matrix", 40)
        self.d.start_phase("a")

    def test_totals_span_every_phase(self):
        # The bar answers "when does the RUN finish", so completion must be
        # over all phases, not just the one in flight.
        self.d.advance(4)
        self.assertEqual(self.d.totals(), (4, 50))

    def test_advance_cannot_exceed_a_phase_total(self):
        self.d.advance(99)
        self.assertEqual(self.d.phases["a"].done, 10)

    def test_finish_phase_completes_it(self):
        self.d.advance(2); self.d.finish_phase()
        self.assertEqual(self.d.phases["a"].done, 10)


class TestEstimateIsHonest(unittest.TestCase):
    def test_no_estimate_before_anything_is_measured(self):
        d = bp.ProgressDisplay(width=100)
        d.add_phase("a", "campaign", 10); d.start_phase("a")
        self.assertIsNone(d.eta_seconds())
        # Elapsed is always shown; "left" only once there is data to base it on.
        stats = d.render()[2][3]
        self.assertIn("elapsed", stats)
        self.assertNotIn("left", stats)

    def test_each_phase_is_costed_with_its_own_observed_time(self):
        # Phases differ by an order of magnitude; costing a variant-matrix
        # compile at campaign-run prices would make the estimate useless.
        d = bp.ProgressDisplay(width=100)
        d.add_phase("a", "campaign", 2)
        d.add_phase("b", "matrix", 10)
        d.start_phase("a")
        d.phases["a"].durations = [10.0, 10.0]
        d.phases["b"].durations = [1.0, 1.0]
        d.phases["a"].done = 1
        # 1 campaign item left at 10s + 10 matrix items at 1s = 20s
        self.assertAlmostEqual(d.eta_seconds(), 20.0, places=6)

    def test_a_phase_with_no_data_falls_back_to_the_global_median(self):
        d = bp.ProgressDisplay(width=100)
        d.add_phase("a", "campaign", 1)
        d.add_phase("b", "matrix", 4)
        d.start_phase("a")
        d.phases["a"].durations = [3.0]
        d.phases["a"].done = 1
        self.assertAlmostEqual(d.eta_seconds(), 12.0, places=6)

    def test_mean_not_median_so_every_second_is_counted(self):
        # The estimate multiplies this by a unit count, so it must be total
        # time over total units; a long compile is time the run spends again.
        p = bp._Phase("k", "k", 10)
        p.durations = [1.0, 1.0, 1.0, 1.0, 96.0]
        self.assertEqual(p.typical(), 20.0)

    def test_durations_are_formatted_without_false_precision(self):
        self.assertEqual(bp._fmt_duration(45), "45s")
        self.assertEqual(bp._fmt_duration(531), "8m51s")
        self.assertEqual(bp._fmt_duration(9000), "2h30m")


class TestRendering(unittest.TestCase):
    def _d(self):
        d = bp.ProgressDisplay(width=100)
        d.add_phase("a", "campaign", 10); d.start_phase("a")
        d.phases["a"].durations = [1.0]
        d.advance(6); d.item("Prog · soa_mut", "compiling")
        return d

    def test_three_rows_that_fit_the_terminal(self):
        rows = self._d().render()
        self.assertEqual(len(rows), 3)
        self.assertEqual(bp.ProgressDisplay.HEIGHT, 3)
        for r in rows:
            text = r if isinstance(r, str) else "".join(r)
            self.assertLessEqual(len(text), 100)

    def test_the_bar_is_two_rows_tall_and_identical(self):
        # Height is the point: one row of text is a few millimetres and reads
        # as a rule, not a bar.
        _, top, bot = self._d().render()
        self.assertEqual((top[1], top[2]), (bot[1], bot[2]))
        self.assertTrue(top[1])

    def test_elapsed_and_remaining_are_both_shown(self):
        stats = self._d().render()[2][3]
        self.assertIn("elapsed", stats)
        self.assertIn("left", stats)

    def test_percent_sits_on_the_top_row(self):
        self.assertIn("%", self._d().render()[1][3])

    def test_context_and_action_are_shown(self):
        head = self._d().render()[0]
        self.assertIn("Prog · soa_mut", head)
        self.assertIn("compiling", head)
        self.assertIn("campaign", head)

    def test_bar_reflects_completion(self):
        _, top, _ = self._d().render()
        self.assertIn(bp._FULL, top[1])
        self.assertIn(bp._TRACK, top[2])
        self.assertIn("60%", top[3])

    def test_no_partial_cells_so_the_bar_meets_the_track(self):
        """Only whole cells are drawn.

        Eighth-width partial blocks are LEFT-aligned within their cell, so the
        unfilled remainder shows the raw terminal background -- a transparent
        notch between the green bar and the textured track. Every cell must be
        either a full block or a track cell.
        """
        for n in (1, 7, 37, 63, 99):
            d = bp.ProgressDisplay(width=100)
            d.add_phase("a", "c", 100); d.start_phase("a")
            d.phases["a"].durations = [1.0]
            d.advance(n)
            _, top, _ = d.render()
            cells = top[1] + top[2]
            self.assertEqual(set(cells) - {bp._FULL, bp._TRACK}, set(),
                             f"non-whole cell at {n}%: {cells!r}")

    def test_partial_block_glyphs_are_gone_from_the_source(self):
        src = (HERE / "bench_progress.py").read_text()
        self.assertNotIn("_EIGHTHS", src)
        for ch in "\u258f\u258e\u258d\u258c\u258b\u258a\u2589":
            self.assertNotIn(ch, src.split("# Whole cells only")[-1].split('"""')[0]
                             if "# Whole cells only" in src else "")

    def test_complete_bar_has_no_track_left(self):
        d = self._d(); d.advance(4)
        _, top, _ = d.render()
        self.assertEqual(top[2], "")

    def _drawn(self, term="xterm-256color"):
        import os
        old = os.environ.get("TERM"); os.environ["TERM"] = term
        oldct = os.environ.pop("COLORTERM", None)
        try:
            buf = io.StringIO()
            d = bp.ProgressDisplay(width=100, stream=buf)
            d.enabled = True; d._installed = True
            d.add_phase("a", "c", 4); d.start_phase("a")
            d.phases["a"].durations = [1.0]; d.advance(2); d.draw()
            return buf.getvalue()
        finally:
            if old is None: os.environ.pop("TERM", None)
            else: os.environ["TERM"] = old
            if oldct is not None: os.environ["COLORTERM"] = oldct

    def test_filled_portion_is_a_strong_visible_green(self):
        # Colour 71 was tried first and reported as "grey, not visible": a
        # desaturated tone defeats the purpose of a progress bar.
        out = self._drawn()
        self.assertIn("\x1b[1;38;5;40m", out)
        self.assertNotIn("38;5;71m", out)
        # Bright green (92 / colour 46) washes out on a light background.
        self.assertNotIn("\x1b[92m", out)
        self.assertNotIn("38;5;46m", out)

    def test_green_is_bold_because_some_themes_render_green_dark(self):
        self.assertIn("1;", bp._green(None))

    def test_green_degrades_on_a_16_colour_terminal(self):
        out = self._drawn(term="xterm")
        self.assertIn("\x1b[1;32m", out)
        self.assertNotIn("38;5;", out)

    def test_no_color_is_honoured(self):
        import os
        os.environ["NO_COLOR"] = "1"
        try:
            # Falls back to the terminal's own foreground, which contrasts
            # with the background by definition.
            self.assertEqual(bp._green(None), "\x1b[1m")
        finally:
            os.environ.pop("NO_COLOR", None)

    def test_the_dim_attribute_is_never_used(self):
        """Nothing is drawn dim.

        The context line and the empty track were dim on the theory that they
        should recede. On a terminal whose theme renders dim as mid-grey they
        were simply unreadable -- and recessive is worthless if invisible. The
        track still reads lighter than the bar because the GLYPH differs
        (light shade vs full block), which no theme can wash out.
        """
        out = self._drawn()
        self.assertNotIn("\x1b[2m", out)
        self.assertNotIn("_DIM", (HERE / "bench_progress.py").read_text())

    def test_only_the_filled_bar_carries_colour(self):
        out = self._drawn()
        # Exactly one colour sequence per bar row, closed before the track.
        self.assertIn("\x1b[1;38;5;40m", out)
        idx = out.index("\x1b[1;38;5;40m")
        rest = out[idx + len("\x1b[1;38;5;40m"):]
        self.assertLess(rest.index("\x1b[0m"), rest.index(bp._TRACK),
                        "colour must be closed before the empty track")

    def test_context_line_uses_the_terminal_foreground(self):
        out = self._drawn()
        # The context line is written with no attribute at all.
        self.assertNotIn("\x1b[2m", out)


class TestDriverIntegration(unittest.TestCase):
    def test_verbose_and_quiet_helpers_exist(self):
        for name in ("set_verbosity", "vprint", "set_progress", "progress"):
            self.assertTrue(hasattr(gb, name), name)

    def test_vprint_is_silent_unless_verbose(self):
        import contextlib
        gb.set_verbosity(False)
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            gb.vprint("routine chatter")
        self.assertEqual(buf.getvalue(), "")
        gb.set_verbosity(True)
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            gb.vprint("routine chatter")
        self.assertIn("routine chatter", buf.getvalue())
        gb.set_verbosity(True)

    def test_progress_returns_a_usable_object_when_unset(self):
        gb.set_progress(None)
        p = gb.progress()
        p.item("x", "y"); p.advance(); p.close()      # must not raise

    def test_diagnostics_are_never_routed_through_vprint(self):
        # Warnings and failures must survive quiet mode: they are the reason
        # to look at the output at all.
        src = (HERE / "gibbon_benchmark.py").read_text()
        offenders = [ln.strip() for ln in src.splitlines()
                     if "vprint(" in ln
                     and re.search(r"(warning|FAILED|Error|error)", ln)]
        self.assertEqual(offenders, [], offenders)


class TestTickerKeepsTheBarAlive(unittest.TestCase):
    """The bar must repaint during work that emits no events.

    A single compile, or a run with --iterations 51, produces no progress
    events for minutes. Without a ticker the elapsed clock freezes and the
    display reads as hung -- which is exactly how it was first reported.
    """

    class _Stream(io.StringIO):
        def isatty(self):
            return True

    def test_repaints_while_nothing_is_happening(self):
        import time
        buf = self._Stream()
        d = bp.ProgressDisplay(stream=buf, width=90)
        d.add_phase("a", "campaign", 10)
        d.install(); d.start_phase("a"); d.item("x", "running x51")
        before = len(buf.getvalue())
        time.sleep(1.2)                       # no events at all
        grew = len(buf.getvalue()) > before
        d.close()
        self.assertTrue(grew, "the bar did not repaint during a silent operation")

    def test_close_stops_the_ticker(self):
        import time
        buf = self._Stream()
        d = bp.ProgressDisplay(stream=buf, width=90)
        d.add_phase("a", "c", 2); d.install(); d.start_phase("a")
        d.close()
        self.assertFalse(d._ticker.is_alive())

    def test_no_repaint_lands_after_the_region_is_released(self):
        import time, re
        buf = self._Stream()
        d = bp.ProgressDisplay(stream=buf, width=90)
        d.add_phase("a", "c", 2); d.install(); d.start_phase("a")
        d.item("x", "running")
        time.sleep(0.8)
        d.close()
        out = buf.getvalue()
        # The final scroll-region reset must be the last escape written; a
        # repaint after it would draw into the restored screen.
        self.assertGreater(out.rindex("\x1b[1;"), out.rindex("\x1b[2K"))

    def test_a_long_step_is_called_out(self):
        import time
        d = bp.ProgressDisplay(width=100)
        d.add_phase("a", "c", 10); d.start_phase("a")
        d.phases["a"].durations = [1.0]
        d.item("Prog", "running x51")
        d._item_started = time.time() - 90
        self.assertIn("this step", d.render()[1][3])

    def test_a_short_step_is_not_called_out(self):
        d = bp.ProgressDisplay(width=100)
        d.add_phase("a", "c", 10); d.start_phase("a")
        d.phases["a"].durations = [1.0]
        d.item("Prog", "compiling")
        self.assertNotIn("this step", d.render()[1][3])

    def test_disabled_display_starts_no_thread(self):
        d = bp.ProgressDisplay(stream=io.StringIO())   # not a tty
        d.add_phase("a", "c", 1); d.install()
        self.assertIsNone(d._ticker)
        d.close()


class TestPhaseAnnouncements(unittest.TestCase):
    """Compiling and running are announced by name.

    Both were reported as confusing in practice: "Compiling 2 file(s)" does
    not say WHICH benchmark is slow, and nothing marked the switch from
    compiling to running -- so a long run read as a stalled compile.
    """

    def setUp(self):
        self.src = (HERE / "gibbon_benchmark.py").read_text()

    def test_compile_message_names_the_sources(self):
        self.assertIn("compiling {_named}", self.src)
        # and the old bare-count spelling is gone
        self.assertNotIn('Compiling {len(tasks)} file(s) using', self.src)

    def test_compile_message_groups_variants_per_program(self):
        import re
        m = re.search(r"_by_prog\.setdefault\(_t\[0\], \[\]\)\.append\(_t\[1\]\)", self.src)
        self.assertIsNotNone(m, "compile message should group variants by program")

    def test_the_switch_to_running_is_announced(self):
        self.assertIn("running   {prog} [{var}]", self.src)

    def test_the_announcement_is_not_suppressed_in_quiet_mode(self):
        # These two lines are the interface when the verbose log is hidden,
        # so they must be print(), never vprint().
        for needle in ("compiling {_named}", "running   {prog} [{var}]"):
            line = [l for l in self.src.splitlines() if needle in l]
            self.assertTrue(line, needle)
            self.assertNotIn("vprint(", line[0], line[0])

    def test_the_run_plan_matches_the_loop_that_follows(self):
        # The message states warmup as `runs x iters`; the loop below runs
        # `warmup_runs_eff` times at `warmup_iters_eff`. If those ever
        # disagree the message misrepresents where the time goes.
        self.assertIn("_wr, _wi = max(0, warmup_runs), max(1, warmup_iterations)", self.src)
        self.assertIn("warmup_runs_eff = max(0, warmup_runs)", self.src)
        self.assertIn("warmup_iters_eff = max(1, warmup_iterations)", self.src)


class TestEstimateArithmeticIsInTheRightCurrency(unittest.TestCase):
    """The estimate must multiply remaining UNITS by a per-UNIT time.

    It originally sampled durations in item(), which fires several times per
    unit (compile, warmup, run), so it multiplied remaining units by a
    sub-step time. Measured on a simulated campaign program that truly took
    100s: it predicted 4.4 minutes remaining where the truth was 23 minutes,
    understating by 5.3x. Durations are now sampled in advance(), in the same
    currency as the count.
    """

    def _clock(self):
        t = [0.0]
        real = bp.time.time
        bp.time.time = lambda: t[0]
        self.addCleanup(lambda: setattr(bp.time, "time", real))
        return t

    def test_a_unit_spanning_many_steps_is_timed_as_one_unit(self):
        t = self._clock()
        d = bp.ProgressDisplay(width=90)
        d.add_phase("a", "campaign", 30); d.start_phase("a")
        for _ctx, _act, dur in [("p", "campaign", 1), ("p", "compiling", 9),
                                ("p", "warmup", 10), ("p", "running", 30),
                                ("p", "compiling", 9), ("p", "warmup", 10),
                                ("p", "running", 31)]:
            d.item(_ctx, _act); t[0] += dur
        d.advance(2)                        # 100s of work == 2 units
        self.assertEqual(d.phases["a"].durations, [50.0, 50.0])

    def test_estimate_matches_the_arithmetic_exactly(self):
        t = self._clock()
        d = bp.ProgressDisplay(width=90)
        d.add_phase("a", "campaign", 30); d.start_phase("a")
        for _ in range(3):
            t[0] += 100.0
            d.advance(2)
        # 24 units left at 50s each
        self.assertAlmostEqual(d.eta_seconds(), 24 * 50.0, places=6)

    def test_item_no_longer_samples_durations(self):
        t = self._clock()
        d = bp.ProgressDisplay(width=90)
        d.add_phase("a", "c", 10); d.start_phase("a")
        d.item("x", "compiling"); t[0] += 7
        d.item("x", "running")
        self.assertEqual(d.phases["a"].durations, [])

    def test_batched_advance_yields_a_per_unit_figure(self):
        t = self._clock()
        d = bp.ProgressDisplay(width=90)
        d.add_phase("a", "c", 10); d.start_phase("a")
        t[0] += 60.0
        d.advance(4)
        self.assertEqual(d.phases["a"].durations, [15.0] * 4)

    def test_a_burst_of_advances_is_costed_at_its_true_rate(self):
        # The variant matrix compiles and runs a program's every
        # configuration, then advances them all at once: one unit carries
        # the whole 100s, the other nine ~0s. A median made that 0s a unit.
        t = self._clock()
        d = bp.ProgressDisplay(width=90)
        d.add_phase("a", "matrix", 20); d.start_phase("a")
        t[0] += 100.0
        for _ in range(10):
            d.advance()
        self.assertAlmostEqual(d.eta_seconds(), 100.0, places=6)


class TestEstimateFromHistory(unittest.TestCase):
    """Programs differ by orders of magnitude, so one per-unit rate cannot
    cost the rest of a run; each program is costed at its own previous time."""

    def _clock(self):
        t = [0.0]
        real = bp.time.time
        bp.time.time = lambda: t[0]
        self.addCleanup(lambda: setattr(bp.time, "time", real))
        return t

    def _display(self, history):
        import json, tempfile
        path = Path(tempfile.mkdtemp()) / "h.json"
        path.write_text(json.dumps({"phases": {"m": history}}))
        d = bp.ProgressDisplay(width=90)
        d.add_phase("m", "matrix", 6, groups={"small": 2, "big": 2, "mid": 2})
        d.load_history(path)
        return d, path

    def test_history_costs_each_group_before_anything_runs(self):
        self._clock()
        d, _ = self._display({"small": 10.0, "big": 1000.0, "mid": 100.0})
        d.start_phase("m")
        self.assertAlmostEqual(d.eta_seconds(), 1110.0, places=6)
        self.assertFalse(d.eta_detail()[1])

    def test_this_runs_pace_scales_the_history(self):
        t = self._clock()
        d, _ = self._display({"small": 10.0, "big": 1000.0, "mid": 100.0})
        d.start_phase("m")
        d.group("small"); t[0] += 20.0; d.advance(2)   # twice as slow
        d.group("big")
        self.assertAlmostEqual(d.eta_seconds(), 2 * 1100.0, places=6)

    def test_the_group_in_progress_is_charged_only_what_is_left(self):
        t = self._clock()
        d, _ = self._display({"small": 10.0, "big": 1000.0, "mid": 100.0})
        d.start_phase("m")
        d.group("big"); t[0] += 400.0
        # big: 1000 - 400 left; small and mid untouched.
        self.assertAlmostEqual(d.eta_seconds(), 600.0 + 10.0 + 100.0, places=6)

    def test_a_group_without_history_uses_the_phase_rate(self):
        t = self._clock()
        d, _ = self._display({"small": 10.0, "big": 1000.0})
        d.start_phase("m")
        d.group("small"); t[0] += 10.0; d.advance(2)
        d.group("big"); t[0] += 1000.0; d.advance(2)
        d.group("mid")
        # mid has no record: 2 units at the phase's 1010s / 4 units.
        self.assertAlmostEqual(d.eta_seconds(), 2 * 1010.0 / 4, places=6)

    def test_completed_groups_are_saved_for_the_next_run(self):
        import json
        t = self._clock()
        d, path = self._display({"mid": 100.0})
        d.start_phase("m")
        d.group("small"); t[0] += 12.0; d.advance(2)
        d.finish_phase()
        saved = json.loads(path.read_text())["phases"]["m"]
        self.assertEqual(saved, {"small": 12.0, "mid": 100.0})

    def test_missing_history_file_is_harmless(self):
        d = bp.ProgressDisplay(width=90)
        d.add_phase("m", "matrix", 2, groups={"a": 2})
        d.load_history("/nonexistent/dir/h.json")
        d.start_phase("m")
        self.assertIsNone(d.eta_seconds())


class TestEstimateHonesty(unittest.TestCase):
    def test_extrapolated_estimates_are_marked_rough(self):
        d = bp.ProgressDisplay(width=96)
        d.add_phase("a", "campaign", 10)
        d.add_phase("b", "variant matrix", 100)
        d.start_phase("a")
        d.phases["a"].durations = [5.0]; d.phases["a"].done = 1
        eta, rough = d.eta_detail()
        self.assertTrue(rough, "phase b has no data of its own")
        self.assertIn("(rough)", d.render()[2][3])

    def test_not_rough_once_every_remaining_phase_has_data(self):
        d = bp.ProgressDisplay(width=96)
        d.add_phase("a", "campaign", 10)
        d.add_phase("b", "matrix", 100)
        d.start_phase("a")
        d.phases["a"].durations = [5.0]; d.phases["a"].done = 1
        d.phases["b"].durations = [2.0]; d.phases["b"].done = 1
        _eta, rough = d.eta_detail()
        self.assertFalse(rough)
        self.assertNotIn("(rough)", d.render()[2][3])

    def test_a_non_estimable_phase_is_excluded(self):
        # Writing tables takes seconds, nothing like a benchmark unit; costing
        # it at a unit's price predicted 3.5s remaining when the answer was 0.
        d = bp.ProgressDisplay(width=96)
        d.add_phase("a", "campaign", 2)
        d.add_phase("r", "tables", 1, estimate=False)
        d.start_phase("a")
        d.phases["a"].durations = [10.0]; d.phases["a"].done = 2
        self.assertEqual(d.eta_seconds(), 0.0)

    def test_the_driver_marks_the_tables_phase_non_estimable(self):
        src = (HERE / "gibbon_benchmark.py").read_text()
        self.assertIn('add_phase("report", "tables", 1, estimate=False)', src)


class TestCampaignPhaseCountsEveryVariant(unittest.TestCase):
    """The campaign phase's size and the count it advances by must be the
    same number, or the bar stops short of 100% however far the run gets."""

    def test_variant_count_matches_the_mode(self):
        self.assertEqual(len(gb.campaign_variants()), 2)
        self.assertEqual(
            len(gb.campaign_variants(benchmark_baseline_gibbon=True)), 3)
        self.assertEqual(len(gb.campaign_variants(benchmark_immutable=True)), 4)
        self.assertEqual(
            len(gb.campaign_variants(benchmark_immutable=True,
                                     benchmark_ghc=True,
                                     benchmark_mlton=True)), 6)

    def test_benchmark_program_runs_exactly_those_variants(self):
        self.assertEqual(
            [name for name, _mut in
             gb.campaign_variants(benchmark_baseline_gibbon=True)],
            ["aos", "aos_imm", "soa"])

    def test_the_driver_advances_by_the_registered_count(self):
        src = (HERE / "gibbon_benchmark.py").read_text()
        main_src = src[src.index("\ndef main("):]
        self.assertIn("_n_variants = len(campaign_variants(", main_src)
        self.assertIn("progress().advance(_n_variants)", main_src)

    def test_a_four_variant_campaign_reaches_a_full_bar(self):
        d = bp.ProgressDisplay(width=90)
        n = len(gb.campaign_variants(benchmark_immutable=True))
        d.add_phase("campaign", "campaign", 2 * n)
        d.start_phase("campaign")
        d.advance(n); d.advance(n)
        self.assertEqual(d.totals(), (2 * n, 2 * n))


class TestGroupTimingStopsWithItsWork(unittest.TestCase):
    """A group's record is used to cost that program in the next run, so it
    must not absorb work done after the program is finished."""

    def _clock(self):
        t = [0.0]
        real = bp.time.time
        bp.time.time = lambda: t[0]
        self.addCleanup(lambda: setattr(bp.time, "time", real))
        return t

    def test_end_group_stops_the_clock(self):
        t = self._clock()
        d = bp.ProgressDisplay(width=90)
        d.add_phase("c", "campaign", 2, groups={"P.hs": 2})
        d.add_phase("r", "tables", 1, estimate=False)
        d.start_phase("c")
        d.group("P.hs"); t[0] += 30.0
        d.end_group()
        t[0] += 900.0                      # reports, width families, roofline
        d.finish_phase()
        self.assertEqual(d.phases["c"].group_seconds, {"P.hs": 30.0})

    def test_without_it_the_last_program_absorbs_the_rest_of_the_run(self):
        t = self._clock()
        d = bp.ProgressDisplay(width=90)
        d.add_phase("c", "campaign", 2, groups={"P.hs": 2})
        d.start_phase("c")
        d.group("P.hs"); t[0] += 30.0
        t[0] += 900.0
        d.finish_phase()
        self.assertEqual(d.phases["c"].group_seconds, {"P.hs": 930.0})

    def test_the_driver_ends_the_campaign_group_with_the_loop(self):
        src = (HERE / "gibbon_benchmark.py").read_text()
        main_src = src[src.index("\ndef main("):]
        self.assertLess(main_src.index("progress().end_group()"),
                        main_src.index('progress().start_phase("pldi")'))

    def test_the_pldi_phase_registers_the_width_selected_programs(self):
        # The matrix itself narrows its program list to the requested payload
        # width; groups registered under the wider names are never reported
        # against, so the phase would never finish.
        src = (HERE / "gibbon_benchmark.py").read_text()
        main_src = src[src.index("\ndef main("):]
        block = main_src[main_src.index("_pldi_programs = resolve_program_selection"):
                         main_src.index('_display.add_phase(\n            "pldi"')]
        self.assertIn("apply_width_selection(", block)


class TestHistoryFileKeepsPhasesThisRunDoesNotHave(unittest.TestCase):
    def test_a_campaign_only_run_does_not_wipe_the_matrix_history(self):
        import json, tempfile
        path = Path(tempfile.mkdtemp()) / "h.json"
        path.write_text(json.dumps(
            {"phases": {"campaign": {"A.hs": 1.0}, "pldi": {"A.hs": 900.0}}}))
        d = bp.ProgressDisplay(width=90)
        d.add_phase("campaign", "campaign", 2, groups={"A.hs": 2})
        d.load_history(path)
        d.save_history()
        saved = json.loads(path.read_text())["phases"]
        self.assertEqual(saved["pldi"], {"A.hs": 900.0})
        self.assertEqual(saved["campaign"], {"A.hs": 1.0})


if __name__ == "__main__":
    unittest.main(verbosity=2)
