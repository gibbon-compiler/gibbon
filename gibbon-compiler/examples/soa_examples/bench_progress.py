#!/usr/bin/env python3
"""A pinned, understated progress display for long benchmark campaigns.

Two lines are reserved at the bottom of the terminal and never move: a
context line naming what is happening right now, and a hairline rule
carrying overall completion and a time estimate.  Everything the driver
prints scrolls above them.

    campaign 12/30 · compiling  DecisionTreeClassify · soa_loop_gccvec_on
    ━━━━━━━━━━━━━━━━━━━━━━━━━┈┈┈┈┈┈┈┈┈┈┈┈┈┈  61%  ·  312/512  ·  ~8m51s

WHY A SCROLL REGION rather than repainting in place: a campaign prints as
it goes, and a bar that is merely redrawn at the cursor gets pushed up the
screen by that output, so the thing you are watching keeps moving.  A DEC
scroll region (`CSI top;bottom r`) confines scrolling to the lines above
the reserved rows, which is what keeps the bar still.

The hazard of that approach is leaving the terminal with a restricted
scroll region if the process dies -- the shell prompt would then be stuck
in a window a few lines short.  'close()' is therefore idempotent and is
wired to both `atexit` and the fatal signals, so the region is released
however the run ends.

Disabled automatically when stdout is not a TTY, so redirecting to a log
writes no escape sequences.
"""
import atexit
import os
import threading
import shutil
import signal
import sys
import time
from typing import Dict, List, Optional


CSI = "\x1b["
_SAVE, _RESTORE = "\x1b7", "\x1b8"
_OFF = f"{CSI}0m"

# NOTE: the dim attribute (CSI 2m) is deliberately NOT used anywhere.
#
# It was used for the context line and the empty track, on the theory that
# they should recede. On a terminal whose theme renders dim as mid-grey, that
# made both unreadable against the background -- and "recessive" is worthless
# if it is invisible. Everything except the filled bar now uses the
# terminal's own foreground colour, which contrasts with its background by
# definition. The track still reads as lighter than the bar because the GLYPH
# differs (light shade vs full block), not because of an attribute.

# Whole cells only. Eighth-width partial blocks (U+258F..U+2589) were used
# for a smoother leading edge, but they are LEFT-aligned within their cell:
# the unfilled remainder of that cell shows the raw terminal background, which
# against the textured light-shade track reads as a transparent notch between
# the bar and the track. The two glyph families do not compose. Sub-cell
# smoothness is not worth a visual artifact on a bar that advances over hours;
# a whole cell on a 60-cell bar is 1.7%.
_FULL, _TRACK = "\u2588", "\u2591"


def _green(stream) -> str:
    """A strong, bold green for the filled portion of the bar.

    The first attempt used 256-colour 71 (a desaturated sea green) on the
    theory that a muted tone reads as "understated". In practice it read as
    grey and was hard to see at all, which defeats the purpose of a progress
    bar. Colour 40 is a saturated mid green with usable contrast against both
    light and dark terminal backgrounds -- unlike bright green (92 / colour
    46), which washes out on a white background.

    Bold is applied as well, because several terminal themes render the
    16-colour green quite dark; bold is what most of them brighten.

    Honours NO_COLOR (https://no-color.org): when set, the bar is drawn with
    the terminal's own foreground colour, which contrasts with the background
    by definition.
    """
    if os.environ.get("NO_COLOR"):
        return f"{CSI}1m"
    term = os.environ.get("TERM", "")
    if "256color" in term or os.environ.get("COLORTERM"):
        return f"{CSI}1;38;5;40m"
    return f"{CSI}1;32m"


def _fmt_duration(seconds: float) -> str:
    """Compact, honest duration: no false precision at large values."""
    if seconds < 0 or seconds != seconds:          # negative or NaN
        return "?"
    s = int(round(seconds))
    if s < 60:
        return f"{s}s"
    if s < 3600:
        return f"{s // 60}m{s % 60:02d}s"
    return f"{s // 3600}h{(s % 3600) // 60:02d}m"


class _Phase:
    __slots__ = ("key", "label", "total", "done", "durations", "estimate",
                 "groups", "group_seconds", "history")

    def __init__(self, key: str, label: str, total: int, estimate: bool = True,
                 groups: Optional[Dict[str, int]] = None):
        self.key = key
        self.label = label
        self.total = max(0, int(total))
        self.done = 0
        # One per-unit sample per completed unit: advance(n) over dt seconds
        # records n samples of dt/n, so their mean is seconds per unit.
        self.durations: List[float] = []
        # Whether this phase should contribute to the time estimate. A phase
        # whose cost is known NOT to resemble the others (writing tables and
        # running pdflatex, a handful of seconds) would otherwise be costed at
        # a benchmark unit's price and dominate the figure near the end of a
        # run -- measured predicting 3.5s remaining when the answer was 0.
        self.estimate = estimate
        # Optional breakdown of the phase into named groups (one per program)
        # with their unit counts, the seconds each completed group took in
        # this run, and the seconds each took in a previous run.
        self.groups: Dict[str, int] = dict(groups or {})
        self.group_seconds: Dict[str, float] = {}
        self.history: Dict[str, float] = {}

    def typical(self) -> Optional[float]:
        """Mean observed seconds per unit for this phase, or None.

        The mean, not the median: the estimate multiplies it by a unit
        count, so it must be total time over total units. A median ignores
        the unit that absorbed a burst (the variant matrix compiles and runs
        a program's every configuration, then advances all of them at once,
        so one unit carries the whole program and the rest carry ~0s), and
        a long compile is real time the run will spend again.
        """
        if not self.durations:
            return None
        return sum(self.durations) / len(self.durations)


class ProgressDisplay:
    """Pinned two-line progress display. All methods are safe when disabled."""

    HEIGHT = 3

    def __init__(self, enabled: bool = True, stream=None, width: Optional[int] = None):
        self.stream = stream if stream is not None else sys.stdout
        self._forced_width = width
        self.enabled = bool(enabled) and self._usable()
        self.phases: Dict[str, _Phase] = {}
        self.order: List[str] = []
        self.current: Optional[str] = None
        self.context = ""
        self.action = ""
        self._installed = False
        self._closed = False
        self._item_started: Optional[float] = None
        # Timing for the ESTIMATE is per completed unit, and is deliberately
        # separate from _item_started (which only drives the "this step"
        # label). They are different clocks: a unit spans several steps.
        self._unit_started: Optional[float] = None
        # The group (program) being worked on in the current phase, and when
        # it started; see 'group'.
        self._group: Optional[str] = None
        self._group_started: Optional[float] = None
        self.history_path = None
        # Phases recorded by a previous run that this run does not have, kept
        # so saving does not discard them: a campaign-only run must not wipe
        # the variant matrix's timings out of the history file.
        self._history_other: Dict[str, Dict[str, float]] = {}
        self._started = time.time()
        self._prev_handlers: Dict[int, object] = {}
        # A compile, or a 51-iteration run, emits no events for minutes. With
        # no ticker the bar freezes mid-operation and reads as hung: the
        # elapsed clock is the only evidence that anything is still happening.
        self._lock = threading.RLock()
        self._ticker: Optional[threading.Thread] = None
        self._stop = threading.Event()

    # -- lifecycle ---------------------------------------------------------

    def _usable(self) -> bool:
        if self._forced_width is not None:
            return True
        try:
            return self.stream.isatty() and os.environ.get("TERM", "") not in ("", "dumb")
        except Exception:
            return False

    def _size(self):
        if self._forced_width is not None:
            return self._forced_width, 24
        try:
            c, l = shutil.get_terminal_size()
            return max(20, c), max(self.HEIGHT + 2, l)
        except Exception:
            return 80, 24

    def install(self) -> "ProgressDisplay":
        if not self.enabled or self._installed:
            return self
        _, lines = self._size()
        w = self.stream.write
        w("\n" * self.HEIGHT)                        # scroll up to make room
        w(f"{CSI}1;{lines - self.HEIGHT}r")          # confine scrolling
        w(f"{CSI}{lines - self.HEIGHT};1H")          # cursor at the last text row
        self.stream.flush()
        self._installed = True
        self._stop.clear()
        self._ticker = threading.Thread(target=self._tick, name="progress",
                                        daemon=True)
        self._ticker.start()
        atexit.register(self.close)
        for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
            try:
                self._prev_handlers[sig] = signal.getsignal(sig)
                signal.signal(sig, self._on_signal)
            except (ValueError, OSError):
                pass                                  # not the main thread
        return self

    def _on_signal(self, signum, frame):
        self.close()
        prev = self._prev_handlers.get(signum)
        if callable(prev):
            prev(signum, frame)
        elif prev == signal.SIG_DFL:
            signal.signal(signum, signal.SIG_DFL)
            os.kill(os.getpid(), signum)

    def _tick(self):
        """Repaint about twice a second, so elapsed advances during long work."""
        while not self._stop.wait(0.5):
            try:
                self.draw()
            except Exception:
                return

    def close(self):
        """Release the scroll region. Idempotent, and safe to call twice."""
        self._stop.set()
        t = self._ticker
        if t is not None and t.is_alive() and t is not threading.current_thread():
            # Wait out at most one tick interval, so no repaint can land
            # after the scroll region has been released.
            t.join(timeout=1.0)
        if self._closed or not self._installed:
            self._closed = True
            return
        _, lines = self._size()
        w = self.stream.write
        with self._lock:
            self._closed = True          # stop any concurrent tick repainting
        w(_SAVE)
        w(f"{CSI}1;{lines}r")                        # full-screen scrolling again
        w(_RESTORE)
        w(f"{CSI}{lines - self.HEIGHT};1H")
        w("\n" * self.HEIGHT)
        try:
            self.stream.flush()
        except Exception:
            pass
        self._closed = True

    def __enter__(self):
        return self.install()

    def __exit__(self, *exc):
        self.close()
        return False

    # -- work model --------------------------------------------------------

    def add_phase(self, key: str, label: str, total: int, estimate: bool = True,
                  groups: Optional[Dict[str, int]] = None):
        """Register a phase of `total` units. `groups`, when given, names the
        phase's groups (one per program) and their unit counts, which lets
        the estimate cost each group from a previous run's timing."""
        if key not in self.phases:
            self.order.append(key)
        self.phases[key] = _Phase(key, label, total, estimate, groups)
        return self

    # -- history -----------------------------------------------------------

    def load_history(self, path) -> "ProgressDisplay":
        """Read per-group seconds from a previous run: {phase: {group: s}}.
        A missing or unreadable file just means no history."""
        self.history_path = path
        try:
            import json
            with open(path) as f:
                data = json.load(f)
        except (OSError, ValueError):
            return self
        for key, groups in (data.get("phases") or {}).items():
            if not isinstance(groups, dict):
                continue
            kept = {g: float(v) for g, v in groups.items()
                    if isinstance(v, (int, float)) and v > 0}
            ph = self.phases.get(key)
            if ph is not None:
                ph.history = kept
            else:
                self._history_other[key] = kept
        return self

    def save_history(self):
        """Write this run's completed group timings, merged over the
        previous history so a partial run keeps the groups it did not reach."""
        if not self.history_path:
            return
        import json
        phases = {k: dict(v) for k, v in self._history_other.items() if v}
        for key, ph in self.phases.items():
            merged = dict(ph.history)
            merged.update(ph.group_seconds)
            if merged:
                phases[key] = merged
        tmp = "%s.tmp" % self.history_path
        try:
            with open(tmp, "w") as f:
                json.dump({"phases": phases}, f, indent=1, sort_keys=True)
            os.replace(tmp, self.history_path)
        except OSError:
            pass

    def group(self, name: str):
        """Start timing the named group of the current phase, closing the
        previous one."""
        self._close_group()
        self._group = name
        self._group_started = time.time()

    def end_group(self):
        """Stop timing the current group without starting another.

        A group's record must cover its own work and nothing else: the
        campaign's last program stays open until the next phase begins, and
        everything done between (writing the report, the width families, the
        roofline probe) would otherwise be charged to it and carried into the
        next run's estimate as that program's cost."""
        self._close_group()

    def _close_group(self):
        ph = self.phases.get(self.current or "")
        if (ph is not None and self._group is not None
                and self._group_started is not None):
            ph.group_seconds[self._group] = (
                ph.group_seconds.get(self._group, 0.0)
                + time.time() - self._group_started)
            self.save_history()
        self._group = None
        self._group_started = None

    def set_total(self, key: str, total: int):
        if key in self.phases:
            self.phases[key].total = max(0, int(total))

    def start_phase(self, key: str):
        self._close_group()
        self.current = key
        self._item_started = None
        self._unit_started = time.time()
        self.draw()

    def item(self, context: str, action: str = ""):
        """Name the work now in scope, and what is being done to it.

        This does NOT sample a duration. It used to, and that was the bug
        behind a wildly optimistic estimate: `item()` fires several times per
        unit (compile, warmup, run), so the sampled median was a SUB-STEP
        time, while the remaining count is in UNITS. Multiplying one by the
        other understated the remaining time by roughly the number of steps
        per unit -- measured at 5.3x on a simulated campaign program.
        Durations are now sampled in 'advance()', in the same currency as
        the count they are multiplied by.
        """
        now = time.time()
        self._item_started = now
        self.context = context or ""
        self.action = action or ""
        self.draw()

    def advance(self, n: int = 1):
        """Record `n` completed units, and time them.

        The duration is divided by `n` so a caller that advances in batches
        (the campaign completes a program as two variants at once) still
        contributes a per-UNIT figure.
        """
        now = time.time()
        ph = self.phases.get(self.current or "")
        if ph is not None:
            if self._unit_started is not None and n > 0:
                ph.durations.extend([(now - self._unit_started) / n] * n)
            ph.done = min(ph.total, ph.done + n) if ph.total else ph.done + n
        self._unit_started = now
        self.draw()

    def finish_phase(self):
        self._close_group()
        ph = self.phases.get(self.current or "")
        if ph is not None and ph.total:
            ph.done = ph.total
        self._item_started = None
        self._unit_started = None
        self.draw()

    # -- estimation --------------------------------------------------------

    def totals(self):
        done = sum(p.done for p in self.phases.values())
        total = sum(p.total for p in self.phases.values())
        return done, total

    def _global_typical(self) -> Optional[float]:
        """Mean seconds per unit over every phase measured so far."""
        alld: List[float] = []
        for p in self.phases.values():
            alld.extend(p.durations)
        if not alld:
            return None
        return sum(alld) / len(alld)

    def _history_scale(self) -> float:
        """How this run's pace compares with the history's: actual over
        recorded seconds, summed over every group completed in this run that
        has a record. 1.0 until there is one. Absorbs a changed iteration
        count, a slower machine, or a cold compile cache."""
        actual = recorded = 0.0
        for p in self.phases.values():
            for g, secs in p.group_seconds.items():
                if g in p.history:
                    actual += secs
                    recorded += p.history[g]
        if recorded <= 0 or actual <= 0:
            return 1.0
        return min(4.0, max(0.25, actual / recorded))

    def _phase_remaining(self, p: "_Phase", glob: Optional[float],
                         scale: float):
        """(seconds left in phase `p`, whether any of it is extrapolated from
        another phase's time), or (None, False) with nothing to go on."""
        own = p.typical()
        rate = own if own is not None else glob
        borrowed = own is None
        if not p.groups:
            left = max(0, p.total - p.done)
            if not left:
                return 0.0, False
            if rate is None:
                return None, False
            return left * rate, borrowed
        remaining = 0.0
        rough = False
        now = time.time()
        for g, units in p.groups.items():
            if g in p.group_seconds and not (p.key == self.current
                                             and g == self._group):
                continue                                # finished
            if g in p.history:
                est = p.history[g] * scale
            elif rate is not None:
                est = units * rate
                rough = rough or borrowed
            else:
                return None, False
            if (p.key == self.current and g == self._group
                    and self._group_started is not None):
                est = max(0.0, est - (now - self._group_started))
            remaining += est
        return remaining, rough

    def eta_detail(self):
        """(remaining_seconds, rough) or (None, False).

        Each remaining group (program) is costed at its own time in the
        previous run, scaled by how this run is pacing against that record;
        the group in progress is charged only what it has left. A group with
        no record, and a phase with no groups, is costed at the phase's mean
        seconds per unit. `rough` is True when that rate is borrowed from
        another phase: a variant-matrix unit is not the same shape of work
        as a campaign unit, so the display says the figure is extrapolated.
        """
        glob = self._global_typical()
        scale = self._history_scale()
        have_history = any(p.history for p in self.phases.values())
        if glob is None and not have_history:
            return None, False
        remaining = 0.0
        rough = False
        for p in self.phases.values():
            if not p.estimate:
                continue
            left, r = self._phase_remaining(p, glob, scale)
            if left is None:
                if max(0, p.total - p.done):
                    return None, False
                continue
            remaining += left
            rough = rough or r
        return remaining, rough

    def eta_seconds(self) -> Optional[float]:
        """Remaining time, or None while nothing has been measured yet.

        Delegates to 'eta_detail' rather than repeating its loop. The two were
        briefly separate copies, and they immediately diverged: adding the
        `estimate` flag fixed one and left the other costing the tables phase
        at a benchmark unit's price.
        """
        return self.eta_detail()[0]

    # -- rendering ---------------------------------------------------------

    def _bar_row(self, frac: float, width: int):
        """One row of the bar: filled cells and track cells, nothing partial.

        Rounds rather than truncates, so the bar is never a whole cell behind
        the figure printed beside it.
        """
        width = max(4, width)
        full = int(round(frac * width))
        full = max(0, min(width, full))
        return _FULL * full, _TRACK * (width - full)

    def render(self) -> List[str]:
        """Context line, then a two-row bar with the figures beside it.

        Two rows rather than one: a single row of text is only a few
        millimetres tall, which is what made the hairline version read as a
        rule rather than as a bar.
        """
        cols, _ = self._size()
        done, total = self.totals()
        frac = min(1.0, max(0.0, (done / total) if total else 0.0))

        ph = self.phases.get(self.current or "")
        left = f"{ph.label} {ph.done}/{ph.total}" if ph and ph.total else (ph.label if ph else "")
        head = "  " + " · ".join(x for x in (left, self.action) if x)
        if self.context:
            head += "  " + self.context
        head = head[: cols - 1]

        elapsed = time.time() - self._started
        eta, eta_rough = self.eta_detail()
        stat_top = f"{int(round(frac * 100))}%"
        if self._item_started is not None:
            here = time.time() - self._item_started
            if here >= 5:            # only once it is worth remarking on
                stat_top += f"   this step {_fmt_duration(here)}"
        stat_bot = f"elapsed {_fmt_duration(elapsed)}"
        if eta is not None:
            stat_bot += f"  ·  ~{_fmt_duration(eta)} left"
            if eta_rough:
                # Extrapolated across phases: say so rather than imply it was
                # measured.
                stat_bot += " (rough)"
        widest = max(len(stat_top), len(stat_bot))
        bar_w = max(8, cols - widest - 7)
        full, track = self._bar_row(frac, bar_w)
        return [head,
                ("  ", full, track, "  " + stat_top),
                ("  ", full, track, "  " + stat_bot)]

    def draw(self):
        if not self.enabled or not self._installed or self._closed:
            return
        _, lines = self._size()
        w = self.stream.write
        green = _green(self.stream)
        # The ticker thread repaints alongside the caller, so serialise the
        # escape sequences: interleaving two cursor-save/restore pairs would
        # leave the cursor somewhere unintended.
        with self._lock:
            if self._closed:
                return
            w(_SAVE)
            for i, row in enumerate(self.render()):
                w(f"{CSI}{lines - self.HEIGHT + 1 + i};1H")
                w(f"{CSI}2K")                        # clear the whole row
                if isinstance(row, str):
                    w(row)                           # normal foreground
                else:
                    pad, full, track, stats = row
                    # Only the filled portion is coloured; the track and the
                    # figures use the terminal's own foreground.
                    w(pad + green + full + _OFF + track + stats)
            w(_RESTORE)
            try:
                self.stream.flush()
            except Exception:
                pass


class NullProgress(ProgressDisplay):
    """Explicitly disabled display, for --verbose and non-TTY runs."""

    def __init__(self):
        super().__init__(enabled=False)
