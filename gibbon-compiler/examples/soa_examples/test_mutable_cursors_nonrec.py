"""--opt-mutable-cursors-nonrec must reach every mutable-cursor compile, and no
immutable-cursor one.

The flag stops a non-recursive SoA reader from returning its input-region ends
-- a CursorArrayTy returned by value through memory -- to a caller that
already holds them. The driver turns it on for the whole run, so every column
of a campaign is compiled the same way; a campaign where some columns have it
and others do not is not comparable. The compiler rejects the flag without
--use-mutable-cursors, so an immutable-cursor compile carrying it would not
build at all.
"""
import inspect
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import gibbon_benchmark as gb

FLAG = "--opt-mutable-cursors-nonrec"


class _Scoped(unittest.TestCase):
    """The setting is run-scoped module state; never leak it between tests."""

    def setUp(self):
        self._saved = gb.MUTABLE_CURSORS_NONREC

    def tearDown(self):
        gb.set_mutable_cursors_nonrec(self._saved)


def cmd(**kw):
    return gb.build_gibbon_command(
        Path("P.hs"), kw.pop("variant", "soa"), Path("P.c"), Path("P.exe"),
        "gcc", **kw)


class TestFlagPlumbing(_Scoped):
    def test_on_by_default(self):
        self.assertTrue(gb.MUTABLE_CURSORS_NONREC)

    def test_a_mutable_cursor_compile_carries_it(self):
        gb.set_mutable_cursors_nonrec(True)
        self.assertIn(FLAG, cmd(use_mutable_cursors=True))

    def test_an_immutable_cursor_compile_never_does(self):
        """The compiler rejects the flag without --use-mutable-cursors."""
        gb.set_mutable_cursors_nonrec(True)
        self.assertNotIn(FLAG, cmd(use_mutable_cursors=False))
        self.assertNotIn(FLAG, cmd(use_mutable_cursors=False,
                                   mutable_cursors_nonrec=True))

    def test_off_when_the_run_disabled_it(self):
        gb.set_mutable_cursors_nonrec(False)
        self.assertNotIn(FLAG, cmd(use_mutable_cursors=True))

    def test_explicit_argument_overrides_the_run_setting(self):
        gb.set_mutable_cursors_nonrec(True)
        self.assertNotIn(FLAG, cmd(use_mutable_cursors=True,
                                   mutable_cursors_nonrec=False))
        gb.set_mutable_cursors_nonrec(False)
        self.assertIn(FLAG, cmd(use_mutable_cursors=True,
                                mutable_cursors_nonrec=True))

    def test_resolved_at_call_time_not_definition_time(self):
        # A default argument would bind once at import, freezing the value
        # before main() reads argv -- the switch would silently do nothing.
        gb.set_mutable_cursors_nonrec(False)
        before = cmd(use_mutable_cursors=True)
        gb.set_mutable_cursors_nonrec(True)
        after = cmd(use_mutable_cursors=True)
        self.assertNotIn(FLAG, before)
        self.assertIn(FLAG, after)

    def test_it_follows_the_mutable_cursor_flag(self):
        """Placed with --use-mutable-cursors, which it depends on."""
        gb.set_mutable_cursors_nonrec(True)
        c = cmd(use_mutable_cursors=True)
        self.assertEqual(c.index(FLAG), c.index("--use-mutable-cursors") + 1)


class TestEveryPldiConfiguration(_Scoped):
    """Every configuration the PLDI matrix compiles, both layouts: the flag is
    present exactly when that configuration uses mutable cursors."""

    def test_present_exactly_on_the_mutable_cursor_configurations(self):
        gb.set_mutable_cursors_nonrec(True)
        accepted = set(inspect.signature(gb.build_gibbon_command).parameters)
        seen_mutable = seen_immutable = 0
        for layout, configs in gb.PLDI_MAP_CONFIGS.items():
            for name, kwargs in configs.items():
                kw = {k: v for k, v in kwargs.items() if k in accepted}
                c = cmd(variant=name, **kw)
                mutable = "--use-mutable-cursors" in c
                self.assertEqual(FLAG in c, mutable, name)
                seen_mutable += mutable
                seen_immutable += not mutable
        # Both kinds must exist, or the test proves nothing about either.
        self.assertGreater(seen_mutable, 0)
        self.assertGreater(seen_immutable, 0)


class TestCommandLine(unittest.TestCase):
    def test_off_switch_parses(self):
        src = Path(gb.__file__).read_text()
        self.assertIn('"--no-mutable-cursors-nonrec"', src)
        self.assertIn("set_mutable_cursors_nonrec(not args.no_mutable_cursors_nonrec)", src)


if __name__ == "__main__":
    unittest.main()
