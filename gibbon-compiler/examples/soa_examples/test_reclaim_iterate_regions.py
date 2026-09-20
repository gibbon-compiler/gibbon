"""--reclaim-iterate-regions must reach EVERY compile, or not be on at all.

Gibbon's `iterate` loop re-grows its output region from chunk 0 each iteration
and strands the previous iteration's chunk chain, so memory grows by one whole
output value per iteration -- 929 MB/iteration for a 100M-element list, which
OOM-kills at --iterate 101.  Gibbon's fix is opt-in, so this driver flag is too.

The property this file exists to pin: when the flag is on, it lands on every
configuration the run compiles.  A campaign where some columns reclaim and
others do not is not comparable, and that failure would be invisible in the
tables -- the numbers would simply be wrong.
"""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import gibbon_benchmark as gb

FLAG = "--reclaim-iterate-regions"


class _Scoped(unittest.TestCase):
    """The setting is run-scoped module state; never leak it between tests."""

    def setUp(self):
        self._saved = gb.RECLAIM_ITERATE_REGIONS

    def tearDown(self):
        gb.set_reclaim_iterate_regions(self._saved)


def cmd(**kw):
    return gb.build_gibbon_command(
        Path("P.hs"), kw.pop("variant", "soa"), Path("P.c"), Path("P.exe"),
        "gcc", **kw)


class TestFlagPlumbing(_Scoped):
    def test_off_by_default(self):
        gb.set_reclaim_iterate_regions(False)
        self.assertNotIn(FLAG, cmd())

    def test_on_when_the_run_selected_it(self):
        gb.set_reclaim_iterate_regions(True)
        self.assertIn(FLAG, cmd())

    def test_explicit_argument_overrides_the_run_setting(self):
        # Tests need to construct either command regardless of run state.
        gb.set_reclaim_iterate_regions(True)
        self.assertNotIn(FLAG, cmd(reclaim_iterate_regions=False))
        gb.set_reclaim_iterate_regions(False)
        self.assertIn(FLAG, cmd(reclaim_iterate_regions=True))

    def test_resolved_at_call_time_not_definition_time(self):
        # A default argument would bind once at import, freezing the value
        # before main() ever reads argv -- the flag would silently do nothing.
        gb.set_reclaim_iterate_regions(False)
        before = cmd()
        gb.set_reclaim_iterate_regions(True)
        after = cmd()
        self.assertNotIn(FLAG, before)
        self.assertIn(FLAG, after)

    def test_emitted_once_not_duplicated(self):
        gb.set_reclaim_iterate_regions(True)
        self.assertEqual(1, cmd().count(FLAG))


class TestReachesEveryConfiguration(_Scoped):
    """The load-bearing one: every config dict the driver compiles from."""

    def _all_config_dicts(self):
        out = []
        for layout in ("aos", "soa"):
            for name, cfgs in (("PLDI_FOLD_CONFIGS", gb.PLDI_FOLD_CONFIGS),
                               ("PLDI_MAP_CONFIGS", gb.PLDI_MAP_CONFIGS)):
                for col, opts in cfgs[layout].items():
                    out.append((f"{name}[{layout}][{col}]", opts))
        for col, opts in gb.ADD1TREE_WIDTH_CONFIGS.items():
            out.append((f"ADD1TREE_WIDTH_CONFIGS[{col}]", opts))
        for width, cfgs in gb.ARITHINTENSITY_WIDTH_CONFIGS.items():
            for col, opts in cfgs.items():
                out.append((f"ARITHINTENSITY_WIDTH_CONFIGS[{width}][{col}]", opts))
        return out

    def test_every_config_dict_gets_the_flag_when_on(self):
        configs = self._all_config_dicts()
        self.assertGreater(len(configs), 20, "config registries not found")
        gb.set_reclaim_iterate_regions(True)
        for label, opts in configs:
            with self.subTest(config=label):
                self.assertIn(FLAG, cmd(**dict(opts)),
                              "%s did not get %s" % (label, FLAG))

    def test_and_none_of_them_get_it_when_off(self):
        gb.set_reclaim_iterate_regions(False)
        for label, opts in self._all_config_dicts():
            with self.subTest(config=label):
                self.assertNotIn(FLAG, cmd(**dict(opts)),
                                 "%s got %s with the run flag off" % (label, FLAG))

    def test_no_config_dict_hardcodes_it(self):
        # It must come from the run-scoped setting, never from a config entry:
        # a hardcoded one would apply in runs that did not ask for it.
        for label, opts in self._all_config_dicts():
            self.assertNotIn("reclaim_iterate_regions", opts,
                             "%s hardcodes the flag" % label)


class TestCli(_Scoped):
    def test_parser_exposes_the_flag_and_defaults_off(self):
        p = gb.build_parser()
        self.assertFalse(p.parse_args([]).reclaim_iterate_regions)
        self.assertTrue(p.parse_args([FLAG]).reclaim_iterate_regions)

    def test_no_flag_turns_it_off(self):
        p = gb.build_parser()
        self.assertIs(p.parse_args(["--no-reclaim-iterate-regions"])
                      .reclaim_iterate_regions, False)

    def test_pldi_submission_defaults_it_on(self):
        self.assertTrue(gb.default_reclaim_iterate_regions(None, True))
        self.assertFalse(gb.default_reclaim_iterate_regions(None, False))

    def test_explicit_choice_overrides_pldi_default(self):
        self.assertFalse(gb.default_reclaim_iterate_regions(False, True))
        self.assertTrue(gb.default_reclaim_iterate_regions(True, False))

    def test_main_resolves_the_default_before_setting_it(self):
        src = Path(gb.__file__).read_text()
        main_src = src[src.index("\ndef main("):]
        self.assertLess(main_src.index("default_reclaim_iterate_regions("),
                        main_src.index("set_reclaim_iterate_regions(args."))

    def test_the_recorded_provenance_names_the_setting(self):
        # --pldi-submission turns it on without the flag appearing in
        # driver_argv, and it changes the measured times, so argv alone no
        # longer says which way a recorded number was compiled.
        args = gb.build_parser().parse_args([])
        for enabled in (True, False):
            gb.set_reclaim_iterate_regions(enabled)
            block = gb.campaign_provenance(args)
            self.assertEqual(block["codegen"]["reclaim_iterate_regions"],
                             enabled)

    def test_help_explains_the_cost_of_leaving_it_off(self):
        h = gb.build_parser().format_help()
        self.assertIn("929 MB/iteration", h)
        self.assertIn("EVERY variant", h)


class TestSetBeforeAnythingReadsIt(_Scoped):
    """Regression: the setter used to run AFTER the run banner printed, so the
    banner reported "off" even when the flag was given.  Anything that reads
    the global -- the banner, every compile -- must come after it in main()."""

    def test_setter_precedes_every_reader_in_main(self):
        src = Path(gb.__file__).read_text()
        main_src = src[src.index("\ndef main("):]
        set_ix = main_src.index("set_reclaim_iterate_regions(args.reclaim_iterate_regions)")
        for reader in ("Region reclaim:", "RECLAIM_ITERATE_REGIONS else"):
            if reader in main_src:
                self.assertLess(
                    set_ix, main_src.index(reader),
                    "main() reads the region-reclaim setting at %r before "
                    "setting it" % reader)

    def test_set_immediately_after_parse_args(self):
        # Not merely "before the banner": before the correctness-only early
        # return too, so every code path out of main() sees the same value.
        src = Path(gb.__file__).read_text()
        main_src = src[src.index("\ndef main("):]
        between = main_src[main_src.index("args = ap.parse_args()"):
                           main_src.index("set_reclaim_iterate_regions(args.")]
        self.assertNotIn("return", between,
                         "a code path can leave main() before the setting is applied")


class TestCaption(_Scoped):
    def test_caption_note_only_when_on(self):
        gb.set_reclaim_iterate_regions(False)
        self.assertEqual("", gb.reclaim_caption_note())
        gb.set_reclaim_iterate_regions(True)
        note = gb.reclaim_caption_note()
        self.assertIn("reclaim-iterate-regions", note)
        self.assertIn("flat in the", note)


if __name__ == "__main__":
    unittest.main()
