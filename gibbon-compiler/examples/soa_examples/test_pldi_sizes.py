#!/usr/bin/env python3
"""Regression tests for --pldi-sizes (per-program input sizes).

  - TestSizesFile: the TOML loader accepts one shape and rejects the rest
    before any work is done; the shipped example loads.
  - TestKnobs: every sizable program's AOS and SOA source has exactly one
    size literal, the rewrite changes that literal and nothing else, and the
    model reproduces the committed oracle at the default size.
  - TestResizedRun: the resized copy lands under the output directory (the
    shipped source is untouched), the oracle is recomputed at the new size,
    captions say the program was resized, and a replot restores the sizes
    from the stored report.
"""
import importlib
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import gibbon_benchmark as gb  # noqa: E402
import bench_provenance as prov  # noqa: E402

PROGRAMS = HERE / "programs"


def _write(text: str) -> Path:
    f = tempfile.NamedTemporaryFile("w", suffix=".toml", delete=False)
    f.write(text)
    f.close()
    return Path(f.name)


class TestSizesFile(unittest.TestCase):
    def test_reads_sizes_with_or_without_extension(self):
        p = _write("[sizes]\nList = 1000\n\"MonoTree.hs\" = 12\n")
        self.assertEqual(gb.load_pldi_sizes_file(p, PROGRAMS),
                         {"List.hs": 1000, "MonoTree.hs": 12})

    def test_rejects_a_program_without_a_size_knob(self):
        p = _write("[sizes]\nTrie = 10\n")
        with self.assertRaisesRegex(ValueError, "'Trie' has no configurable size"):
            gb.load_pldi_sizes_file(p, PROGRAMS)

    def test_rejects_non_positive_and_non_integer_sizes(self):
        for bad in ("0", "-5", "1.5", "true", "\"10\""):
            p = _write("[sizes]\nList = %s\n" % bad)
            with self.assertRaisesRegex(ValueError, "positive integer", msg=bad):
                gb.load_pldi_sizes_file(p, PROGRAMS)

    def test_rejects_the_same_program_twice(self):
        p = _write("[sizes]\nList = 10\n\"List.hs\" = 20\n")
        with self.assertRaisesRegex(ValueError, "given twice"):
            gb.load_pldi_sizes_file(p, PROGRAMS)

    def test_rejects_a_file_without_sizes_or_with_other_tables(self):
        with self.assertRaisesRegex(ValueError, r"no \[sizes\] table"):
            gb.load_pldi_sizes_file(_write("List = 10\n"), PROGRAMS)
        with self.assertRaisesRegex(ValueError, "unknown table"):
            gb.load_pldi_sizes_file(_write("[sizes]\nList = 10\n[pldi]\nconfigs = []\n"),
                                    PROGRAMS)

    def test_the_example_loads(self):
        self.assertEqual(gb.load_pldi_sizes_file(HERE / "pldi_sizes.example.toml", PROGRAMS),
                         {"List.hs": 10000000})


class TestKnobs(unittest.TestCase):
    def setUp(self):
        self.addCleanup(importlib.reload, gb)

    def test_each_source_has_one_literal_and_the_model_matches_the_manifest(self):
        manifest = json.loads((HERE / "oracles" / "manifest.json").read_text())["oracles"]
        for program, knob in gb.PLDI_SIZE_KNOBS.items():
            sizes = {gb.source_size(program, (PROGRAMS / lay / program).read_text())
                     for lay in ("AOS", "SOA") if (PROGRAMS / lay / program).exists()}
            self.assertEqual(len(sizes), 1, program)
            default = sizes.pop()
            self.assertEqual(knob.expected(default).split(),
                             manifest[program[:-3]]["expected"].split(), program)

    def test_rewrite_changes_only_the_size_literal(self):
        for program in gb.PLDI_SIZE_KNOBS:
            gb.PLDI_INPUT_SIZES.clear()
            gb.PLDI_INPUT_SIZES[program] = 7
            for lay in ("AOS", "SOA"):
                src = PROGRAMS / lay / program
                if not src.exists():
                    continue
                before = src.read_text()
                after = gb.resize_source_text(program, before)
                self.assertEqual(gb.source_size(program, after), 7, (program, lay))
                changed = [(a, b) for a, b in zip(before.splitlines(), after.splitlines())
                           if a != b]
                self.assertEqual(len(changed), 1, (program, lay))
                self.assertEqual(len(before.splitlines()), len(after.splitlines()))

    def test_no_override_means_no_rewrite(self):
        text = (PROGRAMS / "AOS" / "List.hs").read_text()
        self.assertEqual(gb.resize_source_text("List.hs", text), text)


class TestResizedRun(unittest.TestCase):
    def setUp(self):
        self.addCleanup(importlib.reload, gb)
        gb.set_pldi_input_sizes({"List.hs": 10, "MonoTree.hs": 4}, PROGRAMS)

    def test_resized_copy_is_compiled_and_the_shipped_source_is_untouched(self):
        shipped = PROGRAMS / "AOS" / "List.hs"
        before = shipped.read_text()
        with tempfile.TemporaryDirectory() as out:
            copy = gb.resized_source(shipped, "List.hs", Path(out))
            self.assertEqual(copy, Path(out) / "resized_src" / "AOS" / "List.hs")
            self.assertIn("lst = mkList 10\n", copy.read_text())
        self.assertEqual(shipped.read_text(), before)

    def test_unresized_programs_compile_their_shipped_source(self):
        shipped = PROGRAMS / "AOS" / "TernaryTree.hs"
        with tempfile.TemporaryDirectory() as out:
            self.assertEqual(gb.resized_source(shipped, "TernaryTree.hs", Path(out)), shipped)

    def test_defaults_are_read_from_the_source(self):
        self.assertEqual(gb.PLDI_DEFAULT_SIZES, {"List.hs": 100000000, "MonoTree.hs": 23})

    def test_the_oracle_is_recomputed_at_the_new_size(self):
        manifest = gb.resized_oracle_manifest(
            prov.OracleManifest.load_default(HERE))
        # mkList 10 -> 10..1, add1 -> 11..2, sum = 65.
        self.assertEqual(manifest.check("List.hs", "'#(65 65 10)")[0], prov.ORACLE_PASS)
        self.assertEqual(manifest.check("List.hs",
                                        "'#(5000000150000000 5000000150000000 100000000)")[0],
                         prov.ORACLE_FAIL)
        # Depth 4: 16 leaves of 1+2+3+4+1 = 11.
        self.assertEqual(manifest.check("MonoTree.hs", "'#(176 176)")[0], prov.ORACLE_PASS)
        self.assertIn("recomputed for", manifest.lookup("List").note)
        # Programs that were not resized keep their committed oracle.
        self.assertEqual(manifest.lookup("TernaryTree").expected, "28697813")

    def test_captions_name_the_size_and_its_default(self):
        note = gb.size_caption_note("List.hs")
        self.assertIn("10", note)
        self.assertIn("default 100,000,000", note)
        self.assertEqual(gb.size_caption_note("TernaryTree.hs"), "")
        overview = gb.sizes_overview_note()
        self.assertIn("List (n (list elements) = 10; default 100,000,000)", overview)
        self.assertIn("MonoTree (depth = 4; default 23)", overview)

    def test_a_replot_restores_the_stored_sizes(self):
        stored = {"campaign": {"codegen": {"input_sizes": {
            "List.hs": {"size": 10, "default": 100000000, "unit": "n (list elements)"}}}}}
        p = _write(json.dumps(stored))
        gb.PLDI_INPUT_SIZES.clear()
        gb.PLDI_DEFAULT_SIZES.clear()
        gb.adopt_stored_campaign_settings(p)
        self.assertEqual(gb.PLDI_INPUT_SIZES, {"List.hs": 10})
        self.assertIn("default 100,000,000", gb.size_caption_note("List.hs"))


class TestCommandLine(unittest.TestCase):
    def _run(self, *argv):
        return subprocess.run([sys.executable, str(HERE / "gibbon_benchmark.py"), *argv],
                              capture_output=True, text=True, cwd=HERE)

    def test_sizes_without_pldi_submission_is_an_error(self):
        r = self._run("--pldi-sizes", str(_write("[sizes]\nList = 10\n")))
        self.assertEqual(r.returncode, 2)
        self.assertIn("use it with --pldi-submission", r.stderr)

    def test_sizes_with_ghc_or_mlton_is_an_error(self):
        r = self._run("--pldi-submission", "--benchmark-ghc",
                      "--pldi-sizes", str(_write("[sizes]\nList = 10\n")))
        self.assertEqual(r.returncode, 2)
        self.assertIn("--benchmark-ghc", r.stderr)

    def test_a_bad_sizes_file_stops_before_any_work(self):
        r = self._run("--pldi-submission", "--pldi-sizes", str(_write("[sizes]\nTrie = 3\n")))
        self.assertEqual(r.returncode, 2)
        self.assertIn("no configurable size", r.stderr)


if __name__ == "__main__":
    unittest.main()
