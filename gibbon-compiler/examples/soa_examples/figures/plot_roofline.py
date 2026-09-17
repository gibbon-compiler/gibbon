#!/usr/bin/env python3
"""Redraw the empirical roofline from roofline.json.

    python3 plot_roofline.py <roofline.json> [out.png]

Emitted alongside the data so the plot can be regenerated, or restyled,
without re-running the measurement (and on a machine that has matplotlib
even if the measuring one did not).
"""
import json
import sys
from pathlib import Path

# Absolute path to the suite directory, written in when this script was
# generated -- --figures-dir may be anywhere, so it cannot be derived from
# this file's own location.
sys.path.insert(0, "/workdisk/git/gibbon/gibbon-compiler/examples/soa_examples")
from gibbon_benchmark import _render_roofline_png  # noqa: E402

if __name__ == "__main__":
    data = json.loads(Path(sys.argv[1]).read_text())
    out = Path(sys.argv[2] if len(sys.argv) > 2 else "roofline.png")
    _render_roofline_png(data, out)
    print("wrote %s" % out)
