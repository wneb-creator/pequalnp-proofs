"""Reproduce the inherited zero-cofactor cuts for Petersen minus vertex 9.

Usage: python3 prepare_minus9_cuts.py SOURCE_JSON OUTPUT_TEXT
SOURCE_JSON is results/orch/combinatorial_zero_cuts.json.
The free OR(4,6) is a physically included gate, counted in the SAT total.
"""

import json
from pathlib import Path
import sys

source, output = map(Path, sys.argv[1:])
rows = json.loads(source.read_text())
assert isinstance(rows, list)
cuts = {}
for row in rows:
    assert isinstance(row, dict)
    removed, lower = row["removed"], row["lower"]
    assert all(isinstance(v, int) and 0 <= v < 10 for v in removed)
    assert isinstance(lower, int)
    if 9 not in removed:
        continue
    mask = sum(1 << v for v in removed if v != 9)
    if mask:
        cuts[mask] = max(cuts.get(mask, 0), lower)
for v in range(9):
    expected = 13 if v in (4, 6, 7) else 12
    assert cuts[1 << v] == expected
    cuts[1 << v] = expected
output.write_text("".join(f"{mask} {lower}\n" for mask, lower in sorted(cuts.items())))
