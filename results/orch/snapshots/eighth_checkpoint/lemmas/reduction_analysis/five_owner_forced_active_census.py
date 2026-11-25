import json
from pathlib import Path
from five_owner_core import ROWS, INPUT_ORIGINAL, NEIGHBORS

HERE = Path(__file__).resolve().parent
lines = INPUT_ORIGINAL[5:]
neighborhoods = [sum(1 << lines.index(v) for v in NEIGHBORS[p]) for p in ROWS]
counts = {}
for mask in range(1 << len(lines)):
    unions = {0}
    for neighbors in neighborhoods:
        unions |= {u | (neighbors & mask) for u in unions}
    counts[mask] = len(unions)
minimal = [mask for mask, count in counts.items() if count > 16 and
           all(counts[mask ^ (1 << j)] <= 16 for j in range(len(lines)) if mask >> j & 1)]
assert len(minimal) == 209
result = {
    'rows': ROWS, 'input_original': INPUT_ORIGINAL,
    'scope': 'For an exact core with at most5 binary ANDs, every AND is true on every listed assignment. All point inputs are true. With only listed lines true, the induced graph has >16 maximal negatives and hence requires5 ANDs. An AND false at that assignment is identically false on its downset and can be replaced by a constant-false OR, contradicting the family bound. Pure-OR features preserve this argument. This is computational data and a mathematical argument, not a Lean theorem.',
    'minimal_assignment_count': len(minimal),
    'assignments': [{'raw_mask': 31 | (m << 5),
                     'line_original': [lines[j] for j in range(len(lines)) if m >> j & 1],
                     'negative_count': counts[m]} for m in minimal],
    'count_histogram': {str(c): sum(v == c for v in counts.values()) for c in sorted(set(counts.values()))},
}
text = json.dumps(result, indent=2) + '\n'
output = HERE / 'five_owner_forced_active_census.json'
assert output.read_text() == text
print('Reproduced all2048 restricted counts and all209 minimal forced-active assignments exactly.')
