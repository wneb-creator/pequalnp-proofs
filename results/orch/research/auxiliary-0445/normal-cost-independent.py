import argparse
import json
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('witness', type=Path)
args = parser.parse_args()
w = json.loads(args.witness.read_text())
assert w['line'] == [0, 1, 3, 9] and len(w['gates']) == 8
columns = [sum(1 << m for m in range(8192) if (m >> p) & 1) for p in range(13)]
band = sum(1 << m for m in range(8192) if m.bit_count() in (7, 8))
mask = (1 << 8192) - 1
actual = columns[:]
cost = [1] * 13
for a, b, and_gate in w['gates']:
    assert 0 <= a < len(actual) and 0 <= b < len(actual)
    actual.append((actual[a] & actual[b]) if and_gate else (actual[a] | actual[b]))
    cost.append(min(cost[a], cost[b]) if and_gate else min(5, cost[a] + cost[b]))
expected = columns[1] | columns[3] | columns[9] | (columns[0] & (columns[2] | columns[4] | columns[5] | columns[6]))
target = columns[0] | columns[1] | columns[3] | columns[9]
assert actual[w['out']] == expected
assert expected & (~target & mask) == 0
assert ((expected ^ target) & band) == 0
assert (expected ^ target).bit_count() == 32
factored = [(2, 4, False), (5, 6, False), (13, 14, False), (0, 15, True), (1, 3, False), (17, 9, False), (16, 18, False)]
fv = columns[:]
fc = [1] * 13
for a, b, and_gate in factored:
    fv.append(fv[a] & fv[b] if and_gate else fv[a] | fv[b])
    fc.append(min(fc[a], fc[b]) if and_gate else min(5, fc[a] + fc[b]))
assert fv[-1] == expected and fc[-1] == 4 and cost[-1] == 5
print('INDEPENDENT PASS: all8192 rows,8gates cost5,globalupper,3003bandrows exact,32globaldifferences; equivalent7gatefactorizationcost4.')
print('Scope: refutes semantic four-zero falsifier implies additive formal cost4; not minimal and not a gap counterexample.')
