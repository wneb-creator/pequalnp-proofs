import json
import sys
from pathlib import Path

case = json.loads(Path(sys.argv[1]).read_text())
gates = json.loads(Path(sys.argv[2]).read_text())
n = case['inputs']
count = 1 << n
values = [int(('1'*(1 << i)+'0'*(1 << i))*(1 << (n-i-1)), 2) for i in range(n)]
expected = 0
for a, b in case['edges']:
    expected |= values[a] & values[b]
for i, gate in enumerate(gates):
    assert len(gate) == 3
    op, a, b = gate
    assert op in (0, 1) and 0 <= a < n+i and 0 <= b < n+i
    values.append((values[a] | values[b]) if op else (values[a] & values[b]))
actual = values[-1]
false_positives = (actual & ~expected).bit_count()
false_negatives = (expected & ~actual).bit_count()
print('assignments', count, 'gates', len(gates), 'false positives', false_positives,
      'false negatives', false_negatives)
assert false_positives == 0 and false_negatives == 0
for x, y in case['tests']:
    assert ((actual >> x) & 1) == y
print('All assignments and stored test basis agree.')
