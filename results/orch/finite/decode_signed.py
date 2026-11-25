import json
import sys
from pathlib import Path


metadata = json.loads(Path(sys.argv[1]).read_text())
solver = Path(sys.argv[2]).read_text().splitlines()
assert any(line == 's SATISFIABLE' for line in solver)
positive = {int(word) for line in solver if line.startswith('v ')
            for word in line[2:].split() if int(word) > 0}
gates = []
for j in range(metadata['size']):
    selected = []
    for key in ('ops', 'left', 'right'):
        choices = [i for i, var in enumerate(metadata[key][j]) if var in positive]
        assert len(choices) == 1
        selected.append(choices[0])
    gates.append(selected)
bad = []
for row in range(1 << metadata['n']):
    bank = [bool((row >> i) & 1) for i in range(metadata['n'])] + [False]
    for op, a, b in gates:
        x, y = bank[a], bank[b]
        bank.append((x and y, x or y, x and not y, not x and y)[op])
    target = any((row >> a) & 1 and (row >> b) & 1 for a, b in metadata['edges'])
    if bank[-1] != target:
        bad.append(row)
report = dict(n=metadata['n'], size=metadata['size'], edges=metadata['edges'],
              operations=['AND', 'OR', 'AND_NOT_RIGHT', 'AND_NOT_LEFT'],
              constant_zero_wire=metadata['n'], gates=gates, mismatches=bad)
Path(sys.argv[3]).write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(dict(gates=gates, mismatches=len(bad))))
assert not bad
