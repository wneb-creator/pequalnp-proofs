from pathlib import Path
import json

root = Path(__file__).resolve().parent
gates = json.loads((root / 'audit-path-center6-summary.log').read_text().splitlines()[1])


def evaluate(mask):
    values = [bool(mask >> i & 1) for i in range(4)]
    for op, a, b in gates:
        values.append((values[a] and values[b]) if op else (values[a] or values[b]))
    return values


assert all(a < b < 4 + j and op in (0, 1) for j, (op, a, b) in enumerate(gates))
for mask in range(16):
    target = any(bool(mask >> a & 1) and bool(mask >> b & 1)
                 for a, b in [(0, 1), (0, 2), (1, 3)])
    assert evaluate(mask)[-1] == target

traces = []
for base, seed in [(0, 1), (1, 0)]:
    values = evaluate(1 << base)
    derivative = [i == seed for i in range(4)]
    for op, a, b in gates:
        derivative.append(((values[a] and derivative[b]) or (derivative[a] and values[b]))
                          if op else (derivative[a] or derivative[b]))
    assert not derivative[-1]
    traces.append(derivative)

expected = json.loads((root / 'audit-path-center-validation.json').read_text())
assert expected['gates'] == gates
assert expected['derivative_traces'] == traces
print('PASS: six-gate witness, all 16 assignments, legal operands, both derivative traces')
