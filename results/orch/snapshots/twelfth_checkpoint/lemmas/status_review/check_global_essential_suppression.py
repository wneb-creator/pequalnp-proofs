"""Independently replay the global soft-tag C++ diagnostic fixtures."""
from pathlib import Path
import hashlib
import itertools
import json


ROOT = Path(__file__).resolve().parents[1] / 'circuit_search'
geometry = json.loads((ROOT / 'geometry.json').read_text())
seeds_path = ROOT / 'global-essential-warm-seeds.json'
fixtures_path = ROOT / 'global-essential-suppressed-fixtures.json'
seeds = json.loads(seeds_path.read_text())
fixtures = json.loads(fixtures_path.read_text())
edges = [sum(1 << i for i in edge) for edge in geometry['edges']]
negatives = [point | (line << 13) for point, line in geometry['maximal_independent_sets']]
basis = edges + negatives + [1 << i for i in range(26)]
small = [0] + [1 << i for i in range(26)]
small += [sum(1 << i for i in pair) for pair in itertools.combinations(range(26), 2)
          if sum(1 << i for i in pair) not in edges]
assert len(basis) == 782 and len(small) == 300
positive = (1 << len(edges)) - 1
columns = [sum(bool(mask & (1 << i)) << j for j, mask in enumerate(basis)) for i in range(26)]
small_columns = [sum(bool(mask & (1 << i)) << j for j, mask in enumerate(small)) for i in range(26)]


def evaluate(gates, initial):
    values = initial.copy()
    for op, a, b in gates:
        assert op in (0, 1) and 0 <= a < len(values) and 0 <= b < len(values)
        values.append(values[a] | values[b] if op else values[a] & values[b])
    return values


def replacement_output(gates, values, gate, replacement):
    altered = values[:26 + gate] + [replacement]
    for op, a, b in gates[gate + 1:]:
        altered.append(altered[a] | altered[b] if op else altered[a] & altered[b])
    return altered[-1]


assert len(seeds) == len(fixtures)
accepted = 0
for index, (seed, fixture) in enumerate(zip(seeds, fixtures)):
    gates = seed['gates']
    assert 0 < len(gates) <= 63
    values = evaluate(gates, columns)
    little = evaluate(gates, small_columns)
    used = {26 + len(gates) - 1}
    for j in reversed(range(len(gates))):
        if 26 + j in used:
            used.update(gates[j][1:])
    dirty = 0
    for j, (op, a, b) in enumerate(gates):
        if op or a == b or 26 + j not in used:
            continue
        if not (little[26 + j] & ~little[-1]) or not (values[26 + j] & positive):
            continue
        if any(replacement_output(gates, values, j, replacement) == values[-1]
               for replacement in (values[a], values[b], 0)):
            continue
        dirty |= little[26 + j]
    witnesses = dirty & ~little[-1]
    mask = small[(witnesses & -witnesses).bit_length() - 1] if witnesses else None
    assert fixture == dict(index=index, essential_suppressed=bool(witnesses), raw_mask=mask), index
    accepted += bool(witnesses)
print(json.dumps(dict(scope='Soft diagnostic tag only, no candidate acceptance or lower-bound claim.',
                      seeds=len(seeds), small_inputs=len(small), complete_boundary_with_guards=len(basis),
                      matched=len(fixtures), essential_suppressed=accepted,
                      ordinary140_first=fixtures[0], suppressed262_second=fixtures[1],
                      seeds_sha256=hashlib.sha256(seeds_path.read_bytes()).hexdigest(),
                      fixtures_sha256=hashlib.sha256(fixtures_path.read_bytes()).hexdigest()), indent=2))
