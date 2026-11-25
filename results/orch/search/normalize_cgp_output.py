"""Normalize logged CGP circuits and independently recheck the complete target function."""
import json
import sys
from pathlib import Path

metadata = json.loads(Path(sys.argv[1]).read_text())
n = metadata['n']
edges = metadata['edges']
tests = metadata['tests']
columns = [sum(1 << j for j, mask in enumerate(tests) if mask >> i & 1) for i in range(n)]

def normalize(gates, output, semantic):
    mapping = list(range(n))
    result = []
    patterns = columns.copy()
    by_pattern = {pattern: i for i, pattern in enumerate(patterns)}
    by_gate = {}
    for op, old_a, old_b in gates:
        a, b = sorted([mapping[old_a], mapping[old_b]])
        pattern = patterns[a] | patterns[b] if op else patterns[a] & patterns[b]
        alias = a if a == b else None
        for child, other in [(a, b), (b, a)]:
            if alias is None and child >= n:
                child_op, left, right = result[child - n]
                if other in (left, right):
                    alias = child if child_op == op else other
        key = (op, a, b)
        if alias is None and key in by_gate:
            alias = by_gate[key]
        if alias is None and semantic and pattern in by_pattern:
            alias = by_pattern[pattern]
        if alias is None:
            alias = n + len(result)
            result.append([op, a, b])
            patterns.append(pattern)
            by_gate[key] = alias
            by_pattern.setdefault(pattern, alias)
        mapping.append(alias)
    output = mapping[output]
    active = set()
    pending = [output]
    while pending:
        wire = pending.pop()
        if wire >= n and wire not in active:
            active.add(wire)
            pending.extend(result[wire - n][1:])
    renumber = {i: i for i in range(n)}
    compact = []
    for j, (op, a, b) in enumerate(result):
        if n + j in active:
            renumber[n + j] = n + len(compact)
            compact.append([op, renumber[a], renumber[b]])
    return compact, renumber[output]

def verify(gates, output):
    for mask in range(1 << n):
        wires = [(mask >> i) & 1 for i in range(n)]
        for j, (op, a, b) in enumerate(gates):
            assert op in (0, 1) and 0 <= a < n + j and 0 <= b < n + j
            wires.append(wires[a] | wires[b] if op else wires[a] & wires[b])
        expected = any((mask >> a) & (mask >> b) & 1 for a, b in edges)
        assert bool(wires[output]) == expected

verified = set()
results = []
for source in sys.argv[3:]:
    for line in Path(source).read_text().splitlines():
        if not line.startswith('{'):
            continue
        record = json.loads(line)
        for semantic in [False, True]:
            gates, output = normalize(record['gates'], record['output'], semantic)
            key = (tuple(map(tuple, gates)), output)
            if key not in verified:
                verify(gates, output)
                verified.add(key)
            results.append({'source': Path(source).name, 'source_kind': record['kind'],
                            'mode': '58-vector aliasing' if semantic else 'structural identities',
                            'original_size': len(record['gates']), 'normalized_size': len(gates),
                            'and_gates': sum(op == 0 for op, a, b in gates),
                            'or_gates': sum(op == 1 for op, a, b in gates),
                            'inputs_verified': 1 << n, 'wrong_inputs': 0,
                            'counterexample_candidate': len(gates) <= 26,
                            'gates': gates, 'output': output})
Path(sys.argv[2]).write_text(json.dumps(results, indent=2) + '\n')
print(json.dumps({'records': len(results), 'distinct_verified_circuits': len(verified),
                  'smallest_normalized': min(row['normalized_size'] for row in results),
                  'counterexample_candidates': sum(row['counterexample_candidate'] for row in results)}))
