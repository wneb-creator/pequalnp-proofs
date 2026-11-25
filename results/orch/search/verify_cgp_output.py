"""Independently verify every emitted CGP circuit on the complete Fano truth table."""
import json
import sys
from itertools import combinations
from pathlib import Path

metadata = json.loads(Path(sys.argv[1]).read_text())
records = [json.loads(line) for line in Path(sys.argv[2]).read_text().splitlines() if line.startswith('{')]
n = metadata['n']
edges = [tuple(edge) for edge in metadata['edges']]
assert n == 14 and len(edges) == len(set(edges)) == 21
assert all(0 <= p < 7 <= line < 14 for p, line in edges)
assert all(sum(line == target for point, line in edges) == 3 for target in range(7, 14))
assert all(sum((p, line) in edges and (q, line) in edges for line in range(7, 14)) == 1
           for p, q in combinations(range(7), 2))

def expected(mask):
    return any((mask >> a) & (mask >> b) & 1 for a, b in edges)

positive_tests = [(j, mask) for j, mask in enumerate(metadata['tests']) if expected(mask)]
negative_tests = [mask for mask in metadata['tests'] if not expected(mask)]
verified = []
for record in records:
    gates = record['gates']
    output = record['output']
    assert len(gates) == record['active_gates'] and 0 <= output < n + len(gates)
    for j, (op, a, b) in enumerate(gates):
        assert op in (0, 1) and 0 <= a < n + j and 0 <= b < n + j
    or_count = sum(op for op, a, b in gates)
    if 'or_gates' in record:
        assert record['or_gates'] == or_count
        assert record['and_gates'] == len(gates) - or_count

    def evaluate(mask):
        wires = [(mask >> i) & 1 for i in range(n)]
        for op, a, b in gates:
            wires.append(wires[a] | wires[b] if op else wires[a] & wires[b])
        return wires

    wrong = [mask for mask in range(1 << n) if bool(evaluate(mask)[output]) != expected(mask)]
    assert not wrong
    unread_mask = 0
    unread_edges = []
    for index, mask in positive_tests:
        p, line = [i for i in range(n) if mask >> i & 1]
        states = [{1} if i == p else {2} if i == line else set() for i in range(n)]
        for op, a, b in gates:
            states.append(states[a] | states[b] if op else
                          {left | right for left in states[a] for right in states[b] if not left & right})
        if not states[output]:
            unread_mask |= 1 << index
            unread_edges.append([p, line])
    if 'unread_mask' in record:
        assert unread_mask == record['unread_mask']
    dirty = [j for j, (op, a, b) in enumerate(gates)
             if op == 0 and any(evaluate(mask)[n + j] for mask in negative_tests)]
    verified.append({'kind': record['kind'], 'active_gates': len(gates), 'and_gates': len(gates) - or_count,
                     'or_gates': or_count, 'inputs_verified': 1 << n, 'wrong_inputs': 0,
                     'unread_edges': unread_edges, 'dirty_AND_gates': dirty,
                     'counterexample_candidate': len(gates) <= 26})
print(json.dumps(verified, indent=2))
