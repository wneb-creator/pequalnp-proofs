"""Verify each emitted C6-corona CGP circuit against the complete statement.

This verifier retains and checks every printed gate. It independently discovers
pure star witnesses by evaluating all input assignments, without trusting the
search's claimed witness indices or output-ancestor pruning.
"""
import argparse
import itertools
import json
from pathlib import Path


def verify(record):
    p, l, n = 6, 6, 12
    core = [0, 6, 1, 7, 2, 8]
    leaves = [9, 3, 10, 4, 11, 5]
    edges = set()
    for i in range(6):
        for w in [core[(i+1)%6], leaves[i]]:
            a, b = core[i], w
            if a >= p:
                a, b = b, a
            edges.add((a, b))
    assert len(edges) == 12
    assert all(not {(a, b), (a, d), (c, b), (c, d)} <= edges
               for a, c in itertools.combinations(range(p), 2)
               for b, d in itertools.combinations(range(p, n), 2))
    minimum_cover = min(mask.bit_count() for mask in range(1 << n)
                        if all(mask >> a & 1 or mask >> b & 1 for a, b in edges))
    assert minimum_cover == 6
    gates = record['gates']
    output = record['output']
    assert len(gates) == record['gate_count']
    assert 0 <= output < n + len(gates)
    reach = [{i} for i in range(n)]
    ancestors = [set() for _ in range(n)]
    for j, (op, a, b) in enumerate(gates):
        assert op in (0, 1) and 0 <= a < n + j and 0 <= b < n + j
        reach.append(reach[a] | reach[b] if op else set())
        ancestors.append(ancestors[a] | ancestors[b] | {j})
    mixed = [j for j, (op, _, _) in enumerate(gates) if op
             and any(v < p for v in reach[n+j]) and any(v >= p for v in reach[n+j])]
    assert not mixed
    tables = [[] for _ in range(n + len(gates))]
    for mask in range(1 << n):
        values = [(mask >> i) & 1 for i in range(n)]
        for op, a, b in gates:
            values.append(values[a] | values[b] if op else values[a] & values[b])
        expected = int(any(mask >> a & 1 and mask >> b & 1 for a, b in edges))
        assert values[output] == expected, ('wrong truth row', mask)
        for wire, value in enumerate(values):
            tables[wire].append(value)
    witnesses = {}
    covered = set()
    for j, (op, _, _) in enumerate(gates):
        if not op:
            continue
        support = {i for i in range(n) if tables[n+j][1 << i]}
        if len(support) < 2:
            continue
        if any(tables[n+j][mask] != int(any(mask >> i & 1 for i in support))
               for mask in range(1 << n)):
            continue
        centres = []
        for c in range(n):
            served = {(c, v) if c < p else (v, c) for v in support}
            if served <= edges:
                centres.append(c)
                covered.update(served)
        if centres:
            assert len(centres) == 1
            witnesses[j] = {'centre': centres[0], 'support': sorted(support)}
    assert covered == edges, ('missing served edges', sorted(edges - covered))
    assert set(record['witness_gate_indices']) <= set(witnesses)
    claimed_covered = set()
    for j in record['witness_gate_indices']:
        c = witnesses[j]['centre']
        claimed_covered.update((c, v) if c < p else (v, c) for v in witnesses[j]['support'])
    assert claimed_covered == edges
    assert record['and_count'] == sum(op == 0 for op, _, _ in gates)
    assert record['t_count'] == 0 and record['edges_served'] == 12 and record['truth_rows'] == 4096
    unused_witnesses = sorted(set(witnesses) - ancestors[output])
    if record['kind'] == 'control_postoutput_witnesses':
        assert len(unused_witnesses) == 6
        assert output < n + len(gates) - 1
    if record['kind'] == 'control_duplicate_and_shields':
        assert sum(a == b for _, a, b in gates) == 6
    return {'kind': record['kind'], 'gates': len(gates), 'and_count': record['and_count'],
            'truth_rows': 4096, 't_count': 0, 'served_edges': 12,
            'unused_witnesses': unused_witnesses, 'cover_number': minimum_cover,
            'counterexample': len(gates) < len(edges) + minimum_cover - 1}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    records = [json.loads(line) for line in args.output.read_text().splitlines()
               if line.startswith('{')]
    assert records
    print(json.dumps([verify(record) for record in records], indent=2))


if __name__ == '__main__':
    main()
