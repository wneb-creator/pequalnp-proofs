#!/usr/bin/env python3
"""Analyze quadratic minterms and capped read-1 witnesses of a candidate."""
import itertools
import json
import pathlib
import sys

problem = json.loads(pathlib.Path(sys.argv[1]).read_text())
circuit = json.loads(pathlib.Path(sys.argv[2]).read_text())


def evaluate(x):
    wires = [bool(x >> i & 1) for i in range(26)]
    for gate in circuit['gates']:
        a, b = wires[gate['a']], wires[gate['b']]
        wires.append(a and b if gate['op'] == 'and' else a or b)
    return wires[circuit['output']]


old_edges = {tuple(sorted(edge)) for edge in problem['edges']}
extra = [(a, b) for a, b in itertools.combinations(range(26), 2)
         if evaluate((1 << a) | (1 << b)) and (a, b) not in old_edges]
assert all(a < 13 <= b for a, b in extra)
edges = problem['edges'] + extra
masks = [0] * 13
for a, b in edges:
    masks[b-13] |= 1 << a
maxfalse = []
for points in range(8192):
    lines = sum(1 << ell for ell, mask in enumerate(masks) if not points & mask)
    covered = 0
    for ell, mask in enumerate(masks):
        if lines >> ell & 1:
            covered |= mask
    if points == 8191 ^ covered:
        maxfalse.append(points | (lines << 13))

read1_failures = []
for a, b in edges:
    vectors = [{(1, 0)} if i == a else {(0, 1)} if i == b else set()
               for i in range(26)]
    for gate in circuit['gates']:
        left, right = vectors[gate['a']], vectors[gate['b']]
        vectors.append(left | right if gate['op'] == 'or' else
                       {(min(2, u+w), min(2, v+x))
                        for u, v in left for w, x in right})
    if (1, 1) not in vectors[circuit['output']]:
        read1_failures.append([a, b])

used, stack = set(), [circuit['output']]
while stack:
    wire = stack.pop()
    if wire in used:
        continue
    used.add(wire)
    if wire >= 26:
        gate = circuit['gates'][wire-26]
        stack.extend([gate['a'], gate['b']])
contains_and, nested = [False] * 26, []
for i, gate in enumerate(circuit['gates']):
    ancestor = contains_and[gate['a']] or contains_and[gate['b']]
    if gate['op'] == 'and' and ancestor:
        nested.append(i)
    contains_and.append(ancestor or gate['op'] == 'and')
result = dict(extra_quadratic_minterms=extra,
              augmented_graph_maximal_false_count=len(maxfalse),
              augmented_graph_false_positives=[x for x in maxfalse if evaluate(x)],
              read1_failed_edges=read1_failures,
              active_gates=sum(wire >= 26 for wire in used),
              nested_and_gate_indices=nested,
              candidate_steps=circuit.get('steps'))
print(json.dumps(result, indent=2))
