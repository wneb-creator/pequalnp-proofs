"""Bounded independent data/semantics audit of a generated Lean circuit witness.

Usage: python3 -B audit_lean_witness.py SOURCE JSON GENERATOR STRATEGY OUTPUT
The Lean theorem itself must separately have a successful kernel build log.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

source, original, generator = map(Path, sys.argv[1:4])
strategy, output_name = sys.argv[4:6]
s, data = source.read_text(), json.loads(original.read_text())
spec = importlib.util.spec_from_file_location('reviewed_witness_generator', generator)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
assert module.render(data, strategy) == s
graph_source = s.split('abbrev witnessGraph', 1)[1].split('def witnessCircuit', 1)[0]
graph_match = re.search(r'edgeGraph (\d+) \[(.*)\]', graph_source)
n = int(graph_match.group(1))
assert 0 < n <= 16, 'exhaustive review intentionally bounded to sixteen inputs'
edges = [list(map(int, pair)) for pair in re.findall(r'\((\d+), (\d+)\)', graph_match.group(2))]
circuit_source = s.split('def witnessCircuit', 1)[1].split('def witnessExpr', 1)[0]
gates = [[op, int(a), int(b)] for op, a, b in
         re.findall(r'⟨\.(and|or), \[(\d+), (\d+)\]⟩', circuit_source)]
out = int(re.search(r'\], (\d+)⟩', circuit_source).group(1))
assert n == data['n'] and edges == data['edges'] and gates == data['gates']
assert len(gates) == data['size'] and out == data.get('output', n + len(gates) - 1)
assert 0 <= out < n + len(gates)
for j, (_, a, b) in enumerate(gates):
    assert 0 <= a < n + j and 0 <= b < n + j
assert not re.search(r'\bsorry\b|\baxiom\b|\bnative_decide\b|\bbv_decide\b|_root_|"|@\[', s)
assert re.findall(r'^import (.+)$', s, re.M) == ['PEqualNP.Defs']
assert set(re.findall(r'set_option (\S+)', s)) <= {'maxRecDepth', 'maxHeartbeats'}
minimum_cover = n
for x in range(1 << n):
    wires = [bool(x >> i & 1) for i in range(n)]
    for op, a, b in gates:
        wires.append(wires[a] and wires[b] if op == 'and' else wires[a] or wires[b])
    assert wires[out] == any(x >> a & 1 and x >> b & 1 for a, b in edges)
    if all(x >> a & 1 or x >> b & 1 for a, b in edges):
        minimum_cover = min(minimum_cover, x.bit_count())
adjacency = [set() for _ in range(n)]
for a, b in edges:
    assert 0 <= a < n and 0 <= b < n and a != b
    adjacency[a].add(b)
    adjacency[b].add(a)
assert len({tuple(sorted(e)) for e in edges}) == len(edges)
assert all(len(adjacency[a] & adjacency[b]) <= 1 for a in range(n) for b in range(a))
color = [None] * n
for root in range(n):
    if color[root] is not None:
        continue
    color[root] = 0
    stack = [root]
    while stack:
        a = stack.pop()
        for b in adjacency[a]:
            if color[b] is None:
                color[b] = 1 - color[a]
                stack.append(b)
            assert color[b] != color[a]
result = dict(verdict='PASS: exact upper witness; no minimality/refutation claim',
              source=source.name, strategy=strategy,
              source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
              json_sha256=hashlib.sha256(original.read_bytes()).hexdigest(),
              generator_sha256=hashlib.sha256(generator.read_bytes()).hexdigest(),
              source_bytes=len(source.read_bytes()), source_lines=len(s.splitlines()),
              n=n, edges=len(edges), gates=len(gates), output=out,
              all_truth_rows=1 << n, exact_minimum_cover=minimum_cover,
              standard_upper=len(edges) + minimum_cover - 1,
              refuting_size_at_most=len(edges) + minimum_cover - 2,
              exact_generator_match=True, bipartite=True, no_four_cycle=True)
Path(output_name).write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
