#!/usr/bin/env python3
"""Independently check saved SAT witnesses; this does not verify UNSAT claims."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def check_graph(graph):
    n, edges = graph['n'], graph['edges']
    assert len({tuple(sorted(e)) for e in edges}) == len(edges)
    assert all(0 <= a < n and 0 <= b < n and a != b for a, b in edges)
    adjacency = [set() for _ in range(n)]
    for a, b in edges:
        adjacency[a].add(b)
        adjacency[b].add(a)
    colors = {}
    for root in range(n):
        if root in colors:
            continue
        colors[root] = 0
        stack = [root]
        while stack:
            a = stack.pop()
            for b in adjacency[a]:
                if b not in colors:
                    colors[b] = 1 - colors[a]
                    stack.append(b)
                assert colors[b] != colors[a]
    c4_free = all(len(adjacency[a] & adjacency[b]) <= 1
                  for a in range(n) for b in range(a + 1, n))
    return c4_free

def verify(graph, gates):
    n, edges = graph['n'], graph['edges']
    for i, gate in enumerate(gates):
        assert gate['op'] in ('and', 'or')
        assert 0 <= gate['left'] < n + i
        assert 0 <= gate['right'] < n + i
    for mask in range(1 << n):
        wires = [bool(mask & (1 << v)) for v in range(n)]
        for gate in gates:
            a, b = wires[gate['left']], wires[gate['right']]
            wires.append(a and b if gate['op'] == 'and' else a or b)
        expected = any(mask & (1 << a) and mask & (1 << b) for a, b in edges)
        assert wires[-1] == bool(expected), (graph['name'], mask)
    return 1 << n

def main():
    evidence = json.loads((ROOT / 'evidence.json').read_text())
    count = 0
    for result in evidence['results']:
        if result['status'] != 'SAT':
            continue
        graph = json.loads((ROOT / 'graphs' / (result['graph'] + '.json')).read_text())
        c4_free = check_graph(graph)
        assert c4_free == (result['graph'] != 'C4')
        rows = verify(graph, result['gates'])
        assert rows == result['truth_rows_checked']
        assert len(result['gates']) == result['k']
        count += 1
        print(f"{result['graph']}: {len(result['gates'])} gates, {rows} assignments checked")
    print(f'{count} SAT witnesses checked; UNSAT claims were not independently certified.')

if __name__ == '__main__':
    main()
