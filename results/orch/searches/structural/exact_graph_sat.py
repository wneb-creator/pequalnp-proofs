import argparse
import json
from itertools import combinations
from pathlib import Path

from fano_sat import CNF


def canonical_star_circuit(n, edges, left):
    gates = []
    stars = []
    def add(op, a, b):
        gates.append((op, a, b))
        return n + len(gates) - 1
    for a in left:
        neighbors = sorted(b if x == a else x for x, b in edges if x == a or b == a)
        assert neighbors
        joined = neighbors[0]
        for b in neighbors[1:]:
            joined = add(1, joined, b)
        stars.append(add(0, a, joined))
    joined = stars[0]
    for b in stars[1:]:
        joined = add(1, joined, b)
    assert joined == n + len(gates) - 1
    mapping = {i: i for i in range(n)}
    remaining = set(range(len(gates)))
    ordered = []
    while remaining:
        ready = []
        for g in remaining:
            op, a, b = gates[g]
            if a in mapping and b in mapping:
                u, v = sorted((mapping[a], mapping[b]))
                ready.append((v, u, op, g))
        assert ready
        v, u, op, g = min(ready)
        mapping[n + g] = n + len(ordered)
        ordered.append((op, u, v))
        remaining.remove(g)
    assert mapping[joined] == n + len(ordered) - 1
    return ordered


def generate(n, edges, k, stem, and_count=None, pins=None):
    edges = sorted({tuple(sorted(e)) for e in edges})
    adjacency = [set() for _ in range(n)]
    for a, b in edges:
        adjacency[a].add(b)
        adjacency[b].add(a)
    mis = []
    for mask in range(1 << n):
        if any(mask >> a & 1 and mask >> b & 1 for a, b in edges):
            continue
        if all(mask >> a & 1 or any(mask >> b & 1 for b in adjacency[a])
               for a in range(n)):
            mis.append(mask)
    rows = mis + [(1 << a) | (1 << b) for a, b in edges]
    c = CNF()
    ops = [c.var() for _ in range(k)]
    selectors = [[[c.var() for _ in range(n + g)] for _ in range(2)] for g in range(k)]
    vals = [[1 if mask >> i & 1 else -1 for mask in rows] for i in range(n)]
    vals += [[c.var() for _ in rows] for _ in range(k)]
    for g in range(k):
        ports = [[c.var() for _ in rows] for _ in range(2)]
        for b in range(2):
            c.exactly_one(selectors[g][b])
            for w, select in enumerate(selectors[g][b]):
                for r in range(len(rows)):
                    c.equivalent_if(select, ports[b][r], vals[w][r])
        for a in range(n + g):
            for b in range(a):
                c.add(-selectors[g][0][a], -selectors[g][1][b])
        for r in range(len(rows)):
            c.gate(ops[g], ports[0][r], ports[1][r], vals[n + g][r])
    for g in range(k - 1):
        c.add(*(selectors[h][b][n + g] for h in range(g + 1, k) for b in range(2)))
    # Every graph vertex here is nonisolated, hence every input must be used.
    assert all(adjacency)
    for w in range(n):
        c.add(*(selectors[g][b][w] for g in range(k) for b in range(2)))
    # Greedy topological ordering by (max operand, min operand, operation).
    for g in range(k - 1):
        for b in range(n + g):
            for smaller_b in range(b):
                c.add(-selectors[g][1][b], -selectors[g + 1][1][smaller_b])
            for a in range(b + 1):
                for smaller_a in range(a):
                    c.add(-selectors[g][1][b], -selectors[g + 1][1][b],
                          -selectors[g][0][a], -selectors[g + 1][0][smaller_a])
                c.add(-selectors[g][1][b], -selectors[g + 1][1][b],
                      -selectors[g][0][a], -selectors[g + 1][0][a], -ops[g], ops[g + 1])
    for r in range(len(rows)):
        c.add(-vals[-1][r] if r < len(mis) else vals[-1][r])
    if and_count is not None:
        c.at_least([-op for op in ops], and_count)
        c.at_least(ops, k - and_count)
    budget = k - n + 1
    assert budget >= 0
    extra = []
    for w in range(n + k - 1):
        readers = [selectors[g][b][w] for g in range(k) for b in range(2) if w < n + g]
        thresholds = c.lower_thresholds(readers, budget + 2)
        c.add(-thresholds[budget + 2])
        extra.extend(thresholds[2:budget + 2])
    threshold = c.lower_thresholds(extra, budget + 1)
    c.add(-threshold[budget + 1])
    if pins is not None:
        assert len(pins) == k
        for g, (op, a, b) in enumerate(pins):
            c.add(ops[g] if op else -ops[g])
            c.add(selectors[g][0][a])
            c.add(selectors[g][1][b])
    metadata = dict(n=n, k=k, edges=edges, mis=mis, rows=rows, ops=ops,
                    selectors=selectors, vals=vals, and_count=and_count,
                    budget=budget, pins=pins, variables=c.n, clauses=len(c.clauses))
    Path(stem + '.json').write_text(json.dumps(metadata))
    Path(stem + '.cnf').write_text('p cnf %d %d\n' % (c.n, len(c.clauses)) +
        ''.join(' '.join(map(str, clause)) + ' 0\n' for clause in c.clauses))
    print(json.dumps({key: metadata[key] for key in ['n', 'k', 'and_count', 'variables', 'clauses']}))


def decode(stem):
    d = json.loads(Path(stem + '.json').read_text())
    solution = Path(stem + '.sol').read_text().splitlines()
    assert any(line == 's SATISFIABLE' for line in solution)
    assignment = {abs(int(x)): int(x) > 0 for line in solution if line.startswith('v ')
                  for x in line[2:].split() if int(x)}
    def value(lit):
        return assignment[abs(lit)] == (lit > 0)
    count = 0
    for line in Path(stem + '.cnf').read_text().splitlines():
        if not line or line[0] in 'cp':
            continue
        clause = [int(x) for x in line.split()[:-1]]
        assert any(value(x) for x in clause), clause
        count += 1
    assert count == d['clauses']
    gates = []
    for op, selectors in zip(d['ops'], d['selectors']):
        ports = [[w for w, select in enumerate(port) if value(select)] for port in selectors]
        assert all(len(p) == 1 for p in ports)
        gates.append([int(value(op)), ports[0][0], ports[1][0]])
    for mask in range(1 << d['n']):
        wires = [bool(mask >> i & 1) for i in range(d['n'])]
        for op, a, b in gates:
            wires.append(wires[a] or wires[b] if op else wires[a] and wires[b])
        wanted = any(mask >> a & 1 and mask >> b & 1 for a, b in d['edges'])
        assert wires[-1] == bool(wanted), mask
    reached = {d['n'] + d['k'] - 1}
    for g in reversed(range(d['k'])):
        if d['n'] + g in reached:
            reached.update(gates[g][1:])
    assert reached == set(range(d['n'] + d['k']))
    and_count = sum(op == 0 for op, _, _ in gates)
    assert d['and_count'] is None or and_count == d['and_count']
    result = dict(status='SAT independently verified', gates=gates, edges=d['edges'],
                  assignments=1 << d['n'], clauses=count, and_count=and_count,
                  or_count=d['k'] - and_count)
    Path(stem + '-decoded.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result))


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--gates', type=int)
    p.add_argument('--and-count', type=int)
    p.add_argument('--stem', required=True)
    p.add_argument('--decode', action='store_true')
    p.add_argument('--control', action='store_true')
    p.add_argument('--graph', choices=['theta', 'fano'], default='theta')
    a = p.parse_args()
    if a.decode:
        decode(a.stem)
    else:
        n = 8 if a.graph == 'theta' else 14
        edges = ([(0, 2), (2, 3), (3, 1), (0, 4), (4, 5),
                  (5, 1), (0, 6), (6, 7), (7, 1)] if a.graph == 'theta' else
                 [(u, 7 + v) for u in range(7) for v in range(7)
                  if (u - v) % 7 in (0, 1, 3)])
        pins = None
        if a.control and a.graph == 'theta':
            pins = [(1, 1, 2), (1, 1, 4), (1, 2, 4), (1, 1, 6),
                    (0, 3, 8), (0, 5, 9), (1, 6, 10), (0, 7, 11),
                    (1, 12, 13), (0, 0, 14), (1, 15, 16), (1, 17, 18)]
        elif a.control:
            pins = canonical_star_circuit(n, edges, range(7))
        generate(n, edges, a.gates, a.stem, a.and_count, pins)
