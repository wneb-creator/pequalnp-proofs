import argparse
import json
from itertools import combinations
from pathlib import Path


class CNF:
    def __init__(self):
        self.n = 1
        self.clauses = [[1]]

    def var(self):
        self.n += 1
        return self.n

    def add(self, *xs):
        if 1 in xs:
            return
        ys = set(xs) - {-1}
        if any(-x in ys for x in ys):
            return
        self.clauses.append(sorted(ys, key=lambda x: (abs(x), x)))

    def and_(self, a, b):
        c = self.var()
        self.add(-a, -b, c)
        self.add(a, -c)
        self.add(b, -c)
        return c

    def or_(self, a, b):
        c = self.var()
        self.add(a, b, -c)
        self.add(-a, c)
        self.add(-b, c)
        return c

    def exactly_one(self, xs):
        self.add(*xs)
        for a, b in combinations(xs, 2):
            self.add(-a, -b)

    def equivalent_if(self, selector, a, b):
        self.add(-selector, -a, b)
        self.add(-selector, a, -b)

    def gate(self, op, a, b, z):
        self.add(-op, a, b, -z)
        self.add(-op, -a, z)
        self.add(-op, -b, z)
        self.add(op, -a, -b, z)
        self.add(op, a, -z)
        self.add(op, b, -z)

    def at_least(self, xs, k):
        if k <= 0:
            return
        prev = [1] + [-1] * k
        for x in xs:
            cur = [1]
            for j in range(1, k + 1):
                cur.append(self.or_(prev[j], self.and_(x, prev[j - 1])))
            prev = cur
        self.add(prev[k])


def generate(k, minimum, core, support, stem, violation=True, omitted=None):
    n = 14
    edges = [(a, 7 + b) for a in range(7) for b in range(7)
             if (a - b) % 7 in (0, 1, 3)]
    adj = [set() for _ in range(n)]
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    independent = []
    for m in range(1 << n):
        if any(m >> a & 1 and m >> b & 1 for a, b in edges):
            continue
        if all(m >> a & 1 or any(m >> b & 1 for b in adj[a]) for a in range(n)):
            independent.append(m)
    rows = independent + [(1 << a) | (1 << b) for a, b in edges] + [1 << a for a in range(n)]
    c = CNF()
    ops = [c.var() for _ in range(k)]
    selectors = [[[c.var() for _ in range(n + g)] for _ in range(2)] for g in range(k)]
    vals = [[1 if m >> i & 1 else -1 for m in rows] for i in range(n)]
    vals += [[c.var() for _ in rows] for _ in range(k)]
    single = [[1 if a == i else -1 for a in range(n)] for i in range(n)]
    single += [[c.var() for _ in range(n)] for _ in range(k)]
    pair = [[-1 for _ in edges] for _ in range(n)]
    pair += [[c.var() for _ in edges] for _ in range(k)]
    ports = []
    for g in range(k):
        for b in range(2):
            c.exactly_one(selectors[g][b])
            if support is not None:
                for a in range(n):
                    if a not in support:
                        c.add(-selectors[g][b][a])
        for a in range(n + g):
            for b in range(a):
                c.add(-selectors[g][0][a], -selectors[g][1][b])
        pv = [[c.var() for _ in rows] for _ in range(2)]
        ps = [[c.var() for _ in range(n)] for _ in range(2)]
        pp = [[c.var() for _ in edges] for _ in range(2)]
        ports.append(pv)
        for b in range(2):
            for a, sel in enumerate(selectors[g][b]):
                for x, y in zip(pv[b], vals[a]):
                    c.equivalent_if(sel, x, y)
                for x, y in zip(ps[b], single[a]):
                    c.equivalent_if(sel, x, y)
                for x, y in zip(pp[b], pair[a]):
                    c.equivalent_if(sel, x, y)
        for r in range(len(rows)):
            c.gate(ops[g], pv[0][r], pv[1][r], vals[n + g][r])
        for a in range(n):
            z = single[n + g][a]
            c.add(ops[g], -z)
            c.add(-ops[g], ps[0][a], ps[1][a], -z)
            c.add(-ops[g], -ps[0][a], z)
            c.add(-ops[g], -ps[1][a], z)
        for e, (a, b) in enumerate(edges):
            cross = c.or_(c.and_(ps[0][a], ps[1][b]), c.and_(ps[0][b], ps[1][a]))
            z = pair[n + g][e]
            c.equivalent_if(-ops[g], z, cross)
            c.add(-ops[g], pp[0][e], pp[1][e], -z)
            c.add(-ops[g], -pp[0][e], z)
            c.add(-ops[g], -pp[1][e], z)
    for g in range(k - 1):
        c.add(*(selectors[h][b][n + g] for h in range(g + 1, k) for b in range(2)))
    if support is not None:
        for a in support:
            c.add(*(selectors[g][b][a] for g in range(k) for b in range(2)))
        if len(support) == k:
            # There are 2k arcs and 2k-1 used nonroot wires: exactly one wire is read twice.
            used_wires = support + list(range(n, n + k - 1))
            repeated = [c.var() for _ in used_wires]
            c.exactly_one(repeated)
            for w, repeat in zip(used_wires, repeated):
                readers = [selectors[g][b][w] for g in range(k) for b in range(2) if w < n + g]
                for a, b in combinations(readers, 2):
                    c.add(-a, -b, repeat)
                for a, b, z in combinations(readers, 3):
                    c.add(-a, -b, -z)
    c.add(-ops[-1])
    for r in range(len(independent)):
        c.add(-vals[-1][r])
    accepts = vals[-1][len(independent):len(independent) + len(edges)]
    c.at_least(accepts, minimum)
    if omitted is not None:
        c.add(-accepts[edges.index(tuple(omitted))])
    # Vertex cover of the residual graph witnesses the strict target violation.
    cover = [c.var() for _ in range(n)]
    for x, (a, b) in zip(accepts, edges):
        c.add(x, cover[a], cover[b])
    if violation:
        c.at_least(accepts + [-x for x in cover], k + 9)
    if core:
        if support is None:
            # By edge transitivity, choose the first graph edge as a repeated accepted edge.
            c.add(accepts[0])
            c.add(-pair[-1][0])
        else:
            c.add(*(c.and_(x, -r) for x, r in zip(accepts, pair[-1])))
        # At least one root operand is not below the graph function.
        c.add(*(ports[-1][b][r] for b in range(2) for r in range(len(independent))))
    Path(stem + '.cnf').write_text('p cnf %d %d\n' % (c.n, len(c.clauses)) +
        ''.join(' '.join(map(str, xs)) + ' 0\n' for xs in c.clauses))
    data = dict(n=n, k=k, minimum=minimum, core=core, support=support, violation=violation, omitted=omitted,
                edges=edges, independent=independent, rows=rows,
                ops=ops, selectors=selectors, vals=vals, pair=pair, cover=cover,
                variables=c.n, clauses=len(c.clauses))
    Path(stem + '.json').write_text(json.dumps(data))
    print(json.dumps({x: data[x] for x in ['k', 'minimum', 'core', 'support', 'variables', 'clauses']}))


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--gates', type=int, required=True)
    p.add_argument('--minimum', type=int, default=0)
    p.add_argument('--no-core', action='store_true')
    p.add_argument('--support')
    p.add_argument('--no-violation', action='store_true')
    p.add_argument('--omit-edge')
    p.add_argument('--stem', required=True)
    a = p.parse_args()
    support = None if a.support is None else [int(x) for x in a.support.split(',')]
    omitted = None if a.omit_edge is None else [int(x) for x in a.omit_edge.split(',')]
    generate(a.gates, a.minimum, not a.no_core, support, a.stem, not a.no_violation, omitted)
