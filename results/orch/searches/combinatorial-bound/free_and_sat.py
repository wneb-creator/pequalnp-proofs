import argparse
import itertools
import json
from pathlib import Path


class CNF:
    def __init__(self):
        self.n = 0
        self.cs = []
        self.ops = []
        self.one = self.var()
        self.add(self.one)

    def var(self):
        self.n += 1
        return self.n

    def add(self, *lits):
        self.cs.append(list(lits))

    def land(self, terms):
        v = self.var()
        self.ops.append((v, 'and', list(terms)))
        for t in terms:
            self.add(-v, t)
        self.add(v, *[-t for t in terms])
        return v

    def lor(self, terms):
        return -self.land([-t for t in terms])


def cycle_graph(n):
    return [(i, (i + 1) % n) for i in range(n)]


def maximal_independent(n, edges):
    independent = [m for m in range(1 << n)
                   if all(not ((m >> u) & 1 and (m >> v) & 1) for u, v in edges)]
    pool = set(independent)
    return [m for m in independent if all(m | (1 << v) not in pool
            for v in range(n) if not m >> v & 1)]


def encode(n, edges, k):
    cnf = CNF()
    selected = [[[cnf.var() for _ in range(n + i)] for _ in range(2)]
                for i in range(k)]
    final = [cnf.var() for _ in range(n + k)]
    for gate in selected:
        for side in gate:
            cnf.add(*side)
    cnf.add(*final)
    # Both sides of every OR are unordered. Binary numerical masks compare
    # lexicographically; only the highest differing bit controls order.
    for a, b in selected:
        same = cnf.one
        for x, y in reversed(list(zip(a, b))):
            cnf.add(-same, -x, y)
            eq = cnf.var()
            cnf.ops.append((eq, 'eq', [x, y]))
            cnf.add(-eq, -x, y)
            cnf.add(-eq, x, -y)
            cnf.add(eq, x, y)
            cnf.add(eq, -x, -y)
            same = cnf.land([same, eq])
    rows = [(1 << u | 1 << v, True) for u, v in edges]
    rows += [(m, False) for m in maximal_independent(n, edges)]
    for mask, expected in rows:
        wires = [cnf.one if mask >> v & 1 else -cnf.one for v in range(n)]
        for gate in selected:
            sides = []
            for side in gate:
                terms = [cnf.lor([-s, value]) for s, value in zip(side, wires)]
                sides.append(cnf.land(terms))
            wires.append(cnf.lor(sides))
        output = cnf.land([cnf.lor([-s, value]) for s, value in zip(final, wires)])
        cnf.add(output if expected else -output)
    return cnf, {'n': n, 'edges': edges, 'or_count': k, 'selected': selected,
                 'final': final, 'rows': rows}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--n', type=int, required=True)
    parser.add_argument('--or-count', type=int, required=True)
    parser.add_argument('--out', required=True)
    args = parser.parse_args()
    cnf, meta = encode(args.n, cycle_graph(args.n), args.or_count)
    path = Path(args.out)
    with path.open('w') as f:
        f.write(f'p cnf {cnf.n} {len(cnf.cs)}\n')
        for cs in cnf.cs:
            f.write(' '.join(map(str, cs)) + ' 0\n')
    path.with_suffix('.json').write_text(json.dumps(meta, indent=2) + '\n')
    print(json.dumps({'vars': cnf.n, 'clauses': len(cnf.cs), 'rows': len(meta['rows'])}))


if __name__ == '__main__':
    main()
