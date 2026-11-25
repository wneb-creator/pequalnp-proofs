import argparse
import itertools
import json
from pathlib import Path
import subprocess
import time

EDGES = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6),
         (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
TARGET = [any((x >> a & 1) and (x >> b & 1) for a, b in EDGES) for x in range(1024)]


class CNF:
    def __init__(self):
        self.n = 0
        self.clauses = []
        self.true = self.var()
        self.add(self.true)

    def var(self):
        self.n += 1
        return self.n

    def add(self, *lits):
        lits = set(lits)
        if any(-x in lits for x in lits):
            return
        self.clauses.append(tuple(sorted(lits, key=abs)))

    def onehot(self, xs):
        self.add(*xs)
        for a, b in itertools.combinations(xs, 2):
            self.add(-a, -b)

    def write(self, path):
        with path.open('w') as f:
            f.write(f'p cnf {self.n} {len(self.clauses)}\n')
            for clause in self.clauses:
                f.write(' '.join(map(str, clause)) + ' 0\n')


def synthesis(rows, size, first, nots):
    c = CNF()
    ops, aa, bb = [], [], []
    for k in range(size):
        op = [c.var() for _ in range(3)]
        a = [c.var() for _ in range(10 + k)]
        b = [c.var() for _ in range(10 + k)]
        c.onehot(op)
        c.onehot(a)
        c.onehot(b)
        # Symmetry for commutative gates; identity gates excluded from this search.
        for i in range(10 + k):
            for j in range(i + 1):
                c.add(op[2], -a[i], -b[j])
        c.add(-op[2], b[0])
        ops.append(op)
        aa.append(a)
        bb.append(b)
    c.add(*(op[2] for op in ops))
    if nots == 1:
        for x, y in itertools.combinations([op[2] for op in ops], 2):
            c.add(-x, -y)
    for k in range(size - 1):
        c.add(*(aa[j][10 + k] for j in range(k + 1, size)),
              *(bb[j][10 + k] for j in range(k + 1, size)))
    if first >= 0:
        possibilities = [(0, 0, 1), (1, 0, 1), (0, 0, 2), (1, 0, 2), (2, 0, 0)]
        op, a, b = possibilities[first]
        c.add(ops[0][op])
        c.add(aa[0][a])
        c.add(bb[0][b])
    for x in rows:
        wire = [c.true if x >> j & 1 else -c.true for j in range(10)]
        for k in range(size):
            av, bv, out = c.var(), c.var(), c.var()
            for i, w in enumerate(wire):
                c.add(-aa[k][i], -av, w)
                c.add(-aa[k][i], av, -w)
                c.add(-bb[k][i], -bv, w)
                c.add(-bb[k][i], bv, -w)
            an, oo, nn = ops[k]
            c.add(-an, -out, av)
            c.add(-an, -out, bv)
            c.add(-an, out, -av, -bv)
            c.add(-oo, out, -av)
            c.add(-oo, out, -bv)
            c.add(-oo, -out, av, bv)
            c.add(-nn, out, av)
            c.add(-nn, -out, -av)
            wire.append(out)
        c.add(wire[-1] if TARGET[x] else -wire[-1])
    return c, ops, aa, bb


def read_model(path):
    values = set()
    for line in path.read_text().splitlines():
        if line.startswith('v '):
            values.update(int(x) for x in line[2:].split() if int(x) > 0)
    return values


def evaluate(gates):
    mismatches = []
    for x in range(1024):
        w = [bool(x >> j & 1) for j in range(10)]
        for op, a, b in gates:
            w.append((w[a] and w[b]) if op == 0 else (w[a] or w[b]) if op == 1 else not w[a])
        if w[-1] != TARGET[x]:
            mismatches.append(x)
    return mismatches


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--solver', required=True)
    p.add_argument('--out', required=True)
    p.add_argument('--seconds', type=int, default=300)
    p.add_argument('--first', type=int, default=-1)
    p.add_argument('--size', type=int, default=19)
    p.add_argument('--nots', type=int, default=1)
    args = p.parse_args()
    out = Path(args.out)
    out.mkdir(exist_ok=True)
    rows = {x for x in range(1024) if not TARGET[x]}
    rows.update((1 << a) | (1 << b) for a, b in EDGES)
    rows.add(1023)
    for iteration in range(50):
        cnf, ops, aa, bb = synthesis(sorted(rows), args.size, args.first, args.nots)
        stem = out / f'iteration-{iteration:02d}'
        cnf.write(stem.with_suffix('.cnf'))
        print(f'iteration={iteration} rows={len(rows)} vars={cnf.n} clauses={len(cnf.clauses)}', flush=True)
        started = time.monotonic()
        with stem.with_suffix('.stdout').open('w') as sout, stem.with_suffix('.stderr').open('w') as serr:
            result = subprocess.run([args.solver, '-t', str(args.seconds),
                                     str(stem.with_suffix('.cnf'))], stdout=sout, stderr=serr)
        print(f'return={result.returncode} seconds={time.monotonic() - started:.3f}', flush=True)
        if result.returncode != 10:
            print('UNSAT restricted search' if result.returncode == 20 else 'solver stopped without a model', flush=True)
            return
        model = read_model(stem.with_suffix('.stdout'))
        gates = [(next(j for j, v in enumerate(op) if v in model),
                  next(j for j, v in enumerate(a) if v in model),
                  next(j for j, v in enumerate(b) if v in model))
                 for op, a, b in zip(ops, aa, bb)]
        mismatches = evaluate(gates)
        stem.with_suffix('.json').write_text(json.dumps({'gates': gates, 'mismatches': mismatches}, indent=2))
        print(f'mismatches={len(mismatches)} gates={gates}', flush=True)
        if not mismatches:
            (out / 'EXACT.json').write_text(json.dumps(gates, indent=2))
            return
        rows.update(mismatches)


if __name__ == '__main__':
    main()
