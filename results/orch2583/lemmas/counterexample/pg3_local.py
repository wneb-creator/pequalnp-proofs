from itertools import product, combinations
from pathlib import Path
import argparse
import json
import subprocess
import time

N = 13
ROOT = Path('/tmp/oec/pequalnp-pilot-110/counterexample2583')
SOLVER = '/tmp/oec/pequalnp-pilot-110/sat_strategy/cadical/build/cadical'


def plane():
    vectors = [v for v in product(range(3), repeat=3)
               if any(v) and next(x for x in v if x) == 1]
    edges = [(i, N+j) for i, a in enumerate(vectors)
             for j, b in enumerate(vectors)
             if sum(x*y for x, y in zip(a, b)) % 3 == 0]
    assert len(vectors) == N and len(edges) == 52
    for j in range(N):
        assert sum(b == N+j for _, b in edges) == 4
    for a, b in combinations(range(N), 2):
        assert sum((a, N+j) in edges and (b, N+j) in edges
                   for j in range(N)) == 1
    return vectors, edges


VECTORS, EDGES = plane()


def target(row):
    return any(row >> a & 1 and row >> b & 1 for a, b in EDGES)


def boundary():
    positive = [(1 << a) | (1 << b) for a, b in EDGES]
    negative = []
    for a in range(1 << N):
        b = sum(1 << (N+j) for j in range(N)
                if not any(a >> i & 1 for i, l in EDGES if l == N+j))
        row = a | b
        if all(target(row | (1 << i)) for i in range(2*N)
               if not row >> i & 1):
            negative.append(row)
    assert len(negative) == 704
    assert not any(target(row) for row in negative)
    return positive + negative


ROWS = boundary()


def baseline(order=range(N)):
    gates, stars = [], []
    for j in order:
        points = [a for a, b in EDGES if b == N+j]
        wire = points[0]
        for p in points[1:]:
            gates.append(('or', wire, p))
            wire = 2*N + len(gates)-1
        gates.append(('and', wire, N+j))
        stars.append(2*N + len(gates)-1)
    wire = stars[0]
    for star in stars[1:]:
        gates.append(('or', wire, star))
        wire = 2*N+len(gates)-1
    assert len(gates) == 64
    return gates


def evaluate(gates, row):
    values = [bool(row >> i & 1) for i in range(2*N)]
    for op, a, b in gates:
        values.append(values[a] and values[b] if op == 'and'
                      else values[a] or values[b])
    return values[-1]


FULL = baseline()
assert all(evaluate(FULL, row) == target(row) for row in ROWS)


def delete_one():
    deleted = 50
    replace_wire = 2*N+49
    def renumber(w):
        if w == 2*N+deleted:
            return replace_wire
        return w-1 if w > 2*N+deleted else w
    result = [(op, renumber(a), renumber(b)) for j, (op, a, b) in enumerate(FULL)
              if j != deleted]
    errors = [row for row in ROWS if evaluate(result, row) != target(row)]
    assert len(result) == 63 and len(errors) == 1
    return result


BASE = delete_one()


def neg(a):
    return not a if type(a) is bool else -a


class CNF:
    def __init__(self):
        self.count = 0
        self.clauses = []

    def var(self):
        self.count += 1
        return self.count

    def add(self, *xs):
        if any(x is True for x in xs):
            return
        values = set(x for x in xs if x is not False)
        if any(-x in values for x in values):
            return
        self.clauses.append(tuple(sorted(values, key=lambda x: (abs(x), x))))

    def exactly_one(self, xs):
        self.add(*xs)
        for a, b in combinations(xs, 2):
            self.add(-a, -b)

    def gate(self, z, op, a, b, guard=False):
        if op == 'and':
            self.add(guard, -z, a)
            self.add(guard, -z, b)
            self.add(guard, z, neg(a), neg(b))
        else:
            self.add(guard, z, neg(a))
            self.add(guard, z, neg(b))
            self.add(guard, -z, a, b)

    def write(self, path):
        with path.open('w') as out:
            out.write(f'p cnf {self.count} {len(self.clauses)}\n')
            for clause in self.clauses:
                out.write(' '.join(map(str, clause)) + ' 0\n')


def encoding(window):
    cnf, selectors = CNF(), {}
    for j in window:
        sources = list(range(2*N+j))
        operation = cnf.var()
        left = [cnf.var() for _ in sources]
        right = [cnf.var() for _ in sources]
        cnf.exactly_one(left)
        cnf.exactly_one(right)
        selectors[j] = (sources, operation, left, right)
        for ia, a in enumerate(left):
            for ib, b in enumerate(right):
                if ia > ib:
                    cnf.add(-a, -b)
    for row in ROWS:
        wires = [bool(row >> i & 1) for i in range(2*N)]
        for j, (op, a, b) in enumerate(BASE):
            if j in selectors:
                sources, operation, left, right = selectors[j]
                z, va, vb = cnf.var(), cnf.var(), cnf.var()
                for sels, value in ((left, va), (right, vb)):
                    for source, sel in zip(sources, sels):
                        cnf.add(-sel, -value, wires[source])
                        cnf.add(-sel, value, neg(wires[source]))
                cnf.gate(z, 'and', va, vb, -operation)
                cnf.gate(z, 'or', va, vb, operation)
            elif type(wires[a]) is bool and type(wires[b]) is bool:
                z = wires[a] and wires[b] if op == 'and' else wires[a] or wires[b]
            else:
                z = cnf.var()
                cnf.gate(z, op, wires[a], wires[b])
            wires.append(z)
        cnf.add(wires[-1] if target(row) else neg(wires[-1]))
    return cnf, selectors


def solve(window, limit):
    name = 'pg3-window-' + '-'.join(map(str, window))
    stem = ROOT / name
    start = time.monotonic()
    cnf, selectors = encoding(window)
    cnf.write(stem.with_suffix('.cnf'))
    generated = time.monotonic()
    with stem.with_suffix('.log').open('w') as output:
        process = subprocess.run([SOLVER, '-t', str(limit), str(stem.with_suffix('.cnf'))],
                                 stdout=output, stderr=subprocess.STDOUT)
    result = {'window': window, 'vars': cnf.count, 'clauses': len(cnf.clauses),
              'generation_seconds': generated-start,
              'total_seconds': time.monotonic()-start, 'returncode': process.returncode,
              'status': {10: 'SAT', 20: 'UNSAT'}.get(process.returncode, 'UNKNOWN')}
    if process.returncode == 10:
        literals = {int(x) for line in stem.with_suffix('.log').read_text().splitlines()
                    if line.startswith('v ') for x in line.split()[1:] if int(x) > 0}
        circuit = BASE[:]
        for j, (sources, operation, left, right) in selectors.items():
            op = 'and' if operation in literals else 'or'
            a = next(a for a, v in zip(sources, left) if v in literals)
            b = next(a for a, v in zip(sources, right) if v in literals)
            circuit[j] = (op, a, b)
        errors = [row for row in ROWS if evaluate(circuit, row) != target(row)]
        assert not errors, errors
        result['circuit'] = circuit
        result['verified_boundary_rows'] = len(ROWS)
        (ROOT / 'COUNTEREXAMPLE.json').write_text(json.dumps(result, indent=2))
    stem.with_suffix('.json').write_text(json.dumps(result, indent=2))
    print(json.dumps(result), flush=True)
    return result


def positive_control(window):
    global BASE
    previous = BASE
    BASE = FULL
    try:
        cnf, selectors = encoding(window)
        for j, (sources, operation, left, right) in selectors.items():
            op, a, b = FULL[j]
            a, b = sorted((a, b))
            cnf.add(operation if op == 'and' else -operation)
            cnf.add(left[sources.index(a)])
            cnf.add(right[sources.index(b)])
        path = ROOT / 'positive-control.cnf'
        cnf.write(path)
        with (ROOT / 'positive-control.log').open('w') as output:
            process = subprocess.run([SOLVER, '-t', '30', str(path)],
                                     stdout=output, stderr=subprocess.STDOUT)
        result = {'positive_control': 'star64 with prescribed valid selectors',
                  'window': window, 'returncode': process.returncode,
                  'vars': cnf.count, 'clauses': len(cnf.clauses)}
        (ROOT / 'positive-control.json').write_text(json.dumps(result, indent=2))
        print(json.dumps(result), flush=True)
        assert process.returncode == 10
    finally:
        BASE = previous


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--limit', type=int, default=60)
    parser.add_argument('--last-lines')
    parser.add_argument('--control', action='store_true')
    parser.add_argument('windows', nargs='*')
    args = parser.parse_args()
    if args.last_lines:
        last = list(map(int, args.last_lines.split(',')))
        assert len(set(last)) == len(last) and all(0 <= j < N for j in last)
        order = [j for j in range(N) if j not in last] + last
        ROOT = ROOT / ('last-lines-' + '-'.join(map(str, last)))
        FULL = baseline(order)
        BASE = delete_one()
    ROOT.mkdir(exist_ok=True, parents=True)
    (ROOT / 'pg3-data.json').write_text(json.dumps({'vectors': VECTORS, 'edges': EDGES,
        'boundary': ROWS, 'baseline64': FULL, 'baseline63': BASE,
        'baseline63_errors': [r for r in ROWS if evaluate(BASE, r) != target(r)]}, indent=2))
    windows = [tuple(map(int, w.split(','))) for w in args.windows]
    if not windows:
        windows = [(48, 49, 50), (48, 49, 50, 62), (48, 49, 50, 61, 62)]
    if args.control:
        positive_control(windows[0])
    for window in windows:
        if solve(window, args.limit)['status'] == 'SAT':
            break
