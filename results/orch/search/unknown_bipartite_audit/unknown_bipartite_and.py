from pathlib import Path
import argparse
import hashlib
import itertools
import json
import subprocess
import time

ROOT = Path('/tmp/oec/pequalnp-pilot-64')
SOLVER = ROOT / 'toolchain/lean-4.36.0-linux/bin/cadical'


class CNF:
    def __init__(self):
        self.n = 0
        self.clauses = []

    def new(self):
        self.n += 1
        return self.n

    def add(self, *literals):
        self.clauses.append(list(literals))

    def land(self, a, b):
        z = self.new()
        self.add(-z, a)
        self.add(-z, b)
        self.add(z, -a, -b)
        return z

    def lor(self, xs):
        z = self.new()
        self.add(-z, *xs)
        for x in xs:
            self.add(z, -x)
        return z

    def write(self, path):
        with path.open('w') as out:
            out.write(f'p cnf {self.n} {len(self.clauses)}\n')
            for clause in self.clauses:
                out.write(' '.join(map(str, clause)) + ' 0\n')


def encode(k, control=False):
    c = CNF()
    edges = [[c.new() for _ in range(4)] for _ in range(4)]
    for i in range(4):
        c.add(edges[i][i])
    for i, j in itertools.combinations(range(4), 2):
        for a, b in itertools.combinations(range(4), 2):
            c.add(-edges[i][a], -edges[i][b], -edges[j][a], -edges[j][b])
    if control:
        for i in range(4):
            for j in range(4):
                if i != j:
                    c.add(-edges[i][j])
    sides = [[[c.new() for _ in range(8 + g)] for _ in range(2)] for g in range(k)]
    outputs = [c.new() for _ in range(k)]
    c.add(*outputs)
    for gate in sides:
        for side in gate:
            c.add(*side)
    # No original-input disjointness, connectivity, sorting or use constraints.
    for mask in range(256):
        values = []
        for g, gate in enumerate(sides):
            operand_values = []
            for side in gate:
                terms = [side[i] for i in range(8) if mask >> i & 1]
                terms += [c.land(side[8 + j], values[j]) for j in range(g)]
                operand_values.append(c.lor(terms))
            values.append(c.land(*operand_values))
        out = c.lor([c.land(s, v) for s, v in zip(outputs, values)])
        target = c.lor([edges[i][j] for i in range(4) for j in range(4)
                        if mask >> i & 1 and mask >> (4 + j) & 1])
        c.add(-out, target)
        c.add(out, -target)
    return c, edges, sides, outputs


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('gates', type=int)
    parser.add_argument('--seconds', type=int, default=30)
    parser.add_argument('--control', action='store_true')
    args = parser.parse_args()
    directory = ROOT / ('unknown-bipartite-' + str(args.gates) + ('-control' if args.control else ''))
    directory.mkdir(exist_ok=True)
    cnf, edge_vars, sides, outputs = encode(args.gates, args.control)
    cnf_path = directory / 'formula.cnf'
    cnf.write(cnf_path)
    command = [str(SOLVER), '-t', str(args.seconds), str(cnf_path)]
    started = time.monotonic()
    with (directory / 'stdout.txt').open('w') as out, (directory / 'stderr.txt').open('w') as err:
        result = subprocess.run(command, stdout=out, stderr=err)
    summary = {'gates': args.gates, 'control': args.control, 'argv': command,
               'seconds': time.monotonic() - started, 'returncode': result.returncode,
               'variables': cnf.n, 'clauses': len(cnf.clauses),
               'cnf_sha256': hashlib.sha256(cnf_path.read_bytes()).hexdigest(),
               'encoder_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               'solver_sha256': hashlib.sha256(SOLVER.read_bytes()).hexdigest()}
    if result.returncode == 10:
        model = set()
        for line in (directory / 'stdout.txt').read_text().splitlines():
            if line.startswith('v '):
                model.update(int(x) for x in line[2:].split() if int(x) > 0)
        assert all(any((x > 0) == (abs(x) in model) for x in clause) for clause in cnf.clauses)
        edges = [(i, j) for i in range(4) for j in range(4) if edge_vars[i][j] in model]
        gates = [[[i for i, v in enumerate(side) if v in model] for side in gate] for gate in sides]
        chosen = [i for i, v in enumerate(outputs) if v in model]
        assert all((i, i) in edges for i in range(4))
        assert not any(all((i, a) in edges for i in rows for a in cols)
                       for rows in itertools.combinations(range(4), 2)
                       for cols in itertools.combinations(range(4), 2))
        for mask in range(256):
            values = [bool(mask >> i & 1) for i in range(8)]
            for left, right in gates:
                values.append(any(values[i] for i in left) and any(values[i] for i in right))
            actual = any(values[8 + i] for i in chosen)
            target = any(mask >> i & 1 and mask >> (4 + j) & 1 for i, j in edges)
            assert actual == target
        summary['candidate'] = {'edges': edges, 'gates': gates, 'outputs': chosen}
        summary['validation'] = 'All CNF clauses and all 256 truth rows pass scalar validation.'
    (directory / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary))


if __name__ == '__main__':
    main()
