import argparse
import itertools
import json
from pathlib import Path
import subprocess
import time


def neg(x):
    return not x if isinstance(x, bool) else -x


class CNF:
    def __init__(self):
        self.n = 0
        self.rows = []

    def var(self):
        self.n += 1
        return self.n

    def clause(self, *xs):
        if any(x is True for x in xs):
            return
        row = list(dict.fromkeys(x for x in xs if x is not False))
        if any(-x in row for x in row):
            return
        self.rows.append(row)

    def conjunction(self, a, b):
        if a is False or b is False:
            return False
        if a is True:
            return b
        if b is True:
            return a
        z = self.var()
        self.clause(-z, a)
        self.clause(-z, b)
        self.clause(z, neg(a), neg(b))
        return z

    def disjunction_into(self, z, terms):
        for t in terms:
            self.clause(neg(t), z)
        self.clause(-z, *terms)

    def write(self, path):
        with path.open('w') as f:
            f.write(f'p cnf {self.n} {len(self.rows)}\n')
            for row in self.rows:
                f.write(' '.join(map(str, row)) + ' 0\n')


def graph(name):
    if name == 'edge':
        return 2, [(0, 1)]
    if name == 'matching2':
        return 4, [(0, 2), (1, 3)]
    if name == 'path4':
        return 4, [(0, 1), (1, 2), (2, 3)]
    if name == 'cycle5':
        return 5, [(i, (i+1) % 5) for i in range(5)]
    if name == 'k4inc':
        pairs = list(itertools.combinations(range(4), 2))
        return 10, [(v, 4+j) for j, pair in enumerate(pairs) for v in pair]
    return 14, [(p, 7+l) for p in range(7) for l in range(7)
                if (p-l) % 7 in (0, 1, 3)]


def solve(args):
    n, edges = graph(args.graph)
    k = args.gates
    primal = lambda x: any((x >> a) & (x >> b) & 1 for a, b in edges)
    target = (lambda x: not primal(((1 << n)-1) ^ x)) if args.dual else primal
    # Direct-input output summands can be omitted exactly because each singleton
    # is rejected.  This includes the Fano, K4-incidence and cycle targets in
    # either polarity, but intentionally excludes such cases as a dual edge.
    assert all(not target(1 << i) for i in range(n)), 'Output-input summands required for this target'
    positives = [x for x in range(1 << n) if target(x)
                 and all(not target(x ^ (1 << i)) for i in range(n) if x >> i & 1)]
    negatives = [x for x in range(1 << n) if not target(x)
                 and all(target(x | (1 << i)) for i in range(n) if not (x >> i & 1))]
    tests = positives + negatives
    cnf = CNF()
    side_members = [[[cnf.var() for _ in range(n+g)] for _ in range(2)] for g in range(k)]
    outputs = [cnf.var() for _ in range(k)]
    values = [[cnf.var() for _ in tests] for _ in range(k)]
    sides = [[[cnf.var() for _ in tests] for _ in range(2)] for _ in range(k)]
    for g in range(k):
        for side in range(2):
            for t, x in enumerate(tests):
                terms = []
                for source, chosen in enumerate(side_members[g][side]):
                    value = bool(x >> source & 1) if source < n else values[source-n][t]
                    terms.append(cnf.conjunction(chosen, value))
                cnf.disjunction_into(sides[g][side][t], terms)
        for t in range(len(tests)):
            a, b, z = sides[g][0][t], sides[g][1][t], values[g][t]
            cnf.clause(-z, a)
            cnf.clause(-z, b)
            cnf.clause(z, -a, -b)
    for t, x in enumerate(tests):
        if target(x):
            cnf.clause(*(cnf.conjunction(outputs[g], values[g][t]) for g in range(k)))
        else:
            for g in range(k):
                cnf.clause(-outputs[g], -values[g][t])
    if args.clique_bare:
        assert args.dual
        edge_set = {tuple(sorted(e)) for e in edges}
        for g in range(k):
            for side in range(2):
                for a, b in itertools.combinations(range(n), 2):
                    if (a, b) not in edge_set:
                        cnf.clause(-side_members[g][side][a], -side_members[g][side][b])
    if args.k4_cofactor_caps:
        assert args.graph == 'k4inc' and args.dual and k == 10
        hits = [[cnf.var() for g in range(k)] for v in range(n)]
        for v in range(n):
            for g in range(k):
                cnf.disjunction_into(hits[v][g], [side_members[g][side][v] for side in range(2)])
        for v in range(4):
            for chosen in itertools.combinations(hits[v], 3):
                cnf.clause(*(neg(x) for x in chosen))
        for a, b in itertools.combinations(range(4, 10), 2):
            union = [cnf.var() for g in range(k)]
            for g in range(k):
                cnf.disjunction_into(union[g], [hits[a][g], hits[b][g]])
            for chosen in itertools.combinations(union, 4):
                cnf.clause(*(neg(x) for x in chosen))
    if args.fix_stars:
        assert args.graph == 'fano' and k == 7 and not args.dual
        for g in range(k):
            cnf.clause(outputs[g])
            for side in range(2):
                expected = {7+g} if side == 0 else {p for p in range(7) if (p, 7+g) in edges}
                for source, variable in enumerate(side_members[g][side]):
                    cnf.clause(variable if source in expected else -variable)
    base = Path(args.output)
    cnf.write(base.with_suffix('.cnf'))
    result = {'graph': args.graph, 'dual': args.dual, 'n': n, 'edges': edges, 'and_gates': k,
              'positive_tests': positives, 'negative_tests': negatives,
              'variables': cnf.n, 'clauses': len(cnf.rows)}
    result['restricted_search'] = bool(args.k4_cofactor_caps or args.clique_bare)
    result['extra_constraints'] = ['point-reader count <= 2', 'line-pair reader union <= 3'] if args.k4_cofactor_caps else []
    if args.clique_bare:
        result['extra_constraints'].append('every bare operand set is an original-graph clique')
    if args.emit_only:
        result['status'] = 'EMITTED'
    else:
        start = time.monotonic()
        with base.with_suffix('.solver.stdout').open('w') as out, base.with_suffix('.solver.stderr').open('w') as err:
            proc = subprocess.run([args.solver, '-t', str(args.seconds), str(base.with_suffix('.cnf'))],
                                  stdout=out, stderr=err)
        result.update(returncode=proc.returncode, seconds=time.monotonic()-start)
        result['status'] = {10: 'SAT', 20: 'UNSAT', 0: 'UNKNOWN'}.get(proc.returncode, 'ERROR')
        if proc.returncode == 10:
            positive = set()
            for line in base.with_suffix('.solver.stdout').read_text().splitlines():
                if line.startswith('v '):
                    positive.update(int(x) for x in line[2:].split() if int(x) > 0)
            gates = [[[i for i, variable in enumerate(side_members[g][side]) if variable in positive]
                      for side in range(2)] for g in range(k)]
            selected = [g for g, variable in enumerate(outputs) if variable in positive]
            truth = [sum(((x >> i) & 1) << x for x in range(1 << n)) for i in range(n)]
            for left, right in gates:
                a = b = 0
                for source in left:
                    a |= truth[source]
                for source in right:
                    b |= truth[source]
                truth.append(a & b)
            actual = 0
            for g in selected:
                actual |= truth[n+g]
            expected = sum(1 << x for x in range(1 << n) if target(x))
            assert actual == expected, 'Decoded model does not compute the graph on all assignments'
            result.update(gates=gates, output_gates=selected, verified_assignments=1 << n,
                          naive_binary_gate_upper=k+sum(max(0, len(s)-1) for gate in gates for s in gate)
                          +max(0, len(selected)-1))
            binary = []
            cache = {}

            def append_gate(op, a, b):
                if a is None or b is None:
                    return (b if a is None else a) if op == 'or' else None
                if a == b:
                    return a
                a, b = sorted((a, b))
                key = (op, a, b)
                if key not in cache:
                    cache[key] = n+len(binary)
                    binary.append(key)
                return cache[key]

            def or_list(wires):
                out = None
                for wire in wires:
                    out = append_gate('or', out, wire)
                return out

            compiled = list(range(n))
            for left, right in gates:
                a = or_list(compiled[i] for i in left)
                b = or_list(compiled[i] for i in right)
                compiled.append(append_gate('and', a, b))
            output = or_list(compiled[n+g] for g in selected)
            assert output is not None
            reachable = set()

            def visit(wire):
                if wire < n or wire-n in reachable:
                    return
                reachable.add(wire-n)
                _, a, b = binary[wire-n]
                visit(a)
                visit(b)

            visit(output)
            remap = {i: i for i in range(n)}
            pruned = []
            for g, (op, a, b) in enumerate(binary):
                if g in reachable:
                    remap[n+g] = n+len(pruned)
                    pruned.append(('or' if op == 'and' else 'and', remap[a], remap[b])
                                  if args.dual else (op, remap[a], remap[b]))
            output = remap[output]
            binary_truth = truth[:n]
            for op, a, b in pruned:
                binary_truth.append(binary_truth[a] | binary_truth[b] if op == 'or'
                                    else binary_truth[a] & binary_truth[b])
            primal_expected = sum(1 << x for x in range(1 << n) if primal(x))
            assert binary_truth[output] == primal_expected
            result.update(binary_circuit=pruned, binary_output=output,
                          binary_size=len(pruned),
                          binary_and_count=sum(op == 'and' for op, _, _ in pruned),
                          binary_or_count=sum(op == 'or' for op, _, _ in pruned))
    base.with_suffix('.result.json').write_text(json.dumps(result, indent=2) + '\n')
    summary = {key: result[key] for key in result if key not in ('edges', 'positive_tests', 'negative_tests')}
    print(json.dumps(summary), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--graph', choices=['edge', 'matching2', 'path4', 'cycle5', 'k4inc', 'fano'], default='fano')
    parser.add_argument('--gates', type=int, required=True)
    parser.add_argument('--seconds', type=int, default=600)
    parser.add_argument('--output', required=True)
    parser.add_argument('--emit-only', action='store_true')
    parser.add_argument('--fix-stars', action='store_true')
    parser.add_argument('--dual', action='store_true')
    parser.add_argument('--k4-cofactor-caps', action='store_true')
    parser.add_argument('--clique-bare', action='store_true')
    parser.add_argument('--solver', default='/tmp/oec/pequalnp-pilot-94/toolchain/toolchains/leanprover--lean4---v4.36.0/bin/cadical')
    solve(parser.parse_args())
