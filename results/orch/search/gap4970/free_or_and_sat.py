"""Exact AND-count synthesis with free OR and syntactic tCount = 0.

Adapted from the earlier andcount_sat.py collapsed free-OR model. Every AND
operand is a nonempty OR of primary inputs and earlier AND outputs. Its primary
inputs must lie in one colour class. AND outputs reset raw OR reach, including
duplicate-input AND gates. Output is an OR of selected AND outputs. Pure star
OR witnesses may be appended without spending any AND gates.
"""
import argparse
import itertools
import json
from pathlib import Path
import resource
import subprocess
import time

from serve_sat import cover_number, graph_data, no_four_cycle, verify


SOLVER = '/tmp/oec/pequalnp-pilot-94/toolchain/toolchains/leanprover--lean4---v4.36.0/bin/cadical'


def neg(value):
    return not value if type(value) is bool else -value


class CNF:
    def __init__(self):
        self.n = 0
        self.rows = []

    def var(self):
        self.n += 1
        return self.n

    def clause(self, *items):
        if any(item is True for item in items):
            return
        row = list(dict.fromkeys(item for item in items if item is not False))
        if any(-item in row for item in row):
            return
        self.rows.append(row)

    def conjunction(self, left, right):
        if left is False or right is False:
            return False
        if left is True:
            return right
        if right is True:
            return left
        out = self.var()
        self.clause(-out, left)
        self.clause(-out, right)
        self.clause(out, neg(left), neg(right))
        return out

    def disjunction_into(self, out, terms):
        for term in terms:
            self.clause(neg(term), out)
        self.clause(-out, *terms)

    def write(self, path):
        with path.open('w') as handle:
            handle.write(f'p cnf {self.n} {len(self.rows)}\n')
            for row in self.rows:
                handle.write(' '.join(map(str, row)) + ' 0\n')


def corona_graph():
    core = [0, 6, 1, 7, 2, 8]
    leaves = [9, 3, 10, 4, 11, 5]
    edges = set()
    for i, vertex in enumerate(core):
        for other in (core[(i + 1) % 6], leaves[i]):
            edges.add((vertex, other) if vertex < 6 else (other, vertex))
    assert len(edges) == 12
    return core, leaves, sorted(edges)


def read_graph(name):
    if name == 'coronaC6':
        _, _, edges = corona_graph()
        return 6, 6, [(a, b - 6) for a, b in edges]
    return graph_data(name)


def make_problem(p, l, local_edges, gates, pin_control=False):
    n = p + l
    assert len(set(local_edges)) == len(local_edges)
    assert all(0 <= a < p and 0 <= b < l for a, b in local_edges)
    assert no_four_cycle(p, l, local_edges)
    edges = [(a, p + b) for a, b in local_edges]

    def target(mask):
        return any(mask >> a & 1 and mask >> b & 1 for a, b in edges)

    positives = [(1 << a) | (1 << b) for a, b in edges]
    negatives = [mask for mask in range(1 << n) if not target(mask)
                 and all(target(mask | (1 << i)) for i in range(n)
                         if not mask >> i & 1)]
    tests = sorted(set(positives + negatives))
    cnf = CNF()
    selectors = [[[cnf.var() for _ in range(n + g)] for _ in range(2)]
                 for g in range(gates)]
    outputs = [cnf.var() for _ in range(gates)]
    values = [[cnf.var() for _ in tests] for _ in range(gates)]
    operands = [[[cnf.var() for _ in tests] for _ in range(2)]
                for _ in range(gates)]
    cnf.clause(*outputs)
    for g in range(gates):
        for side in range(2):
            members = selectors[g][side]
            cnf.clause(*members)
            # Bare primary inputs of an OR operand cannot have both colours.
            for a in range(p):
                for b in range(p, n):
                    cnf.clause(-members[a], -members[b])
            for t, mask in enumerate(tests):
                terms = [cnf.conjunction(chosen, bool(mask >> source & 1)
                                        if source < n else values[source - n][t])
                         for source, chosen in enumerate(members)]
                cnf.disjunction_into(operands[g][side][t], terms)
        for t in range(len(tests)):
            left, right, out = operands[g][0][t], operands[g][1][t], values[g][t]
            cnf.clause(-out, left)
            cnf.clause(-out, right)
            cnf.clause(out, -left, -right)
    for t, mask in enumerate(tests):
        if target(mask):
            cnf.clause(*(cnf.conjunction(outputs[g], values[g][t])
                         for g in range(gates)))
        else:
            for g in range(gates):
                cnf.clause(-outputs[g], -values[g][t])
    if pin_control:
        core, leaves, control_edges = corona_graph()
        assert p == l == gates == 6 and set(edges) == set(control_edges)
        for g in range(gates):
            cnf.clause(outputs[g])
            expected = [{core[g]}, {core[(g + 1) % 6], leaves[g]}]
            for side in range(2):
                for source, chosen in enumerate(selectors[g][side]):
                    cnf.clause(chosen if source in expected[side] else -chosen)
    return cnf, selectors, outputs, tests, edges


def reconstruct(p, l, local_edges, selected_operands, selected_outputs):
    n = p + l
    edges = [(a, p + b) for a, b in local_edges]
    gates = []
    or_cache = {}

    def add_or(left, right):
        if left == right:
            return left
        key = tuple(sorted((left, right)))
        if key not in or_cache:
            or_cache[key] = n + len(gates)
            gates.append([1, *key])
        return or_cache[key]

    def or_list(wires):
        wires = list(wires)
        assert wires
        out = wires[0]
        for wire in wires[1:]:
            out = add_or(out, wire)
        return out

    wires = list(range(n))
    for left, right in selected_operands:
        a = or_list(wires[source] for source in left)
        b = or_list(wires[source] for source in right)
        # Do not simplify AND(x,x): it can be an essential raw-reach barrier.
        wires.append(n + len(gates))
        gates.append([0, a, b])
    output = or_list(wires[n + g] for g in selected_outputs)

    def witness_data():
        full = (1 << (1 << n)) - 1
        tables = [sum(1 << mask for mask in range(1 << n) if mask >> i & 1)
                  for i in range(n)]
        reach = [{i} for i in range(n)]
        witnesses, covered = [], set()
        for j, (op, a, b) in enumerate(gates):
            tables.append(tables[a] | tables[b] if op else tables[a] & tables[b])
            reach.append(reach[a] | reach[b] if op else set())
            assert not (any(v < p for v in reach[-1]) and any(v >= p for v in reach[-1]))
            if not op:
                continue
            support = [i for i in range(n) if tables[-1] >> (1 << i) & 1]
            if len(support) < 2:
                continue
            expected = 0
            for i in support:
                expected |= tables[i]
            if tables[-1] != expected & full:
                continue
            for centre in range(n):
                served = {(centre, v) if centre < p else (v, centre) for v in support}
                if served <= set(edges):
                    witnesses.append(j)
                    covered.update(served)
        expected_output = sum(1 << mask for mask in range(1 << n)
                              if any(mask >> a & 1 and mask >> b & 1 for a, b in edges))
        assert tables[output] == expected_output
        return sorted(set(witnesses)), covered

    witnesses, covered = witness_data()
    # These dead OR witnesses cost no AND gates. A corona has no isolated K2.
    for a, b in edges:
        if (a, b) in covered:
            continue
        for centre in (a, b):
            neighbors = sorted({v if centre == u else u for u, v in edges
                                if centre in (u, v)})
            if len(neighbors) >= 2:
                or_list(neighbors)
                break
        else:
            raise AssertionError('Unservable isolated edge')
        witnesses, covered = witness_data()
    assert covered == set(edges)
    record = {'kind': 'free_or_and', 'p': p, 'l': l, 'edges': local_edges,
              'gates': gates, 'output': output,
              'gate_count': len(gates), 'and_count': len(selected_operands),
              't_count': 0, 'edges_served': len(edges), 'truth_rows': 1 << n,
              'witness_gate_indices': witnesses}
    stars = []
    for centre in range(n):
        neighbors = sorted({v if centre == u else u for u, v in edges
                            if centre in (u, v)})
        for size in range(2, len(neighbors) + 1):
            for leaves in itertools.combinations(neighbors, size):
                stars.append({'center': centre, 'leaves': leaves,
                              'mask': sum(1 << leaf for leaf in leaves),
                              'edges': [(centre, leaf - p) if centre < p else (leaf, centre - p)
                                        for leaf in leaves]})
    verification = verify(p, l, local_edges, gates, output, stars)
    tau = cover_number(p, l, local_edges)
    verification.update(and_count=sum(op == 0 for op, _, _ in gates),
                        gate_count=len(gates), cover_number=tau,
                        counterexample=len(gates) + 1 < len(edges) + tau)
    return record, verification


def run(args):
    base = Path(args.output)
    p, l, local_edges = read_graph(args.graph)
    cnf, selectors, outputs, tests, edges = make_problem(p, l, local_edges, args.gates, args.pin_control)
    cnf.write(base.with_suffix('.cnf'))
    result = {'graph': args.graph, 'p': p, 'l': l, 'edges': local_edges,
              'cover_number': cover_number(p, l, local_edges), 'and_budget': args.gates,
              'pin_control': args.pin_control, 'variables': cnf.n,
              'clauses': len(cnf.rows), 'test_count': len(tests),
              'memory_mb': args.memory_mb, 'seconds_limit': args.seconds,
              'status': 'EMITTED'}
    if not args.emit_only:
        def limit_memory():
            limit = args.memory_mb * 1024 * 1024
            resource.setrlimit(resource.RLIMIT_AS, (limit, limit))
        started = time.monotonic()
        with base.with_suffix('.solver.stdout').open('w') as out, \
                base.with_suffix('.solver.stderr').open('w') as err:
            process = subprocess.run([args.solver, '-t', str(args.seconds),
                                      str(base.with_suffix('.cnf'))], stdout=out,
                                     stderr=err, preexec_fn=limit_memory)
        result.update(seconds=time.monotonic() - started, returncode=process.returncode,
                      status={10: 'SAT', 20: 'UNSAT', 0: 'UNKNOWN'}.get(process.returncode, 'ERROR'))
        if process.returncode == 10:
            positive = set()
            for line in base.with_suffix('.solver.stdout').read_text().splitlines():
                if line.startswith('v '):
                    positive.update(int(word) for word in line[2:].split() if int(word) > 0)
            decoded = [[[source for source, flag in enumerate(side) if flag in positive]
                        for side in pair] for pair in selectors]
            selected_outputs = [g for g, flag in enumerate(outputs) if flag in positive]
            record, verification = reconstruct(p, l, local_edges, decoded, selected_outputs)
            base.with_suffix('.circuit.json').write_text(json.dumps(record, indent=2) + '\n')
            result.update(operands=decoded, output_ands=selected_outputs,
                          verification=verification)
    base.with_suffix('.result.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--graph', default='coronaC6')
    parser.add_argument('--gates', type=int, required=True)
    parser.add_argument('--output', required=True)
    parser.add_argument('--seconds', type=int, default=60)
    parser.add_argument('--memory-mb', type=int, default=512)
    parser.add_argument('--solver', default=SOLVER)
    parser.add_argument('--pin-control', action='store_true')
    parser.add_argument('--emit-only', action='store_true')
    run(parser.parse_args())
