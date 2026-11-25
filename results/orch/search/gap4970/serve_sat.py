"""Exact small-circuit search for gap L-meta-4970, including T=0 and serving stars."""
import argparse
import itertools
import json
import subprocess
import time
from datetime import datetime, timezone
from pathlib import Path

SOLVER = '/tmp/oec/pequalnp-pilot-94/toolchain/toolchains/leanprover--lean4---v4.36.0/bin/cadical'

class CNF:
    def __init__(self):
        self.variables = 0
        self.clauses = []
    def var(self):
        self.variables += 1
        return self.variables
    def clause(self, *items):
        if any(item is True for item in items):
            return
        self.clauses.append([item for item in items if item is not False])
    def exactly_one(self, items):
        self.clause(*items)
        if len(items) < 2:
            return
        chain = [self.var() for _ in items[:-1]]
        self.clause(-items[0], chain[0])
        for j in range(1, len(items) - 1):
            self.clause(-items[j], chain[j])
            self.clause(-chain[j - 1], chain[j])
            self.clause(-items[j], -chain[j - 1])
        self.clause(-items[-1], -chain[-1])

def neg(value):
    return not value if type(value) is bool else -value

def graph_data(name):
    if name == 'path4':
        return 2, 2, [(0, 0), (1, 0), (1, 1)]
    if name == 'cycle6':
        return 3, 3, [(a, b) for a in range(3) for b in range(3) if a != b]
    if name == 'k4inc':
        pairs = list(itertools.combinations(range(4), 2))
        return 4, 6, [(a, b) for b, pair in enumerate(pairs) for a in pair]
    data = json.loads(Path(name).read_text())
    return data['p'], data['l'], [tuple(edge) for edge in data['edges']]

def cover_number(p, l, edges):
    for size in range(p + l + 1):
        for vertices in itertools.combinations(range(p + l), size):
            chosen = set(vertices)
            if all(a in chosen or p + b in chosen for a, b in edges):
                return size
    raise AssertionError

def no_four_cycle(p, l, edges):
    edge_set = set(edges)
    return all(not all((a, b) in edge_set for a in aa for b in bb)
               for aa in itertools.combinations(range(p), 2)
               for bb in itertools.combinations(range(l), 2))

def make_problem(p, l, edges, gates, output_before_last=False):
    n = p + l
    edge_set = set(edges)
    assert len(edge_set) == len(edges) and no_four_cycle(p, l, edges)
    assert all(0 <= a < p and 0 <= b < l for a, b in edges)
    def target(mask):
        return any((mask >> a) & (mask >> (p + b)) & 1 for a, b in edges)
    positives = {(1 << a) | (1 << (p + b)) for a, b in edges}
    negatives = {mask for mask in range(1 << n) if not target(mask) and
                 all(target(mask | (1 << i)) for i in range(n) if not mask >> i & 1)}
    stars = []
    for a in range(p):
        neighbors = [p + b for b in range(l) if (a, b) in edge_set]
        for size in range(2, len(neighbors) + 1):
            for leaves in itertools.combinations(neighbors, size):
                stars.append({'center': a, 'leaves': leaves,
                              'edges': [(a, leaf - p) for leaf in leaves]})
    for b in range(l):
        neighbors = [a for a in range(p) if (a, b) in edge_set]
        for size in range(2, len(neighbors) + 1):
            for leaves in itertools.combinations(neighbors, size):
                stars.append({'center': p + b, 'leaves': leaves,
                              'edges': [(leaf, b) for leaf in leaves]})
    tests = set(positives) | set(negatives) | {1 << i for i in range(n)}
    for star in stars:
        star['mask'] = sum(1 << i for i in star['leaves'])
        tests.add(((1 << n) - 1) ^ star['mask'])
    tests = sorted(tests)
    index = {mask: j for j, mask in enumerate(tests)}
    cnf = CNF()
    ops = [cnf.var() for _ in range(gates)]
    selectors = [[[cnf.var() for _ in range(n + g)] for _ in range(2)] for g in range(gates)]
    values = [[cnf.var() for _ in tests] for _ in range(gates)]
    operands = [[[cnf.var() for _ in tests] for _ in range(2)] for _ in range(gates)]
    colors = [[cnf.var(), cnf.var()] for _ in range(gates)]
    color_operands = [[[cnf.var(), cnf.var()] for _ in range(2)] for _ in range(gates)]
    outputs = [cnf.var() for _ in range(gates)]
    cnf.exactly_one(outputs)
    if output_before_last and gates:
        cnf.clause(-outputs[-1])
    for g in range(gates):
        for side in range(2):
            cnf.exactly_one(selectors[g][side])
            for wire, selected in enumerate(selectors[g][side]):
                for t, mask in enumerate(tests):
                    value = bool(mask >> wire & 1) if wire < n else values[wire - n][t]
                    z = operands[g][side][t]
                    cnf.clause(-selected, neg(value), z)
                    cnf.clause(-selected, value, -z)
                for bit in range(2):
                    value = (wire < p if bit == 0 else p <= wire) if wire < n else colors[wire - n][bit]
                    z = color_operands[g][side][bit]
                    cnf.clause(-selected, neg(value), z)
                    cnf.clause(-selected, value, -z)
        # Commutativity only: equality is allowed because AND(x,x) can hide OR reach.
        for a in range(n + g):
            for b in range(a):
                cnf.clause(-selectors[g][0][a], -selectors[g][1][b])
        op = ops[g]
        for t, mask in enumerate(tests):
            a, b = operands[g][0][t], operands[g][1][t]
            z = values[g][t]
            cnf.clause(op, -a, -b, z)
            cnf.clause(op, a, -z)
            cnf.clause(op, b, -z)
            cnf.clause(-op, a, b, -z)
            cnf.clause(-op, -a, z)
            cnf.clause(-op, -b, z)
            cnf.clause(-outputs[g], z if target(mask) else -z)
        for bit in range(2):
            a, b = color_operands[g][0][bit], color_operands[g][1][bit]
            z = colors[g][bit]
            cnf.clause(op, -z)
            cnf.clause(-op, -a, z)
            cnf.clause(-op, -b, z)
            cnf.clause(-op, a, b, -z)
        cnf.clause(-colors[g][0], -colors[g][1])
    serving = [[cnf.var() for _ in stars] for _ in range(gates)]
    for g in range(gates):
        for s, star in enumerate(stars):
            flag = serving[g][s]
            cnf.clause(-flag, ops[g])
            for leaf in star['leaves']:
                cnf.clause(-flag, values[g][index[1 << leaf]])
            complement = ((1 << n) - 1) ^ star['mask']
            cnf.clause(-flag, -values[g][index[complement]])
    for edge in edges:
        cnf.clause(*(serving[g][s] for g in range(gates) for s, star in enumerate(stars)
                     if edge in star['edges']))
    return cnf, ops, selectors, outputs, stars, tests, target

def verify(p, l, edges, circuit, output, stars):
    n = p + l
    def evaluate(mask):
        values = [(mask >> i) & 1 for i in range(n)]
        for g, (op, a, b) in enumerate(circuit):
            assert op in (0, 1) and 0 <= a < n + g and 0 <= b < n + g
            values.append(values[a] | values[b] if op else values[a] & values[b])
        return values
    tables = [evaluate(mask) for mask in range(1 << n)]
    assert all(bool(row[output]) == any((mask >> a) & (mask >> (p + b)) & 1 for a, b in edges)
               for mask, row in enumerate(tables))
    reach = [1 << i for i in range(n)]
    two_color = []
    for g, (op, a, b) in enumerate(circuit):
        r = reach[a] | reach[b] if op else 0
        reach.append(r)
        if op and r & ((1 << p) - 1) and r >> p:
            two_color.append(g)
    assert not two_color
    witnesses = {}
    for g, (op, a, b) in enumerate(circuit):
        if not op:
            continue
        for star in stars:
            if all(bool(row[n + g]) == bool(mask & star['mask']) for mask, row in enumerate(tables)):
                for edge in star['edges']:
                    witnesses.setdefault(edge, {'gate': g, 'center': star['center'], 'leaves': star['leaves']})
    assert all(edge in witnesses for edge in edges)
    return {'inputs_verified': 1 << n, 'tCount': 0,
            'edge_witnesses': [{'edge': edge, **witnesses[edge]} for edge in edges]}

def main(args):
    p, l, edges = graph_data(args.graph)
    tau = cover_number(p, l, edges)
    cnf, ops, selectors, outputs, stars, tests, target = make_problem(p, l, edges, args.gates, args.output_before_last)
    base = Path(args.output)
    base.parent.mkdir(parents=True, exist_ok=True)
    with base.with_suffix('.cnf').open('w') as f:
        f.write(f'p cnf {cnf.variables} {len(cnf.clauses)}\n')
        for clause in cnf.clauses:
            f.write(' '.join(map(str, clause)) + ' 0\n')
    result = {'p': p, 'l': l, 'edges': edges, 'cover_number': tau, 'gates': args.gates,
              'tests': len(tests), 'star_options': len(stars), 'variables': cnf.variables,
              'clauses': len(cnf.clauses), 'started_utc': datetime.now(timezone.utc).isoformat(),
              'output_before_last': args.output_before_last,
              'bound_counterexample_threshold': len(edges) + tau - 2}
    if args.generate_only:
        result['status'] = 'generated_only'
        base.with_suffix('.result.json').write_text(json.dumps(result, indent=2) + '\n')
        return result
    begin = time.monotonic()
    with base.with_suffix('.solver.stdout').open('w') as out, base.with_suffix('.solver.stderr').open('w') as err:
        proc = subprocess.run([SOLVER, '-t', str(args.seconds), str(base.with_suffix('.cnf'))], stdout=out, stderr=err)
    result.update(seconds=time.monotonic() - begin, returncode=proc.returncode)
    result['status'] = 'SAT' if proc.returncode == 10 else 'UNSAT' if proc.returncode == 20 else 'UNKNOWN'
    if proc.returncode == 10:
        model = set()
        for line in base.with_suffix('.solver.stdout').read_text().splitlines():
            if line.startswith('v '):
                model.update(int(word) for word in line.split()[1:] if int(word) > 0)
        circuit = []
        for g in range(args.gates):
            pair = [next(i for i, var in enumerate(selectors[g][side]) if var in model) for side in range(2)]
            circuit.append([int(ops[g] in model), *pair])
        output = p + l + next(g for g, var in enumerate(outputs) if var in model)
        checked = verify(p, l, edges, circuit, output, stars)
        result.update(circuit=circuit, output=output, verification=checked,
                      counterexample=args.gates + 1 < len(edges) + tau)
    base.with_suffix('.result.json').write_text(json.dumps(result, indent=2) + '\n')
    return result

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--graph', required=True)
    parser.add_argument('--gates', type=int, required=True)
    parser.add_argument('--seconds', type=int, default=30)
    parser.add_argument('--output', required=True)
    parser.add_argument('--generate-only', action='store_true')
    parser.add_argument('--output-before-last', action='store_true')
    print(json.dumps(main(parser.parse_args())))
