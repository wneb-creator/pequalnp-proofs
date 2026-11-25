import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path


class CNF:
    def __init__(self, variables=0):
        self.nv = variables
        self.clauses = []

    def var(self):
        self.nv += 1
        return self.nv

    def add(self, *literals):
        self.clauses.append(list(literals))

    def mux(self, flag, low, high):
        out = self.var()
        self.add(flag, -out, low)
        self.add(flag, out, -low)
        self.add(-flag, -out, high)
        self.add(-flag, out, -high)
        return out

    def at_most(self, literals, bound):
        assert 0 <= bound
        if bound >= len(literals):
            return []
        if bound == 0:
            for literal in literals:
                self.add(-literal)
            return []
        counters = []
        previous = None
        for literal in literals:
            row = [self.var() for _ in range(bound)]
            counters.append(row)
            self.add(-literal, row[0])
            if previous is not None:
                for old, new in zip(previous, row):
                    self.add(-old, new)
                for j in range(1, bound):
                    self.add(-literal, -previous[j - 1], row[j])
                self.add(-literal, -previous[-1])
            previous = row
        return counters


def normalize_gates(data):
    gates = data['gates'] if isinstance(data, dict) else data
    result = []
    for op, left, right in gates:
        if type(op) is int:
            assert op in (0, 1)
            op = 'or' if op else 'and'
        assert op in ('and', 'or')
        result.append([op, *sorted((left, right))])
    return result


def edit_distance(first, second):
    assert len(first) == len(second)
    result = 0
    for (op, a, b), (other_op, c, d) in zip(first, second):
        common = sum((Counter((a, b)) & Counter((c, d))).values())
        result += 2 - common + (op != other_op)
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--cnf', type=Path, required=True)
    parser.add_argument('--seed', type=Path, required=True)
    parser.add_argument('--budget', type=int, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    mapping = json.loads(args.cnf.with_suffix('.map.json').read_text())
    required = {'allow_initial_repeats': True, 'allow_trivial': True,
                'canonical_prefix': False, 'lex_order': False, 'liveness': False,
                'ordered_max': False, 'dirty_and': False, 'shadow_missing': 0,
                'minimal': False, 'minimal_prefix': 0, 'prefix': None}
    assert all(mapping.get(key) == value for key, value in required.items())
    assert 0 <= args.budget <= 3 * mapping['gates']
    seed = normalize_gates(json.loads(args.seed.read_text()))
    assert len(seed) == mapping['gates']
    assert all(0 <= a <= b < mapping['ninputs'] + i for i, (_, a, b) in enumerate(seed))
    cnf = CNF(mapping['nv'])
    changes = []
    flips = []
    for (op, a, b), gate in zip(seed, mapping['structure']):
        flip = cnf.var()
        flips.append(flip)
        left_match = cnf.mux(flip, gate['left'][a], gate['left'][b])
        right_match = cnf.mux(flip, gate['right'][b], gate['right'][a])
        changes += [-left_match, -right_match, -gate['op'] if op == 'or' else gate['op']]
    counters = cnf.at_most(changes, args.budget)
    rows = mapping['rows']
    values = [[bool(mask >> i & 1) for mask in rows] for i in range(mapping['ninputs'])]
    for op, a, b in seed:
        values.append([x or y if op == 'or' else x and y for x, y in zip(values[a], values[b])])
    positives = len(mapping['edges'])
    errors = {'false_negative_boundary_rows': sum(not v for v in values[-1][:positives]),
              'false_positive_boundary_rows': sum(values[-1][positives:])}
    lines = args.cnf.read_text().splitlines(keepends=True)
    headers = [i for i, line in enumerate(lines) if line.startswith('p cnf ')]
    assert len(headers) == 1
    header = headers[0]
    _, _, variables, clauses = lines[header].split()
    assert int(variables) == mapping['nv'] and int(clauses) == mapping['clauses']
    assert not args.output.exists() and not args.output.with_suffix('.map.json').exists()
    lines[header] = f'p cnf {cnf.nv} {mapping["clauses"] + len(cnf.clauses)}\n'
    lines.extend(' '.join(map(str, clause)) + ' 0\n' for clause in cnf.clauses)
    mapping['nv'] = cnf.nv
    mapping['clauses'] += len(cnf.clauses)
    mapping['repair'] = {'budget': args.budget, 'distance': 'unordered operand replacements plus operation flips',
                         'seed': seed, 'seed_errors': errors, 'changes': changes,
                         'orientation_variables': flips, 'counter_variables': counters,
                         'source_sha256': hashlib.sha256(args.cnf.read_bytes()).hexdigest(),
                         'seed_sha256': hashlib.sha256(args.seed.read_bytes()).hexdigest(),
                         'scope': 'fixed topological slot neighborhood, with commutative operands'}
    args.output.write_text(''.join(lines))
    args.output.with_suffix('.map.json').write_text(json.dumps(mapping, separators=(',', ':')) + '\n')
    print(json.dumps({'output': str(args.output), 'budget': args.budget, 'nv': mapping['nv'],
                      'clauses': mapping['clauses'], 'seed_errors': errors}))


if __name__ == '__main__':
    main()
