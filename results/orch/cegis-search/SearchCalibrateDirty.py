"""Check every generated CNF clause against explicit known circuit assignments."""
import argparse
import json
from pathlib import Path


def serialize(n, gates, permutation):
    mapping = {i: permutation[i] for i in range(n)}
    pending = set(range(len(gates)))
    result = []
    while pending:
        ready = []
        for i in pending:
            operation, inputs = gates[i]
            if all(wire in mapping for wire in inputs):
                pair = tuple(sorted(mapping[wire] for wire in inputs))
                ready.append((pair, operation, i))
        pair, operation, i = min(ready)
        mapping[n+i] = n+len(result)
        result.append((operation, pair))
        pending.remove(i)
    return result


def check(cnf, gates):
    data = json.loads(cnf.with_suffix('.map.json').read_text())
    n, k = data['n'], data['k']
    assert len(gates) == k
    values = {}
    for t in data['tests']:
        values[t] = [bool(t >> i & 1) for i in range(n)]
        for operation, (a, b) in gates:
            x, y = values[t][a], values[t][b]
            values[t].append(x and y if operation == 'and' else x or y)
    assignment = {}
    for key, variable in data['variables']:
        kind = key[0]
        if kind == 's':
            _, i, side, wire = key
            value = gates[i][1][side] == wire
        elif kind == 'op':
            value = gates[key[1]][0] == 'and'
        elif kind == 'arg':
            _, i, side, t = key
            value = values[t][gates[i][1][side]]
        elif kind == 'v':
            _, i, t = key
            value = values[t][n+i]
        elif kind == 'exclusive':
            _, i, side, t = key
            value = values[t][gates[i][1][side]] and not values[t][gates[i][1][1-side]]
        elif kind == 'dirty':
            _, i, t = key
            value = gates[i][0] == 'and' and values[t][n+i]
        elif kind == 'dirty_gate':
            i=key[1]
            value=gates[i][0]=='and' and any(values[t][n+i] for t in data['tests']
                if not any(t&(1<<a) and t&(1<<b) for a,b in data['edges']))
        elif kind == 'count':
            _, i, j = key
            value = sum(operation == 'and' for operation, _ in gates[:i]) >= j
        else:
            raise ValueError(key)
        assignment[variable] = bool(value)
    checked = 0
    for line in cnf.read_text().splitlines():
        if line.startswith(('p', 'c')):
            continue
        clause = list(map(int, line.split()))
        assert clause.pop() == 0
        assert any(assignment[abs(literal)] == (literal > 0) for literal in clause), (checked, clause)
        checked += 1
    print(json.dumps({'file': str(cnf), 'gates': gates, 'clauses_checked': checked, 'result': 'PASS'}))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--scratch', type=Path, required=True)
    args = parser.parse_args()
    # One dirty helper changes a 3-star C6 circuit of size8 into a correct size10 circuit.
    c6 = [('or', (0,1)), ('or', (3,4)), ('and', (6,7)), ('and', (0,8)),
          ('or', (4,5)), ('and', (1,10)), ('or', (3,5)), ('and', (2,12)),
          ('or', (9,11)), ('or', (14,13))]
    c6 = serialize(6, c6, list(range(6)))
    check(args.scratch/'search-c6-dirty10-calibration.cnf', c6)
    # Build the known29-gate alternative6 star circuit and canonicalize all24 input automorphisms.
    cnf = args.scratch/'search-alternative6-sym29-calibration.cnf'
    data = json.loads(cnf.with_suffix('.map.json').read_text())
    n = data['n']
    gates, roots = [], []
    def add(operation, a, b):
        gates.append((operation, (a,b)))
        return n+len(gates)-1
    for point in range(6):
        neighbors = sorted(b for a,b in data['edges'] if a == point)
        current = neighbors[0]
        for other in neighbors[1:]:
            current = add('or', current, other)
        roots.append(add('and', point, current))
    current = roots[0]
    for other in roots[1:]:
        current = add('or', current, other)
    symmetry = json.loads((args.scratch/'alternative6-automorphisms.json').read_text())
    serializations = [serialize(n, gates, permutation) for permutation in symmetry['automorphisms']]
    chosen = min(serializations, key=lambda gs: tuple((pair, operation) for operation, pair in gs))
    check(cnf, chosen)


if __name__ == '__main__':
    main()
