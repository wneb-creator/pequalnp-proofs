import itertools
import json
import random
from pathlib import Path

random.seed(3821)


def run(n, gates):
    mask = (1 << (1 << n)) - 1
    wires = [sum(((r >> i) & 1) << r for r in range(1 << n)) for i in range(n)]
    for op, reads in gates:
        values = [wires[i] if i < len(wires) else 0 for i in reads]
        if op == 'and':
            value = mask
            for v in values:
                value &= v
        elif op == 'or':
            value = 0
            for v in values:
                value |= v
        else:
            value = mask ^ (values[0] if values else 0)
        wires.append(value)
    return wires


def cofactor(table, n, fixed, value):
    result = 0
    for row in range(1 << (n - 1)):
        original = (row & ((1 << fixed) - 1)) | (value << fixed) | ((row >> fixed) << (fixed + 1))
        result |= ((table >> original) & 1) << row
    return result


def check(n, gates, fixed, value, output):
    old = run(n, gates)
    tables = [cofactor(t, n, fixed, value) for t in old]
    m = n - 1
    inputs = run(m, [])
    absent = n + len(gates) + 2
    representatives = {0: absent}
    representatives.update({t: i for i, t in enumerate(inputs)})
    new_gates = []
    true_table = (1 << (1 << m)) - 1
    for i, table in enumerate(tables):
        if table in representatives:
            continue
        if i < n:
            assert table == true_table
            gate = ('and', [])
        else:
            op, reads = gates[i - n]
            args = [tables[j] if j < i else 0 for j in reads]
            gate = (op, [representatives[t] for t in args])
        representatives[table] = m + len(new_gates)
        new_gates.append(gate)
    fresh = set(tables) - set(inputs) - {0}
    assert len(new_gates) == len(fresh)
    target = tables[output] if output < len(tables) else 0
    new_output = representatives[target]
    new_values = run(m, new_gates)
    actual = new_values[new_output] if new_output < len(new_values) else 0
    assert actual == target
    return len(fresh)


count = 0
for n in range(1, 6):
    for op in ('and', 'or', 'not'):
        for arity in range(3):
            for reads in itertools.product(range(n + 2), repeat=arity):
                gates = [(op, list(reads))]
                for fixed in range(n):
                    for value in range(2):
                        for output in range(n + 3):
                            check(n, gates, fixed, value, output)
                            count += 1
exhaustive = count
for _ in range(10000):
    n = random.randrange(1, 7)
    gates = []
    for i in range(random.randrange(25)):
        gates.append((random.choice(('and', 'or', 'not')), [random.randrange(n + i + 5) for _ in range(random.randrange(3))]))
    check(n, gates, random.randrange(n), random.randrange(2), random.randrange(n + len(gates) + 5))
    count += 1

result = {
    'status': 'PASS',
    'exhaustive_single_gate_cases': exhaustive,
    'random_multigate_cases': count - exhaustive,
    'tested_features': ['all three operations', 'arity zero/one/two', 'duplicate and invalid reads', 'both cofactor bits', 'input and missing output', 'constant true counted'],
    'scope': 'Computational checks of generic compression only; no proof of Petersen-specific counting premise.'
}
print(json.dumps(result, indent=2))
Path('/tmp/oec/pequalnp-pilot-38/compression-tests.json').write_text(json.dumps(result, indent=2) + '\n')
