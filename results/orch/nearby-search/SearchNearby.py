"""Constrain a general synthesis CNF to a bounded fan-in/operation edit distance."""
import argparse
import itertools
import json
from pathlib import Path


def at_most(literals, budget, previous_count):
    assert budget >= 0
    clauses, variables = [], {}
    count = previous_count
    threshold = budget + 1
    def var(i, j):
        nonlocal count
        if (i, j) not in variables:
            count += 1
            variables[i, j] = count
        return variables[i, j]
    for i in range(len(literals) + 1):
        clauses.append([var(i, 0)])
    for j in range(1, threshold + 1):
        clauses.append([-var(0, j)])
    for i, literal in enumerate(literals, 1):
        for j in range(1, threshold + 1):
            current, same, previous = var(i, j), var(i-1, j), var(i-1, j-1)
            clauses.extend([[-current, same, literal], [-current, same, previous],
                            [current, -same], [current, -literal, -previous]])
    clauses.append([-var(len(literals), threshold)])
    return count, clauses, variables


def self_test():
    tested = 0
    literals = [1, -2, 3, -4, 5, -6, 7, -8]
    for budget in range(5):
        count, clauses, variables = at_most(literals, budget, 8)
        for bits in itertools.product((False, True), repeat=8):
            assignment = {i+1: bit for i, bit in enumerate(bits)}
            values = [assignment[abs(literal)] == (literal > 0) for literal in literals]
            for (i, j), variable in variables.items():
                assignment[variable] = sum(values[:i]) >= j
            valid = all(any(assignment[abs(literal)] == (literal > 0) for literal in clause)
                        for clause in clauses)
            assert valid == (sum(values) <= budget)
            assert max(assignment) == count
            tested += 1
    print(json.dumps({'self_test': 'PASS', 'truth_assignments': tested, 'budgets': list(range(5))}))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--cnf', type=Path)
    parser.add_argument('--nearby', type=Path)
    parser.add_argument('--edits', type=int)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--pad', action='store_true')
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return
    assert args.cnf and args.nearby and args.output and args.edits is not None
    data = json.loads(args.cnf.with_suffix('.map.json').read_text())
    witness = json.loads(args.nearby.read_text())
    gates = witness['gates'] if isinstance(witness, dict) else witness
    original_size = len(gates)
    assert 'ands' not in data
    if isinstance(witness, dict):
        assert witness.get('inputs', data['n']) == data['n']
        assert witness.get('output', data['n']+original_size-1) == data['n']+original_size-1
    if args.pad:
        assert gates and len(gates) <= data['k']
        # Reapplying the final operation with one of its operands is absorbing.
        while len(gates) < data['k']:
            operation, inputs = gates[-1]
            gates.append([operation, sorted([data['n']+len(gates)-1, inputs[0]])])
    assert len(gates) == data['k']
    variables = {tuple(key): value for key, value in data['variables']}
    mismatch = []
    for i, (operation, inputs) in enumerate(gates):
        assert operation in ('and', 'or') and len(inputs) == 2
        assert all(0 <= source < data['n']+i for source in inputs)
        for side, source in enumerate(sorted(inputs)):
            mismatch.append(-variables['s', i, side, source])
        op = variables['op', i]
        mismatch.append(-op if operation == 'and' else op)
    source = args.cnf.read_text().splitlines()
    header = source[0].split()
    assert header[:2] == ['p', 'cnf']
    old_count, old_clauses = map(int, header[2:])
    count, extra, counters = at_most(mismatch, args.edits, old_count)
    assert len(source)-1 == old_clauses
    output = [f'p cnf {count} {old_clauses+len(extra)}'] + source[1:]
    output.extend(' '.join(map(str, clause))+' 0' for clause in extra)
    args.output.write_text('\n'.join(output)+'\n')
    data['variables'].extend([[['nearcount', i, j], value] for (i, j), value in counters.items()])
    data['nearby'] = {'maximum_edits': args.edits, 'original_gates': gates,
                      'padding_gates': len(gates)-original_size,
                      'distance': 'number of changed ordered fan-ins plus changed gate operations'}
    args.output.with_suffix('.map.json').write_text(json.dumps(data)+'\n')
    print(json.dumps({'variables': count, 'clauses': old_clauses+len(extra),
                      'maximum_edits': args.edits, 'positions': len(mismatch)}))


if __name__ == '__main__':
    main()
