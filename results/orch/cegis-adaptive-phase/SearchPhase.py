"""Invert CNF variable polarities so a known circuit is the all-false phase.

This is a bijective variable renaming, not an additional constraint.  The
reference circuit may be invalid on newly added tests.  SAT models must be
translated back before ordinary decoding and complete function verification.
"""
import argparse
import json
from pathlib import Path


def reference_assignment(data):
    gates = data['nearby']['original_gates']
    assert len(gates) == data['k']
    tables = {}
    for x in data['tests']:
        values = [bool(x >> j & 1) for j in range(data['n'])]
        for operation, inputs in gates:
            a, b = sorted(inputs)
            assert 0 <= a < b < len(values)
            values.append(values[a] and values[b] if operation == 'and'
                          else values[a] or values[b])
        tables[x] = values
    assignment = {}
    for key, variable in data['variables']:
        tag, *args = key
        if tag == 's':
            i, side, source = args
            value = sorted(gates[i][1])[side] == source
        elif tag == 'op':
            value = gates[args[0]][0] == 'and'
        elif tag == 'arg':
            i, side, x = args
            value = tables[x][sorted(gates[i][1])[side]]
        elif tag == 'v':
            i, x = args
            value = tables[x][data['n'] + i]
        elif tag == 'nearcount':
            value = args[1] == 0
        else:
            value = False
        assignment[variable] = value
    return assignment


def invert_cnf(source, target):
    data = json.loads(source.with_suffix('.map.json').read_text())
    assignment = reference_assignment(data)
    inverted = {v for v, value in assignment.items() if value}
    with source.open() as src, target.open('w') as dst:
        header = src.readline()
        assert header.split()[:2] == ['p', 'cnf']
        dst.write(header)
        for line in src:
            literals = list(map(int, line.split()))
            assert literals and literals[-1] == 0
            dst.write(' '.join(str(-v if abs(v) in inverted else v)
                               for v in literals) + '\n')
    target.with_suffix('.phase.json').write_text(json.dumps(sorted(inverted)) + '\n')
    return inverted


def restore_model(source, target, inverted):
    with source.open() as src, target.open('w') as dst:
        for line in src:
            if line.startswith('v '):
                literals = list(map(int, line.split()[1:]))
                dst.write('v ' + ' '.join(str(-v if abs(v) in inverted else v)
                                          for v in literals) + '\n')
            else:
                dst.write(line)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--cnf', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    inverted = invert_cnf(args.cnf, args.output)
    print(json.dumps({'polarity_inversions': len(inverted),
                      'meaning': 'equisatisfiable variable renaming only'}))


if __name__ == '__main__':
    main()
