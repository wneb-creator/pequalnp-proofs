#!/usr/bin/env python3
"""Construct order-three projective incidence and a complete monotone test basis."""
import itertools
import json
import pathlib
import sys


def make_problem():
    points = [v for v in itertools.product(range(3), repeat=3)
              if any(v) and next(x for x in v if x) == 1]
    lines = [[i for i, p in enumerate(points)
              if sum(a * b for a, b in zip(p, ell)) % 3 == 0]
             for ell in points]
    assert len(points) == len(lines) == 13
    assert all(len(line) == 4 for line in lines)
    assert all(sum(p in line and q in line for line in lines) == 1
               for p, q in itertools.combinations(range(13), 2))
    edges = [(p, 13 + ell) for ell, line in enumerate(lines) for p in line]
    masks = [sum(1 << p for p in line) for line in lines]
    maxfalse = []
    for ps in range(1 << 13):
        ls = sum(1 << ell for ell, mask in enumerate(masks) if not ps & mask)
        closure = sum(1 << p for p in range(13)
                      if all(not (ls >> ell & 1 and mask >> p & 1)
                             for ell, mask in enumerate(masks)))
        if ps == closure:
            maxfalse.append(ps | (ls << 13))
    mintrue = [(1 << p) | (1 << ell) for p, ell in edges]
    assert len(set(maxfalse)) == 704 and len(set(mintrue)) == 52
    for x in maxfalse:
        assert not any(x >> p & 1 and x >> ell & 1 for p, ell in edges)
        assert all(any((x | (1 << j)) >> p & 1 and
                       (x | (1 << j)) >> ell & 1 for p, ell in edges)
                   for j in range(26) if not (x >> j & 1))
    gates = []
    stars = []
    for ell, line in enumerate(lines):
        wire = line[0]
        for p in line[1:]:
            gates.append({'op': 'or', 'a': wire, 'b': p})
            wire = 25 + len(gates)
        gates.append({'op': 'and', 'a': 13 + ell, 'b': wire})
        stars.append(25 + len(gates))
    wire = stars[0]
    for star in stars[1:]:
        gates.append({'op': 'or', 'a': wire, 'b': star})
        wire = 25 + len(gates)
    assert len(gates) == 64 and wire == 89
    return dict(inputs=26, points=points, lines=lines, edges=edges,
                minimal_true=mintrue, maximal_false=maxfalse,
                gates=gates, output=wire)


def evaluate(gates, x, output):
    wires = [bool(x >> j & 1) for j in range(26)]
    for i, gate in enumerate(gates):
        assert gate['op'] in ('and', 'or')
        a, b = gate['a'], gate['b']
        assert 0 <= a < 26 + i and 0 <= b < 26 + i
        wires.append(wires[a] and wires[b] if gate['op'] == 'and'
                     else wires[a] or wires[b])
    assert 0 <= output < len(wires)
    return wires[output]


def main():
    directory = pathlib.Path(sys.argv[1])
    problem = make_problem()
    for x in problem['minimal_true']:
        assert evaluate(problem['gates'], x, problem['output'])
    for x in problem['maximal_false']:
        assert not evaluate(problem['gates'], x, problem['output'])
    (directory / 'plane3.json').write_text(json.dumps(problem, indent=2) + '\n')
    with (directory / 'plane3.dat').open('w') as stream:
        stream.write('26 13 52 704\n')
        for line in problem['lines']:
            stream.write(' '.join(map(str, line)) + '\n')
        for x in problem['minimal_true']:
            stream.write(f'{x} 1\n')
        for x in problem['maximal_false']:
            stream.write(f'{x} 0\n')
    print('VERIFIED PG(2,3): 26 inputs, 52 edges, 704 maximal false rows, 64 gates.')
    print('Monotonicity makes agreement on these 756 rows equivalent to full equality.')


if __name__ == '__main__':
    main()
