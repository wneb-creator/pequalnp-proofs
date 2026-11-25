"""Scratch exporter smoke/arithmetic/projection checks; no target synthesis run."""
import argparse
import itertools
import json
from pathlib import Path
import subprocess
import time

import bv_dimacs as bv
import free_or_and_query as q
from test_free_or_and_kraft import explicit_values


def solve(solver, directory, text):
    directory.mkdir(parents=True)
    cnf, out, err = directory / 'query.cnf', directory / 'kissat.stdout', directory / 'kissat.stderr'
    cnf.write_text(text)
    with out.open('w') as stdout, err.open('w') as stderr:
        done = subprocess.run([str(solver), '--time=5', str(cnf)], stdout=stdout, stderr=stderr)
    assert done.returncode in [10, 20], (done.returncode, directory)
    return out


def test_arithmetic(solver, root):
    count = 0
    for width in range(1, 5):
        mask = (1 << width) - 1
        for x, y in [(0, 0), (0, mask), (mask, 0), (mask, mask), (1, 1), (mask >> 1, 1)]:
            expected = (((x + y) & mask) ^ ((x << y) & mask)) & mask
            for correct in [True, False]:
                target = expected if correct else expected ^ 1
                source = f'''(set-logic QF_BV)
(declare-const x (_ BitVec {width}))
(declare-const y (_ BitVec {width}))
(declare-const picked Bool)
(assert (= x (_ bv{x} {width})))
(assert (= y (_ bv{y} {width})))
(assert (= (bvxor (bvadd x y) (bvshl x y)) (_ bv{target} {width})))
(assert (= picked (bvult x y)))
(check-sat)
'''
                with bv.BitBlast(source, ['picked']) as encoded:
                    output = solve(solver, root / f'arithmetic-{count}', encoded.dimacs)
                    status, assignment = bv.parse_solution(output.read_text(), len(encoded.atoms))
                    assert (status == 'SATISFIABLE') == correct
                    if correct:
                        assert encoded.readback(assignment) == {'picked': x < y}
                count += 1
    return count


def test_circuits(solver, root):
    square = [(0, 2), (0, 3), (1, 2), (1, 3)]
    examples = [
        ('edge', 2, [(0, 1)], 1, 0, None),
        ('square', 4, square, 1, 2, None),
        ('square_impossible', 4, square, 0, None, None),
        ('false_padding', 4, square, 2, None, ([([], []), ([0, 1], [2, 3])], [4, 5])),
        ('shared_OR', 4, square, 2, None, ([([0, 1], [2]), ([0, 1], [3])], [4, 5])),
    ]
    fixture = json.loads((Path(__file__).resolve().parent / 'graphs' / 'C6book3.json').read_text())
    n, edges, cover = fixture['n'], fixture['edges'], [0, 3, 5, 7, 9, 11, 13]
    neighbors = {v: [] for v in cover}
    for u, v in edges:
        owner = u if u in neighbors else v
        assert owner in neighbors
        neighbors[owner].append(v if owner == u else u)
    gates = []
    for v in cover:
        left, right = [v], sorted(neighbors[v])
        if sum(1 << j for j in left) > sum(1 << j for j in right):
            left, right = right, left
        gates.append((left, right))
    gates.sort(key=lambda gate: (max(gate[0] + gate[1]) + 1,
                                sum(1 << j for j in gate[0]),
                                sum(1 << j for j in gate[1])))
    examples.append(('Book3_planted', n, edges, 7, 15, (gates, list(range(n, n + 7)))))
    reports = []
    for name, n, edges, k, cap, fixed in examples:
        source, meta = q.generate(n, edges, k, private_or_cap=cap, and_kraft=True, and_kraft_full=True)
        if fixed:
            values = explicit_values(meta, *fixed)
            pin = '\n'.join(f'(assert (= {s} {str(v).lower()}))' for s, v in values.items())
            source = source.replace('(check-sat)', pin + '\n(check-sat)')
        directory = root / name
        report = bv.export(source, meta, directory)
        # A second context must reproduce the exact DIMACS bytes before decode.
        with bv.BitBlast(source, meta['selectors']) as encoded:
            assert bv.digest(encoded.dimacs) == report['cnf_sha256']
        out, err = directory / 'kissat.stdout', directory / 'kissat.stderr'
        with out.open('w') as stdout, err.open('w') as stderr:
            done = subprocess.run([str(solver), '--time=5', str(directory / 'query.cnf')], stdout=stdout, stderr=stderr)
        assert done.returncode in [10, 20]
        decoded = bv.decode(directory, out)
        assert (decoded['status'] == 'SATISFIABLE') == (name != 'square_impossible')
        if decoded['status'] == 'SATISFIABLE':
            assert decoded['circuit']['exhaustively_checked_inputs'] == (1 << n)
            if fixed:
                assert decoded['selectors'] == values
        reports.append({'name': name, 'status': decoded['status'],
                        'variables': report['variables'], 'clauses': report['clauses'],
                        'truth_rows': decoded.get('circuit', {}).get('exhaustively_checked_inputs', 0)})
        (directory / 'decoded.json').write_text(json.dumps(decoded, indent=2) + '\n')
    return reports


def test_projections(solver, root):
    # Exhaust every original Boolean selector valuation, including omitted tautology.
    count = 0
    for values in itertools.product([False, True], repeat=3):
        source = '(set-logic QF_BV)\n' + '\n'.join(f'(declare-const {s} Bool)' for s in ['a', 'b', 'unused'])
        source += '\n(assert (or a b))\n(assert (or unused (not unused)))\n'
        source += '\n'.join(f'(assert (= {s} {str(v).lower()}))' for s, v in zip(['a', 'b', 'unused'], values))
        with bv.BitBlast(source, ['a', 'b', 'unused']) as encoded:
            out = solve(solver, root / f'projection-{count}', encoded.dimacs)
            status, assignment = bv.parse_solution(out.read_text(), len(encoded.atoms))
            assert (status == 'SATISFIABLE') == any(values[:2])
            if status == 'SATISFIABLE':
                assert encoded.readback(assignment) == dict(zip(['a', 'b', 'unused'], values))
        count += 1
    # Model completion gives an omitted free selector a valid arbitrary Boolean value.
    source = '(declare-const x Bool)\n(declare-const omitted Bool)\n(assert x)\n'
    with bv.BitBlast(source, ['x', 'omitted']) as encoded:
        out = solve(solver, root / 'omitted-selector', encoded.dimacs)
        status, assignment = bv.parse_solution(out.read_text(), len(encoded.atoms))
        assert status == 'SATISFIABLE'
        recovered = encoded.readback(assignment)
        assert recovered['x'] is True and isinstance(recovered['omitted'], bool)
        assert encoded.selector_ids['omitted'] is None
    return count + 1


def test_rejections():
    for text, count in [('s SATISFIABLE\nv 1 0\n', 2),
                        ('s SATISFIABLE\nv 1 -1 0\n', 1),
                        ('s SATISFIABLE\nv 2 0\n', 1),
                        ('s SATISFIABLE\ns UNSATISFIABLE\n', 0)]:
        try:
            bv.parse_solution(text, count)
        except ValueError:
            pass
        else:
            raise AssertionError('invalid solver output accepted')
    with bv.BitBlast('(declare-const x Bool)\n(assert x)\n', ['x']) as encoded:
        try:
            encoded.readback({1: False})
        except ValueError as error:
            assert 'falsifies CNF clause' in str(error)
        else:
            raise AssertionError('false CNF model accepted')
    return 5


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--solver', type=Path, required=True)
    parser.add_argument('--workdir', type=Path, required=True)
    args = parser.parse_args()
    root = args.workdir / f'bv-tests-{time.time_ns()}'
    root.mkdir(parents=True)
    report = {'directory': str(root), 'arithmetic_queries': test_arithmetic(args.solver, root),
              'circuit_queries': test_circuits(args.solver, root),
              'Boolean_projection_queries': test_projections(args.solver, root),
              'bad_output_rejections': test_rejections(), 'target_synthesis_run': False}
    (root / 'result.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
