import itertools
from pathlib import Path

from and_skeleton_calibration import problem
from and_skeleton_minimal import emit_minimal, verify_minimal_conditions
from and_skeleton_sat import Solver, decode, evaluate, verify


def run(data, seed, positive_live, child_incomparable, dirty=False, fixed=True):
    path = Path('/tmp/oec/pequalnp-pilot-57/and-skeleton-minimal-calibration.cnf')
    selected, output, dirty_inputs, _, _, normalized = emit_minimal(
        path, data, seed, dirty=dirty,
        positive_live=positive_live, child_incomparable=child_incomparable)
    solver = Solver(57189)
    for left, right in selected:
        for literal in left + right:
            solver.freeze(literal)
    for literal in output + (dirty_inputs or []):
        solver.freeze(literal)
    with path.open() as source:
        for line in source:
            if not line.startswith('p'):
                solver.add(*map(int, line.split()[:-1]))
    if fixed:
        for (left, right), gate in zip(selected, normalized['and_gates']):
            for literals, side in ((left, gate['left']), (right, gate['right'])):
                for vertex, literal in enumerate(literals):
                    solver.add(literal if vertex in side else -literal)
        for vertex, literal in enumerate(output):
            solver.add(literal if vertex in normalized['output'] else -literal)
    result = solver.solve(10)
    assert result in (10, 20)
    if result == 10:
        answer = decode(solver, selected, output, data['inputs'])
        mask = (sum(1 << i for i, literal in enumerate(dirty_inputs) if solver.truth(literal))
                if dirty_inputs is not None else None)
        verify(data, answer, mask, full=True)
        verify_minimal_conditions(data, answer, positive_live, child_incomparable)
    solver.close()
    return result


def main():
    data = problem(3, [(0, 1), (0, 2)])
    count = 0
    for left, right in itertools.product(range(8), repeat=2):
        seed = {'inputs': 3, 'and_gates': [{
            'left': [v for v in range(3) if left >> v & 1],
            'right': [v for v in range(3) if right >> v & 1]}], 'output': [3]}
        exact = all(evaluate(seed, t['mask'])[1] == bool(t['label']) for t in data['tests'])
        for positive_live, child_incomparable in itertools.product((False, True), repeat=2):
            expected = exact
            try:
                verify_minimal_conditions(data, seed, positive_live, child_incomparable)
            except AssertionError:
                expected = False
            assert (run(data, seed, positive_live, child_incomparable) == 10) == expected
            count += 1
    path = problem(4, [(0, 1), (2, 1), (2, 3)])
    path_seed = {'inputs': 4, 'and_gates': [
        {'left': [0, 2], 'right': [1, 3]}, {'left': [1, 2], 'right': [4]}], 'output': [5]}
    assert run(path, path_seed, True, True, dirty=True, fixed=False) == 10
    single = problem(2, [(0, 1)])
    unused_false = {'inputs': 2, 'and_gates': [
        {'left': [], 'right': []}, {'left': [0], 'right': [1]}], 'output': [3]}
    assert run(single, unused_false, False, False) == 10
    assert run(single, unused_false, True, False) == 20
    copy_child = {'inputs': 2, 'and_gates': [
        {'left': [0], 'right': [0]}, {'left': [2], 'right': [1]}], 'output': [3]}
    assert run(single, copy_child, True, False) == 10
    assert run(single, copy_child, True, True) == 20
    print('PASS', count, 'fixed actual-solver cases, free P4 dirty2, positive-empty and copy-child rejection')


if __name__ == '__main__':
    main()
