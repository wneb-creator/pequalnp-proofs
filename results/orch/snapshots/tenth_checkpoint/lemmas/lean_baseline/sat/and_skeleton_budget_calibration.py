import json
import random
from pathlib import Path

from and_skeleton_budget_run import assemble_separate, occurrence_count, solve_budget
from and_skeleton_calibration import problem
from and_skeleton_sat import evaluate


def main():
    base = Path(__file__).parent
    scratch = Path('/tmp/oec/pequalnp-pilot-57/and-budget-calibration')
    path = problem(4, [(0, 1), (2, 1), (2, 3)])
    p4 = {'inputs': 4, 'and_gates': [
        {'left': [0, 2], 'right': [1, 3]}, {'left': [1, 2], 'right': [4]}], 'output': [5]}
    assert occurrence_count(p4) == 8
    assert solve_budget(path, p4, scratch / 'p4_exact5', 5, 20,
                        fixed=True, calibration=True) == 10
    assert solve_budget(path, p4, scratch / 'p4_fixed_budget4', 4, 20,
                        fixed=True, calibration=True) == 20
    single = problem(2, [(0, 1)])
    empty = {'inputs': 2, 'and_gates': [
        {'left': [], 'right': []}, {'left': [0], 'right': [1]}], 'output': [3]}
    assert solve_budget(single, empty, scratch / 'reject_empty_cone', 2, 20,
                        dirty=False, fixed=True, calibration=True) == 20
    rng = random.Random(5714)
    for _ in range(200):
        n = rng.randrange(2, 6)
        k = rng.randrange(1, 7)
        gates = []
        for i in range(k):
            sides = [sorted(rng.sample(range(n + i), rng.randrange(1, n + i + 1))) for _ in range(2)]
            gates.append({'left': sides[0], 'right': sides[1]})
        seed = {'inputs': n, 'and_gates': gates,
                'output': sorted(rng.sample(range(n + k), rng.randrange(1, n + k + 1)))}
        circuit = assemble_separate(seed)
        assert circuit['gate_count'] == occurrence_count(seed) - k - 1
        for mask in range(1 << n):
            values = [bool(mask >> v & 1) for v in range(n)]
            for op, a, b in circuit['gates']:
                values.append(values[a] or values[b] if op else values[a] and values[b])
            assert values[circuit['output']] == evaluate(seed, mask)[1]
    data = json.loads((base / 'and_skeleton_full_data.json').read_text())
    for name, seed_name, gates, occurrences, dirty in [
        ('baseline13', 'and_skeleton_baseline13.json', 64, 78, False),
        ('dirty14', 'and_skeleton_full_exact_dirty14_phase.json', 66, 81, True),
    ]:
        seed = json.loads((base / seed_name).read_text())
        assert occurrence_count(seed) == occurrences
        assert solve_budget(data, seed, scratch / f'{name}_exact', gates, 30,
                            dirty=dirty, fixed=True, calibration=True) == 10
        assert solve_budget(data, seed, scratch / f'{name}_one_too_small', gates - 1, 30,
                            dirty=dirty, fixed=True, calibration=True) == 20
    print('PASS P4 budgets, explicit empty-cone rejection,200 arbitrary skeleton assemblies,full64/66 fixed calibrations')


if __name__ == '__main__':
    main()
