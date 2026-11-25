import argparse
import json
import time
from pathlib import Path

from global_synthesis import canonicalize, emit, evaluate
from incremental_cegis import Solver, model
from subset_cegis import stamp


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('problem', type=Path)
    parser.add_argument('seeds', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--index', type=int, default=1)
    parser.add_argument('--seconds', type=int, default=120)
    parser.add_argument('--retries', type=int, default=5)
    parser.add_argument('--seed', type=int, default=5799)
    parser.add_argument('--lex', action='store_true')
    args = parser.parse_args()
    data = json.loads(args.problem.read_text())
    seed = json.loads(args.seeds.read_text())[args.index]
    n, count = data['inputs'], data['max_gates']
    answer = [[op, *sorted((a, b))] for op, a, b in seed['gates']]
    while len(answer) < count:
        last = n + len(answer) - 1
        answer.append([0, last, last])
    assert len(answer) == count
    if args.lex:
        answer = canonicalize(answer, n)
    left = len(data['original_rows'])
    hard = {0, (1 << left) - 1, ((1 << n) - 1) ^ ((1 << left) - 1)}
    hard.update(1 << i for i in range(n))
    samples = list(dict.fromkeys([tuple(t) for t in data['tests']] + [(mask, 0) for mask in hard]))
    assert all(not evaluate(answer, mask, n) for mask in hard)
    assert all(evaluate(answer, mask, n) for mask, label in samples if label)
    errors = sum(evaluate(answer, mask, n) for mask, label in samples if not label)
    args.output.mkdir(parents=True, exist_ok=True)
    levels = []
    path = args.output / 'problem.cnf'
    selected, variables, clauses = emit(path, count, samples, ninputs=n,
                                        order_max=args.lex, order_lex=args.lex,
                                        positive_live=True, positive_incomparable=True,
                                        phase_seed=answer, negative_error_levels=levels,
                                        hard_negative_masks=hard)
    solver = Solver(args.seed)
    for op, sa, sb in selected:
        for lit in [op] + sa + sb:
            solver.freeze(lit)
    for lit in levels:
        solver.freeze(lit)
    with path.open() as source:
        for line in source:
            if not line.startswith('p'):
                solver.add(*[int(word) for word in line.split()[:-1]])
    stamp('INITIAL', seed.get('group'), 'errors', errors, 'variables', variables, 'clauses', clauses)
    for budget in range(errors, -1, -1):
        for attempt in range(args.retries):
            solver.lib.ccadical_assume(solver.ptr, -levels[budget + 1])
            begin = time.monotonic()
            result = solver.solve(args.seconds)
            stamp('SOLVER', 'budget', budget, 'attempt', attempt,
                  'result', result, 'seconds', round(time.monotonic() - begin, 2))
            if result != 0:
                break
        if result != 10:
            break
        answer = model(solver, selected)
        assert all(not evaluate(answer, mask, n) for mask in hard)
        assert all(evaluate(answer, mask, n) for mask, label in samples if label)
        observed = sum(evaluate(answer, mask, n) for mask, label in samples if not label)
        assert observed <= budget
        (args.output / f'candidate-budget-{budget}.json').write_text(json.dumps(answer))
        stamp('CANDIDATE', 'observed_errors', observed)
        if observed == 0:
            verification = data.get('verification_tests', data['tests'])
            remaining = sum(evaluate(answer, mask, n) != bool(label)
                            for mask, label in verification)
            filename = 'EXACT-WITNESS.json' if not remaining else 'BOUNDARY-CANDIDATE.json'
            (args.output / filename).write_text(json.dumps(answer))
            if not remaining:
                stamp('EXACT TARGET WITNESS', len(answer))
            else:
                stamp('BOUNDARY ONLY', 'full_basis_errors', remaining)
            break
    solver.close()


if __name__ == '__main__':
    main()
