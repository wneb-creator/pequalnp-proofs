import argparse
import json
import time
from pathlib import Path

from feature_gadget_sat import assemble, extend, support_constraints, target, verify_problem
from global_synthesis import canonicalize, emit, evaluate
from incremental_cegis import LiveCNF, Solver, model
from subset_cegis import stamp


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('pack', type=Path)
    parser.add_argument('seeds', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--case', type=int, default=1)
    parser.add_argument('--index', type=int, default=0)
    parser.add_argument('--seconds', type=int, default=120)
    parser.add_argument('--retries', type=int, default=3)
    parser.add_argument('--seed', type=int, default=57629)
    parser.add_argument('--crossings', action='store_true')
    args = parser.parse_args()
    case = json.loads(args.pack.read_text())[args.case]
    phase_data = json.loads(args.seeds.read_text())[args.index]
    phase = [list(g) for g in phase_data['gates']]
    n, count = case['inputs'], case['max_gates']
    verify_problem(case)
    while len(phase) < count:
        wire = n + len(phase) - 1
        phase.append([0, wire, wire])
    assert len(phase) == count
    phase = canonicalize(phase, n)
    owners = sorted(set(a for a, _ in case['edges']))
    points = sum(1 << i for i in owners)
    lines = ((1 << case['raw_inputs']) - 1) ^ points
    hard_raw = {0, points, lines} | {1 << i for i in range(case['raw_inputs'])}
    assert all(not target(case, mask) for mask in hard_raw)
    hard = {extend(case, mask) for mask in hard_raw}
    samples = list(dict.fromkeys([tuple(t) for t in case['tests']] + [(mask, 0) for mask in hard]))
    assert all(not evaluate(phase, mask, n) for mask in hard)
    assert all(evaluate(phase, mask, n) for mask, label in samples if label)
    negatives = [i for i, (_, label) in enumerate(case['tests']) if not label]
    pairs = []
    for j, left in enumerate(negatives):
        for right in negatives[:j]:
            joined = case['raw_tests'][left][0] | case['raw_tests'][right][0]
            assert target(case, joined)
            assert extend(case, joined) == case['tests'][left][0] | case['tests'][right][0]
            pairs.append((left, right))
    initial_errors = sum(evaluate(phase, mask, n) for mask, label in samples if not label)
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / 'problem.json').write_text(json.dumps(case))
    levels = []
    path = args.output / 'problem.cnf'
    selected, variables, clauses = emit(path, count, samples, useful=False, ninputs=n,
        order_max=True, order_lex=True, positive_live=True, positive_incomparable=True,
        phase_seed=phase, negative_error_levels=levels, hard_negative_masks=hard,
        zero_join_family_size=len(negatives),
        negative_join_pairs=pairs if args.crossings else None)
    solver = Solver(args.seed)
    for op, sa, sb in selected:
        for literal in [op] + sa + sb:
            solver.freeze(literal)
    for literal in levels:
        solver.freeze(literal)
    with path.open() as source:
        for line in source:
            if not line.startswith('p'):
                solver.add(*[int(word) for word in line.split()[:-1]])
    with (args.output / 'support-clauses.cnfpart').open('w') as journal:
        cnf = LiveCNF(solver, variables, clauses, journal)
        excess = support_constraints(cnf, selected, n, case['raw_inputs'])
        journal.flush()
        stamp('INITIAL FEATURE MAXSAT', case['name'], 'errors', initial_errors,
              'variables', cnf.variables, 'clauses', cnf.clauses, 'excess', excess)
        budget = initial_errors
        while budget >= 0:
            for attempt in range(args.retries):
                solver.lib.ccadical_assume(solver.ptr, -levels[budget + 1])
                start = time.monotonic()
                result = solver.solve(args.seconds)
                stamp('RESULT', 'budget', budget, 'attempt', attempt, result,
                      'seconds', round(time.monotonic() - start, 2))
                if result != 0:
                    break
            if result != 10:
                break
            answer = model(solver, selected)
            assert all(not evaluate(answer, mask, n) for mask in hard)
            assert all(evaluate(answer, mask, n) for mask, label in samples if label)
            errors = sum(evaluate(answer, mask, n) for mask, label in samples if not label)
            assert errors <= budget
            report = dict(case=case['name'], pack=str(args.pack), case_index=args.case,
                          gates=answer, inputs=n, negative_errors=errors,
                          positive_errors=0, exact_witness=False)
            if errors == 0:
                assert all(evaluate(answer, extend(case, raw), n) == target(case, raw)
                           for raw in range(1 << case['raw_inputs']))
                report['full_circuit'] = assemble(case, answer)
                geometry_path = Path(__file__).resolve().parents[2] / 'circuit_search' / 'geometry.json'
                geometry = json.loads(geometry_path.read_text())
                tests = [((1 << a) | (1 << b), True) for a, b in geometry['edges']]
                tests += [(a | (b << 13), False) for a, b in geometry['maximal_independent_sets']]
                assert all(evaluate(report['full_circuit'], mask, 26) == label for mask, label in tests)
                report['exact_witness'] = True
            (args.output / f'candidate-errors-{errors}.json').write_text(json.dumps(report))
            stamp('VERIFIED CANDIDATE', errors, 'negative errors', 'exact', report['exact_witness'])
            if errors == 0:
                (args.output / 'EXACT-FULL63.json').write_text(json.dumps(report))
                break
            budget = errors - 1
    solver.close()


if __name__ == '__main__':
    main()
