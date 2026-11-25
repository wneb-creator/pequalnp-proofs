import argparse
import json
import time
from pathlib import Path

from feature_gadget_sat import assemble, extend, packed_verification, support_constraints, target, verify_problem
from global_synthesis import canonicalize, emit, evaluate
from incremental_cegis import LiveCNF, Solver, add_sample, model
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
    parser.add_argument('--require-feature', action='store_true')
    parser.add_argument('--edit-bound', type=int)
    parser.add_argument('--pair-objective', action='store_true')
    parser.add_argument('--min-and-count', type=int)
    args = parser.parse_args()
    pack = json.loads(args.pack.read_text())
    if isinstance(pack, dict):
        pack = [pack]
    case = pack[args.case]
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
    raw_samples = [tuple(test) for test in case['raw_tests']]
    if args.pair_objective:
        raw_samples = [(mask, label) for mask, label in raw_samples if label]
        raw_samples += [((1 << owner) | (1 << line), 0)
                        for owner in owners for line in range(case['raw_inputs'])
                        if line not in owners and not target(case, (1 << owner) | (1 << line))]
    basis_samples = [(extend(case, mask), label) for mask, label in raw_samples]
    assert len(set(basis_samples)) == len(basis_samples)
    samples = list(dict.fromkeys(basis_samples + [(mask, 0) for mask in hard]))
    assert all(not evaluate(phase, mask, n) for mask in hard)
    assert all(evaluate(phase, mask, n) for mask, label in samples if label)
    negatives = [i for i, (_, label) in enumerate(raw_samples) if not label]
    pairs = []
    for j, left in enumerate(negatives):
        for right in negatives[:j]:
            joined = raw_samples[left][0] | raw_samples[right][0]
            if args.pair_objective and not target(case, joined):
                continue
            assert target(case, joined)
            assert extend(case, joined) == basis_samples[left][0] | basis_samples[right][0]
            pairs.append((left, right))
    initial_errors = sum(evaluate(phase, mask, n) for mask, label in samples if not label)
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / 'problem.json').write_text(json.dumps(case))
    levels = []
    path = args.output / 'problem.cnf'
    selected, variables, clauses = emit(path, count, samples, useful=False, ninputs=n,
        order_max=True, order_lex=True, positive_live=True, positive_incomparable=True,
        phase_seed=phase, negative_error_levels=levels, hard_negative_masks=hard,
        max_edits=args.edit_bound,
        zero_join_family_size=None if args.pair_objective else len(negatives),
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
        if args.min_and_count is not None:
            and_levels = cnf.count_row([-op for op, _, _ in selected], args.min_and_count)
            cnf.clause(and_levels[args.min_and_count])
        if args.require_feature:
            cnf.clause(*(literal for _, sa, sb in selected for side in (sa, sb)
                         for literal in side[case['raw_inputs']:n]))
        journal.flush()
        stamp('INITIAL FEATURE MAXSAT', case['name'], 'errors', initial_errors,
              'variables', cnf.variables, 'clauses', cnf.clauses, 'excess', excess)
        budget = initial_errors
        iteration = 0
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
            full_bad = [mask for mask, label in case['tests']
                        if not label and evaluate(answer, mask, n)]
            report = dict(case=case['name'], pack=str(args.pack), case_index=args.case,
                          gates=answer, inputs=n, negative_errors=len(full_bad),
                          objective_errors=errors, pair_objective=args.pair_objective,
                          positive_errors=0, exact_witness=False,
                          component_edit_bound=args.edit_bound,
                          require_feature=args.require_feature)
            if errors == 0 and not full_bad:
                packed = packed_verification(case, answer)
                assert packed['false_positives'] == packed['false_negatives'] == 0
                report['exact_gadget'] = True
                if 'outside_gates' in case:
                    report['full_circuit'] = assemble(case, answer)
                    geometry_path = Path(__file__).resolve().parents[2] / 'circuit_search' / 'geometry.json'
                    geometry = json.loads(geometry_path.read_text())
                    tests = [((1 << a) | (1 << b), True) for a, b in geometry['edges']]
                    tests += [(a | (b << 13), False) for a, b in geometry['maximal_independent_sets']]
                    assert all(evaluate(report['full_circuit'], mask, 26) == label for mask, label in tests)
                    report['exact_witness'] = True
            filename = (f'candidate-round-{iteration}-pairs-{errors}.json' if args.pair_objective
                        else f'candidate-errors-{errors}.json')
            (args.output / filename).write_text(json.dumps(report))
            iteration += 1
            stamp('VERIFIED CANDIDATE', errors, 'objective errors', len(full_bad),
                  'full negative errors', 'exact', report['exact_witness'])
            if errors == 0 and not full_bad:
                filename = 'EXACT-FULL63.json' if report['exact_witness'] else 'EXACT-KERNEL.json'
                (args.output / filename).write_text(json.dumps(report))
                break
            if errors == 0:
                assert args.pair_objective
                new_masks = set()
                for mask in full_bad:
                    raw = mask & ((1 << case['raw_inputs']) - 1)
                    for bit in range(case['raw_inputs']):
                        smaller = raw & ~(1 << bit)
                        if evaluate(answer, extend(case, smaller), n):
                            raw = smaller
                    assert not target(case, raw)
                    new_masks.add(extend(case, raw))
                for mask in sorted(new_masks):
                    assert mask not in hard
                    add_sample(cnf, selected, n, mask, 0, answer)
                    hard.add(mask)
                stamp('ADDED HARD MINIMAL COUNTEREXAMPLES', len(new_masks))
                budget = 0
            else:
                budget = errors - 1
    solver.close()


if __name__ == '__main__':
    main()
