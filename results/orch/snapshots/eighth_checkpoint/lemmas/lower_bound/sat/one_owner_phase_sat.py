import argparse
import itertools
import json
import time
from pathlib import Path

from feature_gadget_sat import (verify_problem, packed_verification, extend, target, run,
                                support_constraints, first_orbit_constraints, symmetry_phase)
from joint_feature_gadget_sat import compatibility, assemble
from global_synthesis import emit, canonicalize, evaluate
from incremental_cegis import Solver, LiveCNF, model
from subset_cegis import stamp


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('packet', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--phase-file', type=Path, required=True)
    parser.add_argument('--symmetry-data', type=Path, required=True)
    parser.add_argument('--seconds', type=int, default=60)
    parser.add_argument('--seed', type=int, default=57801)
    args = parser.parse_args()
    case = json.loads(args.packet.read_text())[0]
    verify_problem(case)
    assert (case['raw_inputs'], case['inputs'], case['max_gates']) == (14, 41, 18)
    symmetry = json.loads(args.symmetry_data.read_text())
    assert (symmetry['inputs'], symmetry['raw_inputs'], symmetry['edges']) == (
        case['inputs'], case['raw_inputs'], case['edges'])
    phase = json.loads(args.phase_file.read_text())
    if isinstance(phase, dict):
        phase = phase['gates']
    phase = symmetry_phase(canonicalize(phase, 41), 41, symmetry)
    args.output.mkdir(parents=True, exist_ok=True)
    run(case, args.output / 'calibration', 20, args.seed, fixed=True, and_count=5,
        min_and_count=5, symmetry=symmetry, extra_constraints=compatibility)
    owners = sorted({a for a, _ in case['edges']})
    owner_mask = sum(1 << i for i in owners)
    raw_tests = [(mask, label) for mask, label in case['raw_tests']
                 if label or (mask & owner_mask).bit_count() in (0, 1, len(owners))]
    assert len(raw_tests) == 22
    tests = [(extend(case, mask), label) for mask, label in raw_tests]
    negatives = [i for i, (_, label) in enumerate(tests) if not label]
    pairs = list(itertools.combinations(negatives, 2))
    assert all(target(case, raw_tests[a][0] | raw_tests[b][0]) for a, b in pairs)
    path = args.output / 'problem.cnf'
    selected, variables, clauses = emit(path, 18, tests, useful=False, ninputs=41,
        order_max=True, order_lex=True, phase_seed=phase, positive_live=True,
        negative_live=True, incomparable=True, negative_join_pairs=pairs)
    solver = Solver(args.seed + 1)
    for op, left, right in selected:
        for literal in [op] + left + right:
            solver.freeze(literal)
    with path.open() as source:
        for line in source:
            if not line.startswith('p'):
                solver.add(*map(int, line.split()[:-1]))
    with (args.output / 'extra-clauses.cnfpart').open('w') as journal:
        cnf = LiveCNF(solver, variables, clauses, journal)
        support_constraints(cnf, selected, 41, 14)
        first_orbit_constraints(cnf, selected, symmetry)
        compatibility(cnf, selected, case)
        levels = cnf.count_row([-op for op, _, _ in selected], 5)
        cnf.clause(levels[5])
        journal.flush()
        stamp('ONE-OWNER PHASE SEARCH', len(tests), 'tests', cnf.variables, cnf.clauses)
        start = time.monotonic()
        result = solver.solve(args.seconds)
        report = dict(result=result, seconds=round(time.monotonic() - start, 2),
                      scope='Approximate phase search; full correctness checked separately.')
        stamp('RESULT', result, report['seconds'])
        if result == 10:
            gates = model(solver, selected)
            assert all(evaluate(gates, mask, 41) == label for mask, label in tests)
            checked = 0
            for mask in range(1 << 14):
                if (mask & owner_mask).bit_count() <= 1 or mask.bit_count() <= 2:
                    assert evaluate(gates, extend(case, mask), 41) == target(case, mask)
                    checked += 1
            truth = packed_verification(case, gates)
            assert truth['false_negatives'] == 0
            full = assemble(case, gates)
            geometry = json.loads((Path(__file__).resolve().parents[2] /
                                   'circuit_search' / 'geometry.json').read_text())
            full_tests = [((1 << a) | (1 << b), True) for a, b in geometry['edges']]
            full_tests += [(p | (l << 13), False) for p, l in geometry['maximal_independent_sets']]
            full_failures = [mask for mask, label in full_tests if evaluate(full, mask, 26) != label]
            exact = truth['false_positives'] == 0
            if exact:
                assert not full_failures
            report.update(gates=gates, full_circuit=full, truth=truth,
                          one_owner_and_small_inputs_checked=checked,
                          full_boundary_failures=full_failures, exact=exact,
                          status='Exact witness' if exact else 'Approximation; not a witness')
            name = 'EXACT-GADGET.json' if exact else 'APPROXIMATE-GADGET.json'
            (args.output / name).write_text(json.dumps(report))
        (args.output / 'result.json').write_text(json.dumps(report))
    solver.close()


if __name__ == '__main__':
    main()
