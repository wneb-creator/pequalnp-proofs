import argparse
import json
import time
from pathlib import Path

from and_skeleton_minimal import emit_minimal, verify_minimal_conditions, verify_negative_slack
from and_skeleton_sat import Solver, decode, stamp, verify


def solve_count(data, seed, folder, seconds, attempts=1, dirty=False,
                positive_live=False, child_incomparable=False,
                dirty_pairs=None, negative_slack=None, calibration=False):
    folder.mkdir(parents=True, exist_ok=True)
    selected, output, dirty_inputs, nvars, nclauses, seed = emit_minimal(
        folder / 'model.cnf', data, seed, dirty=dirty,
        positive_live=positive_live, child_incomparable=child_incomparable,
        dirty_pairs=dirty_pairs, negative_slack=negative_slack)
    (folder / 'phase.json').write_text(json.dumps(seed))
    spec = {
        'inputs': data['inputs'], 'declared_binary_AND_nodes': len(selected),
        'OR_subsets': 'arbitrary raw and earlier AND subsets; empty means false',
        'constants': 'false via empty OR; no true constant',
        'dirty_required': dirty, 'allowed_dirty_pairs': dirty_pairs,
        'positive_live': positive_live, 'negative_child_incomparability': child_incomparable,
        'negative_equal_child_weight_slack': negative_slack,
        'negative_weight_definition': 'sum over maximal negatives of (2^(number of equal-child AND nodes) - 1)',
        'minimality_cut_scope': 'requires an independent lower bound equal to the declared AND count',
        'dirty_cut_scope': 'a necessary target-budget condition must be supplied separately',
        'total_gate_bound_established': False,
        'UNSAT_scope': 'declared AND-count abstraction with stated constraints; no total gate lower bound',
    }
    (folder / 'model-spec.json').write_text(json.dumps(spec, indent=2))
    solver = Solver(57189)
    for left, right in selected:
        for literal in left + right:
            solver.freeze(literal)
    for literal in output + (dirty_inputs or []):
        solver.freeze(literal)
    with (folder / 'model.cnf').open() as source:
        for line in source:
            if not line.startswith('p'):
                solver.add(*map(int, line.split()[:-1]))
    stamp('AND-COUNT-MODEL', 'inputs', data['inputs'], 'ANDnodes', len(selected),
          'tests', len(data['tests']), 'variables', nvars, 'clauses', nclauses,
          'dirty', dirty, 'positive-live', positive_live,
          'child-incomparable', child_incomparable, 'negative-equal-child-slack', negative_slack,
          'NO-TOTAL-GATE-BOUND')
    result = 0
    for attempt in range(attempts):
        begin = time.monotonic()
        result = solver.solve(seconds)
        stamp('ATTEMPT', attempt, 'SOLVER', result, 'SECONDS', round(time.monotonic() - begin, 4))
        if result != 0:
            break
    if result == 10:
        answer = decode(solver, selected, output, data['inputs'])
        mask = (sum(1 << i for i, literal in enumerate(dirty_inputs) if solver.truth(literal))
                if dirty_inputs is not None else None)
        verify(data, answer, mask, full=True)
        verify_minimal_conditions(data, answer, positive_live, child_incomparable)
        verify_negative_slack(data, answer, negative_slack)
        if dirty_pairs is not None:
            assert mask in {sum(1 << v for v in pair) for pair in dirty_pairs}
        answer.update({
            'edges': data['edges'],
            'input_original': data.get('input_original', list(range(data['inputs']))),
            'and_count': len(selected), 'exact_boundary_verified': True,
            'full_truth_verified': True, 'dirty_input': mask,
            'calibration': calibration, 'total_gate_bound_established': False,
            'status': 'exact AND skeleton; OR assembly and total gate count are not established',
        })
        name = 'CALIBRATION-AND-SKELETON.json' if calibration else 'EXACT-AND-SKELETON.json'
        (folder / name).write_text(json.dumps(answer))
        stamp('EXACT AND SKELETON', 'ANDnodes', len(selected), 'dirty_input', mask, 'NO-TOTAL-GATE-BOUND')
    elif result == 20:
        stamp('UNSAT FOR STATED AND-COUNT ABSTRACTION; NOT A FULL GATE LOWER BOUND')
    else:
        stamp('UNKNOWN FOR STATED AND-COUNT ABSTRACTION')
    solver.close()
    return result


def main():
    parser = argparse.ArgumentParser(description='Raw-input AND-count synthesis with optional reviewed necessary cuts')
    parser.add_argument('problem', type=Path)
    parser.add_argument('seed', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--seconds', type=int, default=300)
    parser.add_argument('--attempts', type=int, default=1)
    parser.add_argument('--dirty', action='store_true')
    parser.add_argument('--positive-live', action='store_true')
    parser.add_argument('--child-incomparable', action='store_true')
    parser.add_argument('--dirty-pairs', type=Path)
    parser.add_argument('--negative-slack', type=int)
    args = parser.parse_args()
    pairs = json.loads(args.dirty_pairs.read_text()) if args.dirty_pairs else None
    solve_count(json.loads(args.problem.read_text()), json.loads(args.seed.read_text()),
                args.output, args.seconds, args.attempts, args.dirty,
                args.positive_live, args.child_incomparable, pairs, args.negative_slack)


if __name__ == '__main__':
    main()
