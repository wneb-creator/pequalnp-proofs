import argparse
import json
import time
from pathlib import Path

from and_skeleton_sat import Solver, decode, emit, stamp, verify
from and_skeleton_symmetry import rephase, representative_clauses, validate_symmetry


def solve_orbits(data, seed, symmetry, folder, seconds, attempts=1, calibration=False,
                 positive_live=False, child_incomparable=False):
    folder.mkdir(parents=True, exist_ok=True)
    representatives, _ = validate_symmetry(data, symmetry)
    seed, phase_metadata = rephase(data, seed, symmetry)
    if positive_live or child_incomparable:
        from and_skeleton_minimal import emit_minimal
        emitted = emit_minimal(folder / 'model.cnf', data, seed, dirty=True,
                               positive_live=positive_live,
                               child_incomparable=child_incomparable)
    else:
        emitted = emit(folder / 'model.cnf', data, seed, dirty=True)
    selected, output, dirty_inputs, nvars, nclauses, seed = emitted
    extra_clauses = representative_clauses(dirty_inputs, representatives)
    (folder / 'phase.json').write_text(json.dumps(seed))
    (folder / 'orbit-clauses.json').write_text(json.dumps(extra_clauses))
    spec = {
        'declared_binary_AND_nodes': len(selected),
        'OR_subsets': 'arbitrary raw and earlier AND subsets; empty means false',
        'constants': 'false via empty OR; no true constant',
        'unused_nodes': 'allowed',
        'fanin_cardinality_caps': None,
        'side_order': 'commutative lexicographic orientation only',
        'dirty_required': True,
        'dirty_pair_representatives': representatives,
        'positive_live': positive_live,
        'negative_child_incomparability': child_incomparable,
        'minimality_cut_scope': 'optional cuts require an independent lower bound equal to the declared AND count',
        'phase_relabeling': phase_metadata,
        'total_gate_bound_established': False,
        'UNSAT_scope': 'declared AND-count abstraction with stated constraints; no total gate lower bound',
    }
    (folder / 'model-spec.json').write_text(json.dumps(spec, indent=2))
    solver = Solver(57189)
    for left, right in selected:
        for literal in left + right:
            solver.freeze(literal)
    for literal in output + dirty_inputs:
        solver.freeze(literal)
    with (folder / 'model.cnf').open() as source:
        for line in source:
            if not line.startswith('p'):
                solver.add(*map(int, line.split()[:-1]))
    for clause in extra_clauses:
        solver.add(*clause)
    stamp('AND-SKELETON-ORBITS', 'inputs', data['inputs'], 'ANDnodes', len(selected),
          'tests', len(data['tests']), 'variables', nvars,
          'clauses', nclauses + len(extra_clauses),
          'dirty-pairs', representatives, 'NO-TOTAL-GATE-BOUND')
    result = 0
    for attempt in range(attempts):
        begin = time.monotonic()
        result = solver.solve(seconds)
        stamp('ATTEMPT', attempt, 'SOLVER', result,
              'SECONDS', round(time.monotonic() - begin, 4))
        if result != 0:
            break
    if result == 10:
        answer = decode(solver, selected, output, data['inputs'])
        dirty_mask = sum(1 << i for i, lit in enumerate(dirty_inputs) if solver.truth(lit))
        assert dirty_mask in [sum(1 << v for v in pair) for pair in representatives]
        assert verify(data, answer, dirty_mask, full=True)
        if positive_live or child_incomparable:
            from and_skeleton_minimal import verify_minimal_conditions
            verify_minimal_conditions(data, answer, positive_live, child_incomparable)
        answer.update({
            'edges': data['edges'],
            'input_original': data.get('input_original', list(range(data['inputs']))),
            'and_count': len(selected),
            'exact_boundary_verified': True, 'full_truth_verified': True,
            'dirty_input': dirty_mask, 'calibration': calibration,
            'total_gate_bound_established': False,
            'status': 'exact AND skeleton; OR assembly and total gate count are not established',
        })
        name = 'CALIBRATION-AND-SKELETON.json' if calibration else 'EXACT-AND-SKELETON.json'
        (folder / name).write_text(json.dumps(answer))
        stamp('EXACT AND SKELETON', 'ANDnodes', len(selected),
              'dirty_input', dirty_mask, 'NO-TOTAL-GATE-BOUND')
    elif result == 20:
        stamp('UNSAT FOR STATED AND-COUNT ABSTRACTION; NOT A FULL GATE LOWER BOUND')
    else:
        stamp('UNKNOWN FOR STATED AND-COUNT ABSTRACTION')
    solver.close()
    return result


def main():
    parser = argparse.ArgumentParser(description='AND skeleton with independently validated dirty-pair orbit symmetry')
    parser.add_argument('problem', type=Path)
    parser.add_argument('seed', type=Path)
    parser.add_argument('symmetry', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--seconds', type=int, default=300)
    parser.add_argument('--attempts', type=int, default=1)
    parser.add_argument('--positive-live', action='store_true')
    parser.add_argument('--child-incomparable', action='store_true')
    args = parser.parse_args()
    solve_orbits(json.loads(args.problem.read_text()), json.loads(args.seed.read_text()),
                 json.loads(args.symmetry.read_text()), args.output, args.seconds, args.attempts,
                 positive_live=args.positive_live, child_incomparable=args.child_incomparable)


if __name__ == '__main__':
    main()
