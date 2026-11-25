import argparse
import json
import time
from pathlib import Path

from and_skeleton_budget_run import assemble_separate, emit_budget, occurrence_count, verify_assembly
from and_skeleton_minimal import verify_minimal_conditions
from and_skeleton_sat import Solver, decode, stamp, verify


def descend(data, seed, folder, upper, start, target, seconds, attempts,
             dirty=True, positive_live=True, child_incomparable=True, calibration=False):
    assert 0 <= target <= start <= upper
    folder.mkdir(parents=True, exist_ok=True)
    counters = {}
    selected, output, dirty_inputs, variables, clauses, seed, _ = emit_budget(
        folder, data, seed, upper, dirty, positive_live, child_incomparable,
        counter_sink=counters)
    row = counters['row']
    (folder / 'phase.json').write_text(json.dumps(seed))
    (folder / 'model-spec.json').write_text(json.dumps({
        'construction': 'separate nonempty binary OR trees for all AND sides and final output',
        'AND_nodes': len(selected), 'upper_gate_budget': upper,
        'first_gate_budget': start, 'target_gate_budget': target,
        'dirty_required': dirty,
        'positive_live_profile': positive_live, 'negative_child_incomparability_profile': child_incomparable,
        'bound_assumptions_reapplied_each_solve': True,
        'same_solver_retained_across_budgets': True,
        'UNSAT_scope': 'only the current gate budget in the stated restricted construction profile',
    }, indent=2))
    solver = Solver(57189)
    for left, right in selected:
        for literal in left + right:
            solver.freeze(literal)
    for literal in output + (dirty_inputs or []) + row:
        if abs(literal) != 1:
            solver.freeze(literal)
    with (folder / 'model.cnf').open() as source:
        for line in source:
            if not line.startswith('p'):
                solver.add(*map(int, line.split()[:-1]))
    stamp('BUDGET-DESCENT', 'ANDnodes', len(selected), 'upper', upper,
          'start', start, 'target', target, 'variables', variables, 'clauses', clauses)
    budget = start
    history = []
    while budget >= target:
        result = 0
        bound_literal = -row[budget + len(selected) + 2]
        for attempt in range(attempts):
            solver.lib.ccadical_assume(solver.ptr, bound_literal)
            begin = time.monotonic()
            result = solver.solve(seconds)
            stamp('BUDGET', budget, 'ATTEMPT', attempt, 'SOLVER', result,
                  'SECONDS', round(time.monotonic() - begin, 4))
            if result != 0:
                break
        if result != 10:
            history.append({'budget': budget, 'result': result,
                            'scope': 'restricted construction at this budget only'})
            (folder / 'history.json').write_text(json.dumps(history, indent=2))
            break
        answer = decode(solver, selected, output, data['inputs'])
        mask = (sum(1 << i for i, literal in enumerate(dirty_inputs) if solver.truth(literal))
                if dirty_inputs is not None else None)
        verify(data, answer, mask, full=True)
        verify_minimal_conditions(data, answer, positive_live, child_incomparable)
        assert all(gate['left'] and gate['right'] for gate in answer['and_gates']) and answer['output']
        assert occurrence_count(answer) <= budget + len(selected) + 1
        circuit = assemble_separate(answer)
        verify_assembly(data, circuit)
        assert circuit['gate_count'] <= budget
        met = circuit['gate_count'] <= target
        circuit.update({'skeleton': answer, 'dirty_input': mask,
                        'full_truth_verified': True, 'target_budget': target,
                        'target_met': met, 'calibration': calibration})
        if calibration:
            name = f'CALIBRATION-CIRCUIT-{circuit["gate_count"]}.json'
        elif met:
            name = 'EXACT-BUDGETED-CIRCUIT.json'
        else:
            name = f'EXACT-OVERBUDGET-CIRCUIT-{circuit["gate_count"]}.json'
        (folder / name).write_text(json.dumps(circuit))
        history.append({'budget': budget, 'result': 10,
                        'actual_gate_count': circuit['gate_count'], 'target_met': met})
        (folder / 'history.json').write_text(json.dumps(history, indent=2))
        stamp('EXACT CIRCUIT', 'actual-gates', circuit['gate_count'],
              'target-met', met, 'calibration', calibration)
        if met:
            break
        budget = circuit['gate_count'] - 1
    (folder / 'history.json').write_text(json.dumps(history, indent=2))
    solver.close()
    return history


def main():
    parser = argparse.ArgumentParser(description='Incremental sufficient gate-budget descent; no OR-sharing completeness claim')
    parser.add_argument('problem', type=Path)
    parser.add_argument('seed', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--upper', type=int, required=True)
    parser.add_argument('--start', type=int, required=True)
    parser.add_argument('--target', type=int, required=True)
    parser.add_argument('--seconds', type=int, default=300)
    parser.add_argument('--attempts', type=int, default=4)
    args = parser.parse_args()
    descend(json.loads(args.problem.read_text()), json.loads(args.seed.read_text()),
            args.output, args.upper, args.start, args.target, args.seconds, args.attempts)


if __name__ == '__main__':
    main()
