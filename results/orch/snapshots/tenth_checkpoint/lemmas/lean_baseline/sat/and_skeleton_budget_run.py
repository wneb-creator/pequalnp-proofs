import argparse
import json
import time
from pathlib import Path

from and_skeleton_minimal import emit_minimal, verify_minimal_conditions
from and_skeleton_sat import CNF, Solver, decode, stamp, thresholds, truth_columns, verify


def occurrence_count(skeleton):
    return sum(len(gate['left']) + len(gate['right']) for gate in skeleton['and_gates']) + len(skeleton['output'])


def assemble_separate(skeleton):
    n = skeleton['inputs']
    gates = []
    wires = list(range(n))

    def disjoin(features):
        assert features
        output = wires[features[0]]
        for feature in features[1:]:
            gates.append([1, output, wires[feature]])
            output = n + len(gates) - 1
        return output

    for item in skeleton['and_gates']:
        left = disjoin(item['left'])
        right = disjoin(item['right'])
        gates.append([0, left, right])
        wires.append(n + len(gates) - 1)
    output = disjoin(skeleton['output'])
    assert len(gates) == occurrence_count(skeleton) - len(skeleton['and_gates']) - 1
    assert all(op in (0, 1) and 0 <= a < n + i and 0 <= b < n + i
               for i, (op, a, b) in enumerate(gates))
    return {'inputs': n, 'gates': gates, 'output': output, 'gate_count': len(gates)}


def verify_assembly(data, circuit):
    values = truth_columns(data['inputs'])
    expected = 0
    for a, b in data['edges']:
        expected |= values[a] & values[b]
    for op, a, b in circuit['gates']:
        values.append(values[a] | values[b] if op else values[a] & values[b])
    assert values[circuit['output']] == expected


def emit_budget(folder, data, seed, maximum_gates, dirty, positive_live, child_incomparable,
                 fixed=False, counter_sink=None):
    emitted = emit_minimal(folder / 'base.cnf', data, seed, dirty=dirty,
                           positive_live=positive_live, child_incomparable=child_incomparable)
    selected, output, dirty_inputs, variables, clauses, seed = emitted
    bound = maximum_gates + len(selected) + 1
    assert bound >= 0
    extra = CNF(folder / 'budget.cnf')
    extra.variables = variables
    active = []
    for (left, right), gate in zip(selected, seed['and_gates']):
        extra.clause(*left)
        extra.clause(*right)
        active.extend((literal, v in gate['left']) for v, literal in enumerate(left))
        active.extend((literal, v in gate['right']) for v, literal in enumerate(right))
        if fixed:
            for literals, side in ((left, gate['left']), (right, gate['right'])):
                for v, literal in enumerate(literals):
                    extra.clause(literal if v in side else -literal)
    extra.clause(*output)
    active.extend((literal, v in seed['output']) for v, literal in enumerate(output))
    if fixed:
        for v, literal in enumerate(output):
            extra.clause(literal if v in seed['output'] else -literal)
    count = thresholds(extra, active, bound)
    if counter_sink is not None:
        counter_sink['row'] = count
    extra.clause(-count[bound + 1])
    extra.finish()
    with (folder / 'model.cnf').open('w') as target:
        target.write(f'p cnf {extra.variables} {clauses + extra.clauses}\n')
        for name in ['base.cnf', 'budget.cnf']:
            with (folder / name).open() as source:
                for line in source:
                    if not line.startswith('p'):
                        target.write(line)
    return selected, output, dirty_inputs, extra.variables, clauses + extra.clauses, seed, bound


def solve_budget(data, seed, folder, maximum_gates, seconds, attempts=1, dirty=True,
                  positive_live=False, child_incomparable=False, fixed=False, calibration=False):
    folder.mkdir(parents=True, exist_ok=True)
    selected, output, dirty_inputs, variables, clauses, seed, bound = emit_budget(
        folder, data, seed, maximum_gates, dirty, positive_live, child_incomparable, fixed)
    (folder / 'phase.json').write_text(json.dumps(seed))
    spec = {
        'construction': 'every AND side and final output has a separate binary OR tree',
        'all_OR_cones_explicitly_nonempty': True,
        'declared_AND_nodes': len(selected), 'maximum_total_gates': maximum_gates,
        'maximum_selector_occurrences': bound,
        'cost_identity': 'selector occurrences minus AND nodes minus one',
        'OR_sharing': 'not modeled; this is a sufficient restricted construction profile',
        'positive_live_profile': positive_live, 'negative_child_incomparability_profile': child_incomparable,
        'dirty_required': dirty, 'fixed_phase_calibration': fixed,
        'UNSAT_scope': 'only the stated separate-OR-tree construction profile and explicit restrictions',
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
    stamp('BUDGETED-AND-SKELETON', 'inputs', data['inputs'], 'ANDnodes', len(selected),
          'maximum-gates', maximum_gates, 'occurrence-bound', bound,
          'variables', variables, 'clauses', clauses, 'RESTRICTED-CONSTRUCTION')
    result = 0
    for attempt in range(attempts):
        start = time.monotonic()
        result = solver.solve(seconds)
        stamp('ATTEMPT', attempt, 'SOLVER', result, 'SECONDS', round(time.monotonic() - start, 4))
        if result != 0:
            break
    if result == 10:
        answer = decode(solver, selected, output, data['inputs'])
        mask = (sum(1 << i for i, literal in enumerate(dirty_inputs) if solver.truth(literal))
                if dirty_inputs is not None else None)
        verify(data, answer, mask, full=True)
        verify_minimal_conditions(data, answer, positive_live, child_incomparable)
        assert all(gate['left'] and gate['right'] for gate in answer['and_gates']) and answer['output']
        assert occurrence_count(answer) <= bound
        circuit = assemble_separate(answer)
        assert circuit['gate_count'] <= maximum_gates
        verify_assembly(data, circuit)
        circuit.update({'skeleton': answer, 'dirty_input': mask, 'calibration': calibration,
                        'exact_full_truth_verified': True, 'construction_profile': spec['construction']})
        name = 'CALIBRATION-CIRCUIT.json' if calibration else 'EXACT-BUDGETED-CIRCUIT.json'
        (folder / name).write_text(json.dumps(circuit))
        stamp('EXACT BUDGETED CIRCUIT', 'actual-gates', circuit['gate_count'], 'dirty-input', mask)
    elif result == 20:
        stamp('UNSAT ONLY FOR STATED RESTRICTED-CONSTRUCTION PROFILE')
    else:
        stamp('UNKNOWN FOR STATED RESTRICTED-CONSTRUCTION PROFILE')
    solver.close()
    return result


def main():
    parser = argparse.ArgumentParser(description='Sufficient total-gate budget through separate OR-cone assembly')
    parser.add_argument('problem', type=Path)
    parser.add_argument('seed', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--gates', type=int, required=True)
    parser.add_argument('--seconds', type=int, default=300)
    parser.add_argument('--attempts', type=int, default=1)
    parser.add_argument('--positive-live', action='store_true')
    parser.add_argument('--child-incomparable', action='store_true')
    args = parser.parse_args()
    solve_budget(json.loads(args.problem.read_text()), json.loads(args.seed.read_text()),
                  args.output, args.gates, args.seconds, args.attempts,
                  positive_live=args.positive_live, child_incomparable=args.child_incomparable)


if __name__ == '__main__':
    main()
