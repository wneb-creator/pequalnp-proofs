import argparse
import json
import runpy
import time
from pathlib import Path

from and_skeleton_correlated import emit, validate_case, verify_core
from and_skeleton_budget_run import verify_assembly
from and_skeleton_sat import CNF, Solver, decode, stamp, thresholds


def run(case, full_data, source, folder, gates, seconds, first, maximum, step,
         calibration=False):
    assert 0 <= first <= maximum and step > 0
    validate_case(case, full_data)
    folder.mkdir(parents=True, exist_ok=True)
    selected, output, dirty_inputs, variables, clauses, seed = emit(folder / 'base.cnf', case, source, gates)
    edits = CNF(folder / 'edits.cnf')
    edits.variables = variables
    changed = []
    for (left, right), gate in zip(selected, seed['and_gates']):
        for literals, side in ((left, gate['left']), (right, gate['right'])):
            changed.extend((-literal if v in side else literal, False)
                           for v, literal in enumerate(literals))
    changed.extend((-literal if v in seed['output'] else literal, False)
                   for v, literal in enumerate(output))
    row = thresholds(edits, changed, maximum)
    edits.finish()
    with (folder / 'model.cnf').open('w') as target:
        target.write(f'p cnf {edits.variables} {clauses + edits.clauses}\n')
        for name in ['base.cnf', 'edits.cnf']:
            with (folder / name).open() as source_file:
                for line in source_file:
                    if not line.startswith('p'):
                        target.write(line)
    radii = list(range(first, maximum + 1, step))
    if radii[-1] != maximum:
        radii.append(maximum)
    (folder / 'phase.json').write_text(json.dumps(seed))
    (folder / 'model-spec.json').write_text(json.dumps({
        'raw_inputs': 17, 'available_inputs': 42, 'AND_nodes': len(selected),
        'maximum_core_gates': gates, 'outside_cost': 35,
        'compatible_zero_extra_prefixes': case['optional_prefix_groups'],
        'selector_edit_metric': 'Hamming distance over all left/right/output membership bits',
        'radii': radii, 'seconds_per_radius': seconds,
        'same_solver_retained': True, 'radius_assumption_reapplied': True,
        'positive_live_and_child_incomparability': 'construction-profile restrictions',
        'dirty_required': True,
        'UNSAT_scope': 'only this Hamming-radius neighborhood of the stated correlated construction profile',
    }, indent=2))
    solver = Solver(57189)
    for left, right in selected:
        for literal in left + right:
            solver.freeze(literal)
    for literal in output + dirty_inputs + row:
        if abs(literal) != 1:
            solver.freeze(literal)
    with (folder / 'model.cnf').open() as handle:
        for line in handle:
            if not line.startswith('p'):
                solver.add(*map(int, line.split()[:-1]))
    history = []
    stamp('CORRELATED-SELECTOR-EDITS', 'core-gates', gates, 'radii', radii,
          'variables', edits.variables, 'clauses', clauses + edits.clauses)
    for radius in radii:
        solver.lib.ccadical_assume(solver.ptr, -row[radius + 1])
        start = time.monotonic()
        result = solver.solve(seconds)
        stamp('LOCAL-RADIUS', radius, 'SOLVER', result,
              'SECONDS', round(time.monotonic() - start, 4))
        entry = {'radius': radius, 'result': result, 'scope': 'local neighborhood only'}
        history.append(entry)
        (folder / 'history.json').write_text(json.dumps(history, indent=2))
        if result != 10:
            continue
        answer = decode(solver, selected, output, 42)
        distance = sum(len(set(old[side]) ^ set(new[side]))
                       for old, new in zip(seed['and_gates'], answer['and_gates'])
                       for side in ('left', 'right'))
        distance += len(set(seed['output']) ^ set(answer['output']))
        assert distance <= radius
        mask = sum(1 << i for i, literal in enumerate(dirty_inputs) if solver.truth(literal))
        core = verify_core(case, answer, mask, gates)
        assembler = Path(__file__).resolve().parents[2] / 'circuit_search' / 'assemble_joint_four.py'
        full, metadata = runpy.run_path(str(assembler))['assemble_joint'](case, core['gates'], core['output'])
        assert metadata['prefix_extra_cost'] == 0 and metadata['outside_gates'] == 34
        assert len(full) <= gates + 35
        assert all(op in (0, 1) and 0 <= a < 26 + i and 0 <= b < 26 + i
                   for i, (op, a, b) in enumerate(full))
        verify_assembly(full_data, {'gates': full, 'output': 25 + len(full)})
        met = len(full) <= 63
        obj = {'inputs': 26, 'gates': full, 'output': 25 + len(full),
               'gate_count': len(full), 'target_met': met, 'calibration': calibration,
               'core': core, 'skeleton': answer, 'dirty_raw_input': mask,
               'assembly': metadata, 'selector_distance': distance,
               'core_full_truth_verified': True, 'full_truth_verified': True}
        name = 'CALIBRATION-CIRCUIT.json' if calibration else ('EXACT-FULL63-CIRCUIT.json' if met else 'EXACT-OVERBUDGET-CIRCUIT.json')
        (folder / name).write_text(json.dumps(obj))
        entry.update({'selector_distance': distance, 'actual_full_gates': len(full), 'target_met': met})
        (folder / 'history.json').write_text(json.dumps(history, indent=2))
        stamp('EXACT CORRELATED CIRCUIT', 'full-gates', len(full), 'target-met', met, 'calibration', calibration)
        break
    solver.close()
    return history


def main():
    parser = argparse.ArgumentParser(description='Increasing local selector-edit bounds on the exact correlated-prefix budget model')
    parser.add_argument('packet', type=Path)
    parser.add_argument('full_data', type=Path)
    parser.add_argument('phase', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--gates', type=int, default=28)
    parser.add_argument('--seconds', type=int, default=60)
    parser.add_argument('--first', type=int, default=4)
    parser.add_argument('--maximum', type=int, default=32)
    parser.add_argument('--step', type=int, default=4)
    args = parser.parse_args()
    run(json.loads(args.packet.read_text())[0], json.loads(args.full_data.read_text()),
        json.loads(args.phase.read_text()), args.output, args.gates, args.seconds,
        args.first, args.maximum, args.step)


if __name__ == '__main__':
    main()
