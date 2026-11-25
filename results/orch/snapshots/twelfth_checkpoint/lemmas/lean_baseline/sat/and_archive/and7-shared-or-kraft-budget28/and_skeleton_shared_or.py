import argparse
import itertools
import json
import runpy
import time
from pathlib import Path

from and_skeleton_budget_run import assemble_separate, occurrence_count, verify_assembly
from and_skeleton_sat import (
    CNF, Solver, boundary, conjunction, decode, disjunction, normalize,
    side_value, stamp, thresholds, truth_columns,
)


def validate_case(case, full_data):
    raw, available = case['raw_inputs'], case['inputs']
    assert raw == 17 and available == 42 and len(case['features']) == 25
    positives, negatives = boundary(raw, case['edges'])
    assert set(map(tuple, case['raw_tests'])) == {(m, 1) for m in positives} | {(m, 0) for m in negatives}
    assert len(case['raw_tests']) == 76
    full_edges = set(map(tuple, full_data['edges']))
    assert full_data['inputs'] == 26 and len(case['input_original']) == raw
    assert len(set(case['input_original'])) == raw
    assert {(case['input_original'][a], case['input_original'][b]) for a, b in case['edges']} <= full_edges
    for feature in case['features']:
        source = feature['raw_indices']
        assert source == sorted(set(source)) and len(source) in (2, 3)
        assert all(0 <= v < raw for v in source)
        assert feature['original_lines'] == [case['input_original'][v] for v in source]
        assert all((feature['outside_owner'], line) in full_edges for line in feature['original_lines'])
    groups = case['optional_prefix_groups']
    assert len(groups) == 6 and all(len(group) == 3 for group in groups)
    flattened = list(itertools.chain.from_iterable(groups))
    assert len(set(flattened)) == len(flattened)
    for group in groups:
        features = [case['features'][v - raw] for v in group]
        assert all(f['kind'] == 'optional_pair' for f in features)
        assert len({f['outside_owner'] for f in features}) == 1
        support = sorted(set(itertools.chain.from_iterable(f['raw_indices'] for f in features)))
        assert len(support) == 3
        assert {tuple(f['raw_indices']) for f in features} == set(itertools.combinations(support, 2))
    assert set(flattened) == {raw + i for i, f in enumerate(case['features']) if f['kind'] == 'optional_pair'}
    assert case['outside_base_cost'] == 34 and case['final_or_cost'] == 1
    assert {o['outside_point'] for o in case['outside_owners']} == set(range(13)) - set(case['group'])
    for owner in case['outside_owners']:
        assert set(owner['original_neighbors']) == {v for p, v in full_edges if p == owner['outside_point']}
    for (mask, label), (encoded, encoded_label) in zip(case['raw_tests'], case['tests'], strict=True):
        values = available_values(case, mask)
        assert encoded == sum(1 << v for v, value in enumerate(values) if value)
        assert label == encoded_label


def available_values(case, mask):
    values = [bool(mask >> v & 1) for v in range(case['raw_inputs'])]
    return values + [any(values[v] for v in f['raw_indices']) for f in case['features']]


def evaluate(case, skeleton, mask):
    values = available_values(case, mask)
    values.append(any(values[v] for v in skeleton['shared_or']))
    for gate in skeleton['and_gates']:
        values.append(any(values[v] for v in gate['left']) and any(values[v] for v in gate['right']))
    return values, any(values[v] for v in skeleton['output'])


def lift_phase(case, source):
    raw, available = case['raw_inputs'], case['inputs']
    if 'shared_or' in source:
        assert source['inputs'] == available
        normalized = normalize({'inputs': available + 1, 'and_gates': source['and_gates'], 'output': source['output']})
        normalized['inputs'] = available
        normalized['shared_or'] = sorted(set(source['shared_or']))
        assert normalized['shared_or'] and all(0 <= v < available for v in normalized['shared_or'])
        return normalized
    from and_skeleton_correlated import lift_phase as lift_plain
    source = lift_plain(case, source)
    cones = [set(g[side]) for g in source['and_gates'] for side in ('left', 'right')] + [set(source['output'])]
    pairs = {pair for cone in cones for pair in itertools.combinations(sorted(v for v in cone if v < available), 2)}
    assert pairs
    pair = min(pairs, key=lambda pair: (-sum(set(pair) <= cone for cone in cones), pair))
    def move_cone(cone):
        cone = set(cone)
        moved = {v if v < available else v + 1 for v in cone}
        if set(pair) <= cone:
            moved.difference_update(pair)
            moved.add(available)
        return sorted(moved)
    result = {'inputs': available, 'shared_or': list(pair),
              'and_gates': [{side: move_cone(g[side]) for side in ('left', 'right')} for g in source['and_gates']],
              'output': move_cone(source['output'])}
    return lift_phase(case, result)


def encode_assignment(cnf, case, shared, selected, output, seed, raw_literals, hint_mask):
    hints, _ = evaluate(case, seed, hint_mask)
    values = raw_literals.copy()
    for i, feature in enumerate(case['features']):
        terms = [raw_literals[v] for v in feature['raw_indices']]
        value = 1 if 1 in terms else disjunction(cnf, [v for v in terms if v != -1], hints[case['raw_inputs'] + i])
        values.append(value)
    values.append(side_value(cnf, shared, values, seed['shared_or'], hints))
    sides = []
    for i, ((left, right), gate) in enumerate(zip(selected, seed['and_gates'])):
        a = side_value(cnf, left, values, gate['left'], hints)
        b = side_value(cnf, right, values, gate['right'], hints)
        sides.append((a, b))
        values.append(conjunction(cnf, a, b, hints[case['inputs'] + 1 + i]))
    return values, side_value(cnf, output, values, seed['output'], hints), sides


def emit(path, case, seed, maximum_gates, fixed=False, kraft=False):
    raw, n = case['raw_inputs'], case['inputs'] + 1
    seed = lift_phase(case, seed)
    cnf = CNF(path)
    shared = [cnf.var(v in seed['shared_or']) for v in range(n - 1)]
    cnf.clause(*shared)
    selected = []
    for i, gate in enumerate(seed['and_gates']):
        left = [cnf.var(v in gate['left']) for v in range(n + i)]
        right = [cnf.var(v in gate['right']) for v in range(n + i)]
        selected.append((left, right))
        cnf.clause(*left)
        cnf.clause(*right)
        equal, hint_equal = 1, True
        for v, (a, b) in enumerate(zip(left, right)):
            cnf.clause(-equal, a, -b)
            hint_equal = hint_equal and ((v in gate['left']) == (v in gate['right']))
            next_equal = cnf.var(hint_equal)
            cnf.clause(-next_equal, equal)
            cnf.clause(-next_equal, -a, b)
            cnf.clause(-next_equal, a, -b)
            cnf.clause(-equal, -a, -b, next_equal)
            cnf.clause(-equal, a, b, next_equal)
            equal = next_equal
    output = [cnf.var(v in seed['output']) for v in range(n + len(selected))]
    cnf.clause(*output)
    positives, negatives = [], []
    for mask, label in case['raw_tests']:
        values, final, sides = encode_assignment(cnf, case, shared, selected, output, seed,
                                                [1 if mask >> v & 1 else -1 for v in range(raw)], mask)
        cnf.clause(final if label else -final)
        if label:
            positives.append(values[n:])
        else:
            hints, _ = evaluate(case, seed, mask)
            negatives.append((sides, [(any(hints[v] for v in gate['left']),
                                       any(hints[v] for v in gate['right'])) for gate in seed['and_gates']]))
    if kraft:
        from and_skeleton_kraft import add_equal_child_kraft
        add_equal_child_kraft(cnf, negatives, len(selected))
    for i in range(len(selected)):
        cnf.clause(*(values[i] for values in positives))
        left_only, right_only = [], []
        for sides, hints in negatives:
            a, b = sides[i]
            ha, hb = hints[i]
            left_only.append(conjunction(cnf, a, -b, ha and not hb))
            right_only.append(conjunction(cnf, b, -a, hb and not ha))
        cnf.clause(*left_only)
        cnf.clause(*right_only)
    possible = [0] + [1 << v for v in range(raw)] + [(1 << a) | (1 << b) for a, b in itertools.combinations(range(raw), 2)]
    possible = [m for m in possible if not any(m >> a & 1 and m >> b & 1 for a, b in case['edges'])]
    def score(mask):
        values, final = evaluate(case, seed, mask)
        return not any(values[n:]), final, mask.bit_count(), mask
    hint_mask = min(possible, key=score)
    dirty_inputs = [cnf.var(bool(hint_mask >> v & 1)) for v in range(raw)]
    count = thresholds(cnf, [(literal, bool(hint_mask >> i & 1)) for i, literal in enumerate(dirty_inputs)], 2)
    cnf.clause(-count[3])
    for a, b in case['edges']:
        cnf.clause(-dirty_inputs[a], -dirty_inputs[b])
    values, final, _ = encode_assignment(cnf, case, shared, selected, output, seed, dirty_inputs, hint_mask)
    cnf.clause(-final)
    cnf.clause(*values[n:])
    used = {}
    phase_sources = set(seed['shared_or']) | set(seed['output']) | {v for gate in seed['and_gates'] for side in ('left', 'right') for v in gate[side]}
    for group in case['optional_prefix_groups']:
        for feature in group:
            occurrences = [shared[feature]] + [side[feature] for left, right in selected for side in (left, right)] + [output[feature]]
            used[feature] = disjunction(cnf, occurrences, feature in phase_sources)
        for a, b in itertools.combinations(group, 2):
            cnf.clause(-used[a], -used[b])
    active = [(literal, v in seed['shared_or']) for v, literal in enumerate(shared)]
    if fixed:
        for v, literal in enumerate(shared):
            cnf.clause(literal if v in seed['shared_or'] else -literal)
    for (left, right), gate in zip(selected, seed['and_gates']):
        for literals, side in ((left, gate['left']), (right, gate['right'])):
            active.extend((literal, v in side) for v, literal in enumerate(literals))
            if fixed:
                for v, literal in enumerate(literals):
                    cnf.clause(literal if v in side else -literal)
    active.extend((literal, v in seed['output']) for v, literal in enumerate(output))
    if fixed:
        for v, literal in enumerate(output):
            cnf.clause(literal if v in seed['output'] else -literal)
    bound = maximum_gates + len(selected) + 2
    count = thresholds(cnf, active, bound)
    cnf.clause(-count[bound + 1])
    cnf.finish()
    return shared, selected, output, dirty_inputs, cnf.variables, cnf.clauses, seed


def count_occurrences(skeleton):
    return len(skeleton['shared_or']) + sum(len(g['left']) + len(g['right']) for g in skeleton['and_gates']) + len(skeleton['output'])


def assemble_core(skeleton):
    available = skeleton['inputs']
    assert skeleton['shared_or'] and all(0 <= v < available for v in skeleton['shared_or'])
    gates = []
    wires = list(range(available))
    def make_or(sources):
        assert sources
        result = wires[sources[0]]
        for v in sources[1:]:
            gates.append([1, result, wires[v]])
            result = available + len(gates) - 1
        return result
    wires.append(make_or(skeleton['shared_or']))
    for i, gate in enumerate(skeleton['and_gates']):
        assert all(0 <= v < available + 1 + i for side in ('left', 'right') for v in gate[side])
        left, right = make_or(gate['left']), make_or(gate['right'])
        gates.append([0, left, right])
        wires.append(available + len(gates) - 1)
    output = make_or(skeleton['output'])
    expected = count_occurrences(skeleton) - len(skeleton['and_gates']) - 2
    assert len(gates) == expected
    return {'inputs': available, 'gates': gates, 'output': output, 'gate_count': len(gates)}


def verify_core(case, skeleton, mask, maximum_gates):
    raw, available = case['raw_inputs'], case['inputs']
    n = available + 1
    assert skeleton['inputs'] == available
    assert skeleton['shared_or'] and all(0 <= v < available for v in skeleton['shared_or'])
    assert all(0 <= v < n + len(skeleton['and_gates']) for v in skeleton['output'])
    assert all(gate['left'] and gate['right'] for gate in skeleton['and_gates']) and skeleton['output']
    source_refs = set(skeleton['shared_or']) | set(skeleton['output']) | {v for gate in skeleton['and_gates'] for side in ('left', 'right') for v in gate[side]}
    assert all(len(source_refs.intersection(group)) <= 1 for group in case['optional_prefix_groups'])
    for sample, label in case['raw_tests']:
        assert evaluate(case, skeleton, sample)[1] == bool(label)
    assert 0 <= mask < (1 << raw) and mask.bit_count() <= 2
    assert not any(mask >> a & 1 and mask >> b & 1 for a, b in case['edges'])
    values, final = evaluate(case, skeleton, mask)
    assert not final and any(values[n:])
    for i, gate in enumerate(skeleton['and_gates']):
        assert all(0 <= v < n + i for side in ('left', 'right') for v in gate[side])
        live, left_only, right_only = False, False, False
        for sample, label in case['raw_tests']:
            values, _ = evaluate(case, skeleton, sample)
            a = any(values[v] for v in gate['left'])
            b = any(values[v] for v in gate['right'])
            live |= bool(label) and a and b
            left_only |= not label and a and not b
            right_only |= not label and b and not a
        assert live and left_only and right_only
    assert count_occurrences(skeleton) <= maximum_gates + len(skeleton['and_gates']) + 2
    core = assemble_core(skeleton)
    assert core['gate_count'] <= maximum_gates
    values = truth_columns(raw)
    for feature in case['features']:
        value = 0
        for v in feature['raw_indices']:
            value |= values[v]
        values.append(value)
    expected = 0
    for a, b in case['edges']:
        expected |= values[a] & values[b]
    for op, a, b in core['gates']:
        values.append(values[a] | values[b] if op else values[a] & values[b])
    assert values[core['output']] == expected
    return core


def solve(case, full_data, source, folder, maximum_gates, seconds, attempts=1, fixed=False, calibration=False, kraft=False):
    validate_case(case, full_data)
    folder.mkdir(parents=True, exist_ok=True)
    shared, selected, output, dirty_inputs, variables, clauses, seed = emit(folder / 'model.cnf', case, source, maximum_gates, fixed, kraft)
    (folder / 'phase.json').write_text(json.dumps(seed))
    (folder / 'model-spec.json').write_text(json.dumps({
        'raw_inputs': 17, 'available_inputs': 42, 'paid_shared_OR_nodes': 1, 'AND_nodes': len(selected),
        'cost': 'all source occurrences minus AND nodes minus shared OR nodes minus one',
        'maximum_core_gates': maximum_gates, 'outside_cost': 35,
        'feature_correlations': case['features'], 'at_most_one_used_optional_prefix_per_group': case['optional_prefix_groups'],
        'all_OR_cones_nonempty': True, 'positive_live_and_child_incomparability': 'construction-profile restrictions',
        'dirty_required': True, 'fixed_phase_calibration': fixed,
        'equal_child_kraft_enabled': kraft,
        'maximum_kraft_weight_sum': (1 << len(selected)) if kraft else None,
        'maximum_kraft_slack_charge': ((1 << len(selected)) - 52) if kraft else None,
        'scope': 'sufficient construction with one paid shared source-OR, separate remaining cones and compatible zero-extra outside prefixes; no completeness claim',
    }, indent=2))
    solver = Solver(57189)
    for literal in shared:
        solver.freeze(literal)
    for left, right in selected:
        for literal in left + right:
            solver.freeze(literal)
    for literal in output + dirty_inputs:
        solver.freeze(literal)
    with (folder / 'model.cnf').open() as handle:
        for line in handle:
            if not line.startswith('p'):
                solver.add(*map(int, line.split()[:-1]))
    stamp('CORRELATED-SHARED-OR-BUDGET', 'raw17', 'available42', 'ANDnodes', len(selected),
          'core-gates', maximum_gates, 'variables', variables, 'clauses', clauses)
    result = 0
    for attempt in range(attempts):
        start = time.monotonic()
        result = solver.solve(seconds)
        stamp('ATTEMPT', attempt, 'SOLVER', result, 'SECONDS', round(time.monotonic() - start, 4))
        if result != 0:
            break
    if result == 10:
        answer = decode(solver, selected, output, 43)
        answer['inputs'] = 42
        answer['shared_or'] = [v for v, literal in enumerate(shared) if solver.truth(literal)]
        mask = sum(1 << i for i, literal in enumerate(dirty_inputs) if solver.truth(literal))
        core = verify_core(case, answer, mask, maximum_gates)
        if kraft:
            from and_skeleton_kraft import verify_equal_child_kraft
            kraft_check = verify_equal_child_kraft(case, answer, evaluate)
        else:
            kraft_check = None
        assembler_path = Path(__file__).resolve().parents[2] / 'circuit_search' / 'assemble_joint_four.py'
        assemble_joint = runpy.run_path(str(assembler_path))['assemble_joint']
        full, metadata = assemble_joint(case, core['gates'], core['output'])
        assert all(op in (0, 1) and 0 <= a < 26 + i and 0 <= b < 26 + i
                   for i, (op, a, b) in enumerate(full))
        assert metadata['prefix_extra_cost'] == 0 and metadata['outside_gates'] == 34
        assert len(full) <= maximum_gates + 35
        verify_assembly(full_data, {'gates': full, 'output': 25 + len(full)})
        met = len(full) <= 63
        result_object = {'inputs': 26, 'gates': full, 'output': 25 + len(full),
                         'gate_count': len(full), 'target_met': met, 'calibration': calibration,
                         'core': core, 'skeleton': answer, 'dirty_raw_input': mask,
                         'assembly': metadata, 'core_full_truth_verified': True, 'full_truth_verified': True,
                         'equal_child_kraft': kraft_check}
        name = 'CALIBRATION-CIRCUIT.json' if calibration else ('EXACT-FULL63-CIRCUIT.json' if met else 'EXACT-OVERBUDGET-CIRCUIT.json')
        (folder / name).write_text(json.dumps(result_object))
        stamp('EXACT CORRELATED CIRCUIT', 'full-gates', len(full), 'target-met', met, 'calibration', calibration)
    elif result == 20:
        stamp('UNSAT FOR STATED CORRELATED CONSTRUCTION PROFILE ONLY')
    else:
        stamp('UNKNOWN FOR STATED CORRELATED CONSTRUCTION PROFILE')
    solver.close()
    return result


def main():
    parser = argparse.ArgumentParser(description='Raw17/available42 AND-subset construction with one paid shared source-OR and compatible outside prefixes')
    parser.add_argument('packet', type=Path)
    parser.add_argument('full_data', type=Path)
    parser.add_argument('phase', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--gates', type=int, default=28)
    parser.add_argument('--seconds', type=int, default=300)
    parser.add_argument('--attempts', type=int, default=4)
    parser.add_argument('--kraft', action='store_true')
    args = parser.parse_args()
    packet = json.loads(args.packet.read_text())
    solve(packet[0], json.loads(args.full_data.read_text()), json.loads(args.phase.read_text()),
          args.output, args.gates, args.seconds, args.attempts, kraft=args.kraft)


if __name__ == '__main__':
    main()
