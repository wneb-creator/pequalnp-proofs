#!/usr/bin/env python3
"""Validate an auxiliary selected-DAG packing example, not a gap refutation."""
import argparse
import json
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('witness', type=Path)
args = parser.parse_args()
w = json.loads(args.witness.read_text())
assert isinstance(w, dict)
gates = w['gates']
outputs = w['outputs']
lines = [set(line) for line in w['lines']]
selections = [{int(k): v for k, v in d.items()} for d in w['selected_and_child']]
assert len(lines) == len(outputs) == len(selections) == 4
assert len(gates) == 28
for i, gate in enumerate(gates):
    assert set(gate) == {'op', 'inputs'}
    assert gate['op'] in ['and', 'or']
    assert len(gate['inputs']) == 2
    assert all(type(p) is int and 0 <= p < 13+i for p in gate['inputs'])
assert len(set(outputs)) == 4 and all(13 <= o < 41 for o in outputs)
assert [sum(g['op'] == op for g in gates) for op in ['and', 'or']] == [18, 10]

# Reconstruct the graph independently from the stated six routers.
rebuilt = []
def add(op, a, b):
    rebuilt.append({'op': op, 'inputs': [a,b]})
    return 12+len(rebuilt)
def router(xs):
    left = add('and', xs[0], xs[1])
    right = add('and', xs[2], xs[3])
    return add('and', left, right)
a = [1,4,6,2]; b = [3,5,10,8]; c = [9,7,11,12]
a1, a2 = router(a), router(a)
b1, b2 = router(b), router(b)
c1, c2 = router(c), router(c)
u = add('or', 0, a1); v = add('or', a2, b1)
w0 = add('or', b2, c1); z = add('or', c2, 0)
h = add('or', u, w0); k = add('or', v, z)
rebuilt_outputs = [add('or', h, k) for _ in range(4)]
assert rebuilt == gates and rebuilt_outputs == outputs
singer_ids = [0,4,10,12]
assert lines == [{(j+i)%13 for j in [0,1,3,9]} for i in singer_ids]
assert all(len(lines[i] & lines[j]) == 1 for i in range(4) for j in range(i))

def evaluate(bits):
    values = [bool(bits & (1 << p)) for p in range(13)]
    for gate in gates:
        a,b = [values[p] for p in gate['inputs']]
        values.append((a and b) if gate['op'] == 'and' else (a or b))
    return values

def reach(root, children, forbidden):
    seen = set(); todo = [root]
    while todo:
        p = todo.pop()
        if p in seen or p in forbidden: continue
        seen.add(p)
        todo.extend(children.get(p, []))
    return seen

nodes = []; selected_children = []; false_choice_checks = 0
for i in range(4):
    negative = evaluate(sum(1 << p for p in range(13) if p not in lines[i]))
    assert not negative[outputs[i]]
    children = {}; pending = [outputs[i]]; visited = set()
    while pending:
        p = pending.pop()
        if p in visited: continue
        visited.add(p)
        if p < 13: continue
        gate = gates[p-13]
        assert not negative[p]
        if gate['op'] == 'or':
            child = list(gate['inputs'])
        else:
            assert p in selections[i]
            q = selections[i][p]
            assert q in gate['inputs'] and not negative[q]
            false_choice_checks += 1
            child = [q]
        children[p] = child
        pending.extend(child)
    assert visited & set(range(13)) == lines[i]
    assert set(selections[i]) == {p for p in visited if p >= 13 and gates[p-13]['op'] == 'and'}
    nodes.append(visited); selected_children.append(children)

nondomination_checks = 0
collective_failures = []
for i in range(4):
    for j in range(4):
        if i == j: continue
        shared_gates = {p for p in nodes[i] & nodes[j] if p >= 13}
        for gate in shared_gates:
            remaining = reach(outputs[i], selected_children[i], {gate})
            for terminal in lines[i]-lines[j]:
                assert terminal in remaining
                nondomination_checks += 1
        remaining = reach(outputs[i], selected_children[i], nodes[j])
        missing = sorted((lines[i]-lines[j])-remaining)
        assert missing
        collective_failures.append({'line': i, 'other_line': j, 'missing': missing})
assert nondomination_checks == 504

errors = [0]*4; band_rows = 0; upper_checks = 0
for bits in range(1 << 13):
    values = evaluate(bits)
    in_band = 13-bits.bit_count() in [5,6]
    band_rows += in_band
    for i in range(4):
        target = any(values[p] for p in lines[i])
        assert not values[outputs[i]] or target
        upper_checks += 1
        if in_band and values[outputs[i]] != target: errors[i] += 1
assert band_rows == 3003 and errors == [867]*4
assert w['total_gates'] == 28 and w['or_gates'] == 10
assert w['domination_checks_passed'] == nondomination_checks
assert w['band_errors_per_output'] == errors
assert w['global_upper_checked_assignments'] == 8192
assert w['global_upper_holds'] is True and w['band_correct'] is False
print(json.dumps({
    'scope': 'Auxiliary counterexample only: individual nondomination does not imply OR-branch packing. Not band-correct; not a posted-gap refutation.',
    'verdict': 'PASS', 'total_gates': 28, 'and_gates': 18, 'or_gates': 10,
    'reconstructed_gate_list_exactly': True, 'singer_line_ids': singer_ids,
    'selected_and_false_checks': false_choice_checks,
    'individual_nondomination_checks': nondomination_checks,
    'global_bound_assignments': 8192, 'global_bound_output_checks': upper_checks,
    'band_rows': band_rows, 'band_errors_per_output': errors,
    'collective_avoidance_fails_all_ordered_pairs': len(collective_failures),
    'collective_failure_details': collective_failures,
}, indent=2, sort_keys=True))
