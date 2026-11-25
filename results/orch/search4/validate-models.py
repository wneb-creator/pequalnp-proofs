import hashlib
import json
from pathlib import Path


def evaluate(n, gates, assignment, disabled=None):
    wires = [bool(assignment & (1 << i)) for i in range(n)]
    for j, (op, a, b) in enumerate(gates):
        assert op in ('and', 'or') and 0 <= a < n + j and 0 <= b < n + j
        wires.append(False if j == disabled else
                     (wires[a] and wires[b] if op == 'and' else wires[a] or wires[b]))
    return wires


def validate(path, data):
    n, gates = data['n'], data['gates']
    edges = {tuple(sorted(e)) for e in data['edges']}
    assert all(0 <= a < b < n for a, b in edges)
    assert len(gates) == data['gate_count']
    dirty = set()
    for assignment in range(1 << n):
        expected = any(assignment & (1 << a) and assignment & (1 << b) for a, b in edges)
        values = evaluate(n, gates, assignment)
        assert values[-1] == expected
        if not expected:
            dirty.update(j for j, (op, _, _) in enumerate(gates) if op == 'and' and values[n + j])
    cones = []
    actual_owned = {}
    for j, (op, a, b) in enumerate(gates):
        cone = set()
        for wire in (a, b):
            if wire >= n:
                cone |= cones[wire - n] | {wire - n}
        cones.append(cone)
        if op == 'and':
            actual_owned[j] = sorted(
                [a, b] for a, b in edges
                if (values := evaluate(n, gates, (1 << a) | (1 << b)))[n + j]
                and not any(gates[h][0] == 'and' and values[n + h] for h in cone))
    recorded_owned = {item['gate']: sorted(item['edges']) for item in data['ownership']}
    assert recorded_owned == actual_owned
    if data.get('all_owned'):
        assert all(actual_owned.values())
    if data.get('forced_unowned'):
        assert any(not owned for owned in actual_owned.values())
    if data.get('singleton_safe'):
        assert all(not evaluate(n, gates, 1 << i)[n + j]
                   for j, (op, _, _) in enumerate(gates) if op == 'and' for i in range(n))
    actual_pivotal = {}
    for j in range(len(gates)):
        actual_pivotal[j] = sorted([a, b] for a, b in edges
                                   if not evaluate(n, gates, (1 << a) | (1 << b), j)[-1])
    if 'pivotal_witnesses' in data:
        assert {row['gate']: sorted(row['lost_edges']) for row in data['pivotal_witnesses']} == actual_pivotal
    if data.get('pivotal_gates'):
        assert all(actual_pivotal.values())
    if data.get('unowned_two_pivots'):
        assert all(len(actual_pivotal[j]) >= 2 for j, owned in actual_owned.items() if not owned)
    if data.get('defective_two_pivots'):
        assert all(len(actual_pivotal[j]) >= 2 for j in dirty)
    top_form = all(gates[i][0] != 'and' or i in dirty
                   for j, (op, _, _) in enumerate(gates) if op == 'and' for i in cones[j])
    if data.get('top_form'):
        assert top_form
    if 'top_form_validated' in data:
        assert top_form == data['top_form_validated']
    if 'dirty_ands' in data:
        assert sorted(dirty) == data['dirty_ands']
    for certificate in data.get('pure_or_violations', []):
        j = certificate['gate']
        a, b = certificate['inputs']
        u, v = certificate['lost_edge']
        assert gates[j] == ['or', a, b] and a < n and b < n
        assert [u, v] in actual_pivotal[j]
        assert not ((u == a and tuple(sorted((b, v))) in edges) or
                    (v == a and tuple(sorted((b, u))) in edges) or
                    (u == b and tuple(sorted((a, v))) in edges) or
                    (v == b and tuple(sorted((a, u))) in edges))
    for certificate in data.get('shared_or_certificates', []):
        j, h, other = (certificate[k] for k in ('unowned_and', 'shared_or', 'other_and'))
        assert gates[j][0] == 'and' and not actual_owned[j]
        assert gates[h][0] == 'or' and h in cones[j]
        assert gates[other][0] == 'and' and n + h in gates[other][1:]
        assert j not in cones[other] and other not in cones[j]
    return {'file': path.name, 'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
            'n': n, 'gates': len(gates), 'all_inputs_checked': 1 << n,
            'all_owned': all(actual_owned.values()),
            'every_gate_pivotal': all(actual_pivotal.values()), 'top_form': top_form,
            'dirty_ands': sorted(dirty), 'verdict': 'PASS'}


def main():
    root = Path(__file__).resolve().parent
    results = []
    for path in sorted(root.glob('sat-*.json')):
        data = json.loads(path.read_text())
        if isinstance(data, dict) and data.get('returncode') == 10 and 'gates' in data:
            results.append(validate(path, data))
    assert results
    report = {'note': 'Independent full truth-table, exact strict-cone ownership, '
                       'shared-factor, forced-false pivotal witnesses, joint two-pivots, TopForm and pure-OR violation validation.',
              'models': results, 'verdict': 'PASS'}
    (root / 'model-validation.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'models': len(results), 'verdict': 'PASS'}))


if __name__ == '__main__':
    main()
