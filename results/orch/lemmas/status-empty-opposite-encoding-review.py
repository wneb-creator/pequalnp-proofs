import hashlib
import itertools
import json
import sys
from pathlib import Path

BASE = Path(sys.argv[1]) if len(sys.argv) > 1 else Path('/tmp/oec/pequalnp-pilot-81')

def cnf(path):
    lines = path.read_text().splitlines()
    _, _, nv, nc = lines[0].split()
    clauses = [list(map(int, line.split()))[:-1] for line in lines[1:]]
    assert len(clauses) == int(nc)
    return int(nv), clauses

inputs = [sum(1 << m for m in range(16384) if (m >> i) & 1) for i in range(14)]
def truth(control):
    values = []
    for atom in control['atoms']:
        slots = []
        for slot in atom['slots']:
            word = 0
            for i in slot['primary']:
                word |= inputs[i]
            for j in slot['prior']:
                assert j < len(values)
                word |= values[j]
            slots.append(word)
        values.append(slots[0] & slots[1])
    output = 0
    for j in control['final']:
        output |= values[j]
    expected = 0
    for p in range(7):
        for line in range(7):
            if ((p - line) % 7 in (0, 1, 3)) if control['graph'] == 'fano' else p == line:
                expected |= inputs[p] & inputs[7 + line]
    assert output == expected

def trace(control, base, seed):
    values, traces = [], []
    for atom in control['atoms']:
        sv, sd = [], []
        for slot in atom['slots']:
            sv.append(base in slot['primary'] or any(values[j] for j in slot['prior']))
            sd.append(seed in slot['primary'] or any(traces[j] for j in slot['prior']))
        values.append(sv[0] and sv[1])
        traces.append((sv[0] and sd[1]) or (sd[0] and sv[1]))
    return any(traces[j] for j in control['final'])

reports = []
for tag in ['sat-p14-compact-empty18-target', 'sat-p14-compact-empty28-control', 'sat-p14-compact-empty-host-control']:
    m = json.loads((BASE / (tag + '.metadata.json')).read_text())
    nv, clauses = cnf(BASE / (tag + '.cnf'))
    ext = m['empty_opposite']
    expected = []
    for j, entry in enumerate(ext['slots']):
        assert entry['nonempty'] == ext['variable_begin'] + j + 1
        atom = m['atoms'][entry['atom']]
        side = entry['empty_side']
        own, other = atom['slots'][side]['primary'], atom['slots'][1 - side]['primary']
        y = entry['nonempty']
        expected.append([-y] + own)
        expected.extend([[-v, y] for v in own])
        for group in [range(7), range(7, 14)]:
            expected.extend([[y, -other[a], -other[b]] for a, b in itertools.combinations(group, 2)])
    assert clauses[ext['clause_begin']:ext['clause_end']] == expected
    assert ext['clause_end'] == len(clauses) and nv == m['variables']
    assert nv - ext['variable_begin'] == len(ext['slots'])
    if ext['enabled']:
        assert m['equality'] and len(ext['slots']) == 2 * m['cap']
        assert len(expected) == 57 * 2 * m['cap']
    if tag.endswith('target'):
        old_nv, old_clauses = cnf(BASE / 'sat-p14-compact-partition18-target.cnf')
        assert clauses[:ext['clause_begin']] == old_clauses and old_nv == ext['variable_begin']
        reports.append({'tag': tag, 'variables': nv, 'clauses': len(clauses), 'added_variables': len(ext['slots']), 'added_clauses': len(expected), 'unchanged_partition_prefix': True})
        continue
    assignment = {int(k): bool(v) for k, v in json.loads((BASE / (tag + '.complete-assignment.json')).read_text()).items()}
    assert set(assignment) == set(range(1, nv + 1))
    assert all(any(assignment[abs(v)] == (v > 0) for v in clause) for clause in clauses)
    for entry in ext['slots']:
        own = m['atoms'][entry['atom']]['slots'][entry['empty_side']]['primary']
        assert assignment[entry['nonempty']] == any(assignment[v] for v in own)
    control = json.loads((BASE / (tag + '.compact-control.json')).read_text())
    truth(control)
    assert not trace(control, 0, 7) and not trace(control, 7, 0)
    reports.append({'tag': tag, 'variables': nv, 'clauses': len(clauses), 'complete_assignment_pass': True, 'truth_rows': 16384, 'raw_derivatives': [False, False], 'empty_opposite_enabled': ext['enabled'], 'graph': control['graph']})

abstract_cases = 0
for mask in range(1 << 14):
    for nonempty in [False, True]:
        encoded = all(nonempty or not ((mask >> a) & 1) or not ((mask >> b) & 1) for group in [range(7), range(7, 14)] for a, b in itertools.combinations(group, 2))
        intended = nonempty or ((mask & 127).bit_count() <= 1 and (mask >> 7).bit_count() <= 1)
        assert encoded == intended
        abstract_cases += 1
print(json.dumps({'verdict': 'PASS independent exact-extension and complete-control audit', 'encoder_sha256': hashlib.sha256((BASE / 'sat-p14-compact-empty.py').read_bytes()).hexdigest(), 'abstract_opposite_masks_and_guards_checked': abstract_cases, 'reports': reports, 'scope': 'The new at-most-one-per-side cut only; complete positive-control clauses and direct truth/derivatives also checked. No solver outcome or full-target certificate.'}, indent=2))
