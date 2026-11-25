import ast
import hashlib
import itertools
import json
import sys
import types
from pathlib import Path

BASE = Path(sys.argv[1]) if len(sys.argv) > 1 else Path('/tmp/oec/pequalnp-pilot-81')
core_path = BASE / 'sat-fano-full.py'
encoder_path = BASE / 'sat-collinear4.py'
core = ast.parse(core_path.read_text())
ns = {'itertools': itertools}
exec(compile(ast.Module(body=[node for node in core.body if isinstance(node, (ast.FunctionDef, ast.ClassDef)) and node.name in ('neg', 'CNF')], type_ignores=[]), str(core_path), 'exec'), ns)
enc = ast.parse(encoder_path.read_text())
selected = []
for node in enc.body:
    if isinstance(node, ast.FunctionDef) and node.name != 'main':
        selected.append(node)
    elif isinstance(node, ast.Assign) and all(isinstance(t, ast.Name) and t.id in ('POINTS', 'ORIGINAL', 'EDGES') for t in node.targets):
        selected.append(node)
scope = {'broad': types.SimpleNamespace(CNF=ns['CNF'])}
exec(compile(ast.Module(body=selected, type_ignores=[]), str(encoder_path), 'exec'), scope)

def read_cnf(path):
    lines = path.read_text().splitlines()
    assert lines[0].startswith('p cnf ')
    _, _, nv, nc = lines[0].split()
    clauses = []
    for line in lines[1:]:
        row = list(map(int, line.split()))
        assert row[-1] == 0
        clauses.append(row[:-1])
    assert len(clauses) == int(nc)
    return int(nv), clauses

INPUTS = {}
def input_words(n):
    if n not in INPUTS:
        INPUTS[n] = [sum(1 << m for m in range(1 << n) if (m >> i) & 1) for i in range(n)]
    return INPUTS[n]

def words(gates, n):
    table = list(input_words(n))
    for j, (op, a, b) in enumerate(gates):
        assert op in ('and', 'or') and 0 <= a < n + j and 0 <= b < n + j and a != b
        table.append(table[a] & table[b] if op == 'and' else table[a] | table[b])
    return table

def direct_trace(gates, n, base, seed):
    value = [i == base for i in range(n)]
    trace = [i == seed for i in range(n)]
    for op, a, b in gates:
        value.append(value[a] and value[b] if op == 'and' else value[a] or value[b])
        trace.append((value[a] and trace[b]) or (trace[a] and value[b]) if op == 'and' else trace[a] or trace[b])
    return value, trace

edges = [(p, 4 + line) for p in range(4) for line in range(7) if (p + 3 + line) % 7 in (0, 1, 3)]
assert len(edges) == 12 and edges == scope['EDGES']
local_expected = 0
for a, b in edges:
    local_expected |= input_words(11)[a] & input_words(11)[b]
positive = [(1 << a) | (1 << b) for a, b in edges]
negative = [m for m in range(2048) if not (local_expected >> m) & 1 and all((local_expected >> (m | (1 << i))) & 1 for i in range(11) if not (m >> i) & 1)]
full_expected = 0
for p in range(7):
    for line in range(7):
        if (p - line) % 7 in (0, 1, 3):
            full_expected |= input_words(14)[p] & input_words(14)[7 + line]

tags = ['sat-collinear4-ordinary15-control'] + [f'sat-collinear4-quiet16-{i}-control' for i in range(4)]
reports = []
quiet_edges = set()
for tag in tags + ['sat-collinear4-15-target']:
    metadata = json.loads((BASE / (tag + '.metadata.json')).read_text())
    regenerated, regenerated_metadata = scope['build'](metadata['size'], metadata['double'])
    nv, clauses = read_cnf(BASE / (tag + '.cnf'))
    assert nv == regenerated.n and clauses == regenerated.cs
    assert metadata == json.loads(json.dumps(regenerated_metadata))
    assert metadata['positive'] == positive and metadata['negative'] == negative
    if tag.endswith('target'):
        reports.append({'tag': tag, 'variables': nv, 'clauses': len(clauses), 'exact_source_regeneration': True})
        continue
    control = json.loads((BASE / (tag + '.complete-controls.json')).read_text())
    gates = control['gates']
    table = words(gates, 11)
    assert table[-1] == local_expected
    assert all(a < b for _, a, b in gates)
    assert [(b, a) for _, a, b in gates] == sorted((b, a) for _, a, b in gates)
    used = {w for _, a, b in gates for w in (a, b)}
    assert set(range(11 + len(gates) - 1)) <= used
    assert all(any((word >> m) & 1 for m in positive) for word in table[11:])
    full = control['full_splice']
    full_table = words(full['gates'], 14)
    assert full_table[-1] == full_expected and len(full['gates']) == len(gates) + 12
    assert full['output'] == 14 + len(full['gates']) - 1
    mapping = [3, 4, 5, 6] + [7 + (-line) % 7 for line in range(7)]
    for j, ((op, a, b), actual) in enumerate(zip(gates, full['gates'])):
        assert actual == [op, mapping[a], mapping[b]]
        mapping.append(14 + j)
    for case in control['cases']:
        edge = tuple(case['edge'])
        assert edge in edges
        assignment = {int(k): bool(v) for k, v in case['assignment'].items()}
        assert set(assignment) == set(range(1, nv + 1))
        assert all(any(assignment[abs(lit)] == (lit > 0) for lit in clause) for clause in clauses)
        assert [e for e, flag in zip(edges, metadata['flags']) if assignment[flag]] == [edge]
        for direction in range(2):
            assert [assignment[var] for var in metadata['bases'][direction]] == [i == edge[direction] for i in range(11)]
        outputs = []
        for direction in range(2):
            base, seed = edge[direction], edge[1 - direction]
            value, trace = direct_trace(gates, 11, base, seed)
            outputs.append(trace[-1])
            for j, (gate, (op, a, b)) in enumerate(zip(metadata['gates'], gates)):
                t = gate['traces'][direction]
                expected = {'selected_a': trace[a], 'selected_b': trace[b], 'term_a': value[a] and trace[b], 'term_b': trace[a] and value[b], 'both': (value[a] and trace[b]) or (trace[a] and value[b]), 'out': trace[11 + j]}
                assert all(assignment[t[k]] == v for k, v in expected.items())
                assert assignment[gate['outputs'][len(metadata['tests']) + direction]] == value[11 + j]
            _, full_trace = direct_trace(full['gates'], 14, mapping[base], mapping[seed])
            assert full_trace[-1] == trace[-1]
        assert outputs == case['derivatives']
        if metadata['double']:
            assert outputs == [False, False]
            quiet_edges.add(edge)
    reports.append({'tag': tag, 'variables': nv, 'clauses': len(clauses), 'complete_assignments': len(control['cases']), 'local_truth_rows': 2048, 'full_truth_rows': 16384, 'splice_size': len(full['gates']), 'all_checks_passed': True})
assert quiet_edges == set(edges)
report = {'verdict': 'PASS independent source, complete CNF assignment, truth-table and raw-derivative audit', 'encoder_sha256': hashlib.sha256(encoder_path.read_bytes()).hexdigest(), 'primitive_sha256': hashlib.sha256(core_path.read_bytes()).hexdigest(), 'positive_rows': len(positive), 'maximal_negative_rows': len(negative), 'all_12_edge_flags_have_quiet_positive_controls': True, 'reports': reports, 'scope': 'Control and encoding review only. No local15 SAT witness or UNSAT certificate. Positive-support/live/essential/order constraints retain the mathematical normalization obligations described in the review.'}
print(json.dumps(report, indent=2))
