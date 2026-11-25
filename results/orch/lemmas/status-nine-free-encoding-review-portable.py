"""Independent finite-geometry and complete-model checks for the new SAT cut."""
import hashlib
import ast
from types import SimpleNamespace
import json
import sys
from pathlib import Path

BASE = Path(sys.argv[1]).resolve()
HERE = BASE
namespace = {}
for filename, names in [('sat-p14-compact.py', {'neg', 'CNF'}),
                        ('sat-p14-compact-nine.py', {'free_originals'})]:
    tree = ast.parse((BASE / filename).read_text(), filename=filename)
    nodes = [node for node in tree.body if isinstance(node, (ast.FunctionDef, ast.ClassDef))
             and node.name in names]
    assert {node.name for node in nodes} == names
    exec(compile(ast.Module(body=nodes, type_ignores=[]), filename, 'exec'), namespace)
nine = SimpleNamespace(free_originals=namespace['free_originals'],
                       quiet=SimpleNamespace(core=SimpleNamespace(CNF=namespace['CNF'])))
tables = json.loads((HERE / 'status-cofactor-tables.json').read_text())['tables']
for row in tables:
    assert set(nine.free_originals(row['posted_center'])) == set(row['posted_free_originals'])

reports = []
for tag in ['sat-p14-compact-nine35-control', 'sat-p14-compact-nine-host-control']:
    meta = json.loads((BASE / (tag + '.metadata.json')).read_text())
    control = json.loads((BASE / (tag + '.compact-control.json')).read_text())
    assignment = {int(k): v for k, v in json.loads(
        (BASE / (tag + '.complete-assignment.json')).read_text()).items()}
    assert set(assignment) == set(range(1, meta['variables'] + 1))
    slot_sets = []
    for j, atom in enumerate(meta['atoms']):
        for s, slot in enumerate(atom['slots']):
            primary = set(control['atoms'][j]['slots'][s]['primary']) if j < len(control['atoms']) else set()
            assert all(assignment[v] == (x in primary) for x, v in enumerate(slot['primary']))
            slot_sets.append(primary)
    for pair in meta['enhancements']['cooccurrence']:
        x, y = pair['pair']
        expected = [x in slot and y in slot for slot in slot_sets]
        assert all(assignment[v] == truth for v, truth in zip(pair['terms'], expected))
        assert assignment[pair['out']] == any(expected)
    for center in meta['enhancements']['centers']:
        x = center['center']
        cooccurring = set().union(*(slot for slot in slot_sets if x in slot)) - {x}
        free = set(nine.free_originals(x))
        assert set(center['free_originals']) == free
        for field, expected in [('all_at_least_six', len(cooccurring) >= 6),
                                ('free_at_least_two', len(cooccurring & free) >= 2)]:
            table = center[field]
            for cell in table['cells']:
                assert assignment[cell['var']] == (
                    sum(assignment[v] for v in table['literals'][:cell['prefix']]) >= cell['threshold'])
            assert assignment[table['root']] == expected
        assert len(cooccurring) <= 5 or len(cooccurring & free) >= 2
    count = 0
    with (BASE / (tag + '.cnf')).open() as stream:
        assert stream.readline().split() == ['p', 'cnf', str(meta['variables']), str(meta['clauses'])]
        for line in stream:
            literals = [int(v) for v in line.split()]
            assert literals.pop() == 0
            assert any(assignment[abs(v)] == (v > 0) for v in literals)
            count += 1
    assert count == meta['clauses']
    reports.append({'tag': tag, 'variables': len(assignment), 'all_clauses_checked': count,
                    'nine_free_enabled': meta['enhancements']['nine_free']})

cnf = nine.quiet.core.CNF()
bits = [cnf.var() for _ in range(13)]
six, two = cnf.threshold(bits, 6), cnf.threshold(bits[:4], 2)
cnf.add(-six['root'], two['root'])
rejected = 0
for mask in range(8192):
    values = {v: bool(mask & (1 << i)) for i, v in enumerate(bits)}
    for table in [six, two]:
        for cell in table['cells']:
            values[cell['var']] = sum(values[v] for v in table['literals'][:cell['prefix']]) >= cell['threshold']
    actual = all(any(values[abs(v)] == (v > 0) for v in clause) for clause in cnf.cs)
    expected = mask.bit_count() <= 5 or (mask & 15).bit_count() >= 2
    assert actual == expected
    rejected += not actual

report = {'verdict': 'PASS independent nine-free geometry and clause review',
          'source_sha256': hashlib.sha256((BASE / 'sat-p14-compact-nine.py').read_bytes()).hexdigest(),
          'geometry_centers_checked': 14, 'controls': reports,
          'cardinality_rows_checked': 8192, 'cardinality_rows_rejected': rejected,
          'scope': 'Nine-free cooccurrence/cardinality cut only. Max-prior ordering is independently reviewed elsewhere. The enabled-cut control is matching, not Fano; no satisfiability result is claimed.'}
print(json.dumps(report, indent=2))
