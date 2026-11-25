import hashlib
import itertools
import json
import pathlib

base = pathlib.Path(__file__).resolve().parent
manifest = json.loads((base / 'manifest.json').read_text())
assert hashlib.sha256((base / 'synth-small.py').read_bytes()).hexdigest() == manifest['generator_sha256']
dimensions = {'c6': (3,3), 'c8': (4,4), 'path6': (3,3), 'star4': (1,3),
              'b3': (3,3), 'b34': (3,4), 'tetra': (4,6), 'pendant3': (3,6), 'fano': (7,7)}
records = []
for entry in manifest['records']:
    record = base / entry['record']
    log = base / entry['solver_log']
    assert hashlib.sha256(record.read_bytes()).hexdigest() == entry['record_sha256']
    assert hashlib.sha256(log.read_bytes()).hexdigest() == entry['solver_log_sha256']
    d = json.loads(record.read_text())
    np, nl = dimensions[d['case']]
    n = np + nl
    assert d['n'] == n
    edges = set(map(tuple,d['edges']))
    assert all(0 <= p < np and 0 <= l < nl for p,l in edges)
    assert not any(all((p,l) in edges for p in ps for l in ls)
                   for ps in itertools.combinations(range(np),2)
                   for ls in itertools.combinations(range(nl),2))
    text = log.read_text()
    if d['returncode'] == 10:
        assert '\ns SATISFIABLE\n' in text
        circuit = d['circuit']
        assert len(circuit) == d['gates']
        for i,(op,a,b) in enumerate(circuit):
            assert op in ('and','or') and 0 <= a < n+i and 0 <= b < n+i
        for t in range(1 << n):
            wires = [bool(t & (1 << i)) for i in range(n)]
            for op,a,b in circuit:
                wires.append((wires[a] and wires[b]) if op == 'and' else (wires[a] or wires[b]))
            target = any((t & (1 << p)) and (t & (1 << (np+l))) for p,l in edges)
            assert wires[-1] == target
        assert d['independent_truth_table_check'] is True
    elif d['returncode'] == 20:
        assert '\ns UNSATISFIABLE\n' in text
    else:
        assert d['returncode'] == 0 and '\nc exit 0\n' in text
        assert '\ns SATISFIABLE\n' not in text and '\ns UNSATISFIABLE\n' not in text
    records.append(d)

for case,np,nl in (('b3',3,3),('b34',3,4)):
    census = json.loads((base / ('census-'+case+'.json')).read_text())
    checked = 0
    for row in census:
        if row['predicted'] == 1:
            assert row['edges'] == 1 and row['matching'] == 1
            continue
        matching = [d for d in records if d['case'] == case
                    and sum(1 << (nl*p+l) for p,l in d['edges']) == row['mask']
                    and d['gates'] == row['predicted']-1]
        assert any(d['returncode'] == 20 for d in matching)
        assert not any(d['returncode'] == 10 for d in matching)
        checked += 1
    print(case, 'nonempty types', len(census), 'computed UNSAT below bound', checked,
          'single-edge zero-gate case', len(census)-checked)

counts = {str(code): sum(d['returncode'] == code for d in records) for code in (10,20,0)}
print('Verified artifact hashes, solver status text, C4-freeness, census coverage, and all SAT truth tables.')
print('Solver return-code counts (10 SAT, 20 computed UNSAT, 0 UNKNOWN):', json.dumps(counts))
print('UNSAT results are computed evidence, not Lean-certified proofs. UNKNOWN gives no conclusion.')
