import hashlib
import itertools
import json
import sys
from pathlib import Path

BASE = Path(sys.argv[1]).resolve()
ENCODER_HASH = 'c428fe71d33b713a32c1899e51dcd40a7aa35a21e516d8cbfb02c60332a3f57c'
EDGES = [(i, 4+t) for i, p in enumerate([3, 4, 5, 6])
         for t in range(7) if (p+t) % 7 in [0, 1, 3]]
FULL_EDGES = [(p, 7+t) for p in range(7) for t in range(7)
              if (p-t) % 7 in [0, 1, 3]]
REPS = [(0, 4), (0, 8), (0, 9), (2, 9)]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(name):
    return json.loads((BASE/name).read_text())


def cnf(name):
    rows = (BASE/name).read_text().splitlines()
    header = rows.pop(0).split()
    assert header[:2] == ['p', 'cnf']
    clauses = [list(map(int, row.split()))[:-1] for row in rows]
    assert all(row.split()[-1] == '0' for row in rows)
    assert len(clauses) == int(header[3])
    assert all(0 < abs(v) <= int(header[2]) for c in clauses for v in c)
    return int(header[2]), clauses


def evaluate(gates, n, mask):
    w = [bool(mask >> i & 1) for i in range(n)]
    for op, a, b in gates:
        w.append(w[a] and w[b] if op == 'and' else w[a] or w[b])
    return w


def derivative(gates, n, base, seed):
    w = evaluate(gates, n, 1 << base)
    d = [i == seed for i in range(n)]
    for op, a, b in gates:
        d.append((w[a] and d[b]) or (d[a] and w[b])
                 if op == 'and' else d[a] or d[b])
    return d


def splice(gates):
    mapping = [3, 4, 5, 6] + [7+(-i) % 7 for i in range(7)]
    result = []
    for op, a, b in gates:
        result.append([op, mapping[a], mapping[b]])
        mapping.append(13+len(result))
    outputs = [13+len(result)]
    for p in range(3):
        ns = [7+(p-d) % 7 for d in [0, 1, 3]]
        result.append(['or', ns[0], ns[1]])
        result.append(['or', 13+len(result), ns[2]])
        result.append(['and', p, 13+len(result)])
        outputs.append(13+len(result))
    out = outputs[0]
    for v in outputs[1:]:
        result.append(['or', out, v])
        out = 13+len(result)
    return result


def extension(metadata):
    info = metadata['minimality']
    assert info['minimal'] and info['orbits']
    expected, variables = [], []
    rowsets = [list(range(12, 27)), list(range(12))]
    for gate, blocks in zip(metadata['gates'], info['gates']):
        assert len(blocks) == 2
        for op, rows, block in zip(['and', 'or'], rowsets, blocks):
            assert block['operation'] == op and block['rows'] == rows
            assert len(block['directions']) == 2
            for first, second, terms in [(gate['selected_a'], gate['selected_b'], block['directions'][0]),
                                         (gate['selected_b'], gate['selected_a'], block['directions'][1])]:
                assert len(terms) == len(rows)
                for row, z in zip(rows, terms):
                    a, b = first[row], second[row]
                    expected.extend([[-a, b, z], [a, -z], [-b, -z]])
                    variables.append(z)
                expected.append([-gate['op'] if op == 'and' else gate['op']] + terms)
        expected.append([-gate['outputs'][row] for row in rowsets[0]])
    for edge, flag in zip(EDGES, metadata['flags']):
        if edge not in REPS:
            expected.append([-flag])
    assert variables == list(range(info['variable_begin']+1, metadata['variables']+1))
    return expected


assert digest(BASE/'sat-collinear4-minimal.py') == ENCODER_HASH
symmetry = load('sat-collinear4-symmetry.json')
maps = []
for perm in itertools.permutations(range(3)):
    mapping = list(range(11))
    for group in [[0, 1, 3], [9, 7, 6], [4, 10, 5]]:
        for i in range(3):
            mapping[group[i]] = group[perm[i]]
    assert {(mapping[a], mapping[b]) for a, b in EDGES} == set(EDGES)
    maps.append(mapping)
assert symmetry['permutations'] == maps
orbits = [sorted({(f[a], f[b]) for f in maps}) for a, b in REPS]
assert all(len(x) == 3 for x in orbits)
assert set().union(*map(set, orbits)) == set(EDGES)
assert symmetry['orbits'] == [[list(e) for e in orbit] for orbit in orbits]

reports = []
tags = ['15-target', 'ordinary15-control', 'quiet16-1-control',
        'quiet16-2-control', 'quiet16-3-control']
for suffix in tags:
    tag = 'sat-collinear4-minimal-' + suffix
    m = load(tag+'.metadata.json')
    count, clauses = cnf(tag+'.cnf')
    oldtag = 'sat-collinear4-' + suffix
    old = load(oldtag+'.metadata.json')
    oldcount, oldclauses = cnf(oldtag+'.cnf')
    assert {k:v for k,v in m.items() if k not in ['minimality', 'variables', 'clauses']} == {
        k:v for k,v in old.items() if k not in ['variables', 'clauses']}
    info = m['minimality']
    assert info['variable_begin'] == oldcount and info['clause_begin'] == len(oldclauses)
    assert clauses[:len(oldclauses)] == oldclauses
    extra = extension(m)
    assert clauses[len(oldclauses):] == extra
    assert count == m['variables'] and len(clauses) == m['clauses'] == info['clause_end']
    assert m['edges'] == [list(x) for x in EDGES]
    negative = [mask for mask in range(2048)
                if not any(mask >> a & 1 and mask >> b & 1 for a,b in EDGES)
                and all(any((mask | 1 << i) >> a & 1 and (mask | 1 << i) >> b & 1
                            for a,b in EDGES) for i in range(11) if not mask >> i & 1)]
    assert m['positive'] == [(1 << a) | (1 << b) for a,b in EDGES]
    assert m['negative'] == negative and len(negative) == 15
    report = dict(tag=tag, variables=count, clauses=len(clauses),
                  extension_variables=count-oldcount, extension_clauses=len(extra))
    if suffix != '15-target':
        control = load(tag+'.complete-controls.json')
        gates = control['gates']
        for j, (op,a,b) in enumerate(gates):
            assert op in ['and','or'] and 0 <= a < b < 11+j
        for mask in range(2048):
            assert evaluate(gates,11,mask)[-1] == any(mask >> a & 1 and mask >> b & 1 for a,b in EDGES)
        full = splice(gates)
        assert control['full_splice']['gates'] == full
        for mask in range(16384):
            assert evaluate(full,14,mask)[-1] == any(mask >> a & 1 and mask >> b & 1 for a,b in FULL_EDGES)
        for case in control['cases']:
            edge = tuple(case['edge']); assert edge in REPS
            assignment = {int(k):v for k,v in case['assignment'].items()}
            assert set(assignment) == set(range(1,count+1))
            assert all(type(v) is bool for v in assignment.values())
            assert all(any(assignment[abs(v)] == (v > 0) for v in clause) for clause in clauses)
            expected = {}
            def put(v,b):
                assert v not in expected
                expected[v] = bool(b)
            for e,v in zip(EDGES,m['flags']): put(v,e==edge)
            for direction in range(2):
                for i,v in enumerate(m['bases'][direction]):put(v,i==edge[direction])
            rows=m['tests']+[1 << edge[0],1 << edge[1]]
            all_values=[evaluate(gates,11,row) for row in rows]
            traces=[derivative(gates,11,edge[0],edge[1]),derivative(gates,11,edge[1],edge[0])]
            for j,(gate,(op,a,b)) in enumerate(zip(m['gates'],gates)):
                put(gate['op'],op=='and')
                for i,v in enumerate(gate['select_a']):put(v,i==a)
                for i,v in enumerate(gate['select_b']):put(v,i==b)
                for row,w in enumerate(all_values):
                    put(gate['selected_a'][row],w[a]);put(gate['selected_b'][row],w[b]);put(gate['outputs'][row],w[11+j])
                for r,t in enumerate(gate['traces']):
                    d=traces[r];w=all_values[-2+r];ta=w[a] and d[b];tb=d[a] and w[b]
                    for key,value in [('selected_a',d[a]),('selected_b',d[b]),('term_a',ta),('term_b',tb),('both',ta or tb),('out',d[11+j])]:put(t[key],value)
            for gate,blocks in zip(m['gates'],info['gates']):
                for block in blocks:
                    for first,second,terms in [(gate['selected_a'],gate['selected_b'],block['directions'][0]),(gate['selected_b'],gate['selected_a'],block['directions'][1])]:
                        for row,v in zip(block['rows'],terms):put(v,expected[first[row]] and not expected[second[row]])
            assert expected == assignment
            flags=[d[-1] for d in traces];assert flags == case['derivatives']
            assert not m['double'] or flags == [False,False]
            p=[3,4,5,6][edge[0]];l=7+(-(edge[1]-4))%7
            assert [derivative(full,14,p,l)[-1],derivative(full,14,l,p)[-1]] == flags
        report.update(complete_assignments=len(control['cases']),local_truth_rows=2048,full_truth_rows=16384)
    reports.append(report)

result=dict(verdict='PASS',encoder_sha256=ENCODER_HASH,artifacts=reports,
            checks=['Exact independent clause delta and variable allocation',
                    'Byte-for-byte previously reviewed base CNF and matching base metadata',
                    'Independent15 maximal-negative census and12 positive edges',
                    'All complete control assignments reconstructed from actual gates',
                    'Every control clause,2048 local rows,16384 spliced rows and both marked traces',
                    'Six explicit arm automorphisms and four complete size3 edge orbits'],
            scope='Encoder/control audit only; no local15 quiet witness, solver result or Lean certificate.')
(BASE/'constructive-collinear-minimal-review.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
