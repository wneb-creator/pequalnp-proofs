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

import ast
source = BASE / 'sat-p14-compact-shared.py'
module = ast.parse(source.read_text())
function = next(n for n in module.body if isinstance(n, ast.FunctionDef) and n.name == 'neighbors')
namespace = {}
exec(compile(ast.Module(body=[function], type_ignores=[]), str(source), 'exec'), namespace)
def adj(a,b):
    return (a<7<=b and (a-(b-7))%7 in (0,1,3)) or (b<7<=a and (b-(a-7))%7 in (0,1,3))
for a in range(14):
    assert namespace['neighbors'](a) == [b for b in range(14) if adj(a,b)]
pairs = [{'labels':[a,b], 'neighbors':[z for z in range(14) if adj(a,z) or adj(b,z)]} for side in [range(7),range(7,14)] for a,b in itertools.combinations(side,2)]
assert len(pairs)==42 and all(len(p['neighbors'])==5 for p in pairs)
reports=[]
for suffix in ['18-target','28-control','-host-control']:
    tag='sat-p14-compact-shared'+suffix
    m=json.loads((BASE/(tag+'.metadata.json')).read_text())
    nv,clauses=cnf(BASE/(tag+'.cnf'))
    ext=m['shared_slot'];assert ext['enabled'] and ext['pairs']==pairs
    expected=[]
    for atom in m['atoms']:
        for side in range(2):
            own=atom['slots'][side]['primary'];other=atom['slots'][1-side]['primary']
            for pair in pairs:
                a,b=pair['labels'];expected.append([-own[a],-own[b]]+[other[z] for z in pair['neighbors']])
    assert clauses[ext['clause_begin']:]==expected
    assert ext['clause_end']==len(clauses) and nv==ext['variable_begin']==m['variables']
    assert len(expected)==84*m['cap']
    old_nv,old_clauses=cnf(BASE/('sat-p14-compact-empty'+suffix+'.cnf'))
    assert old_nv==nv and clauses[:ext['clause_begin']]==old_clauses
    record={'tag':tag,'variables':nv,'clauses':len(clauses),'added_clauses':len(expected),'unchanged_empty_prefix':True}
    if not suffix.endswith('target'):
        assignment={int(k):bool(v) for k,v in json.loads((BASE/(tag+'.complete-assignment.json')).read_text()).items()}
        assert set(assignment)==set(range(1,nv+1))
        assert all(any(assignment[abs(v)]==(v>0) for v in clause) for clause in clauses)
        control=json.loads((BASE/(tag+'.compact-control.json')).read_text());truth(control)
        assert not trace(control,0,7) and not trace(control,7,0)
        record.update(complete_assignment_pass=True,truth_rows=16384,raw_derivatives=[False,False],graph=control['graph'],shared_slot_enabled=True)
    reports.append(record)
count=0
for pair in pairs:
    a,b=pair['labels'];side=range(7,14) if a<7 else range(7)
    for mask in range(128):
        opposite={z for j,z in enumerate(side) if mask>>j&1}
        for ownA,ownB in itertools.product([False,True],repeat=2):
            encoded=not ownA or not ownB or bool(opposite.intersection(pair['neighbors']))
            intended=not (ownA and ownB) or any(adj(a,z) or adj(b,z) for z in opposite)
            assert encoded==intended;count+=1
print(json.dumps({'verdict':'PASS independent exact-extension, Fano geometry and complete-control audit','encoder_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'abstract_pair_guard_assignments':count,'reports':reports,'scope':'Only the newly proved shared-slot productivity extension and exact preserved encoder prefix; controls checked independently on every clause, all16384 truth inputs and both direct traces. No solver outcome or target theorem.'},indent=2))
