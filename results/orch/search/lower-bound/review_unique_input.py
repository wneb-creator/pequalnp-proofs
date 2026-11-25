#!/usr/bin/env python3
"""Independent review of unique-input CNF normalization and its smoke models."""
from pathlib import Path
from itertools import combinations, permutations, product
import hashlib
import json

P=Path('/tmp/oec/pequalnp-pilot-70/circuit-search')
E=[(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),
 (3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),
 (6,8),(6,9),(6,11)]
target=lambda m:any(m&(1<<a) and m&(1<<b) for a,b in E)
assert (P/'unique0-26-original-equivalence.cnf').read_bytes()==(P/'unique0-26-permissive-base.cnf').read_bytes()
original=(P/'repair_base.py').read_text()
new=(P/'unique_input_base.py').read_text()
assert new==original.replace("entry={'left':left,'right':right,'op':op,'out':out}",
 "entry={'left':left,'right':right,'op':op,'out':out,'left_values':lv,'right_values':rv}")

def cnf(path):
    text=path.read_text().splitlines()
    header=text[0].split()
    assert header[:2]==['p','cnf']
    nv,nc=map(int,header[2:])
    clauses=[]
    for line in text[1:]:
        if not line or line.startswith('c '):continue
        c=list(map(int,line.split()))
        assert c[-1]==0 and all(0<abs(v)<=nv for v in c[:-1])
        clauses.append(c[:-1])
    assert len(clauses)==nc
    return nv,clauses

reports=[]
for prefix,n,final_suffix in [('unique0-26-permissive',26,'final'),('unique0-27-smoke',27,'fanout'),('unique0-28-pad',28,'fanout')]:
    bm=json.loads((P/(prefix+'-base.map.json')).read_text())
    cm=json.loads((P/(prefix+'-critical.map.json')).read_text())
    fm=json.loads((P/(prefix+'-'+final_suffix+'.map.json')).read_text())
    nv,b=cnf(P/(prefix+'-base.cnf'))
    cv,c=cnf(P/(prefix+'-critical.cnf'))
    fv,f=cnf(P/(prefix+'-'+final_suffix+'.cnf'))
    assert nv==cv==fv==bm['nv']==cm['nv']==fm['nv']
    assert bm['gates']==n and bm['ninputs']==14
    assert bm['liveness'] and bm['allow_initial_repeats'] and bm['allow_trivial'] and bm['lex_order']
    assert not bm['canonical_prefix'] and bm['prefix'] is None
    assert not bm['minimal'] and not bm['minimal_prefix'] and not bm['shadow_missing'] and not bm['dirty_and'] and not bm['ordered_max']
    for key,value in bm.items():
        if key!='clauses':assert cm[key]==value
    for key,value in cm.items():
        if key!='clauses':assert fm[key]==value
    rows=bm['rows'];st=bm['structure']
    assert len(rows)==58 and len(st)==n
    incident=[i for i,m in enumerate(rows) if m&1 and target(m)]
    false=[i for i,m in enumerate(rows) if not(m&1) and not target(m)]
    assert len(incident)==3 and len(false)==25
    for i in incident:assert rows[i].bit_count()==2 and not target(rows[i]^1)
    for i in false:
        assert target(rows[i]|1)
        assert all(rows[i]&(1<<v) or target(rows[i]|(1<<v)) for v in range(14))
    slots=[s[side][0] for s in st for side in ('left','right')]
    assert len(slots)==len(set(slots))==2*n
    expected=[slots]+[[-x,-y] for x,y in combinations(slots,2)]
    count=len(expected)
    for s in st:
        for r in incident+false:
            expected.append([-s['left'][0],s['op'],s['right_values'][r]])
            expected.append([-s['left'][0],-s['op'],-s['right_values'][r]])
    assert c[:len(b)]==b and c[len(b):]==expected
    assert cm['unique_input']['exactly_one_clauses']==count
    assert cm['unique_input']['critical_row_clauses']==56*n
    assert cm['unique_input']['critical_row_masks']==[rows[i] for i in incident+false]
    assert cm['unique_input']['base_sha256']==hashlib.sha256((P/(prefix+'-base.cnf')).read_bytes()).hexdigest()
    expected_fan=[]
    for i,s in enumerate(st):
        for a,z in combinations(range(14),2):
            for raw in (a,z):
                expected_fan.append([-s['left'][a],-s['right'][z]]+
                    [other[side][raw] for j,other in enumerate(st) if j!=i for side in ('left','right')])
    assert f[:len(c)]==c and f[len(c):]==expected_fan
    assert len(expected_fan)==182*n
    for consumer,op,other in product((False,True),repeat=3):
        two_clauses=(not consumer or op or other) and (not consumer or not op or not other)
        assert two_clauses==((not consumer) or (other!=op))
    row_report=dict(prefix=prefix,variables=nv,base_clauses=len(b),
        exactly_one_clauses=count,critical_clauses=56*n,fanout_clauses=len(expected_fan),
        final_clauses=len(f),final_sha256=hashlib.sha256((P/(prefix+'-'+final_suffix+'.cnf')).read_bytes()).hexdigest())
    if n>26:
        mv,model_clauses=cnf(P/(prefix+'.cnf'))
        assert mv==nv and model_clauses[:len(f)]==f
        vals={}
        for line in (P/(prefix+'-solve.log')).read_text().splitlines():
            if line.startswith('v '):
                for x in map(int,line.split()[1:]):
                    if not x:continue
                    assert abs(x) not in vals or vals[abs(x)]==(x>0)
                    vals[abs(x)]=x>0
        assert all(any(vals[abs(v)]==(v>0) for v in clause) for clause in model_clauses)
        network=json.loads((P/(prefix+'-witness.json')).read_text())
        assert len(network)==n and sum(a==0 for _,a,b in network)+sum(b==0 for _,a,b in network)==1
        for i,(op,a,z) in enumerate(network):
            assert op in ('and','or') and 0<=a<=z<14+i
            assert [j for j,v in enumerate(st[i]['left']) if vals[v]]==[a]
            assert [j for j,v in enumerate(st[i]['right']) if vals[v]]==[z]
            assert vals[st[i]['op']]==(op=='or')
        for mask in range(16384):
            wires=[bool(mask&(1<<i)) for i in range(14)]
            for op,a,z in network:wires.append(wires[a] and wires[z] if op=='and' else wires[a] or wires[z])
            assert wires[-1]==target(mask)
        if n==28:assert network[-1]==['or',40,40]
        row_report.update(model_clauses_checked=len(model_clauses),truth_assignments_checked=16384)
    reports.append(row_report)

# Check the exact assignment graph's required vertex transitivity directly.
adj=[{b if a==v else a for a,b in E if v in (a,b)} for v in range(14)]
line_of={frozenset(adj[r]):r for r in range(7,14)}
automorphisms=[]
for p in permutations(range(7)):
    image=[frozenset(p[v] for v in adj[r]) for r in range(7,14)]
    if all(t in line_of for t in image):automorphisms.append(tuple(p)+tuple(line_of[t] for t in image))
assert len(automorphisms)==168
polarity=None
for p in permutations(range(7,14)):
    if all((p[j] in adj[i])==(p[i] in adj[j]) for i in range(7) for j in range(7)):
        q=list(p)+[0]*7
        for i,r in enumerate(p):q[r]=i
        polarity=tuple(q);break
assert polarity is not None
edges_set={frozenset(e) for e in E}
full_group=automorphisms+[tuple(polarity[v] for v in p) for p in automorphisms]
assert all({frozenset((p[a],p[b])) for a,b in E}==edges_set for p in full_group)
assert {p[0] for p in full_group}==set(range(14))
print(json.dumps(dict(status='PASS',source_change='metadata-only; base CNFs byte-identical',
    conditional_truth_assignments_per_gate=8,critical_rows=28,
    vertex_transitivity_checked_automorphisms=len(full_group),instances=reports),sort_keys=True))
