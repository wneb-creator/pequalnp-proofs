#!/usr/bin/env python3
"""Independent audit of optional unique-input soft phases; does not solve."""
from pathlib import Path
from collections import Counter
import hashlib
import json

P=Path('/tmp/oec/pequalnp-pilot-70/circuit-search')
auto_path=Path('/tmp/oec/pequalnp-pilot-70/sat-review/verified_symmetry.json')
report=json.loads((P/'unique0-26-near-report.json').read_text())
meta=json.loads((P/'unique0-26-permissive-final.map.json').read_text())
old=json.loads((P/'near26.json').read_text())
network=json.loads((P/'unique0-26-near-seed.json').read_text())
automorphisms=json.loads(auto_path.read_text())['automorphisms']
cnf=P/'unique0-26-permissive-final.cnf'
phases_path=P/'unique0-26-near.phases'
for field,path in [('cnf_sha256',cnf),('source_sha256',P/'unique_input_phases.py'),
 ('original_seed_sha256',P/'near26.json'),('automorphisms_sha256',auto_path),('phase_sha256',phases_path)]:
    assert report[field]==hashlib.sha256(path.read_bytes()).hexdigest()
assert report['cnf_sha256']=='86c036aaf5381cf4d574958b036eb8e32fa257d525fb2e4dd4fa2a33f4c86244'
E={tuple(e) for e in meta['edges']}
target=lambda mask:any(mask&(1<<a) and mask&(1<<b) for a,b in E)
rows=meta['rows']
critical=meta['unique_input']['incident_edge_rows']+meta['unique_input']['critical_false_rows']
assert len(network)==len(old)==26 and len(critical)==28

def run(program,mask):
    vals=[bool(mask&(1<<v)) for v in range(14)]
    for op,a,b in program:
        assert op in ('and','or') and 0<=a<=b<len(vals)
        vals.append(vals[a] and vals[b] if op=='and' else vals[a] or vals[b])
    return vals

def reorder(program,permutation):
    translation={v:permutation[v] for v in range(14)}
    remaining=set(range(len(program)))
    result=[]
    while remaining:
        ready=[]
        for i in remaining:
            op,a,b=program[i]
            if a in translation and b in translation:
                x,y=sorted((translation[a],translation[b]))
                ready.append((x,y,op=='or',i))
        x,y,is_or,i=min(ready)
        translation[14+i]=14+len(result)
        result.append(['or' if is_or else 'and',x,y])
        remaining.remove(i)
    assert translation[39]==39
    return result

eligible=[]
unique_before_critical=0
for p in automorphisms:
    assert sorted(p)==list(range(14))
    assert {tuple(sorted((p[a],p[b]))) for a,b in E}==E
    occurrences=sum(p[v]==0 for op,a,b in old for v in (a,b) if v<14)
    if occurrences!=1:continue
    unique_before_critical+=1
    candidate=reorder(old,p)
    positions=[(i,g) for i,g in enumerate(candidate) if 0 in g[1:]]
    assert len(positions)==1
    index,(op,a,b)=positions[0]
    assert a==0 and b!=0
    if all(run(candidate,rows[r])[b]==(op=='and') for r in critical):eligible.append(candidate)
assert len(eligible)==report['eligible_automorphisms']==144
assert network==min(eligible,key=lambda gs:[(a,b,op=='or') for op,a,b in gs])

literals=[int(x) for x in phases_path.read_text().splitlines()]
assert all(1<=abs(lit)<=meta['nv'] for lit in literals)
assert len(literals)==len(set(map(abs,literals)))==report['phase_literals']==5928
assert list(map(abs,literals))==sorted(map(abs,literals))
preferences={abs(lit):lit>0 for lit in literals}
expected={}
def put(var,value):
    assert var not in expected or expected[var]==bool(value)
    expected[var]=bool(value)
values=[run(network,mask) for mask in rows]
for i,(op,a,b) in enumerate(network):
    st=meta['structure'][i]
    for j,var in enumerate(st['left']):put(var,j==a)
    for j,var in enumerate(st['right']):put(var,j==b)
    put(st['op'],op=='or')
    for r,rowvalues in enumerate(values):
        put(st['left_values'][r],rowvalues[a])
        put(st['right_values'][r],rowvalues[b])
        put(st['out'][r],rowvalues[14+i])
assert expected==preferences
assert meta['nv']-len(preferences)==report['unphased_variables']==1325
mismatch=[i for i,m in enumerate(rows) if values[i][-1]!=target(m)]
assert mismatch==report['boundary_mismatches']==[5] and rows[5]==8194
errors=[]
remaining=E-{(1,13)}
for mask in range(16384):
    result=run(network,mask)[-1]
    assert result==any(mask&(1<<a) and mask&(1<<b) for a,b in remaining)
    if result!=target(mask):
        assert not result and target(mask)
        errors.append(mask)
assert len(errors)==report['full_errors']==47 and report['full_truth_assignments_checked']==16384

counts=Counter();violated=[];clause_count=0
for line in cnf.read_text().splitlines():
    if not line or line.startswith(('p ','c ')):continue
    clause=list(map(int,line.split()))
    assert clause[-1]==0
    clause=clause[:-1];clause_count+=1
    if any(preferences[abs(v)]==(v>0) for v in clause if abs(v) in preferences):counts['satisfied']+=1
    elif any(abs(v) not in preferences for v in clause):counts['unresolved']+=1
    else:violated.append(clause)
assert clause_count==208826
assert counts['satisfied']==report['partially_assigned_clauses_satisfied']==205934
assert counts['unresolved']==report['partially_assigned_clauses_unresolved']==2891
assert violated==report['fully_falsified_clauses']==[[7199]]
print(json.dumps(dict(status='PASS',eligible_automorphisms=len(eligible),
    unique_input_automorphisms_before_critical_filter=unique_before_critical,
    phase_literals=len(preferences),unphased_variables=1325,boundary_mismatch=rows[5],
    full_truth_assignments=16384,false_negatives=len(errors),
    satisfied_clauses=counts['satisfied'],unresolved_clauses=counts['unresolved'],violated_clauses=violated,
    phase_sha256=report['phase_sha256'],cnf_sha256=report['cnf_sha256'],
    scope='Soft phases only; exact target minus edge(1,13), not a witness'),sort_keys=True))
