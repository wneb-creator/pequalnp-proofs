#!/usr/bin/env python3
"""Independent append-only DIMACS and exact-witness review; no solving."""
import argparse
import hashlib
import json
from pathlib import Path

p=argparse.ArgumentParser()
p.add_argument('base',type=Path)
p.add_argument('augmented',type=Path)
p.add_argument('--model',type=Path)
p.add_argument('--witness',type=Path)
a=p.parse_args()

def read_cnf(path):
    lines=path.read_text().splitlines()
    headers=[i for i,s in enumerate(lines) if s.startswith('p ')]
    assert len(headers)==1
    h=headers[0]
    mark,kind,nv,nc=lines[h].split()
    assert mark=='p' and kind=='cnf'
    nv,nc=int(nv),int(nc)
    clauses=[]
    for s in lines:
        if not s or s.startswith(('p ','c ')): continue
        q=list(map(int,s.split()))
        assert q[-1]==0 and 0 not in q[:-1]
        assert all(abs(x)<=nv for x in q[:-1])
        clauses.append(tuple(q[:-1]))
    assert len(clauses)==nc
    return lines,h,nv,nc,clauses

before=read_cnf(a.base)
after=read_cnf(a.augmented)
bm=json.loads(a.base.with_suffix('.map.json').read_text())
am=json.loads(a.augmented.with_suffix('.map.json').read_text())
assert before[2]==after[2]==bm['nv']==am['nv']
assert before[3]==bm['clauses'] and after[3]==am['clauses']
assert after[4][:before[3]]==before[4]
assert after[0][:before[1]]==before[0][:before[1]]
assert after[0][before[1]+1:len(before[0])]==before[0][before[1]+1:]
for key,value in bm.items():
    if key!='clauses': assert am[key]==value,(key,'metadata changed')
assert set(am)-set(bm)=={'raw_pair_fanout'}
assert am['raw_pair_fanout']['source_sha256']==hashlib.sha256(a.base.read_bytes()).hexdigest()

structures=bm['structure']
n=len(structures)
assert n==bm['gates'] and bm['ninputs']==14
expected=[]
for gate_number in range(n):
    selectors=structures[gate_number]
    for first in range(14):
        for second in range(first+1,14):
            condition=(-selectors['left'][first],-selectors['right'][second])
            for raw in (first,second):
                consequences=[]
                for other_number in range(n):
                    if other_number==gate_number: continue
                    for side in ('left','right'):
                        consequences.append(structures[other_number][side][raw])
                expected.append(condition+tuple(consequences))
delta=after[4][before[3]:]
assert delta==expected
assert len(delta)==n*14*13
assert all(len(clause)==2*n for clause in delta)
assert am['raw_pair_fanout']['added_clauses']==len(delta)

edges=[tuple(e) for e in bm['edges']]
assert len(edges)==21
target=lambda mask:any(mask&(1<<u) and mask&(1<<v) for u,v in edges)
adj=[{v if u==x else u for u,v in edges if x in (u,v)} for x in range(14)]
assert all(len(s)==3 for s in adj)
assert all(len(adj[x]&adj[y])<=1 for x in range(14) for y in range(x))
necessity_witnesses=0
for x in range(14):
    for y in range(14):
        if x==y: continue
        for canalizing in (0,1):
            # If x only feeds op(x,y), fixing y to this value hides x.
            # Exhibit a target restriction where x remains essential instead.
            found=False
            for mask in range(1<<14):
                if mask&(1<<x) or bool(mask&(1<<y))!=bool(canalizing): continue
                if target(mask)!=target(mask|(1<<x)):
                    found=True
                    break
            assert found,(x,y,canalizing)
            necessity_witnesses+=1

model_clauses=0
if a.model:
    values={}
    for line in a.model.read_text().splitlines():
        if line.startswith('v '):
            for lit in map(int,line.split()[1:]):
                if not lit: continue
                if abs(lit) in values: assert values[abs(lit)]==(lit>0)
                values[abs(lit)]=lit>0
    assert all(v in values for clause in after[4] for v in map(abs,clause))
    for clause in after[4]:
        assert any(values[abs(lit)]==(lit>0) for lit in clause)
    model_clauses=len(after[4])

truth_inputs=0
if a.witness:
    network=json.loads(a.witness.read_text())
    assert len(network)==n
    for i,(op,left,right) in enumerate(network):
        assert op in ('and','or') and 0<=left<=right<14+i
    for mask in range(1<<14):
        wires=[bool(mask&(1<<v)) for v in range(14)]
        for op,left,right in network:
            wires.append((wires[left] and wires[right]) if op=='and' else (wires[left] or wires[right]))
        assert wires[-1]==target(mask),mask
        truth_inputs+=1
    if a.model:
        for i,(op,left,right) in enumerate(network):
            st=structures[i]
            assert [j for j,var in enumerate(st['left']) if values[var]]==[left]
            assert [j for j,var in enumerate(st['right']) if values[var]]==[right]
            assert values[st['op']]==(op=='or')

print(json.dumps(dict(status='PASS',base=str(a.base),augmented=str(a.augmented),
    unchanged_variables=after[2],unchanged_base_clauses=before[3],
    exactly_reconstructed_new_clauses=len(delta),clause_length=2*n,
    target_necessity_witnesses=necessity_witnesses,
    satisfied_model_clauses=model_clauses,full_truth_inputs=truth_inputs,
    source_sha256=hashlib.sha256(a.base.read_bytes()).hexdigest(),
    output_sha256=hashlib.sha256(a.augmented.read_bytes()).hexdigest()),sort_keys=True))
