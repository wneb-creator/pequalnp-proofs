#!/usr/bin/env python3
"""Independent static/data audit of the frozen joint TEN phase preferences."""
from pathlib import Path
import hashlib
import json

base=Path('/tmp/oec/pequalnp-pilot-70/constructive')
meta_path=base/'joint-ten10.map.json'
seed_path=base/'four-star-cut-cone-seed10-missing-1-13.json'
phase_path=base/'joint-ten10-branch3-near.phases'
report=json.loads((base/'joint-ten10-branch3-near.json').read_text())
m=json.loads(meta_path.read_text())
seed=json.loads(seed_path.read_text())
cnf=base/'joint-ten10.cnf'
for key,path in [('metadata_sha256',meta_path),('seed_sha256',seed_path),('cnf_sha256',cnf)]:
    assert report[key]==hashlib.sha256(path.read_bytes()).hexdigest()
assert report['cnf_sha256']==m['cnf_sha256']
assert m['format']=='joint-correlated-v1' and m['ninputs']==18 and m['gates']==10
assert report['branch']==3 and report['variant']==3
d=m['variants'][3]['data']
assert d['real_inputs']==10 and d['cut_inputs']==18
gates=report['normalized_gates']
assert len(gates)==10 and seed['output']==27 and seed['cut_inputs']==18
original=[['or' if op==1 else 'and',a,b] for op,a,b in seed['gates']]
assert all(op in (0,1) for op,a,b in seed['gates'])
for i,(op,a,b) in enumerate(gates):
    assert op in ('and','or') and 0<=a<=b<18+i

def run(values,network):
    v=list(values)
    for op,a,b in network:
        assert 0<=a<len(v) and 0<=b<len(v)
        v.append(v[a] and v[b] if op=='and' else v[a] or v[b])
    return v

def cuts(mask):
    values=[bool(mask&(1<<i)) for i in range(10)]
    return values+[any(values[v] for v in support) for support in d['free_or_supports']]

def edge_value(values,edges):
    return any(values[a] and values[b] for a,b in edges)

phase_lits=[int(s) for s in phase_path.read_text().splitlines()]
assert phase_lits and all(1<=abs(lit)<=m['nv'] for lit in phase_lits)
assert len(set(map(abs,phase_lits)))==len(phase_lits)==991
assert list(map(abs,phase_lits))==sorted(map(abs,phase_lits))
phases={abs(lit):lit>0 for lit in phase_lits}
expected={}
def put(literal,value):
    var=abs(literal)
    value=bool(value) if literal>0 else not bool(value)
    assert 1<=var<=m['nv']
    assert var not in expected or expected[var]==value
    expected[var]=value
put(m['truth'],True)
for branch,var in enumerate(m['variant_selectors']): put(var,branch==3)

rows=m['variants'][3]['ordered_rows']
assert [r['mask'] for r in rows]==m['ordered_base_masks']
bad_rows=[]
for r,row in enumerate(rows):
    initial=cuts(row['mask'])
    assert initial==list(map(bool,row['cuts']))
    assert bool(row['value'])==edge_value(initial,d['edges'])
    values=run(initial,gates)
    for wire,truth in enumerate(initial): put(m['input_values'][wire][r],truth)
    for index,(op,left,right) in enumerate(gates):
        st=m['structure'][index]
        put(st['lv'][r],values[left]);put(st['rv'][r],values[right])
        put(st['out'][r],values[18+index])
    if values[-1]!=bool(row['value']): bad_rows.append(row['mask'])
for index,(op,left,right) in enumerate(gates):
    st=m['structure'][index]
    for wire,var in enumerate(st['left']): put(var,wire==left)
    for wire,var in enumerate(st['right']): put(var,wire==right)
    put(st['op'],op=='or')
assert phases==expected
assert bad_rows==report['boundary_mismatches']==[513]

missing=tuple(seed['missing_local_edge'])
assert missing==(0,9)
assert tuple(d['original_variables'][v] for v in missing)==tuple(seed['missing_original_edge'])==(1,13)
remaining=[e for e in d['edges'] if tuple(e)!=missing]
residual_errors=0
for mask in range(1024):
    initial=cuts(mask)
    result=run(initial,gates)[-1]
    assert result==run(initial,original)[-1]
    assert result==edge_value(initial,remaining)
    residual_errors+=result!=edge_value(initial,d['edges'])
assert residual_errors==report['residual_target_errors']==16

heawood=[(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),
 (3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),
 (6,8),(6,9),(6,11)]
full=[['or' if op==1 else 'and',a,b] for op,a,b in d['fixed_gates']]
mapping=list(d['original_variables'])+list(d['fixed_cut_wires'])
for op,a,b in gates:
    full.append([op,mapping[a],mapping[b]])
    mapping.append(14+len(full)-1)
full.append(['or',d['fixed_output'],mapping[-1]])
assert len(full)==report['full_gate_count']==26
full_errors=0
for mask in range(16384):
    initial=[bool(mask&(1<<i)) for i in range(14)]
    fixed=run(initial,full[:15])
    local_mask=sum(int(initial[original])<<i for i,original in enumerate(d['original_variables']))
    assert [fixed[i] for i in d['original_variables']+d['fixed_cut_wires']]==cuts(local_mask)
    result=run(initial,full)[-1]
    assert result==edge_value(initial,[e for e in heawood if e!=(1,13)])
    full_errors+=result!=edge_value(initial,heawood)
assert full_errors==report['full_target_errors']==47
assert report['checked_residual_assignments']==1024 and report['checked_full_assignments']==16384

all_clauses=[]
for line in cnf.read_text().splitlines():
    if line.startswith('p '):
        assert line==f'p cnf {m["nv"]} {m["clauses"]}'
    elif line and not line.startswith('c '):
        ints=list(map(int,line.split()))
        assert ints[-1]==0
        all_clauses.append(ints[:-1])
assert len(all_clauses)==m['clauses']==24789
false=[clause for clause in all_clauses
    if all(abs(lit) in phases for lit in clause)
    and not any(phases[abs(lit)]==(lit>0) for lit in clause)]
assert len(false)==report['fully_phased_false_clauses']==1
assert false==[[m['structure'][-1]['out'][6]]]
assert report['phase_count']==991 and report['unphased_auxiliaries']==m['nv']-991==432

print(json.dumps(dict(status='PASS',branch=3,phases=991,unphased=432,nv=m['nv'],
    boundary_mismatches=bad_rows,residual_assignments=1024,residual_target_errors=residual_errors,
    full_assignments=16384,full_target_errors=full_errors,
    full_gate_count=len(full),fully_phased_false_clauses=false,
    phase_sha256=hashlib.sha256(phase_path.read_bytes()).hexdigest(),
    cnf_sha256=report['cnf_sha256'],scope='Soft preferences only; near-seed is not a target witness'),sort_keys=True))
