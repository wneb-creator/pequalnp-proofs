from pathlib import Path
import json,hashlib
base=Path('/tmp/oec/pequalnp-pilot-121/plane2056-cegis');pre=base/'warm-dirty2-control67-fixed-negative';mapping=json.loads(pre.with_suffix('.mapping.json').read_text());meta=json.loads(pre.with_suffix('.json').read_text());assert meta['exit_code']==20
sol=pre.with_suffix('.sol').read_text();assert 's UNSATISFIABLE' in sol
rows=mapping['rows'];pos={(1<<p)|(1<<(13+l)) for p in range(13) for l in range(13) if (p+l)%13 in {0,1,3,9}};target=sum((r in pos)<<k for k,r in enumerate(rows));negmask=((1<<len(rows))-1)^target
vs=[sum(((r>>i)&1)<<k for k,r in enumerate(rows)) for i in range(26)]
for j,(op,u,v) in enumerate(mapping['warm_gates']):assert op in (0,1) and 0<=u<26+j and 0<=v<26+j;vs.append(vs[u]|vs[v] if op else vs[u]&vs[v])
assert vs[-1]==target and len(mapping['warm_gates'])==67 and meta['fixed_prefix']==67
flip=set(mapping['flipped_variables']);dirty=[]
for j,(op,u,v) in enumerate(mapping['warm_gates']):
 clean=not bool(vs[26+j]&negmask);d=op==0 and not clean
 assert (mapping['clean_flags'][j] in flip)==clean and (mapping['dirty_and_flags'][j] in flip)==d
 if d:dirty.append(26+j)
assert len(dirty)==1 and mapping['dirty_at_least_two_variable'] not in flip
fail=[];count=0
with pre.with_suffix('.cnf').open('rb') as f:
 h=f.readline().split();assert list(map(int,h[2:]))==[meta['variables'],meta['clauses']]
 for i,line in enumerate(f,1):
  xs=line.split();assert xs[-1]==b'0'
  if not any(x.startswith(b'-') for x in xs[:-1]):fail.append({'index':i,'clause':[int(x) for x in xs[:-1]]})
  count+=1
assert count==meta['clauses'] and len(fail)==1 and fail[0]['clause']==[mapping['dirty_at_least_two_variable']]
r={'scope':'Fixed correct67-gate one-dirty control rejected; not a global UNSAT or circuit lower-bound result','native_status':'UNSAT fixed control','native_exit':20,'clauses':count,'variables':meta['variables'],'cnf_sha256':hashlib.sha256(pre.with_suffix('.cnf').read_bytes()).hexdigest(),'fixed_gates':67,'warm_boundary_errors':0,'actual_warm_dirty_AND_wires':dirty,'only_phase_failure':fail[0],'all_other_clauses_pass':True}
out=Path('/tmp/oec/pequalnp-pilot-121/dirty2-negative67-independent-review.json');out.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
