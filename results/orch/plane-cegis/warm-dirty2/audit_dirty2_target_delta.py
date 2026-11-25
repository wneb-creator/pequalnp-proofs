from pathlib import Path
import json,hashlib
base=Path('/tmp/oec/pequalnp-pilot-121/plane2056-cegis')
old=base/'warm-nonread-and13-near63-query';new=base/'warm-dirty2-near63-query'
om=json.loads(old.with_suffix('.mapping.json').read_text());nm=json.loads(new.with_suffix('.mapping.json').read_text());meta=json.loads(new.with_suffix('.json').read_text())
with old.with_suffix('.cnf').open('rb') as a,new.with_suffix('.cnf').open('rb') as b:
 oh=a.readline().split();nh=b.readline().split();ov,oc=map(int,oh[2:]);nv,nc=map(int,nh[2:]);assert [nv,nc]==[meta['variables'],meta['clauses']]
 for i,line in enumerate(a,1):assert line==b.readline(),('old prefix mismatch',i)
 assert i==oc
 tail=list(b);assert len(tail)==nc-oc
for k,v in om.items():
 if k=='flipped_variables':assert v==[x for x in nm[k] if x<=ov]
 else:assert v==nm[k],k
rows=nm['rows'];edges=[(p,13+l) for p in range(13) for l in range(13) if (p+l)%13 in {0,1,3,9}]
pos={(1<<u)|(1<<v) for u,v in edges};mask=(1<<len(rows))-1
vals=[sum(((r>>i)&1)<<k for k,r in enumerate(rows)) for i in range(26)]
for op,u,v in nm['warm_gates']:vals.append(vals[u]|vals[v] if op else vals[u]&vals[v])
target=sum((r in pos)<<k for k,r in enumerate(rows));bad=[k for k in range(len(rows)) if ((vals[-1]^target)>>k)&1]
assert all(rows[k] in pos and not(vals[-1]>>k&1) for k in bad)
flip=set(nm['flipped_variables']);expected=[nm['outputs'][k] for k in bad]+[nm['dirty_at_least_two_variable']]
assert all(v not in flip for v in expected)
failures=[];seen=0
with new.with_suffix('.cnf').open('rb') as f:
 f.readline()
 for i,line in enumerate(f,1):
  xs=line.split();assert xs[-1]==b'0'
  if not any(x.startswith(b'-') for x in xs[:-1]):failures.append({'index':i,'clause':[int(x) for x in xs[:-1]]})
  seen+=1
assert seen==nc and sorted(x['clause'] for x in failures)==sorted([[x] for x in expected])
negmask=sum((r not in pos)<<k for k,r in enumerate(rows));dirty=[26+j for j,(op,u,v) in enumerate(nm['warm_gates']) if op==0 and vals[26+j]&negmask]
assert len(dirty)==1
report={'scope':'Full dirty2 target phase/delta audit only; no target SAT or UNSAT result','old_clauses_byte_identical':oc,'new_clauses':nc-oc,'new_variables':nv-ov,'target_clauses':nc,'target_variables':nv,'target_sha256':hashlib.sha256(new.with_suffix('.cnf').read_bytes()).hexdigest(),'phase_failures':failures,'missing_positive_rows':[rows[k] for k in bad],'actual_warm_dirty_AND_wires':dirty,'all_old_mapping_fields_preserved':True,'unexpected_failures':0}
out=Path('/tmp/oec/pequalnp-pilot-121/dirty2-target-delta-independent-review.json');out.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
