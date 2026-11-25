from pathlib import Path
import json,hashlib
base=Path('/tmp/oec/pequalnp-pilot-121/plane2056-cegis')
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
pre=base/'warm-and13-control64-free3-v2';mapping=json.loads(pre.with_suffix('.mapping.json').read_text());meta=json.loads(pre.with_suffix('.json').read_text());assignment={};sat=False
for line in pre.with_suffix('.sol').read_text().splitlines():
 if line.startswith('s '):sat=line=='s SATISFIABLE'
 if line.startswith('v '):
  for x in map(int,line.split()[1:]):
   if x:assert abs(x) not in assignment or assignment[abs(x)]==(x>0);assignment[abs(x)]=x>0
assert sat and set(assignment)==set(range(1,meta['variables']+1))
true_tokens={str(v if t else -v).encode() for v,t in assignment.items()};all_false=not any(assignment.values());count=0
with pre.with_suffix('.cnf').open('rb') as f:
 header=f.readline().split();assert list(map(int,header[2:]))==[meta['variables'],meta['clauses']]
 for line in f:
  xs=line.split();assert xs[-1]==b'0' and (b'-' in line if all_false else any(x in true_tokens for x in xs[:-1]));count+=1
assert count==meta['clauses']
flip=set(mapping['flipped_variables']);truth=lambda x:x if isinstance(x,bool) else assignment[x]^(x in flip)
gates=[]
for op,ls,rs in zip(mapping['ops'],mapping['left'],mapping['right']):
 aa=[i for i,x in enumerate(ls) if truth(x)];bb=[i for i,x in enumerate(rs) if truth(x)];assert len(aa)==len(bb)==1;gates.append([int(truth(op)),aa[0],bb[0]])
assert gates==meta['gates'];assert gates[:meta['fixed_prefix']]==mapping['warm_gates'][:meta['fixed_prefix']]
positives={(1<<p)|(1<<(13+l)) for p in range(13) for l in range(13) if (p+l)%13 in {0,1,3,9}};negatives=set()
for points in range(1<<13):
 lines=sum(1<<l for l in range(13) if all(not(points>>p&1) or (p+l)%13 not in {0,1,3,9} for p in range(13)))
 closed=sum(1<<p for p in range(13) if all(not(lines>>l&1) or (p+l)%13 not in {0,1,3,9} for l in range(13)))
 if closed==points:negatives.add(points|(lines<<13))
rows=mapping['rows'];assert len(rows)==756 and set(rows)==positives|negatives and len(positives)==52 and len(negatives)==704
v=[sum(((row>>i)&1)<<j for j,row in enumerate(rows)) for i in range(26)]
for j,(op,a,b) in enumerate(gates):assert op in (0,1) and 0<=a<26+j and 0<=b<26+j;v.append(v[a]|v[b] if op else v[a]&v[b])
target=sum((row in positives)<<j for j,row in enumerate(rows));assert v[-1]==target
for j,x in enumerate(mapping['outputs']):assert truth(x)==bool(target>>j&1)
assert sum(op==0 for op,a,b in gates)>=13
report={'scope':'Future full-SAT AND13 first-layer positive control only; no63 witness.','source_sha256':digest(base/'direct_cnf_warm_first_and13.py'),'native_clauses_checked':count,'native_variables':meta['variables'],'decoded_gates':len(gates),'decoded_ANDs':sum(op==0 for op,a,b in gates),'fixed_prefix_verified':meta['fixed_prefix'],'native_model_sha256':digest(pre.with_suffix('.sol')),'native_cnf_sha256':digest(pre.with_suffix('.cnf')),'full_geometry_rows_verified':len(rows),'native_model_all_false':all_false}
assert pre.with_suffix('.cnf').read_bytes()==(base/'warm-and13-control64-free3.cnf').read_bytes()
report['first_UNKNOWN_query_byte_identical']=True
Path('/tmp/oec/pequalnp-pilot-121/and13-native64-independent-review.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
