from pathlib import Path
import json,hashlib
base=Path('/tmp/oec/pequalnp-pilot-121/plane2056-cegis')
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
pre=base/'warm-dirty2-control69-free3';mapping=json.loads(pre.with_suffix('.mapping.json').read_text());meta=json.loads(pre.with_suffix('.json').read_text());assignment={};sat=False
for line in pre.with_suffix('.sol').read_text().splitlines():
 if line.startswith('s '):sat=line=='s SATISFIABLE'
 if line.startswith('v '):
  for x in map(int,line.split()[1:]):
   if x:assert abs(x) not in assignment or assignment[abs(x)]==(x>0);assignment[abs(x)]=x>0
assert sat and set(assignment)==set(range(1,meta['variables']+1))
true_tokens={str(v if t else -v).encode() for v,t in assignment.items()};count=0
with pre.with_suffix('.cnf').open('rb') as f:
 header=f.readline().split();assert list(map(int,header[2:]))==[meta['variables'],meta['clauses']]
 for line in f:
  xs=line.split();assert xs[-1]==b'0' and any(x in true_tokens for x in xs[:-1]);count+=1
assert count==meta['clauses']
flip=set(mapping['flipped_variables']);truth=lambda x:x if isinstance(x,bool) else assignment[x]^(x in flip)
gates=[]
for op,ls,rs in zip(mapping['ops'],mapping['left'],mapping['right']):
 aa=[i for i,x in enumerate(ls) if truth(x)];bb=[i for i,x in enumerate(rs) if truth(x)];assert len(aa)==len(bb)==1;gates.append([int(truth(op)),aa[0],bb[0]])
assert gates==meta['gates'];assert gates[:meta['fixed_prefix']]==mapping['warm_gates'][:meta['fixed_prefix']]
edgechoices=[edge for edge,var in zip(mapping['joint_edges'],mapping['joint_edge_selectors']) if truth(var)];assert len(edgechoices)==1
p,l=edgechoices[0];proof=[{(1,0)} if i==p else {(0,1)} if i==l else set() for i in range(26)]
for op,a,b in gates:
 if op:proof.append(proof[a]|proof[b])
 else:proof.append({(x1+x2,y1+y2) for x1,y1 in proof[a] for x2,y2 in proof[b] if x1+x2<=1 and y1+y2<=1})
for counts,flags in zip(proof,mapping['joint_profiles']):assert [truth(x) for x in flags]==[(1,0) in counts,(0,1) in counts,(1,1) in counts]
assert (1,1) not in proof[-1] and edgechoices[0]==meta['model_non_read1_edge']
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
negative_mask=sum((row in negatives)<<j for j,row in enumerate(rows))
dirty=[]
for j,(op,a,b) in enumerate(gates):
 is_clean=not bool(v[26+j]&negative_mask)
 is_dirty_and=op==0 and not is_clean
 assert truth(mapping['clean_flags'][j])==is_clean
 assert truth(mapping['dirty_and_flags'][j])==is_dirty_and
 if is_dirty_and:dirty.append(26+j)
assert len(dirty)>=2 and dirty==meta['model_dirty_AND_wires']
assert truth(mapping['dirty_at_least_two_variable'])
report={'scope':'Full-SAT dirty2 preparation positive69 control only; no63 witness.','source_sha256':digest(base/'direct_cnf_warm_dirty2.py'),'native_clauses_checked':count,'native_variables':meta['variables'],'decoded_gates':len(gates),'actual_dirty_AND_wires':dirty,'clean_and_dirty_flags_all_replayed':True,'decoded_ANDs':sum(op==0 for op,a,b in gates),'fixed_prefix_verified':meta['fixed_prefix'],'native_model_sha256':digest(pre.with_suffix('.sol')),'native_cnf_sha256':digest(pre.with_suffix('.cnf')),'selected_edge':edgechoices[0],'independent_capped_read_counts_match_every_wire':True,'full_geometry_rows_verified':len(rows)}
Path('/tmp/oec/pequalnp-pilot-121/dirty2-native69-independent-review.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
