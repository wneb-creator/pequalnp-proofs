from pathlib import Path
import json,resource,hashlib,itertools,time
resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(30,30));job=Path('/tmp/oec/pequalnp-pilot-79');source=job/'meta3773-five-patch-near-budget.json';model=job/'meta3773-five-patch-data.json';hashes={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [source,model]};p=json.loads(source.read_text());d=json.loads(model.read_text());R=d['raw_inputs'];N=d['inputs_with_free_or_signals'];samples=[(x,True) for x in d['positive_raw_masks']]+[(x,False) for x in d['maximal_negative_raw_masks']];target=(1<<len(d['positive_raw_masks']))-1;values=[0]*N;dependencies=[0]*N
for row,(raw,expected) in enumerate(samples):
 v=[bool(raw>>i&1) for i in range(R)]
 for a,b in p['free_ors']:v.append(v[a] or v[b])
 assert len(v)==N
 for i,b in enumerate(v):
  if b:values[i]|=1<<row
for i,(op,a,b) in enumerate(p['gates']):
 assert a<N+i and b<N+i;values.append((values[a]|values[b]) if op else (values[a]&values[b]));dependencies.append(dependencies[a]|dependencies[b]|(1<<i))
start=time.monotonic();found=None
for a in range(len(values)):
 for b in range(a,len(values)):
  for op in [0,1]:
   z=(values[a]|values[b]) if op else (values[a]&values[b]);dep=dependencies[a]|dependencies[b]
   if z==target and dep.bit_count()+1<=23:found=[[op,a,b]];break
   for c in range(len(values)):
    if (dep|dependencies[c]).bit_count()+2>23:continue
    for op2 in [0,1]:
     result=(z|values[c]) if op2 else (z&values[c])
     if result==target:found=[[op,a,b],[op2,len(values),c]];break
    if found:break
   if found:break
  if found:break
 if found:break
out={'classification':'Exact exhaustive search for one/two new output gates over the saved prefix; no general circuit exclusion','found':bool(found),'seconds':time.monotonic()-start,'source_hashes':hashes}
if found:
 gates=p['gates']+found;root=N+len(gates)-1;used=set()
 def visit(w):
  if w<N or w in used:return
  used.add(w);_,a,b=gates[w-N];visit(a);visit(b)
 visit(root);mapping={i:i for i in range(N)};answer=[]
 for w in sorted(used):
  op,a,b=gates[w-N];mapping[w]=N+len(answer);answer.append([op,mapping[a],mapping[b]])
 assert len(answer)<=23
 for raw in range(1<<R):
  vals=[bool(raw>>i&1) for i in range(R)]
  for a,b in p['free_ors']:vals.append(vals[a] or vals[b])
  for op,a,b in answer:vals.append((vals[a] or vals[b]) if op else (vals[a] and vals[b]))
  target_value=any(vals[a] and vals[b] for a,b in d['edges']);assert vals[mapping[root]]==target_value
 out.update(gates=answer,output=mapping[root],free_ors=p['free_ors'],size=len(answer),physical_truth_table_verified=True)
assert all(hashlib.sha256((job/name).read_bytes()).hexdigest()==digest for name,digest in hashes.items());(job/'meta3773-five-patch-output-repair.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
