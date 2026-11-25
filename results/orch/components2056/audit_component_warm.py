import argparse,hashlib,itertools,json
from pathlib import Path

ap=argparse.ArgumentParser()
for k in ['library','original','warm','output']:ap.add_argument('--'+k,required=True)
ap.add_argument('--model')
ap.add_argument('--unrenamed-model')
a=ap.parse_args()
original=Path(a.original);warm=Path(a.warm)
lib=json.loads(Path(a.library).read_text())
mapping=json.loads(original.with_suffix('.mapping.json').read_text())
phase=json.loads(warm.with_suffix('.phase.json').read_text())
mask=(warm.parent/phase['mask_name']).read_bytes()
assert hashlib.sha256(mask).hexdigest()==phase['mask_sha256']
assert len(mask)==(mapping['variables']+7)//8
def flip(v):return bool(mask[(v-1)//8]&(1<<((v-1)%8)))
preferred={v:not flip(v) for v in range(1,mapping['variables']+1)}
baseline=lib['baseline64']
selected={q for q,v in enumerate(mapping['selected']) if preferred[v]}
assert selected==set(range(26))|set(baseline['topological_profiles'])
picked={tuple(lib['productions'][i]) for i,v in enumerate(mapping['chosen']) if preferred[v]}
assert picked==set(map(tuple,baseline['chosen']))
depth={q:0 for q in range(len(lib['profiles']))}
by_parent={q:(u,v) for q,op,u,v in baseline['chosen']}
for q in baseline['topological_profiles']:
 u,v=by_parent[q];depth[q]=max(depth[u],depth[v])+1
depth[lib['goal']]=mapping['bound']
for q in range(26,len(lib['profiles'])):
 assert sum((1<<j) for j,v in enumerate(mapping['ranks'][q]) if preferred[v])==depth[q]
def load_model(path):
 model={};sat=False
 for line in Path(path).read_text().splitlines():
  if line.startswith('s '):sat=line.strip()=='s SATISFIABLE'
  if line.startswith('v '):
   for lit in map(int,line[2:].split()):
    if lit:
     assert abs(lit) not in model or model[abs(lit)]==(lit>0)
     model[abs(lit)]=lit>0
 assert sat and set(model)==set(range(1,mapping['variables']+1))
 return model
model=load_model(a.model) if a.model else None
inverse={v:value^flip(v) for v,value in model.items()} if model else None
if a.unrenamed_model:assert inverse==load_model(a.unrenamed_model)
count=0;bad=[];sha1=hashlib.sha256();sha2=hashlib.sha256()
with original.with_suffix('.cnf').open('rb') as f,warm.with_suffix('.cnf').open('rb') as g:
 for x,y in itertools.zip_longest(f,g):
  assert x is not None and y is not None
  sha1.update(x);sha2.update(y)
  if x.startswith((b'p',b'c')) or not x.strip():assert x==y;continue
  old=list(map(int,x.split()));new=list(map(int,y.split()))
  assert old[-1]==new[-1]==0
  assert new[:-1]==[-v if flip(abs(v)) else v for v in old[:-1]]
  count+=1
  if not any(preferred[abs(v)]==(v>0) for v in old[:-1]):bad.append({'index':count,'literals':old[:-1]})
  if model:
   assert any(model[abs(v)]==(v>0) for v in new[:-1])
   assert any(inverse[abs(v)]==(v>0) for v in old[:-1])
assert count==mapping['clauses']==phase['clauses']
assert bad==phase['violated_original_clauses'] and len(bad)==64-mapping['bound']
assert sha1.hexdigest()==phase['original_cnf_sha256'] and sha2.hexdigest()==phase['warm_cnf_sha256']
result={'source_scope':'Independent exact clause-by-clause sign-renaming and baseline replay; no added constraints','bound':mapping['bound'],'variables':mapping['variables'],'clauses':count,'original_sha256':sha1.hexdigest(),'warm_sha256':sha2.hexdigest(),'phase_failures':bad,'model_checked_both_signs':bool(model),'unrenamed_model_matches_inverse':bool(a.unrenamed_model)}
if inverse:
 selected={q for q,v in enumerate(mapping['selected']) if inverse[v]}
 producers={}
 for i,var in enumerate(mapping['chosen']):
  if inverse[var]:
   q,op,u,v=lib['productions'][i]
   assert q not in producers and {q,u,v}<=selected
   producers[q]=(op,u,v)
 assert set(producers)==selected-set(range(26))
 assert len(producers)<=mapping['bound']
 rank={q:0 for q in range(26)}
 for q in producers:rank[q]=sum(1<<j for j,v in enumerate(mapping['ranks'][q]) if inverse[v])
 wire={q:q for q in range(26)};gates=[]
 for q in sorted(producers,key=lambda q:(rank[q],q)):
  op,u,v=producers[q];assert rank[u]<rank[q] and rank[v]<rank[q]
  gates.append([op,wire[u],wire[v]]);wire[q]=26+len(gates)-1
 output=wire[lib['goal']]
 edges={(p,13+l) for p in range(13) for l in range(13) if (p+l)%13 in (0,1,3,9)}
 neighbors=[sum(1<<l for l in range(13) if (p,13+l) in edges) for p in range(13)]
 negatives=set()
 for points in range(8192):
  lines=8191
  for p in range(13):
   if points&(1<<p):lines&=~neighbors[p]
  if points==sum(1<<p for p in range(13) if not neighbors[p]&lines):negatives.add(points|(lines<<13))
 positives={(1<<p)|(1<<l) for p,l in edges}
 assert len(positives)==52 and len(negatives)==704
 for row in positives|negatives:
  values=[bool(row&(1<<p)) for p in range(26)]
  for op,u,v in gates:values.append(values[u] or values[v] if op else values[u] and values[v])
  assert values[output]==(row in positives)
 result.update(decoded_size=len(gates),regenerated_rows_checked=756)
Path(a.output).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
