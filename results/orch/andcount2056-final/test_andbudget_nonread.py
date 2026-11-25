from pathlib import Path
import importlib.util,json,random,hashlib,datetime
base=Path('/tmp/oec/pequalnp-pilot-121');source=base/'andcount2056/andcount_budget_profile_nonread2056.py'
spec=importlib.util.spec_from_file_location('enc',source);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
edges,rows=m.geometry();rng=random.Random(20561125)
def traces(c,p,l):
 v=[{(1,0)} if i==p else {(0,1)} if i==l else set() for i in range(26)]
 for op,a,b in c['gates']:
  v.append(v[a]|v[b] if op else {(min(2,x+u),min(2,y+w)) for x,y in v[a] for u,w in v[b]})
 return set() if c['constant_false'] else v[c['output']]
def check(model):
 _,expected=m.evaluate(model,rows);literal=m.literal_materialize(model);optimized=m.materialize(model)
 assert m.ordinary_eval(literal,rows)==expected==m.ordinary_eval(optimized,rows)
 direct=[k for k,(p,l) in enumerate(edges) if (1,1) in traces(literal,p,l)]
 assert direct==m.split_read1_edges(model,edges)==m.ordinary_read1_edges(literal,edges)
 optimized_direct=[k for k,(p,l) in enumerate(edges) if (1,1) in traces(optimized,p,l)]
 assert optimized_direct==m.ordinary_read1_edges(optimized,edges)
 A=sum(bool(r['left']) for r in model['ands']);M=sum(len(r['left'])+len(r['right']) for r in model['ands'])+len(model['output'])
 if expected:assert literal['size']<=M-A-1
 return direct,optimized_direct
for trial in range(500):
 K=rng.randrange(1,20);records=[]
 for j in range(K):
  if rng.randrange(6)==0:records.append({'left':[],'right':[]})
  else:records.append({side:sorted(rng.sample(range(26+j),rng.randrange(1,6))) for side in ['left','right']})
 model={'ands':records,'output':sorted(rng.sample(range(K),rng.randrange(1,K+1)))};check(model)
example={'ands':[{'left':[0],'right':[0]},{'left':[26],'right':[13]}],'output':[1]};lit,opt=check(example);assert not lit and edges.index((0,13)) in opt
star=m.star_model(16,edges);assert len(check(star)[0])==52
result={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','random_models':500,'rows_each':756,'edges_each':52,'independent_reference':'full capped leaf-multiplicity pair sets per edge','alias_example':{'literal_read1_edges':lit,'optimized_read1_edges':opt},'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'test_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(base/'not-elimination/andbudget-nonread-differential.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
