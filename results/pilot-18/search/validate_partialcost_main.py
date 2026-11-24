import importlib.util,itertools,json,hashlib,functools,random,time
from pathlib import Path
P=Path('/tmp/oec/pequalnp-pilot-18');source=P/'search_l1342_shard17_partialcost.py'
spec=importlib.util.spec_from_file_location('candidate',source);mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
started=time.monotonic();totalizer_cases=0
for n in range(10):
 for cap in range(1,n+2):
  cnf=mod.CNF();inputs=[cnf.var() for _ in range(n)]
  out=mod.totalizer_atleast(cnf,inputs,cap)
  for mask in range(1<<n):
   true={v for i,v in enumerate(inputs) if mask>>i&1}
   # Generator is topological; a single forward pass evaluates its Horn closure.
   for clause in cnf.clauses:
    assert clause[-1]>0 and all(x<0 for x in clause[:-1])
    if all(-x in true for x in clause[:-1]):true.add(clause[-1])
   assert [v in true for v in out]==[mask.bit_count()>=j for j in range(1,len(out)+1)]
   totalizer_cases+=1
edges=mod.EDGES;inc=[sum(1<<i for i,e in enumerate(edges) if v in e) for v in range(11)]
@functools.lru_cache(None)
def tau(mask):
 if not mask:return 0
 u,v=edges[(mask&-mask).bit_length()-1]
 return 1+min(tau(mask&~inc[u]),tau(mask&~inc[v]))
cost=[12]*(1<<16)
for cover in range(1<<11):
 covered=0
 for v in range(11):
  if cover>>v&1:covered|=inc[v]
 cost[covered]=min(cost[covered],cover.bit_count())
for bit in range(16):
 for mask in range(1<<16):
  if not mask>>bit&1:cost[mask]=min(cost[mask],cost[mask|(1<<bit)])
assert all(cost[mask]==tau(mask) for mask in range(1<<16))
# Random actual clean-prefix circuits: finite evidence only, not mathematical proof.
rng=random.Random(134217);circuit_checks=0;full=(1<<11)-1
for trial in range(1024):
 supports=[1<<v for v in range(11)]+[0,full]
 values=[inc[v] for v in range(11)]+[0,(1<<16)-1]
 for gate in range(21):
  feasible=[]
  if trial%3!=0:
   for a in range(len(supports)):
    for b in range(a,len(supports)):
     sa,sb=supports[a],supports[b]
     if sa and sb and all(u!=v and (min(u,v),max(u,v)) in edges for u in range(11) if sa>>u&1 for v in range(11) if sb>>v&1):feasible.append((a,b))
  if feasible and rng.random()<0.6:
   a,b=rng.choice(feasible);s=0;e=values[a]&values[b]
  else:
   a=rng.randrange(len(supports));b=rng.randrange(len(supports));s=supports[a]|supports[b];e=values[a]|values[b]
  supports.append(s);values.append(e)
  if s!=full:
   residual=e
   for v in range(11):
    if s>>v&1:residual&=~inc[v]
   assert s.bit_count()+residual.bit_count()+tau(residual)-1<=gate+1,(trial,gate,s,e)
  circuit_checks+=1
report={'status':'PASS: finite implementation controls; mathematical and independent code review separate','source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'totalizer_projection_assignments':totalizer_cases,'vertex_cover_graph_subsets':65536,'random_clean_prefix_wire_checks':circuit_checks,'seconds':round(time.monotonic()-started,3)}
(P/'partialcost-main-validation.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
