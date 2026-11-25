from pathlib import Path
import itertools,json,hashlib,resource
resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(30,30));job=Path('/tmp/oec/pequalnp-pilot-79')
for stem in ['five','six','six-dense']:
 source=job/('meta3773-'+stem+'-patch-data.json');digest=hashlib.sha256(source.read_bytes()).hexdigest();d=json.loads(source.read_text());R=d['raw_inputs'];N=d['inputs_with_free_or_signals'];K=len(d['point_inputs']);neighbors=[{b for a,b in d['edges'] if a==i} for i in range(K)];best=None;count=0
 for a,c in itertools.combinations(range(K),2):
  common=neighbors[a]&neighbors[c];assert len(common)==1
  us=sorted(neighbors[a]-common);vs=sorted(neighbors[c]-common)
  for perm in itertools.permutations(vs):
   selections={};signals=[]
   for u,v in zip(us,perm):
    possible=[(i,j) for i,g in enumerate(d['outside_groups']) for j,var in enumerate(g['variants']) if set(var[0])=={u,v}]
    if not possible:break
    i,j=possible[0];assert i not in selections;selections[i]=j;signals.append(d['outside_groups'][i]['first_free_wire'])
   if len(signals)!=3:continue
   free=[]
   for i,g in enumerate(d['outside_groups']):free.extend(g['variants'][selections.get(i,0)])
   support=[{i} for i in range(R)]
   for x,y in free:assert x<len(support) and y<len(support);support.append(support[x]|support[y])
   assert set().union(*(support[x] for x in signals),common)==neighbors[a]|neighbors[c]
   gates=[]
   def gate(op,x,y):gates.append([op,x,y]);return N+len(gates)-1
   def union(xs):
    out=xs[0]
    for x in xs[1:]:out=gate(1,out,x)
    return out
   terms=[gate(0,gate(1,a,c),union(signals+list(common)))]
   for i in range(K):
    if i not in [a,c]:terms.append(gate(0,i,union(sorted(neighbors[i]))))
   output=union(terms);assert len(gates)==5*K-5;fn=[];fp=[]
   for raw,expected in [(x,True) for x in d['positive_raw_masks']]+[(x,False) for x in d['maximal_negative_raw_masks']]:
    values=[bool(raw>>i&1) for i in range(R)]
    for x,y in free:values.append(values[x] or values[y])
    for op,x,y in gates:values.append((values[x] or values[y]) if op else(values[x] and values[y]))
    if values[output]!=expected:(fn if expected else fp).append(raw)
   assert not fn;count+=1
   if best is None or len(fp)<len(best['false_positive_samples']):best={'scope':'Three free cross-pair ORs form a matched-neighbor overapproximation; sample-verified invalid seed, not a circuit witness','model_sha256':digest,'raw_points_merged':[a,c],'free_tree_choices':selections,'gates':gates,'output':output,'size':len(gates),'free_ors':free,'false_negative_samples':fn,'false_positive_samples':fp,'physical_truth_table_verified':False}
 if best:
  best['matched_seeds_examined']=count;(job/('meta3773-'+stem+'-matched-over-seed.json')).write_text(json.dumps(best,indent=2)+'\n');print(json.dumps({'stem':stem,'size':best['size'],'false_positives':len(best['false_positive_samples']),'raw_points':best['raw_points_merged'],'seeds_examined':count}),flush=True)
 assert hashlib.sha256(source.read_bytes()).hexdigest()==digest
