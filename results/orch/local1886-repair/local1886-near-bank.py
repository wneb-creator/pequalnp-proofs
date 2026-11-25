import json,pathlib,collections
p=pathlib.Path('/tmp/oec/pequalnp-pilot-92')
source=json.loads((p/'local-improved-seed.json').read_text())[0]
orig=source['gates'];unused_not=14
assert orig[unused_not][0]=='not'
mp=lambda w:w-1 if w>10+unused_not else w
near=[(op,mp(u),mp(v)) for i,(op,u,v) in enumerate(orig) if i!=unused_not]
allbits=(1<<1024)-1
raw=[sum(1<<x for x in range(1024) if x>>i&1) for i in range(10)]
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
target=0
for u,v in edges:target|=raw[u]&raw[v]
def evaluate(gs,bank,output):
 w=raw+[bank]
 for op,u,v in gs:w.append(w[u]&w[v] if op=='and' else w[u]|w[v] if op=='or' else allbits^w[u])
 return w[output]
lift=lambda w:w if w<10 else w+1
gs=[(op,lift(u),lift(v)) for op,u,v in near]
neartruth=evaluate(gs,0,28)
assert (neartruth^target).bit_count()==4
records=[]
for e in edges:
 for bankop in ['and','or']:
  bank=raw[e[0]]&raw[e[1]] if bankop=='and' else raw[e[0]]|raw[e[1]]
  for d in range(18):
   def mm(w):return 10 if w==11+d else w-1 if w>11+d else w
   cs=[(op,mm(u),mm(v)) for i,(op,u,v) in enumerate(gs) if i!=d]
   output=mm(28);got=evaluate(cs,bank,output);error=got^target
   records.append({'edge':e,'bank_op':bankop,'deleted_gate':d,'error_count':error.bit_count(),'preserves_near_function':got==neartruth,'gates':cs,'output':output,'errors':[x for x in range(1024) if error>>x&1]})
records.sort(key=lambda r:r['error_count'])
report={'tested':len(records),'best_errors':records[0]['error_count'],'preserve_near_function_count':sum(r['preserves_near_function'] for r in records),'error_histogram':dict(sorted(collections.Counter(r['error_count'] for r in records).items())),'scope':'Replace all uses of one of the18 near-circuit gates with a supplied edge AND or OR, then delete that gate; no other edits.'}
(p/'local1886-near-bank-analysis.json').write_text(json.dumps(report,indent=2)+'\n')
(p/'local1886-near-bank-seeds.json').write_text(json.dumps(records[:40],indent=2)+'\n')
print(json.dumps(report))
