from pathlib import Path
import json,hashlib
p=Path('/tmp/oec/pequalnp-pilot-70/constructive')
d=json.loads((p/'matching-cut-cone-rows.json').read_text());base=json.loads((p/'matching-cut-cone-baseline15.json').read_text());seed=json.loads((p/'matching-cut-cone-seed14.json').read_text());saved=json.loads((p/'matching-cut-cone-seed26-embedded.json').read_text())
H={(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)}
V=[0,3,5,6,7,8,9,10,11,12];pairs=[(4,6),(5,9),(7,8)]
R={(V.index(a),V.index(b)) for a,b in H if a not in [1,2,4]}
assert d['original_variables']==V and {tuple(e) for e in d['edges']}==R and d['free_or_sums']==[list(e) for e in pairs]
def values(m,n):return [(m>>i)&1 for i in range(n)]
def target(w,edges):return int(any(w[a] and w[b] for a,b in edges))
def cuts(m):
 w=values(m,10)
 return w+[w[a]|w[b] for a,b in pairs]
def run(w,gs):
 w=list(w)
 for op,a,b in gs:
  assert op in [0,1] and 0<=a<len(w) and 0<=b<len(w)
  w.append((w[a]|w[b]) if op else (w[a]&w[b]))
 return w
positive=[];negative=[]
for m in range(1024):
 value=target(values(m,10),R)
 if value and all(not target(values(m^(1<<i),10),R) for i in range(10) if m&(1<<i)):positive.append(m)
 if not value and all(target(values(m|(1<<i),10),R) for i in range(10) if not m&(1<<i)):negative.append(m)
assert positive==d['positive_rows'] and negative==d['negative_rows']
assert len(positive)==12 and len(negative)==12
assert {r['mask'] for r in d['rows']}==set(positive+negative)
for r in d['rows']:assert r['cuts']==cuts(r['mask']) and r['value']==target(values(r['mask'],10),R)
residual_errors=0
for m in range(1024):
 w=cuts(m);t=target(w,R)
 assert any((b&m)==b for b in positive) if t else any((m&b)==m for b in negative)
 assert run(w,base['gates'])[base['output']]==t
 got=run(w,seed['gates'])[seed['output']]
 assert got==target(w,R-{(0,4)})
 residual_errors+=got!=t
prefix=[[1,7,9],[1,13,14],[0,1,15],[1,8,12],[1,13,17],[0,2,18],[1,10,11],[1,13,20],[0,4,21],[1,16,19],[1,23,22]]
assert d['fixed_gates']==prefix and d['fixed_sum_wires']==[14,17,20] and d['fixed_output']==24
def embed(artifact):
 gs=list(prefix);wmap=V+[14,17,20]
 for op,a,b in artifact['gates']:
  gs.append([op,wmap[a],wmap[b]]);wmap.append(14+len(gs)-1)
 gs.append([1,24,wmap[artifact['output']]])
 return gs
B=embed(base);S=embed(seed);assert len(B)==27 and len(S)==26 and S==saved['gates']
full_errors=0
for m in range(16384):
 w=values(m,14);pw=run(w,prefix);submask=sum(w[v]<<i for i,v in enumerate(V))
 assert [pw[i] for i in V+[14,17,20]]==cuts(submask)
 assert pw[24]==target(w,{e for e in H if e[0] in [1,2,4]})
 assert run(w,B)[-1]==target(w,H)
 got=run(w,S)[-1];assert got==target(w,H-{(0,7)})
 full_errors+=got!=target(w,H)
assert residual_errors==13 and full_errors==47
print(json.dumps({'boundary_rows':24,'positive_rows':12,'negative_rows':12,'residual_assignments':1024,'full_assignments':16384,'baseline_cone_gates':15,'baseline_full_gates':27,'seed_cone_gates':14,'seed_full_gates':26,'seed_residual_false_negatives':residual_errors,'seed_full_false_negatives':full_errors,'false_positives':0,'status':'passed','rows_sha256':hashlib.sha256((p/'matching-cut-cone-rows.json').read_bytes()).hexdigest()},indent=2))
