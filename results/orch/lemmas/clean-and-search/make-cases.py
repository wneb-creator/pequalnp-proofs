from pathlib import Path
import json,itertools
root=Path('/tmp/oec/pequalnp-pilot-184/clean-and-search');cases={}
for n in (5,6,7):cases['cycle'+str(n)]=(n,[(i,(i+1)%n) for i in range(n)])
cases['theta233']=(7,[(0,2),(2,1),(0,3),(3,4),(4,1),(0,5),(5,6),(6,1)])
cases['shared_or8']=(8,[(4,0),(4,1),(5,2),(5,3),(6,0),(6,3),(7,1),(7,2),(0,2),(1,3)])
reports=[]
for name,(n,edges) in cases.items():
 es={tuple(sorted(e)) for e in edges}
 adj=lambda a,b:tuple(sorted((a,b))) in es
 triangle=any(adj(a,b) and adj(b,c) and adj(c,a) for a,b,c in itertools.permutations(range(n),3))
 square=any(adj(a,b) and adj(b,c) and adj(c,d) and adj(d,a) for a,b,c,d in itertools.permutations(range(n),4))
 covers=[m for m in range(1<<n) if all((m>>a&1) or (m>>b&1) for a,b in edges)]
 cover=min(covers,key=int.bit_count);stars={v:[] for v in range(n) if cover>>v&1}
 for a,b in edges:
  v=a if a in stars else b;stars[v].append(b if v==a else a)
 gates=[];outputs=[]
 for v,ns in stars.items():
  if not ns:continue
  z=ns[0]
  for u in ns[1:]:gates.append((1,z,u));z=n+len(gates)-1
  gates.append((0,v,z));outputs.append(n+len(gates)-1)
 z=outputs[0]
 for v in outputs[1:]:gates.append((1,z,v));z=n+len(gates)-1
 errors=[];unsafe=[]
 for r in range(1<<n):
  f=any((r>>a&1) and (r>>b&1) for a,b in edges);w=[bool(r>>i&1) for i in range(n)]
  for i,(op,a,b) in enumerate(gates):
   w.append((w[a] and w[b]) if op==0 else (w[a] or w[b]))
   if op==0 and w[-1] and not f:unsafe.append((r,i))
  if w[z]!=bool(f):errors.append(r)
 assert not triangle and not square and not errors and not unsafe
 (root/(name+'.edges.json')).write_text(json.dumps(edges))
 report={'name':name,'n':n,'edges':edges,'girth_at_least_five':True,'minimum_vertex_cover_size':cover.bit_count(),'upper_bound':len(gates),'witness_gates':gates,'witness_output':z,'truth_errors':errors,'unsafe_ANDs':unsafe}
 reports.append(report)
(root/'cases.json').write_text(json.dumps(reports,indent=2));print([(r['name'],r['upper_bound']) for r in reports])
