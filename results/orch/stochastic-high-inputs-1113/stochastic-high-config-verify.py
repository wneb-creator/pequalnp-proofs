import collections,hashlib,json,sys
from pathlib import Path
path=Path(sys.argv[1]);raw=path.read_text();it=iter(map(int,raw.split()));ni,ng,budget,np,nn,ns,mp,ml,rp,rl=[next(it) for _ in range(10)];original=[next(it) for _ in range(ni)];rows=[next(it) for _ in range(np+nn)]
assert ni==14 and original==list(range(14)) and (mp,ml)==(0,7)
truth=[sum(1<<x for x in range(1<<ni) if x>>i&1) for i in range(ni)];want=0;edges=set()
for l in range(7):
 for p in [l,(l+1)%7,(l+3)%7]:want|=truth[p]&truth[7+l];edges.add((1<<p)|(1<<(7+l)))
assert set(rows[:np])==edges and np==21
maxneg=[]
for x in range(1<<14):
 if want>>x&1:continue
 if all(want>>(x|(1<<i))&1 for i in range(14) if not(x>>i&1)):maxneg.append(x)
assert set(rows[np:])==set(maxneg) and nn==37
sizes=collections.Counter();structures=collections.Counter();trace_patterns=collections.Counter()
for sid in range(ns):
 m,o=next(it),next(it);g=[[next(it),next(it),next(it)] for _ in range(m)];v=list(truth);fan=[0]*(14+m);sup=[1<<i for i in range(14)]
 for j,(op,a,b) in enumerate(g):
  assert op in [0,1] and a!=b and 0<=a<14+j and 0<=b<14+j
  v.append(v[a]&v[b] if op else v[a]|v[b]);sup.append(sup[a]&sup[b] if op else sup[a]|sup[b]);fan[a]+=1;fan[b]+=1
 assert v[o]==want,(sid,'truth')
 trace=[]
 for bv,dv in [(mp,ml),(ml,mp)]:
  vals=[i==bv for i in range(14)];der=[i==dv for i in range(14)]
  for op,a,b in g:
   der.append((der[a] and vals[b]) or (vals[a] and der[b]) if op else der[a] or der[b]);vals.append(vals[a] and vals[b] if op else vals[a] or vals[b])
  assert not vals[o],(sid,'singleton',bv,dv)
  trace.append(der[o])
 trace_patterns[tuple(trace)]+=1
 assert trace==([True,True] if m==27 else [False,False]),(sid,'expected trace class')
 used=set()
 def visit(w):
  if w in used:return
  used.add(w)
  if w>=14:visit(g[w-14][1]);visit(g[w-14][2])
 visit(o);assert len(used)==14+m,(sid,'dead wire')
 eligible=bp=bz=0
 for w in range(14+m):
  if fan[w]>1:
   if sup[w]:eligible|=sup[w];bp+=fan[w]-1
   else:bz+=fan[w]-1
 sizes[m]+=1;structures[(m,eligible.bit_count(),bp,bz)]+=1
assert next(it,None) is None
print(json.dumps({'config':str(path),'sha256':hashlib.sha256(raw.encode()).hexdigest(),'verified_seeds':ns,'full_truth_rows_per_seed':16384,'marked_inputs':[0,7],'trace_patterns':[[*k,v] for k,v in sorted(trace_patterns.items())],'boundary_rows':{'positive':21,'maximal_negative':37},'sizes':dict(sizes),'structures_gate_p_Bplus_Bzero':[[*k,v] for k,v in sorted(structures.items())],'verdict':'PASS'},indent=2))
