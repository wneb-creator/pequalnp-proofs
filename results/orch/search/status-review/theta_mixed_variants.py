import itertools,json,functools
from pathlib import Path
p=Path('/tmp/oec/pequalnp-pilot-65/status-review');out=p/'theta-mixed-variants';out.mkdir(exist_ok=True)
D=json.loads((p/'polarized-225.json').read_text());es=[(5,1),(5,2),(5,3),(5,4),(6,2),(9,3)]
vs=[sum(1<<r for r in range(1024) if r>>i&1) for i in range(10)]
target=0
for a,b in D['edges']:target|=vs[a]&vs[b]
@functools.lru_cache(None)
def trees(xs):
 if len(xs)==1:return (xs[0],)
 result=[]
 for bits in range(1,1<<len(xs)):
  if not bits&1 or bits==(1<<len(xs))-1:continue
  a=tuple(x for i,x in enumerate(xs) if bits>>i&1);b=tuple(x for i,x in enumerate(xs) if not bits>>i&1)
  for u in trees(a):
   for v in trees(b):result.append((u,v))
 return tuple(result)
def verify(gs):
 v=vs[:]
 for op,a,b in gs:v.append(v[a]&v[b] if op=='and' else v[a]|v[b])
 assert v[-1]==target
 for base,source in [(1,7),(7,1)]:
  w=[i==base for i in range(10)];d=[i==source for i in range(10)]
  for op,a,b in gs:
   d.append((w[a] and d[b]) or (d[a] and w[b]) if op=='and' else d[a] or d[b])
   w.append(w[a] and w[b] if op=='and' else w[a] or w[b])
  assert not d[-1]
index=[];signatures=set()
for cover in itertools.combinations([1,2,3,4,5,6,9],3):
 choices=[[x for x in e if x in cover] for e in es]
 if any(not x for x in choices):continue
 for owners in itertools.product(*choices):
  ns={c:[] for c in cover}
  for (a,b),c in zip(es,owners):ns[c].append(b if a==c else a)
  if any(not x for x in ns.values()):continue
  for shapes in itertools.product(*(trees(tuple(sorted(ns[c]))) for c in cover)):
   for nonlinear_shape in trees((6,7,9)):
    for finalshape in trees((0,1,2)):
     gs=[]
     def add(op,a,b):gs.append([op,a,b]);return 9+len(gs)
     def ortree(t,lookup=None):
      if isinstance(t,int):return t if lookup is None else lookup[t]
      return add('or',ortree(t[0],lookup),ortree(t[1],lookup))
     prod=add('and',1,7);u=add('or',0,prod);rr=ortree(nonlinear_shape)
     xx=add('or',4,u);yy=add('and',u,rr);zz=add('or',8,yy);branch=add('and',xx,zz)
     ts=[add('and',c,ortree(t)) for c,t in zip(cover,shapes)]
     oth=ortree(finalshape,ts);add('or',branch,oth)
     assert len(gs)==17
     sig=tuple(tuple(x) for x in gs)
     if sig in signatures:continue
     signatures.add(sig);verify(gs)
     name=f'mixed-{len(index):03}.json';(out/name).write_text(json.dumps(dict(n=10,edges=D['edges'],gates=gs,output=26,double_edges=[[1,7]],cover=cover),indent=2)+'\n');index.append(str(out/name))
(p/'theta-mixed-variants-index.json').write_text(json.dumps(index,indent=2)+'\n')
print('saved',len(index),'exact17gate mixedvariants',out)
