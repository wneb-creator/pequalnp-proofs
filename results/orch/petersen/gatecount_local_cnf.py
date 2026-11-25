import json
import sys
from pathlib import Path
mode=sys.argv[1]
folder=Path(sys.argv[2])
if mode=='p5':
 n=5;rows=list(range(32));k=4
 xs=[[bool(s>>i&1) for s in rows] for i in range(n)]
 xs += [[xs[0][t] or xs[4][t] for t in range(32)], [xs[4][t] or xs[1][t] for t in range(32)], [xs[0][t] or xs[3][t] for t in range(32)]]
 target=[any(s>>a&1 and s>>b&1 for a,b in [(0,1),(1,2),(2,3),(3,4)]) for s in rows]
 prefix=[]
else:
 n=10;k=5
 es=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
 pos=[(1<<a)|(1<<b) for a,b in es]
 neg=[]
 for s in range(1<<n):
  if any(s>>a&1 and s>>b&1 for a,b in es):continue
  if all(s>>v&1 or any(((s|(1<<v))>>a&1) and ((s|(1<<v))>>b&1) for a,b in es) for v in range(n)):neg.append(s)
 rows=pos+neg;target=[True]*len(pos)+[False]*len(neg)
 xs=[[bool(s>>i&1) for s in rows] for i in range(n)]
 prefix=[('or',0,2),('or',10,6),('or',2,4),('or',12,8),('or',8,9),('or',0,7),('or',15,8),('and',1,11),('and',3,13),('or',17,18),('and',5,16),('or',19,20),('and',6,14),('or',21,22)]
 for op,a,b in prefix:xs.append([(x and y) if op=='and' else(x or y) for x,y in zip(xs[a],xs[b])])

if len(sys.argv)>3:k=int(sys.argv[3])
clauses=[[1]];labels={};nv=1

def new(name):
 global nv
 nv+=1;labels[name]=nv;return nv

def add(*ls):
 if 1 in ls:return
 ss=set(l for l in ls if l!=-1)
 if any(-l in ss for l in ss):return
 clauses.append(sorted(ss,key=abs))

def onehot(vs):
 add(*vs)
 for i,a in enumerate(vs):
  for b in vs[i+1:]:add(-a,-b)

sigs=[[1 if v else -1 for v in x] for x in xs]
selectors=[];ops=[]
for j in range(k):
 op=new(f'op_{j}');ops.append(op)
 sel=[];vals=[]
 for b in range(2):
  ss=[new(f'sel_{j}_{b}_{w}') for w in range(len(sigs))];onehot(ss);sel.append(ss)
  vv=[new(f'side_{j}_{b}_{t}') for t in range(len(rows))];vals.append(vv)
  for w,choose in enumerate(ss):
   for t,v in enumerate(sigs[w]):add(-choose,-vv[t],v);add(-choose,vv[t],-v)
 for a in range(len(sigs)):
  for b in range(a):add(-sel[0][a],-sel[1][b])
 out=[]
 for t in range(len(rows)):
  a,b=vals[0][t],vals[1][t];g=new(f'g_{j}_{t}');out.append(g)
  add(-op,-g,a);add(-op,-g,b);add(-op,g,-a,-b)
  add(op,g,-a);add(op,g,-b);add(op,-g,a,b)
 sigs.append(out);selectors.append(sel)
for t,v in enumerate(target):add(sigs[-1][t] if v else -sigs[-1][t])
stem=folder/f'gatecount-local-{mode}{"-positive" if len(sys.argv)>3 else ""}'
with stem.with_suffix('.cnf').open('w') as f:
 f.write(f'p cnf {nv} {len(clauses)}\n')
 for c in clauses:f.write(' '.join(map(str,c))+' 0\n')
stem.with_suffix('.json').write_text(json.dumps({'mode':mode,'n':n,'k':k,'rows':rows,'target':target,'prefix':prefix,'input_vectors':xs,'labels':labels,'ops':ops,'selectors':selectors}))
print(mode,'vars',nv,'clauses',len(clauses),'rows',len(rows),'newgates',k)
