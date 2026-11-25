import argparse,json,subprocess,time,itertools
from pathlib import Path
p=argparse.ArgumentParser()
p.add_argument('graph',choices=['house','c5','c6','bowtie','k4','theta4'])
p.add_argument('budget',type=int)
p.add_argument('--edge',default='0,1')
p.add_argument('--double',action='store_true')
p.add_argument('--seconds',type=int,default=180)
p.add_argument('--ordered',action='store_true')
p.add_argument('--live',action='store_true')
p.add_argument('--critical',action='store_true')
p.add_argument('--and-count',type=int)
a=p.parse_args()
if a.graph=='theta4': n=10; edges=[e for i in range(4) for e in [(0,2+i),(2+i,6+i),(6+i,1)]]
elif a.graph=='k4': n=4; edges=[(i,j) for i in range(4) for j in range(i+1,4)]
elif a.graph=='bowtie': n=5; edges=[(0,1),(0,2),(1,2),(0,3),(0,4),(3,4)]
elif a.graph=='house': n=5; edges=[(0,1),(1,2),(2,3),(3,0),(1,4),(2,4)]
elif a.graph=='c5': n=5; edges=[(i,(i+1)%5) for i in range(5)]
else: n=6; edges=[(i,(i+1)%6) for i in range(6)]
p0,p1=map(int,a.edge.split(','));k=a.budget
root=Path('/tmp/oec/pequalnp-pilot-65/status-review')
label=f'{a.graph}-{k}-'+(f'double-{p0}-{p1}' if a.double else 'ordinary')
label += (f'-and{a.and_count}' if a.and_count is not None else '') + ('-critical' if a.critical else '') + ('-ordered' if a.ordered else '') + ('-live' if a.live else '')
cnf=root/(label+'.cnf');log=root/(label+'.solver.log');err=root/(label+'.solver.err');metadata=root/(label+'.meta.json')
clauses=[];nv=0
def new():
 global nv
 nv+=1; return nv
def neg(x): return not x if isinstance(x,bool) else -x
def cl(*xs):
 if any(x is True for x in xs):return
 ys=set(x for x in xs if x is not False)
 if any(-x in ys for x in ys):return
 clauses.append(tuple(sorted(ys)))
def one(xs):
 cl(*xs)
 for i,x in enumerate(xs):
  for y in xs[i+1:]:cl(-x,-y)
def guarded_eq(s,u,v):cl(-s,-u,v);cl(-s,u,neg(v))
def andeq(z,x,y):cl(-z,x);cl(-z,y);cl(z,neg(x),neg(y))
def gate(z,x,y,op):
 cl(-op,-z,x);cl(-op,-z,y);cl(-op,z,neg(x),neg(y))
 cl(op,z,neg(x));cl(op,z,neg(y));cl(op,-z,x,y)
rows=list(range(1<<n))
if a.critical:
 positives=[(1<<u)|(1<<v) for u,v in edges]
 def indep(r):return not any((r>>u&1) and (r>>v&1) for u,v in edges)
 negatives=[r for r in range(1<<n) if indep(r) and all(not indep(r|(1<<i)) for i in range(n) if not r>>i&1)]
 rows=sorted(set(positives+negatives+([1<<p0,1<<p1] if a.double else [])))
value=[{r:new() for r in rows} for j in range(k)]
ops=[new() for j in range(k)];choose=[];picked=[]
der=[[new() for t in range(2)] for j in range(k)] if a.double else []
def vv(i,r):return bool(r>>i&1) if i<n else value[i-n][r]
def dd(i,t):return i==[p1,p0][t] if i<n else der[i-n][t]
for j in range(k):
 sels=[[new() for i in range(n+j)] for h in range(2)];choose.append(sels)
 for sel in sels:one(sel)
 for i,s in enumerate(sels[0]):
  for z,t in enumerate(sels[1]):
   if i>=z:cl(-s,-t)
 av=[{r:new() for r in rows} for h in range(2)];picked.append(av)
 for h in range(2):
  for i,s in enumerate(sels[h]):
   for r in rows:guarded_eq(s,av[h][r],vv(i,r))
 for r in rows:gate(value[j][r],av[0][r],av[1][r],ops[j])
 if a.double:
  ds=[[new() for t in range(2)] for h in range(2)]
  for h in range(2):
   for i,s in enumerate(sels[h]):
    for t in range(2):guarded_eq(s,ds[h][t],dd(i,t))
  for t in range(2):
   base=1<<[p0,p1][t]
   u,v=new(),new();andeq(u,av[0][base],ds[1][t]);andeq(v,ds[0][t],av[1][base])
   z=der[j][t];op=ops[j]
   cl(-op,z,-u);cl(-op,z,-v);cl(-op,-z,u,v)
   cl(op,z,-ds[0][t]);cl(op,z,-ds[1][t]);cl(op,-z,ds[0][t],ds[1][t])
if a.and_count is not None:
 for ss in itertools.combinations(ops,a.and_count+1):cl(*(-x for x in ss))
 for ss in itertools.combinations(ops,k-a.and_count+1):cl(*ss)
if a.ordered:
 for j in range(k-1):
  for b,s0 in enumerate(choose[j][1]):
   for c,s1 in enumerate(choose[j+1][1]):
    if b>c:cl(-s0,-s1)
    elif b==c:
     for i,x in enumerate(choose[j][0]):
      for h,y in enumerate(choose[j+1][0]):
       if i>h:cl(-s0,-s1,-x,-y)
if a.live:
 for j in range(k-1):cl(*(choose[l][h][n+j] for l in range(j+1,k) for h in range(2)))
for r in rows:
 expected=any((r>>u&1) and (r>>v&1) for u,v in edges)
 cl(value[-1][r] if expected else -value[-1][r])
if a.double:
 for x in der[-1]:cl(-x)
with cnf.open('w') as f:
 f.write(f'p cnf {nv} {len(clauses)}\n')
 for c in clauses:f.write(' '.join(map(str,c))+' 0\n')
metadata.write_text(json.dumps(dict(graph=a.graph,n=n,edges=edges,k=k,ops=ops,choose=choose,p0=p0,p1=p1,double=a.double),indent=2)+'\n')
print(f'{label}: variables={nv} clauses={len(clauses)}',flush=True)
cmd=['/tmp/oec/pequalnp-pilot-65/toolchain/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical','-t',str(a.seconds),str(cnf)]
t0=time.monotonic()
with log.open('w') as so,err.open('w') as se:r=subprocess.run(cmd,stdout=so,stderr=se)
s=log.read_text();status=[x for x in s.splitlines() if x.startswith('s ')]
print(f'{label}: exit={r.returncode} seconds={time.monotonic()-t0:.2f} status={status}',flush=True)
if 's SATISFIABLE' not in status:raise SystemExit(0)
model=set()
for line in s.splitlines():
 if line.startswith('v '):model.update(int(x) for x in line[2:].split() if int(x)>0)
gs=[]
for j in range(k):
 ins=[next(i for i,x in enumerate(sel) if x in model) for sel in choose[j]]
 gs.append(['and' if ops[j] in model else 'or',*ins])
def evaluate(r):
 w=[bool(r>>i&1) for i in range(n)]
 for op,u,v in gs:w.append(w[u] and w[v] if op=='and' else w[u] or w[v])
 return w
bad=[]
for r in range(1<<n):
 expected=any((r>>u&1) and (r>>v&1) for u,v in edges)
 if evaluate(r)[-1]!=expected:bad.append(r)
def trace(base,source):
 w=evaluate(1<<base);d=[i==source for i in range(n)]
 for j,(op,u,v) in enumerate(gs):d.append((w[u] and d[v]) or (d[u] and w[v]) if op=='and' else d[u] or d[v])
 return d[-1]
ds=[trace(p0,p1),trace(p1,p0)]
print('witness',gs,'bad_rows',bad,'traces',ds,flush=True)
assert not bad
assert not a.double or not any(ds)
(root/(label+'.witness.json')).write_text(json.dumps(dict(n=n,edges=edges,gates=gs,output=n+k-1,bad_rows=bad,traces=ds),indent=2)+'\n')
