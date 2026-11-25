import argparse,itertools,random,time,json
p=argparse.ArgumentParser();p.add_argument('--graph',choices=['theta233','petersen'],default='theta233');p.add_argument('--seconds',type=int,default=300);p.add_argument('--seed',type=int,default=54);a=p.parse_args()
rng=random.Random(a.seed)
if a.graph=='theta233':
 n=7;edges=[(0,2),(2,1),(0,3),(3,4),(4,1),(0,5),(5,6),(6,1)]
else:
 pairs=list(itertools.combinations(range(5),2));n=len(pairs)
 edges=[(i,j) for i in range(n) for j in range(i+1,n) if not set(pairs[i])&set(pairs[j])]
ind=[x for x in range(1<<n) if not any((x>>u)&1 and (x>>v)&1 for u,v in edges)]
maxind=[x for x in ind if all((x|(1<<v)) not in ind for v in range(n) if not ((x>>v)&1))]
alpha=max(x.bit_count() for x in ind)
covers=[tuple(i for i in range(n) if not ((x>>i)&1)) for x in ind if x.bit_count()==alpha]
samples=[(1<<u)|(1<<v) for u,v in edges]+maxind
base=[sum(1<<i for i,x in enumerate(samples) if (x>>j)&1) for j in range(n)]
target=(1<<len(edges))-1
upper=len(edges)+n-alpha-1

def evaluate(gs):
 vals=base.copy()
 for op,u,v in gs:vals.append(vals[u]|vals[v] if op else vals[u]&vals[v])
 return vals

def new_start():
 own={c:[] for c in rng.choice(covers)}
 for u,v in edges:
  avail=[x for x in (u,v) if x in own];c=rng.choice(avail);own[c].append(v if c==u else u)
 cs=list(own);rng.shuffle(cs);gs=[];outs=[]
 for c in cs:
  leaves=own[c];rng.shuffle(leaves);acc=leaves[0]
  for v in leaves[1:]:gs.append((1,acc,v));acc=n+len(gs)-1
  gs.append((0,c,acc));outs.append(n+len(gs)-1)
 rng.shuffle(outs);acc=outs[0]
 for v in outs[1:]:gs.append((1,acc,v));acc=n+len(gs)-1
 assert len(gs)==upper
 assert evaluate(gs)[-1]==target
 k=rng.choice([i for i,g in enumerate(gs) if g[0]==1]);replacement=rng.choice(gs[k][1:])
 out=[]
 for i,(op,u,v) in enumerate(gs):
  if i==k:continue
  def remap(w):return replacement if w==n+k else w-1 if w>n+k else w
  out.append((op,remap(u),remap(v)))
 return out

start=time.monotonic();iters=0;restarts=0;best=999
print(json.dumps({'graph':a.graph,'n':n,'edges':edges,'upper':upper,'search_gates':upper-1,'samples':len(samples),'minimum_covers':len(covers),'seed':a.seed}),flush=True)
while time.monotonic()-start<a.seconds:
 gs=new_start();vals=evaluate(gs);score=(vals[-1]^target).bit_count();restarts+=1
 for step in range(20000):
  iters+=1
  if score<best:
   best=score;print('best',best,'iterations',iters,'seconds',time.monotonic()-start,flush=True)
  if score==0:
   for x in range(1<<n):
    vs=[bool((x>>j)&1) for j in range(n)]
    for op,u,v in gs:vs.append(vs[u] or vs[v] if op else vs[u] and vs[v])
    assert vs[-1]==any(vs[u] and vs[v] for u,v in edges)
   print('WITNESS',json.dumps(gs),flush=True);raise SystemExit(0)
  k=rng.randrange(len(gs));old=gs[k];op,u,v=old
  move=rng.randrange(10)
  if move==0:op=1-op
  elif move<6:u=rng.randrange(n+k)
  else:v=rng.randrange(n+k)
  if u==v:continue
  gs[k]=(op,min(u,v),max(u,v))
  nv=vals[:n+k]
  for op1,u1,v1 in gs[k:]:nv.append(nv[u1]|nv[v1] if op1 else nv[u1]&nv[v1])
  ns=(nv[-1]^target).bit_count()
  temperature=0.45*(1-step/20000)+0.05
  accept=ns<=score or rng.random()<2.718281828459045**((score-ns)/temperature)
  if accept:vals=nv;score=ns
  else:gs[k]=old
  if iters%10000==0 and time.monotonic()-start>=a.seconds:break
print('NO_WITNESS','iterations',iters,'restarts',restarts,'best_error',best,'seconds',time.monotonic()-start,flush=True)
