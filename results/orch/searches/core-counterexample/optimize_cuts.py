from pathlib import Path
import sys,json,time,random,math
sys.path.insert(0,'/tmp/oec/pequalnp-pilot-71/core-counterexample')
from sparse_evaluator import SparseModel
scope={}
exec(compile(Path('/tmp/oec/pequalnp-pilot-71/core-counterexample/plane_dense.py').read_text().split('import math\nr=Random')[0],'plane-definitions','exec'),scope)
seeded,mutate,canon=scope['seeded'],scope['mutate'],scope['canon']
base=Path('/tmp/oec/pequalnp-pilot-71/core-counterexample')
r=random.Random(29622024)
def mis(n,left,edges):
 neighbors=[sum(1<<(b-left) for a,b in edges if a==p) for p in range(left)];allr=(1<<(n-left))-1;union=[0]*(1<<left);answer=[]
 for S in range(1<<left):
  if S:
   b=S&-S;union[S]=union[S^b]|neighbors[b.bit_length()-1]
  B=allr^union[S];closure=sum(1<<p for p in range(left) if not(neighbors[p]&B))
  if closure==S:answer.append(S|(B<<left))
 return answer
models=[];seeds={}
for q in [7,13]:
 row=json.loads((base/('explicit-one-over-plane'+str(q)+'.json')).read_text());n=row['n'];left=n//2;es=row['edges'];M=SparseModel(n,left,es,'plane'+str(q),mis(n,left,es));models.append(M);seeds[M.name]=row['gates']
def cyclic(M,D):
 parent=list(range(M.n))
 def root(x):
  while parent[x]!=x:x=parent[x]
  return x
 for k,(a,b) in enumerate(M.edges):
  if D>>k&1:
   a,b=root(a),root(b)
   if a==b:return True
   parent[a]=b
 return False
def assess(M,ans):
 t,s,D,mc,g=ans;a=sum(op==0 for op,_,_ in g);o=len(g)-a
 return (o+mc-D.bit_count(),a-M.tau(D),a+M.tau(M.all^D)-M.base,a,o)
def score(M,ans,which):
 v=assess(M,ans);cost=v[3] if which==0 else v[4]
 return v[which]+.003*cost+.001*(len(M.edges)-ans[2].bit_count())
def two_seeds(M):
 n=M.n;g=list(seeds[M.name]);h=list(seeds[M.name]);shift=r.randrange(n//2)
 perm=[(x+shift)%(n//2) if x<n//2 else n//2+(x-n//2+shift)%(n//2) for x in range(n)]
 off=len(g)
 for op,a,b in h:g.append((op,perm[a] if a<n else a+off,perm[b] if b<n else b+off))
 return canon(n,g)
tasks=[(M,k) for M in models for k in range(3)];archives={};current={};best={};count=valid=0;last=0;start=time.time();turn=0
for M,k in tasks:
 key=(M.name,k);ans=M.analyze(seeds[M.name]);archives[key]={(ans[2],ans[3],assess(M,ans)[3 if k==0 else 4]):ans};current[key]=ans
while time.time()-start<1200:
 M,k=tasks[turn%len(tasks)];turn+=1;key=(M.name,k);archive=archives[key]
 for step in range(400):
  p=r.random()
  if p<.025:g=seeds[M.name]
  elif p<.04:g=two_seeds(M)
  elif p<.075:g=seeded(M,r)
  else:
   src=current[key] if r.random()<.7 else r.choice(list(archive.values()));g=mutate(M,src[-1],r)
   if r.random()<.15:g=mutate(M,g,r)
  ans=M.analyze(g);count+=1
  if ans is None or ans[2].bit_count()<5 or not cyclic(M,ans[2]):continue
  valid+=1;vals=assess(M,ans);sk=(ans[2],ans[3],vals[3 if k==0 else 4]);s=score(M,ans,k)
  if s<=score(M,current[key],k) or r.random()<math.exp((score(M,current[key],k)-s)/.6):current[key]=ans
  old=archive.get(sk)
  if old is None or s<score(M,old,k) or s==score(M,old,k) and r.random()<.4:archive[sk]=ans
  if len(archive)>900:
   keys=sorted(archive,key=lambda z:score(M,archive[z],k));archive={z:archive[z] for z in keys[:600]};archives[key]=archive
  changed=key not in best or vals[k]<best[key]
  if changed:
   best[key]=vals[k];out=dict(kind='best',seconds=time.time()-start,count=count,valid=valid,graph=M.name,objective=k,n=M.n,left=M.left,edges=M.edges,gates=ans[-1],D=ans[2],mc=ans[3],target=ans[0],stronger=ans[1],edge_margin=vals[0],strong_cover_margin=vals[1],cover_margin=vals[2],AND=vals[3],OR=vals[4]);print(json.dumps(out),flush=True);(base/('cuts-optimized-best-'+M.name+'-'+str(k)+'.json')).write_text(json.dumps(out,indent=2))
  if min(vals[:3])<0:
   out=dict(kind='FOUND',seconds=time.time()-start,count=count,valid=valid,graph=M.name,objective=k,n=M.n,left=M.left,edges=M.edges,gates=ans[-1],D=ans[2],mc=ans[3],target=ans[0],stronger=ans[1],edge_margin=vals[0],strong_cover_margin=vals[1],cover_margin=vals[2],AND=vals[3],OR=vals[4]);print(json.dumps(out),flush=True);(base/'cuts-optimized-counterexample.json').write_text(json.dumps(out,indent=2));raise SystemExit
 now=time.time()-start
 if now-last>60:
  print(json.dumps(dict(kind='progress',seconds=now,count=count,valid=valid,best={str(z):v for z,v in best.items()})),flush=True);last=now
print(json.dumps(dict(kind='done',seconds=time.time()-start,count=count,valid=valid,best={str(z):v for z,v in best.items()})),flush=True)
