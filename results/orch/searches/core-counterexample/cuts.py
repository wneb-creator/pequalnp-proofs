from pathlib import Path
import sys,json,time,random
sys.path.insert(0,'/tmp/oec/pequalnp-pilot-71/core-counterexample')
from sparse_evaluator import SparseModel
scope={}
exec(compile(Path('/tmp/oec/pequalnp-pilot-71/core-counterexample/dense.py').read_text().split('import math\nr=Random')[0],'dense-definitions','exec'),scope)
seeded,mutate=scope['seeded'],scope['mutate']
def mis(n,left,edges):
 neighbors=[sum(1<<(b-left) for a,b in edges if a==p) for p in range(left)];allr=(1<<(n-left))-1;union=[0]*(1<<left);answer=[]
 for S in range(1<<left):
  if S:
   b=S&-S;union[S]=union[S^b]|neighbors[b.bit_length()-1]
  B=allr^union[S];closure=sum(1<<p for p in range(left) if not(neighbors[p]&B))
  if closure==S:answer.append(S|(B<<left))
 return answer
models=[];best=[999,999];count=0;seen={}
def check(M,g,label):
 global count,best
 ans=M.analyze(g);count+=1
 if ans is None:return False
 t,s,D,mc,g=ans;a=sum(op==0 for op,_,_ in g);o=len(g)-a
 em=o+mc-D.bit_count();cm=a-M.base+M.tau(M.all^D)
 if em<best[0] or cm<best[1]:
  best=[min(best[0],em),min(best[1],cm)]
  print(json.dumps(dict(kind='best',label=label,count=count,edges_margin=em,cover_margin=cm,target=t,graph=M.name,n=M.n,left=M.left,edges=M.edges,D=D,mc=mc,gates=g)),flush=True)
 if em<0 or cm<0:
  Path('/tmp/oec/pequalnp-pilot-71/core-counterexample/cut-counterexample.json').write_text(json.dumps(dict(label=label,n=M.n,left=M.left,edges=M.edges,gates=g,D=D,mc=mc,edges_margin=em,cover_margin=cm,target=t),indent=2))
  print('CUT COUNTEREXAMPLE',flush=True);return True
 return False
for filename in Path('/tmp/oec/pequalnp-pilot-71/core-counterexample/best-files.txt').read_text().splitlines():
 row=json.loads(Path(filename).read_text());key=(row['n'],tuple(tuple(e) for e in row['edges']))
 if key not in seen:
  n,edges=key;left=min(b for a,b in edges);M=SparseModel(n,left,edges,row['graph'],mis(n,left,edges));seen[key]=M;models.append(M)
 if check(seen[key],row['gates'],'saved-best'):raise SystemExit
r=random.Random(2962333);start=time.time()
while time.time()-start<45:
 M=r.choice(models);g=seeded(M,r)
 for _ in range(r.randrange(1,6)):g=mutate(M,g,r)
 if check(M,g,'fresh-mutation'):break
print(json.dumps(dict(kind='done',count=count,seconds=time.time()-start,best=best)),flush=True)
