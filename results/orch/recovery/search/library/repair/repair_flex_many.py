import sys,json,time,random,argparse
from pathlib import Path
sys.path.insert(0,'/tmp/oec/pequalnp-pilot-109/counterexample/z3-5.3.3-x64-glibc-2.39/bin/python')
import z3
E=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
TRIPLES=[(0,7,8),(0,2,6),(4,6,7),(2,4,8)]
PREFIX=[[1,0,7],[1,10,8],[1,0,2],[1,12,6],[1,4,6],[1,14,7],[1,2,4],[1,16,8],[0,5,11],[0,1,13],[0,9,15],[1,18,19],[1,20,21]]
p=argparse.ArgumentParser();p.add_argument('--seed',type=int,default=11);p.add_argument('--timeout',type=int,default=600000);p.add_argument('--free-stars',action='store_true');a=p.parse_args()
if a.free_stars:PREFIX=PREFIX[:8]
K=19-len(PREFIX);N=10+len(PREFIX)
s=z3.SolverFor('QF_BV');s.set(timeout=a.timeout,random_seed=a.seed)
pair=[z3.BitVec('p%d'%i,2) for i in range(4)]
for p in pair:s.add(z3.ULE(p,2))
ops=[z3.BitVec('o%d'%i,2) for i in range(K)]
left=[z3.BitVec('l%d'%i,5) for i in range(K)]
right=[z3.BitVec('r%d'%i,5) for i in range(K)]
for i in range(K):
 s.add(z3.ULE(ops[i],2),z3.ULT(left[i],N+i),z3.ULT(right[i],N+i))
 s.add(z3.If(ops[i]==2,left[i]==right[i],z3.ULT(left[i],right[i])))
s.add(z3.Or(*[o==2 for o in ops]))

for i in range(K-1):
 s.add(z3.Implies(z3.And(ops[i]==ops[i+1],left[i+1]!=N+i,right[i+1]!=N+i),z3.ULE(left[i],left[i+1])))
seen=set()
def target(x):return any((x>>u)&1 and (x>>v)&1 for u,v in E)
def add(xs):
 xs=[x for x in xs if x not in seen];seen.update(xs)
 if not xs:return
 B=len(xs);w=[z3.BitVecVal(sum(((x>>j)&1)<<k for k,x in enumerate(xs)),B) for j in range(10)]
 for i,(u,v,q) in enumerate(TRIPLES):
  w.append(z3.If(pair[i]==0,w[u]|w[v],z3.If(pair[i]==1,w[u]|w[q],w[v]|w[q])))
  w.append(w[u]|w[v]|w[q])
 for o,l,r in PREFIX[8:]:w.append(w[l]&w[r] if o==0 else w[l]|w[r])
 def pick(sel):
  v=w[-1]
  for j in range(len(w)-2,-1,-1):v=z3.If(sel==j,w[j],v)
  return v
 for i in range(K):
  l,r=pick(left[i]),pick(right[i]);v=z3.BitVec('v%d_%d'%(len(seen),i),B)
  s.add(v==z3.If(ops[i]==0,l&r,z3.If(ops[i]==1,l|r,~l)));w.append(v)
 s.add(w[-1]==z3.BitVecVal(sum(int(target(x))<<k for k,x in enumerate(xs)),B))
def eval(gs,x):
 w=[bool(x>>i&1) for i in range(10)]
 for o,l,r in gs:w.append(w[l] and w[r] if o==0 else w[l] or w[r] if o==1 else not w[l])
 return w[-1]
add([x for x in range(1024) if not target(x) or x.bit_count()==2 or x&((1<<1)|(1<<3)|(1<<5)|(1<<9))==0])
print('start',time.time(),'fixed',len(PREFIX),'free',K,'samples',len(seen),flush=True)
for i in range(30):
 t=time.time();ans=s.check();print('iteration',i,ans,'seconds',time.time()-t,flush=True)
 if ans!=z3.sat:print(s.statistics(),flush=True);break
 m=s.model();prefix=[]
 for j,tri in enumerate(TRIPLES):
  pick=m.eval(pair[j]).as_long();ids=([0,1,2] if pick==0 else [0,2,1] if pick==1 else [1,2,0])
  prefix.extend([[1,tri[ids[0]],tri[ids[1]]],[1,10+2*j,tri[ids[2]]]])
 prefix+=PREFIX[8:]
 gs=prefix+[[m.eval(ops[j]).as_long(),m.eval(left[j]).as_long(),m.eval(right[j]).as_long()] for j in range(K)]
 bad=[x for x in range(1024) if eval(gs,x)!=target(x)]
 print('candidate',json.dumps(gs),'errors',bad,flush=True)
 if not bad:
  path=Path('/tmp/oec/pequalnp-pilot-109/library/repair/witness.json');path.write_text(json.dumps(gs));print('WITNESS',path,flush=True);break
 random.Random(a.seed+i).shuffle(bad);add(bad[:100])
