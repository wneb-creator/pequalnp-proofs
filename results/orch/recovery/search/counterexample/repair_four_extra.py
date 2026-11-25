import sys, json, time, argparse, random
sys.path.insert(0, '/tmp/oec/pequalnp-pilot-109/counterexample/z3-5.3.3-x64-glibc-2.39/bin/python')
import z3
E=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def target(x): return any((x>>i)&1 and (x>>j)&1 for i,j in E)
def evaluate(gs):
 out=[]
 for x in range(1024):
  w=[bool((x>>j)&1) for j in range(10)]
  for op,a,b in gs:
   w.append((w[a] and w[b]) if op==0 else (w[a] or w[b]) if op==1 else not w[a])
  out.append(w[-1])
 return out
p=argparse.ArgumentParser(); p.add_argument('--gates',type=int,default=19); p.add_argument('--nots',type=int,default=1);p.add_argument('--seed',type=int,default=1);p.add_argument('--timeout',type=int,default=600000);p.add_argument('--first',type=int,default=-1);p.add_argument('--normalize-not',action='store_true');p.add_argument('--dense',action='store_true');p.add_argument('--changes',type=int,default=3)
a=p.parse_args(); K=a.gates
s=z3.SolverFor('QF_BV'); s.set(timeout=a.timeout,random_seed=a.seed)
ops=[z3.BitVec('op%d'%g,2) for g in range(K)]
as_=[z3.BitVec('a%d'%g,5) for g in range(K)]
bs=[z3.BitVec('b%d'%g,5) for g in range(K)]
for g in range(K):
 s.add(z3.ULE(ops[g],2),z3.ULT(as_[g],10+g),z3.ULT(bs[g],10+g))
 s.add(z3.If(ops[g]==2,as_[g]==bs[g],z3.ULT(as_[g],bs[g])))

s.add(sum([z3.If(o==2,z3.BitVecVal(1,5),z3.BitVecVal(0,5)) for o in ops],z3.BitVecVal(0,5))==a.nots)
# Two successive independent gates of equal operation can be ordered canonically.
with open('/tmp/oec/pequalnp-pilot-109/counterexample/near-three-extra.json') as f: baseline=json.load(f)
s.add(z3.ULE(sum([z3.If(z3.Or(ops[g]!=v[0],as_[g]!=v[1],bs[g]!=v[2]),z3.BitVecVal(1,5),z3.BitVecVal(0,5)) for g,v in enumerate(baseline)],z3.BitVecVal(0,5)),a.changes))
if a.normalize_not:
 for g in range(1,K):
  s.add(z3.Implies(ops[g]==2,z3.Or(z3.And(as_[g]==9+g,ops[g-1]!=2),z3.And(ops[g-1]==2,z3.ULT(as_[g],10),z3.ULT(as_[g-1],as_[g])))))
if a.first>=0:
 if a.first==4:s.add(ops[0]==2,as_[0]==0)
 else:s.add(ops[0]==a.first//2,as_[0]==0,bs[0]==(1 if a.first%2==0 else 2))
seen=set()
def add_samples(samples):
 samples=[x for x in samples if x not in seen]; seen.update(samples)
 if not samples:return
 n=len(samples)
 wires=[z3.BitVecVal(sum(((x>>j)&1)<<i for i,x in enumerate(samples)),n) for j in range(10)]
 def pick(sel):
  v=wires[-1]
  for j in range(len(wires)-2,-1,-1): v=z3.If(sel==j,wires[j],v)
  return v
 for g in range(K):
  va,vb=pick(as_[g]),pick(bs[g]); v=z3.BitVec('v%d_%d'%(len(seen),g),n)
  s.add(v==z3.If(ops[g]==0,va&vb,z3.If(ops[g]==1,va|vb,~va)))
  wires.append(v)
 s.add(wires[-1]==z3.BitVecVal(sum(int(target(x))<<i for i,x in enumerate(samples)),n))
add_samples([x for x in range(1024) if not target(x) or x.bit_count()==2 or (a.dense and (x.bit_count()==3 or x.bit_count()>=9))])
print('start',time.time(),'gates',K,'nots',a.nots,'samples',len(seen),flush=True)
for it in range(100):
 t=time.time(); r=s.check(); print('check',it,str(r),'seconds',time.time()-t,flush=True)
 if r!=z3.sat:
  print(s.statistics(),flush=True); break
 m=s.model(); gs=[[m.eval(ops[g]).as_long(),m.eval(as_[g]).as_long(),m.eval(bs[g]).as_long()] for g in range(K)]
 bad=[x for x,v in enumerate(evaluate(gs)) if v!=target(x)]
 print('candidate',gs,'bad',len(bad),flush=True)
 if not bad:
  print('WITNESS',json.dumps(gs),flush=True);break
 random.Random(a.seed+it).shuffle(bad);add_samples(bad[:50])
