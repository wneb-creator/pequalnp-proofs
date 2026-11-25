import argparse,json,random,sys,time
sys.path.insert(0,'/tmp/oec/pequalnp-pilot-109/counterexample/z3-5.3.3-x64-glibc-2.39/bin/python')
import z3
E=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def target(x): return any(((x>>a)&1) and ((x>>b)&1) for a,b in E)
def evaluate(gs,flip):
 out=[]
 for x in range(1024):
  w=[bool((x>>j)&1) for j in range(10)]
  for op,a,b,na,nb in gs:
   av,bv=w[a]^na,w[b]^nb
   w.append((av and bv) if op==0 else (av or bv))
  out.append(w[-1]^flip)
 return out
p=argparse.ArgumentParser()
p.add_argument('--binary',type=int,default=15)
p.add_argument('--negations',type=int,default=4)
p.add_argument('--seed',type=int,default=1)
p.add_argument('--timeout',type=int,default=300000)
p.add_argument('--fan2',action='store_true')
p.add_argument('--collapsed-fan2',action='store_true')
p.add_argument('--covered',action='store_true')
p.add_argument('--twins',action='store_true')
p.add_argument('--first',type=int,default=-1)
p.add_argument('--rows',choices=['91','full','boundary'],default='91')
p.add_argument('--pin')
p.add_argument('--output',default='/tmp/oec/pequalnp-pilot-109/finite/signed-witness.json')
a=p.parse_args(); K=a.binary; N=10
s=z3.SolverFor('QF_BV'); s.set(timeout=a.timeout,random_seed=a.seed)
ops=[z3.Bool('op%d'%g) for g in range(K)]
as_=[z3.BitVec('a%d'%g,5) for g in range(K)]
bs=[z3.BitVec('b%d'%g,5) for g in range(K)]
nas=[z3.Bool('na%d'%g) for g in range(K)]
nbs=[z3.Bool('nb%d'%g) for g in range(K)]
neg=[z3.Bool('neg%d'%w) for w in range(N+K)]
flip=z3.Bool('flip')
branches=[z3.Bool('branch%d'%w) for w in range(N+K)]
for g in range(K):
 s.add(z3.ULT(as_[g],N+g),z3.ULT(bs[g],N+g),z3.ULT(as_[g],bs[g]))
for w in range(N+K):
 pu=[z3.And(as_[g]==w,z3.Not(nas[g])) for g in range(K)]
 pu+=[z3.And(bs[g]==w,z3.Not(nbs[g])) for g in range(K)]
 nu=[z3.And(as_[g]==w,nas[g]) for g in range(K)]
 nu+=[z3.And(bs[g]==w,nbs[g]) for g in range(K)]
 total=sum(z3.If(v,z3.BitVecVal(1,8),z3.BitVecVal(0,8)) for v in pu+nu)
 s.add(branches[w]==(total==2))
 if a.collapsed_fan2 or a.covered or a.twins:s.add(z3.ULE(total,2))
 need=z3.Or(*(nu+([flip] if w==N+K-1 else [])))
 s.add(neg[w]==need)
 if w<N+K-1:
  s.add(z3.Or(*(pu+nu)))
 if a.fan2:
  s.add(z3.ULE(sum(z3.If(v,z3.BitVecVal(1,8),z3.BitVecVal(0,8)) for v in pu+[neg[w]]),2))
  s.add(z3.ULE(sum(z3.If(v,z3.BitVecVal(1,8),z3.BitVecVal(0,8)) for v in nu),2))
s.add(z3.ULE(sum(z3.If(v,z3.BitVecVal(1,8),z3.BitVecVal(0,8)) for v in neg),a.negations))
if a.covered and not a.twins:
 uncovered=[z3.BoolVal(True) for w in range(N)]
 for g in range(K):
  def carry(sel):
   val=z3.And(uncovered[-1],z3.Not(branches[len(uncovered)-1]))
   for w in range(len(uncovered)-2,-1,-1):val=z3.If(sel==w,z3.And(uncovered[w],z3.Not(branches[w])),val)
   return val
  u=z3.Bool('uncovered%d'%g)
  s.add(u==z3.Or(carry(as_[g]),carry(bs[g])))
  s.add(z3.Implies(branches[N+g],u));uncovered.append(u)
if a.twins:
 neighbor=[sum(1<<v for v in range(N) if (w,v) in E or (v,w) in E) for w in range(N)]
 masks=[z3.BitVecVal(1<<w,N) for w in range(N)]
 below=z3.BitVecVal(0,N)
 for w in range(N):below=below|z3.If(branches[w],masks[w],z3.BitVecVal(0,N))
 for g in range(K):
  def carry_mask(sel):
   val=z3.If(branches[len(masks)-1],z3.BitVecVal(0,N),masks[-1])
   for w in range(len(masks)-2,-1,-1):val=z3.If(sel==w,z3.If(branches[w],z3.BitVecVal(0,N),masks[w]),val)
   return val
  mask=z3.BitVec('firstmask%d'%g,N)
  s.add(mask==(carry_mask(as_[g])|carry_mask(bs[g])))
  s.add(z3.Implies(branches[N+g],mask!=0),mask&below==0)
  for u,v in E:s.add((mask&((1<<u)|(1<<v)))!=((1<<u)|(1<<v)))
  for u in range(N):
   for v in range(u+1,N):
    both=(mask&((1<<u)|(1<<v)))==((1<<u)|(1<<v))
    ru=z3.BitVecVal(neighbor[u],N)&~below
    rv=z3.BitVecVal(neighbor[v],N)&~below
    s.add(z3.Implies(z3.And(branches[N+g],both,ru!=0,rv!=0),ru==rv))
  masks.append(mask)
  below=below|z3.If(branches[N+g],mask,z3.BitVecVal(0,N))
 s.add((below|masks[-1])==(1<<N)-1)
# Canonical order of adjacent independent gates: predecessor indices are unchanged by swapping.
keys=[z3.Concat(as_[g],bs[g],z3.If(ops[g],z3.BitVecVal(1,1),z3.BitVecVal(0,1)),z3.If(nas[g],z3.BitVecVal(1,1),z3.BitVecVal(0,1)),z3.If(nbs[g],z3.BitVecVal(1,1),z3.BitVecVal(0,1))) for g in range(K)]
for g in range(K-1):
 s.add(z3.Implies(z3.And(as_[g+1]!=N+g,bs[g+1]!=N+g),z3.ULE(keys[g],keys[g+1])))
# The first pair has one of the two Petersen automorphism orbits.
if a.first>=0:
 # 0..11 = op AND/OR, edge/nonedge, signs 00/01/11.
 orb=a.first%2; mode=(a.first//2)%3; op=(a.first//6)%2
 s.add(as_[0]==0,bs[0]==(1 if orb==0 else 2),ops[0]==bool(op))
 s.add(nas[0]==(mode==2),nbs[0]==(mode>=1))
if a.pin:
 with open(a.pin) as stream: pinned=json.load(stream)
 assert len(pinned['gates'])==K
 for g,(op,aa,bb,na,nb) in enumerate(pinned['gates']):
  s.add(ops[g]==bool(op),as_[g]==aa,bs[g]==bb,nas[g]==na,nbs[g]==nb)
 s.add(flip==pinned['flip'])
seen=set()
def add_samples(rows):
 rows=[r for r in rows if r not in seen];seen.update(rows)
 if not rows:return
 sz=len(rows); tag=len(seen)
 wires=[z3.BitVecVal(sum(((r>>j)&1)<<i for i,r in enumerate(rows)),sz) for j in range(N)]
 def pick(sel):
  v=wires[-1]
  for j in range(len(wires)-2,-1,-1):v=z3.If(sel==j,wires[j],v)
  return v
 for g in range(K):
  va,vb=pick(as_[g]),pick(bs[g]);va=z3.If(nas[g],~va,va);vb=z3.If(nbs[g],~vb,vb)
  v=z3.BitVec('v%d_%d'%(tag,g),sz)
  s.add(v==z3.If(ops[g],va|vb,va&vb));wires.append(v)
 out=z3.If(flip,~wires[-1],wires[-1]); wanted=sum(int(target(r))<<i for i,r in enumerate(rows))
 s.add(out==z3.BitVecVal(wanted,sz))
if a.rows=='full': rows=list(range(1024))
elif a.rows=='boundary':
 rows=[r for r in range(1024) if (target(r) and r.bit_count()==2) or (not target(r) and all(target(r|(1<<j)) for j in range(10) if not ((r>>j)&1)))]
else:rows=[r for r in range(1024) if not target(r) or r.bit_count()==2]
add_samples(rows)
print('start',time.time(),'binary',K,'negations',a.negations,'fan2',a.fan2,'collapsed_fan2',a.collapsed_fan2,'covered',a.covered,'twins',a.twins,'first',a.first,'samples',len(seen),flush=True)
for it in range(100):
 t=time.time();r=s.check();print('check',it,str(r),'seconds',time.time()-t,'samples',len(seen),flush=True)
 if r!=z3.sat:
  print('reason',s.reason_unknown() if r==z3.unknown else 'proved UNSAT by search only',flush=True)
  print(s.statistics(),flush=True);break
 m=s.model();gs=[[int(z3.is_true(m.eval(ops[g]))),m.eval(as_[g]).as_long(),m.eval(bs[g]).as_long(),z3.is_true(m.eval(nas[g])),z3.is_true(m.eval(nbs[g]))] for g in range(K)]
 f=z3.is_true(m.eval(flip));bad=[x for x,v in enumerate(evaluate(gs,f)) if v!=target(x)]
 print('candidate',json.dumps(gs),'flip',f,'bad',len(bad),flush=True)
 if not bad:
  data={'gates':gs,'flip':f,'negative_sources':[w for w in range(N+K) if z3.is_true(m.eval(neg[w]))]}
  with open(a.output,'w') as stream:json.dump(data,stream,indent=2)
  print('WITNESS',json.dumps(data),flush=True);break
 random.Random(a.seed+it).shuffle(bad);add_samples(bad[:50])
