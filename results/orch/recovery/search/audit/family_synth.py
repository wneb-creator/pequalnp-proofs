import sys,json,time,argparse
from pathlib import Path
sys.path.insert(0,'/tmp/oec/pequalnp-pilot-109/counterexample/z3-5.3.3-x64-glibc-2.39/bin/python')
import z3
p=argparse.ArgumentParser();p.add_argument('--gates',type=int,default=11);p.add_argument('--nots',type=int,default=1);p.add_argument('--timeout',type=int,default=180000);p.add_argument('--seed',type=int,default=1);p.add_argument('--partial',action='store_true');p.add_argument('--out');a=p.parse_args();N=6;K=a.gates
triples=[(0,2,5),(1,3,5),(2,3,4),(0,1,4)]
Ts=[sum(int(any((x>>j)&1 for j in t))<<x for x in range(64)) for t in triples]
M=sum(int(any((x>>i)&1 and (x>>j)&1 for i,j in [(0,3),(1,2),(4,5)]))<<x for x in range(64))
s=z3.SolverFor('QF_BV');s.set(timeout=a.timeout,random_seed=a.seed)
ops=[z3.BitVec('op%d'%g,2) for g in range(K)];aa=[z3.BitVec('a%d'%g,5) for g in range(K)];bb=[z3.BitVec('b%d'%g,5) for g in range(K)];outs=[z3.BitVec('o%d'%i,5) for i in range(5)]
for g in range(K):
 s.add(z3.ULE(ops[g],2),z3.ULT(aa[g],N+g),z3.ULT(bb[g],N+g))
 s.add(z3.If(ops[g]==2,aa[g]==bb[g],z3.ULT(aa[g],bb[g])))
 s.add(z3.Or(*[z3.Or(aa[h]==N+g,bb[h]==N+g) for h in range(g+1,K)],*[o==N+g for o in outs]))
 if g<K-1:s.add(z3.Implies(z3.And(ops[g]==ops[g+1],aa[g+1]!=N+g,bb[g+1]!=N+g),z3.ULE(aa[g],aa[g+1])))
s.add(sum([z3.If(o==2,z3.BitVecVal(1,5),z3.BitVecVal(0,5)) for o in ops],z3.BitVecVal(0,5))==a.nots)
for o in outs:s.add(z3.UGE(o,N),z3.ULT(o,N+K))
s.add(z3.Distinct(*outs))
w=[z3.BitVecVal(sum(((x>>j)&1)<<x for x in range(64)),64) for j in range(N)]
def pick(sel,values):
 r=values[-1]
 for j in range(len(values)-2,-1,-1):r=z3.If(sel==j,values[j],r)
 return r
for g in range(K):
 va,vb=pick(aa[g],w),pick(bb[g],w);v=z3.BitVec('v%d'%g,64)
 s.add(v==z3.If(ops[g]==0,va&vb,z3.If(ops[g]==1,va|vb,~va)));w.append(v)
for i in range(4):s.add(pick(outs[i],w)==Ts[i])
if a.partial:s.add((pick(outs[4],w)&Ts[3])==M)
else:s.add(pick(outs[4],w)==M)
print('start',time.time(),'gates',K,'nots',a.nots,'partial',a.partial,flush=True)
r=s.check();print('result',r,'time',time.time(),flush=True)
if r==z3.sat:
 model=s.model();gs=[[model.eval(ops[g]).as_long(),model.eval(aa[g]).as_long(),model.eval(bb[g]).as_long()] for g in range(K)];oo=[model.eval(o).as_long() for o in outs]
 vals=[sum(((x>>j)&1)<<x for x in range(64)) for j in range(N)]
 for op,i,j in gs:vals.append(vals[i]&vals[j] if op==0 else vals[i]|vals[j] if op==1 else ((1<<64)-1)^vals[i])
 assert [vals[o] for o in oo[:4]]==Ts
 assert (vals[oo[4]]&Ts[3] if a.partial else vals[oo[4]])==M
 d={'gates':gs,'outputs':oo,'partial':a.partial,'nots':a.nots};print(json.dumps(d),flush=True)
 if a.out:Path(a.out).write_text(json.dumps(d)+'\n')
print(s.statistics(),flush=True)
