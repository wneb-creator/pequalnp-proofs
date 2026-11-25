import sys,time,json,argparse
sys.path.insert(0,'/tmp/oec/pequalnp-pilot-109/counterexample/z3-5.3.3-x64-glibc-2.39/bin/python')
import z3
p=argparse.ArgumentParser();p.add_argument('--gates',type=int,default=5);p.add_argument('--timeout',type=int,default=300000);args=p.parse_args()
raw=[0,2,3,4,6,7,8];exprs=[[0],[2],[3],[4],[6],[7],[8],[6,7],[0,2],[0,7],[0,7,8],[0,2,6],[4,8],[2,4,8],[4,6,7]]
def truth(S,x):return any(x>>raw.index(i)&1 for i in S)
T=sum(int((truth([0],x) and truth([4],x)) or (truth([2],x) and truth([7],x)) or (truth([6],x) and truth([8],x)) or (truth([3],x) and truth([2,4,8],x)))<<x for x in range(128))
w=[z3.BitVecVal(sum(int(truth(S,x))<<x for x in range(128)),128) for S in exprs]
s=z3.SolverFor('QF_BV');s.set(timeout=args.timeout)
K=args.gates;op=[z3.BitVec('op%d'%i,2)for i in range(K)];a=[z3.BitVec('a%d'%i,5)for i in range(K)];b=[z3.BitVec('b%d'%i,5)for i in range(K)]
for i in range(K):
 s.add(z3.ULE(op[i],2),z3.ULT(a[i],len(w)),z3.ULT(b[i],len(w)),z3.If(op[i]==2,a[i]==b[i],z3.ULT(a[i],b[i])))
 def pick(v):
  t=w[-1]
  for j in range(len(w)-2,-1,-1):t=z3.If(v==j,w[j],t)
  return t
 va,vb=pick(a[i]),pick(b[i]);v=z3.BitVec('v%d'%i,128);s.add(v==z3.If(op[i]==0,va&vb,z3.If(op[i]==1,va|vb,~va)));w.append(v)
s.add(z3.Or(*[o==2 for o in op]),w[-1]==z3.BitVecVal(T,128))
print('start',time.time(),'gates',K,flush=True);r=s.check();print(r,flush=True)
if r==z3.sat:
 m=s.model();gs=[[m.eval(o).as_long(),m.eval(x).as_long(),m.eval(y).as_long()]for o,x,y in zip(op,a,b)];print('WITNESS',json.dumps(gs),flush=True);print('available',exprs,flush=True)
print(s.statistics(),flush=True)
