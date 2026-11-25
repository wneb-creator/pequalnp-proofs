from pathlib import Path
import sys, json, subprocess, time
sys.path.insert(0, '/workspace/pequalnp-proofs/results/orch/search')
from repair_nearmiss_v3 import CNF, SOLVER
root=Path('/tmp/oec/pequalnp-pilot-64')
c=CNF(); ops=[]; sels=[]; k=6
for j in range(k):
 ops.append(c.new())
 a=[c.new() for _ in range(4+j)];b=[c.new() for _ in range(4+j)]
 c.choose(a);pref=c.choose(b)
 for i in range(4+j):c.add(-a[i],-pref[i])
 sels.append((a,b))
def ev(mask):
 w=[1 if mask>>i&1 else -1 for i in range(4)];args=[]
 for j in range(k):
  a,b=[c.mux(s,w) for s in sels[j]];args.append((a,b));w.append(c.op(ops[j],a,b))
 return w,args
def der(base,seed):
 _,args=ev(1<<base);d=[1 if i==seed else -1 for i in range(4)]
 for j in range(k):
  a,b=[c.mux(s,d) for s in sels[j]];av,bv=args[j]
  z=c.lor(c.land(av,b),c.land(a,bv));o=c.lor(a,b);v=c.new()
  c.add(-ops[j],-v,z);c.add(-ops[j],v,-z);c.add(ops[j],-v,o);c.add(ops[j],v,-o)
  d.append(v)
 c.add(-d[-1])
for mask in range(16):
 target=any((mask>>a&1) and (mask>>b&1) for a,b in [(0,1),(0,2),(1,3)])
 vals,_=ev(mask);c.add(vals[-1] if target else -vals[-1])
der(0,1);der(1,0)
cnf=root/'audit-path-center6.cnf';c.write(cnf)
start=time.time()
with (root/'audit-path-center6.stdout').open('w') as out,(root/'audit-path-center6.stderr').open('w') as err:
 p=subprocess.run([str(SOLVER),'-t','20',str(cnf)],stdout=out,stderr=err)
print(json.dumps({'gates':k,'variables':c.n,'clauses':len(c.cs),'solver_code':p.returncode,'seconds':time.time()-start}))
if p.returncode==10:
 truth={int(t) for line in (root/'audit-path-center6.stdout').read_text().splitlines() if line.startswith('v ') for t in line[2:].split() if int(t)>0}
 gates=[]
 for j in range(k):
  a,b=[[i for i,v in enumerate(s) if v in truth] for s in sels[j]]
  assert len(a)==len(b)==1
  gates.append([int(ops[j] in truth),a[0],b[0]])
 print(json.dumps(gates))
