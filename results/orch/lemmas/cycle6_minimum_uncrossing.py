import json,time,z3
from pathlib import Path
from datetime import datetime,timezone
from itertools import permutations
base=Path(__file__).resolve().parent
N=3;n=6;s=8;width=64;bits=4
solver=z3.Solver();solver.set(timeout=90000);solver.from_file(str(base/'iso3_238_minimum_dirty.smt2'))
a=[z3.BitVec('a'+str(j),bits)for j in range(s)];b=[z3.BitVec('b'+str(j),bits)for j in range(s)];op=[z3.Bool('and'+str(j))for j in range(s)];w=[z3.BitVec('w'+str(j),width)for j in range(s)]
es={(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)}
mask=sum(1<<((1<<i)|(1<<(N+j)))for i in range(N)for j in range(N)if(i,j)not in es)
solver.add(z3.Or([z3.And(op[j],w[j]&mask!=0)for j in range(s)]))
for j in range(s-1):
 independent=z3.And(a[j+1]!=n+j,b[j+1]!=n+j)
 lex=z3.Or(z3.ULT(a[j],a[j+1]),z3.And(a[j]==a[j+1],z3.Or(z3.ULT(b[j],b[j+1]),z3.And(b[j]==b[j+1],z3.Or(op[j],z3.Not(op[j+1]))))))
 solver.add(z3.Implies(independent,lex))
autos=[]
for rp in permutations(range(N)):
 for cp in permutations(range(N)):
  if{(rp[i],cp[j])for i,j in es}==es:autos.append(tuple(rp)+tuple(N+j for j in cp))
  if{(cp[j],rp[i])for i,j in es}==es:autos.append(tuple(N+i for i in rp)+tuple(cp))
allowed=[]
for i in range(n):
 for j in range(i+1,n):
  if(i,j)==min(tuple(sorted((au[i],au[j])))for au in autos):allowed.append(z3.And(a[0]==i,b[0]==j))
solver.add(z3.Or(allowed))
(base/'cycle6_minimum_dirty_sym.smt2').write_text(solver.to_smt2())
start=time.monotonic();r=solver.check()
out={'at':datetime.now(timezone.utc).isoformat(),'case':'cycle6','size':8,'query':'some nonedge-dirty AND in minimum circuit, lex and input automorphism symmetry','result':str(r),'seconds':round(time.monotonic()-start,3),'automorphisms':len(autos)}
if r==z3.sat:
 m=solver.model(); vals=[sum(1<<x for x in range(1<<n)if x>>i&1)for i in range(n)];circ=[];dirty=[]
 for j in range(s):
  av=m[a[j]].as_long();bv=m[b[j]].as_long();isand=z3.is_true(m[op[j]]);v=vals[av]&vals[bv]if isand else vals[av]|vals[bv];vals.append(v);circ.append(['and'if isand else'or',av,bv]);
  if isand and v&mask:dirty.append(j)
 target=sum(1<<x for x in range(1<<n)if any(x>>i&1 and x>>(N+j)&1 for i,j in es));assert vals[-1]==target;assert dirty
 out['circuit']=circ;out['dirty']=dirty
elif r==z3.unknown:out['reason']=solver.reason_unknown()
(base/'cycle6_minimum_uncrossing_result.json').write_text(json.dumps(out,indent=2)+'\n')
(base/'cycle6_minimum_uncrossing_solver.log').write_text(str(solver.statistics())+'\n')
print(json.dumps(out),flush=True)
