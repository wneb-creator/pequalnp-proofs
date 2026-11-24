import z3,time,json,sys
from pathlib import Path
from datetime import datetime,timezone
N=int(sys.argv[1]);edges=[tuple(map(int,e.split(':')))for e in sys.argv[2].split(',')];size=int(sys.argv[3]);clean=bool(int(sys.argv[4]));stem=sys.argv[5];n=2*N
p=Path(__file__).resolve().parent
target=lambda r:any((r>>i&1)and(r>>(N+j)&1)for i,j in edges)
fbd={1<<i for i in range(n)}|{(1<<i)|(1<<(N+j))for i in range(N)for j in range(N)if(i,j)not in edges}
rows=sorted(fbd|{(1<<i)|(1<<(N+j))for i,j in edges}|{r for r in range(1<<n)if not target(r)and all(target(r|(1<<i))for i in range(n)if not r>>i&1)})
solver=z3.Then('simplify','card2bv','tseitin-cnf','sat').solver();solver.set(timeout=120000)
w=[[z3.Bool(f'w{j}_{r}')for r in rows]for j in range(size)];a=[[z3.Bool(f'a{j}_{k}')for k in range(n+j)]for j in range(size)];b=[[z3.Bool(f'b{j}_{k}')for k in range(n+j)]for j in range(size)];op=[z3.Bool(f'and{j}')for j in range(size)];sides=[[[z3.Bool(f'side{d}_{j}_{r}')for r in rows]for j in range(size)]for d in range(2)]
for j in range(size):
 for src,side in [(a[j],sides[0][j]),(b[j],sides[1][j])]:
  solver.add(z3.PbEq([(x,1)for x in src],1))
  for k,v in enumerate(src):
   for ri,r in enumerate(rows):solver.add(z3.Implies(v,side[ri]==(z3.BoolVal(bool(r>>k&1))if k<n else w[k-n][ri])))
 for k in range(n+j):
  for l in range(k+1):solver.add(z3.Or(z3.Not(a[j][k]),z3.Not(b[j][l])))
 for ri,r in enumerate(rows):
  solver.add(w[j][ri]==z3.If(op[j],z3.And(sides[0][j][ri],sides[1][j][ri]),z3.Or(sides[0][j][ri],sides[1][j][ri])))
  if clean and r in fbd:solver.add(z3.Or(z3.Not(op[j]),z3.Not(w[j][ri])))
 for i in range(j):solver.add(z3.Or([w[j][ri]!=w[i][ri]for ri in range(len(rows))]))
for j in range(size-1):solver.add(z3.Or([src[k][n+j]for k in range(j+1,size)for src in [a,b]]))
for ri,r in enumerate(rows):solver.add(w[-1][ri]==z3.BoolVal(target(r)))
# Lex order of adjacent independent gates.
for j in range(size-1):
 for k in range(n+j):
  for l in range(k):solver.add(z3.Or(z3.Not(a[j][k]),z3.Not(a[j+1][l]),a[j+1][n+j],b[j+1][n+j]))
 for k in range(n+j):
  for l in range(n+j):
   for m in range(l):solver.add(z3.Or(z3.Not(a[j][k]),z3.Not(a[j+1][k]),z3.Not(b[j][l]),z3.Not(b[j+1][m]),a[j+1][n+j],b[j+1][n+j]))
t=time.monotonic();r=solver.check();out={'at':datetime.now(timezone.utc).isoformat(),'N':N,'edges':edges,'size':size,'clean':clean,'result':str(r),'seconds':time.monotonic()-t,'rows':len(rows)}
log=str(solver.statistics())+'\n'
if r==z3.sat:
 m=solver.model();circ=[];vals=[sum(1<<r for r in range(1<<n)if r>>i&1)for i in range(n)];mask=sum(1<<r for r in fbd)
 for j in range(size):
  av=next(k for k,v in enumerate(a[j])if z3.is_true(m[v]));bv=next(k for k,v in enumerate(b[j])if z3.is_true(m[v]));opv=z3.is_true(m[op[j]]);v=vals[av]&vals[bv]if opv else vals[av]|vals[bv];vals.append(v);circ.append(['and'if opv else'or',av,bv]);assert not(clean and opv and v&mask)
 assert vals[-1]==sum(1<<r for r in range(1<<n)if target(r));out['circuit']=circ
elif r==z3.unknown:out['reason']=solver.reason_unknown()
(p/(stem+'.json')).write_text(json.dumps(out,indent=2));(p/(stem+'.log')).write_text(log);print(json.dumps(out),flush=True)
