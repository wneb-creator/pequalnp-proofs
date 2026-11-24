import z3
import subprocess
import sys
import json
import time
from pathlib import Path
from datetime import datetime, timezone
base=Path(__file__).resolve().parent
from itertools import permutations,combinations
N=3;perms=list(permutations(range(N)));orbits=set();total=0
for mask in range(1<<(N*N)):
 edges={(i,j)for i in range(N)for j in range(N)if mask>>(i*N+j)&1}
 if any(all((i,j)in edges for i in [p,q]for j in [l,m])for p,q in combinations(range(N),2)for l,m in combinations(range(N),2)):continue
 total+=1;vals=[]
 for rp in perms:
  for cp in perms:
   vals.append(sum(1<<(rp[i]*N+cp[j])for i,j in edges));vals.append(sum(1<<(cp[j]*N+rp[i])for i,j in edges))
 orbits.add(min(vals))
cases=[]
for mask in sorted(orbits-{0}):
 edges=[(i,j)for i in range(N)for j in range(N)if mask>>(i*N+j)&1]
 active=len(set(i for i,j in edges))+len(set(j for i,j in edges))
 tau=min(m.bit_count()for m in range(1<<(2*N))if all((m>>i&1)or(m>>(N+j)&1)for i,j in edges))
 cases.append((f'iso3_{mask}',N,','.join(f'{i}:{j}'for i,j in edges),active-1,len(edges)+tau-1))
print('C4-free matrices',total,'classes',len(orbits),flush=True)
results=[]
for name,N,estr,lo,hi in cases:
 edges=[tuple(map(int,e.split(':'))) for e in estr.split(',')]
 for clean in [False,True]:
  for s in range(minimum if clean else lo,hi+1):
   key=f'{name}_{"clean" if clean else "free"}_{s}'; smt=base/(key+'.smt2')
   cmd=[sys.executable,str(base/'synth_smt.py'),'--N',str(N),'--edges',estr,'--size',str(s),'--out',str(smt),'--timeout-ms','45000']+(['--clean'] if clean else [])
   gen=subprocess.run(cmd,capture_output=True,text=True,check=True)
   solver=z3.Solver();solver.set(timeout=45000);solver.from_file(str(smt));beg=time.monotonic();r=solver.check();dt=time.monotonic()-beg
   row={'at':datetime.now(timezone.utc).isoformat(),'case':name,'N':N,'edges':edges,'clean':clean,'size':s,'result':str(r),'seconds':round(dt,3)}
   log=gen.stdout+gen.stderr+'\n'+str(r)+'\n'+str(solver.statistics())+'\n'
   if r==z3.sat:
    m=solver.model();log+=str(m)+'\n'; rows=1<<(2*N);w=[sum(1<<r for r in range(rows) if r>>i&1) for i in range(2*N)];circ=[];fb=sum(1<<(1<<i) for i in range(2*N))|sum(1<<((1<<i)|(1<<(N+j))) for i in range(N) for j in range(N) if (i,j) not in edges)
    for j in range(s):
     a=m[z3.BitVec(f'a{j}',(2*N+s-1).bit_length())].as_long(); b=m[z3.BitVec(f'b{j}',(2*N+s-1).bit_length())].as_long(); isand=z3.is_true(m[z3.Bool(f'and{j}')]);v=w[a]&w[b] if isand else w[a]|w[b];assert a<b<2*N+j;w.append(v);circ.append(['and' if isand else 'or',a,b]);assert not(clean and isand and v&fb)
    target=sum(1<<r for r in range(rows) if any((r>>i&1)and(r>>(N+j)&1)for i,j in edges));assert w[-1]==target
    row['circuit']=circ
   elif r==z3.unknown: row['reason']=solver.reason_unknown()
   (base/(key+'.log')).write_text(log)
   results.append(row);(base/'all3_results.json').write_text(json.dumps(results,indent=2));print(json.dumps(row),flush=True)
   if r==z3.sat:
    minimum=s
    break
