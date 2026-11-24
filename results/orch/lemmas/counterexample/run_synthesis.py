import z3
import subprocess
import sys
import json
import time
from pathlib import Path
from datetime import datetime, timezone
base=Path(__file__).resolve().parent
cases=[('p4',2,'0:0,0:1,1:1',3,4),('double_star6',3,'0:0,0:1,0:2,1:0,2:0',5,6),('subdivided_star6',3,'0:0,0:1,0:2,1:0,2:1',5,7),('cycle6',3,'0:0,0:1,1:1,1:2,2:0,2:2',5,8),('cycle8',4,'0:0,0:1,1:1,1:2,2:2,2:3,3:3,3:0',7,11)]
results=[]
for name,N,estr,lo,hi in cases:
 edges=[tuple(map(int,e.split(':'))) for e in estr.split(',')]
 for clean in [False,True]:
  for s in range(lo,hi+1):
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
   results.append(row);(base/'synthesis_results.json').write_text(json.dumps(results,indent=2));print(json.dumps(row),flush=True)
   if r==z3.sat: break
