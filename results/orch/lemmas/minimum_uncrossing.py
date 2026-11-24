import json,time,z3,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
base=Path(__file__).resolve().parent
saved=base/'counterexample'
rows=json.loads((saved/'all3_results.json').read_text())
answers=[]
for row in rows:
 if row['clean'] or row['result']!='sat':continue
 N=row['N']; n=2*N; s=row['size']; es={tuple(e)for e in row['edges']}
 path=base/(row['case']+'_minimum_dirty.smt2')
 subprocess.run([sys.executable,str(saved/'synth_smt.py'),'--N',str(N),'--edges',','.join(str(i)+':'+str(j)for i,j in es),'--size',str(s),'--out',str(path),'--timeout-ms','20000'],check=True,capture_output=True,text=True)
 solver=z3.Solver();solver.set(timeout=20000);solver.from_file(str(path))
 mask=sum(1<<((1<<i)|(1<<(N+j)))for i in range(N)for j in range(N)if(i,j)not in es)
 solver.add(z3.Or([z3.And(z3.Bool('and'+str(j)),z3.BitVec('w'+str(j),1<<n)&mask!=0)for j in range(s)]))
 start=time.monotonic();r=solver.check()
 out={'at':datetime.now(timezone.utc).isoformat(),'case':row['case'],'N':N,'edges':row['edges'],'size':s,'query':'some nonedge-dirty AND in minimum circuit','result':str(r),'seconds':round(time.monotonic()-start,3)}
 if r==z3.sat:
  m=solver.model(); vals=[sum(1<<x for x in range(1<<n)if x>>i&1)for i in range(n)];circ=[];dirty=[]
  for j in range(s):
   a=m[z3.BitVec('a'+str(j),(n+s-1).bit_length())].as_long();b=m[z3.BitVec('b'+str(j),(n+s-1).bit_length())].as_long();isand=z3.is_true(m[z3.Bool('and'+str(j))]);v=vals[a]&vals[b]if isand else vals[a]|vals[b];vals.append(v);circ.append(['and'if isand else'or',a,b]);
   if isand and v&mask:dirty.append(j)
  target=sum(1<<x for x in range(1<<n)if any(x>>i&1 and x>>(N+j)&1 for i,j in es));assert vals[-1]==target;assert dirty
  out['circuit']=circ;out['dirty']=dirty
 elif r==z3.unknown:out['reason']=solver.reason_unknown()
 answers.append(out)
 (base/'minimum_uncrossing_results.json').write_text(json.dumps(answers,indent=2)+'\n')
 (base/(row['case']+'_minimum_dirty_solver.log')).write_text(str(solver.statistics())+'\n')
 print(json.dumps(out),flush=True)
