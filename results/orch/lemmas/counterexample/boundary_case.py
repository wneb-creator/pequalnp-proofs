import z3,sys,json,time,subprocess
from pathlib import Path
from datetime import datetime,timezone
p=Path(__file__).resolve().parent
name,N,estr,s,clean=sys.argv[1],int(sys.argv[2]),sys.argv[3],int(sys.argv[4]),bool(int(sys.argv[5]))
key=f'{name}_boundary_{"clean" if clean else "free"}_{s}'
cmd=[sys.executable,str(p/'synth_smt.py'),'--N',str(N),'--edges',estr,'--size',str(s),'--out',str(p/(key+'.smt2')),'--timeout-ms','120000','--lex','--boundary']+(['--clean']if clean else[])
gen=subprocess.run(cmd,capture_output=True,text=True,check=True)
solver=z3.Solver();solver.set(timeout=120000);solver.from_file(str(p/(key+'.smt2')));t=time.monotonic();r=solver.check();out={'at':datetime.now(timezone.utc).isoformat(),'name':name,'size':s,'clean':clean,'result':str(r),'seconds':time.monotonic()-t}
log=gen.stdout+gen.stderr+'\n'+str(solver.statistics())+'\n'
if r==z3.sat:
 m=solver.model();log+=str(m)+'\n';edges=[tuple(map(int,e.split(':')))for e in estr.split(',')];rows=1<<(2*N);vals=[sum(1<<r for r in range(rows) if r>>i&1)for i in range(2*N)];circ=[];fb=sum(1<<(1<<i)for i in range(2*N))|sum(1<<((1<<i)|(1<<(N+j)))for i in range(N)for j in range(N)if(i,j)not in edges)
 for j in range(s):
  a=m[z3.BitVec(f'a{j}',(2*N+s-1).bit_length())].as_long();b=m[z3.BitVec(f'b{j}',(2*N+s-1).bit_length())].as_long();op=z3.is_true(m[z3.Bool(f'and{j}')]);v=vals[a]&vals[b]if op else vals[a]|vals[b];vals.append(v);circ.append(['and'if op else'or',a,b]);assert not(clean and op and v&fb)
 target=sum(1<<r for r in range(rows)if any((r>>i&1)and(r>>(N+j)&1)for i,j in edges));assert vals[-1]==target;out['circuit']=circ
out['reason']=solver.reason_unknown()if r==z3.unknown else None
(p/(key+'.log')).write_text(log);(p/(key+'.json')).write_text(json.dumps(out,indent=2));print(json.dumps(out),flush=True)
