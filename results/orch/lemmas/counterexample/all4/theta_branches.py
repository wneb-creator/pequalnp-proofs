import z3,json,time,subprocess,sys,threading
from pathlib import Path
from itertools import permutations
from concurrent.futures import ThreadPoolExecutor,as_completed
from datetime import datetime,timezone
base=Path(__file__).resolve().parent;D=json.loads((base/'classes.json').read_text());N=D['N'];g=next(g for g in D['classes']if g['id']=='g59731');edges=set(map(tuple,g['edges']));auts=[]
for rp in permutations(range(N)):
 for cp in permutations(range(N)):
  if{(rp[i],cp[j])for i,j in edges}==edges:auts.append(tuple(rp)+tuple(N+j for j in cp))
  if{(cp[j],rp[i])for i,j in edges}==edges:auts.append(tuple(N+i for i in rp)+tuple(cp))
pairs=[(i,j)for i in range(2*N)for j in range(i+1,2*N)if(i,j)==min(tuple(sorted((au[i],au[j])))for au in auts)]
source=base/'g59731_free_atmost11.smt2';forms=z3.parse_smt2_file(str(source));branches=[]
for i,(u,v)in enumerate(pairs):
 for op in [False,True]:
  tag=f'theta_branch_{i}_{int(op)}';path=base/'branches'/tag;path.mkdir(parents=True,exist_ok=True);s=z3.Solver();s.add(forms);s.add(z3.BitVec('a0',5)==u,z3.BitVec('b0',5)==v,z3.Bool('and0')==op);(path/source.name).write_text(s.to_smt2());branches.append({'tag':tag,'pair':[u,v],'op':'and'if op else'or','smt':str(path/source.name)})
(base/'theta_branches.json').write_text(json.dumps({'automorphisms':len(auts),'pairs':pairs,'branches':branches},indent=2)+'\n');results=[];lock=threading.Lock();stop=threading.Event();start=time.monotonic()
def work(br):
 if stop.is_set():return
 with(base/(br['tag']+'.run.log')).open('w')as f:
  proc=subprocess.run([sys.executable,str(base/'kissat_probe.py'),'--smt',br['smt'],'--tag',br['tag'],'--seconds','180'],stdout=f,stderr=subprocess.STDOUT)
 resultfile=base/(br['tag']+'_'+source.stem+'_kissat.json')
 row=json.loads(resultfile.read_text())if proc.returncode==0 and resultfile.exists()else{'tag':br['tag'],'result':'adapter_error','exitcode':proc.returncode}
 row.update(pair=br['pair'],op=br['op'])
 with lock:
  results.append(row);(base/'theta_branch_results.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(row),flush=True)
 if row['result']=='sat':stop.set()
with ThreadPoolExecutor(max_workers=2)as ex:
 fs=[ex.submit(work,b)for b in branches]
 for f in as_completed(fs):f.result()
print(json.dumps({'at':datetime.now(timezone.utc).isoformat(),'result':'branches_complete','seconds':time.monotonic()-start,'count':len(results),'candidate':stop.is_set()}),flush=True)
