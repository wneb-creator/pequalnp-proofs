import json,os,signal,subprocess,sys,time
from datetime import datetime,timezone
from pathlib import Path

base=Path('/tmp/oec/pequalnp-pilot-70/circuit-search')
def stamp():return datetime.now(timezone.utc).isoformat()
general=None
for pid in subprocess.check_output(['pgrep','-x','cadical'],text=True).split():
 argv=(Path('/proc')/pid/'cmdline').read_bytes().split(b'\0')
 if str(base/'heawood26.cnf').encode() in argv:general=int(pid)
if general is None:raise SystemExit('general solver not found; inspect before launching')
os.kill(general,signal.SIGSTOP)
start=time.time();events=[{'event':'pause_general','at':stamp(),'pid':general}]
print(json.dumps(events[-1]),flush=True)
try:
 for name,budget in [('subgraph-3-0',60),('subgraph-3-1',60),('subgraph-4-0',120),('subgraph-4-1',120)]:
  graph=json.loads((base/f'{name}.json').read_text());cnf=base/f'{name}.cnf'
  with (base/f'{name}-encode.log').open('w') as log:
   subprocess.run([sys.executable,str(base/'synthesize.py'),'--gates',str(graph['target_gates']),'--edge-file',str(base/f'{name}.json'),'--no-canon','--output',str(cnf)],stdout=log,stderr=subprocess.STDOUT,check=True)
  at=stamp();begin=time.time();solve=base/f'{name}-solve.log'
  with solve.open('w') as log:
   result=subprocess.run([str(base/'cadical/build/cadical'),'-t',str(budget),str(cnf)],stdout=log,stderr=subprocess.STDOUT)
  event={'event':'subgraph_result','name':name,'started_at':at,'finished_at':stamp(),'wall_seconds':time.time()-begin,'exit_code':result.returncode,'status':{10:'SAT',20:'UNSAT',0:'UNKNOWN'}.get(result.returncode,'ERROR')}
  events.append(event);print(json.dumps(event),flush=True)
  if result.returncode==10:
   with (base/f'{name}-verified.log').open('w') as log:
    subprocess.run([sys.executable,str(base/'decode.py'),str(cnf.with_suffix('.map.json')),str(solve)],stdout=log,stderr=subprocess.STDOUT,check=True)
   break
  if result.returncode not in (0,20):break
finally:
 try:os.kill(general,signal.SIGCONT)
 except ProcessLookupError:pass
 events.append({'event':'resume_general','at':stamp(),'pid':general,'pause_seconds':time.time()-start})
 (base/'subgraph-round.json').write_text(json.dumps(events,indent=2))
 print(json.dumps(events[-1]),flush=True)
