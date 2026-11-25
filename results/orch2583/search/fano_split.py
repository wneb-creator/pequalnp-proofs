from pathlib import Path
from datetime import datetime,timezone
import subprocess,json,time,os,signal,hashlib,shutil
root=Path('/tmp/oec/pequalnp-pilot-103/orch2583');dst=Path('/workspace/pequalnp-proofs/results/orch2583/search');dst.mkdir(exist_ok=True)
orb=json.loads((root/'fano-orbits.json').read_text())['pair_orbits']
cases=[(op,*o['representative'])for op in[0,1]for o in orb]
report=[]
for k,(op,a,b)in enumerate(cases):
 tag=f'fano26-case{k}-'+('or'if op else'and')+f'-{a}-{b}'
 argv=['python3',str(root/'fano_cnf.py'),'--gates','26','--seconds','120','--first',f'{op},{a},{b}','--tag',tag]
 start=time.monotonic();began=datetime.now(timezone.utc).isoformat();timed_out=False
 with(root/f'{tag}.log').open('w')as out,(root/f'{tag}.driver.stderr').open('w')as err:
  p=subprocess.Popen(argv,stdout=out,stderr=err,start_new_session=True)
  try:code=p.wait(timeout=145)
  except subprocess.TimeoutExpired:
   timed_out=True;os.killpg(p.pid,signal.SIGTERM)
   try:code=p.wait(timeout=5)
   except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);code=p.wait()
 rp=root/f'{tag}-result.json'
 result=json.loads(rp.read_text())if rp.exists()else{'status':'UNKNOWN','external_timeout':timed_out}
 row={'case':k,'first_gate':[op,a,b],'started_at':began,'finished_at':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-start,'argv':argv,'driver_exit':code,'result':result}
 report.append(row)
 for suffix in['.log','.driver.stderr','.stdout','.stderr','-result.json','-witness.json']:
  src=root/f'{tag}{suffix}'
  if src.exists():shutil.copy2(src,dst/src.name)
 (dst/'fano26-split-report.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps(row,sort_keys=True),flush=True)
 if result.get('status')=='SAT':
  print((root/f'{tag}.log').read_text(),flush=True);break
print('COMPLETED_CASES',len(report),flush=True)
