from pathlib import Path
from datetime import datetime,timezone
import subprocess,sys,json
from cnflib import decode
base=Path('/tmp/oec/pequalnp-pilot-97/counterexample')
solver=sys.argv[1]
for mask in [521,276,773,116]:
 print(datetime.now(timezone.utc).isoformat(),'start orbit',mask,flush=True)
 log=base/f'essential-not1-{mask}.log'
 with log.open('w') as f:
  p=subprocess.run([solver,'-t','300','--sat','--seed=97',str(base/f'essential-not1-{mask}.cnf')],stdout=f,stderr=subprocess.STDOUT)
 print(datetime.now(timezone.utc).isoformat(),'end orbit',mask,'return',p.returncode,flush=True)
 if p.returncode==10:
  d=decode(log)
  (base/f'essential-not1-{mask}-model.json').write_text(json.dumps(d,indent=2))
  print('errors',len(d['bad_rows']),flush=True)
  if not d['bad_rows']:break
