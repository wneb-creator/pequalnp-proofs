from pathlib import Path
from datetime import datetime,timezone
import subprocess,json
start=datetime.now(timezone.utc).isoformat()
with Path('signed-cost-solve.stdout.txt').open('w') as out,Path('signed-cost-solve.stderr.txt').open('w') as err:
 r=subprocess.run(['./phase-signed','signed18-cost19.cnf','signed18-seed.txt','1200'],stdout=out,stderr=err)
report={'started':start,'finished':datetime.now(timezone.utc).isoformat(),'returncode':r.returncode}
if r.returncode==10:
 with Path('signed-model-decode.stdout.txt').open('w') as out,Path('signed-model-decode.stderr.txt').open('w') as err:
  dec=subprocess.run(['python3','decode-signed.py','signed-cost-solve.stdout.txt','signed-actual-model.json'],stdout=out,stderr=err)
 report['decoder_returncode']=dec.returncode
 if dec.returncode==0:
  data=json.loads(Path('signed-actual-model.json').read_text())
  for key in ['binary_gates','minimum_not_count','actual_size','actual_not_count','errors','held_gap_counterexample']:
   report[key]=data[key]
Path('signed-cost-solve.result.json').write_text(json.dumps(report,indent=2))
print(json.dumps(report),flush=True)
