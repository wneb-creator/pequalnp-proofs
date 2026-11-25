from pathlib import Path
from datetime import datetime,timezone
import subprocess,json
start=datetime.now(timezone.utc).isoformat()
with Path('mono18-solve.stdout.txt').open('w') as out,Path('mono18-solve.stderr.txt').open('w') as err:
 r=subprocess.run(['./phase-mono','mono18-boundary.cnf','signed18-seed.txt','1200'],stdout=out,stderr=err)
report={'started':start,'finished':datetime.now(timezone.utc).isoformat(),'returncode':r.returncode}
if r.returncode==10:
 with Path('mono18-decode.stdout.txt').open('w') as out,Path('mono18-decode.stderr.txt').open('w') as err:
  dec=subprocess.run(['python3','decode-mono.py','mono18-solve.stdout.txt','mono18-actual-model.json'],stdout=out,stderr=err)
 report['decoder_returncode']=dec.returncode
 if dec.returncode==0:
  data=json.loads(Path('mono18-actual-model.json').read_text())
  for key in ['actual_size','actual_not_count','errors','held_gap_counterexample']: report[key]=data[key]
Path('mono18-solve.result.json').write_text(json.dumps(report,indent=2))
print(json.dumps(report),flush=True)
