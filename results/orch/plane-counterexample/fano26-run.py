from pathlib import Path
from datetime import datetime,timezone
import subprocess,json
start=datetime.now(timezone.utc).isoformat()
Path('fano26-solve.started.json').write_text(json.dumps({'started':start,'seconds':2700,'status':'running'},indent=2))
with Path('fano26-solve.stdout.txt').open('w') as out,Path('fano26-solve.stderr.txt').open('w') as err:
 r=subprocess.run(['./phase-fano','fano26-onehot.cnf','fano26-seed.txt','fano-rows.txt','2700'],stdout=out,stderr=err)
report={'started':start,'finished':datetime.now(timezone.utc).isoformat(),'returncode':r.returncode}
if r.returncode==10:
 with Path('fano26-decode.stdout.txt').open('w') as out,Path('fano26-decode.stderr.txt').open('w') as err:
  dec=subprocess.run(['python3','decode-fano.py','fano26-solve.stdout.txt','fano26-actual-model.json'],stdout=out,stderr=err)
 report['decoder_returncode']=dec.returncode
 if dec.returncode==0:
  data=json.loads(Path('fano26-actual-model.json').read_text())
  for key in ['actual_size','is_ao2','verified_rows','errors','not_read1_edges','candidate_refutation']:report[key]=data[key]
Path('fano26-solve.result.json').write_text(json.dumps(report,indent=2))
print(json.dumps(report),flush=True)
