from pathlib import Path
from datetime import datetime,timezone
import subprocess,json
start=datetime.now(timezone.utc).isoformat()
Path('fano26-heuristic.started.json').write_text(json.dumps({'started':start,'seconds':1800,'status':'running'},indent=2))
with Path('fano26-heuristic.stdout.txt').open('w') as out,Path('fano26-heuristic.stderr.txt').open('w') as err:
 run=subprocess.run(['./search-fano','fano-rows.txt','fano-edges.txt','1800'],stdout=out,stderr=err)
report={'started':start,'finished':datetime.now(timezone.utc).isoformat(),'returncode':run.returncode}
if run.returncode==0:
 n,s,A=14,26,99
 p=lambda kd,j,a:(kd*(s+1)+j)*A+a+1
 gates=[list(map(int,t.split()))[1:] for t in Path('fano26-heuristic-witness.txt').read_text().splitlines()[1:]]
 truth={p(6,0,n+s-1)}
 for j,(op,a,b) in enumerate(gates):truth.update([p(0,j,op),p(1,j,a),p(2,j,b)])
 Path('fano26-heuristic-model.txt').write_text('v '+' '.join(map(str,sorted(truth)))+' 0\n')
 with Path('fano26-heuristic-decode.stdout.txt').open('w') as out,Path('fano26-heuristic-decode.stderr.txt').open('w') as err:
  dec=subprocess.run(['python3','decode-fano.py','fano26-heuristic-model.txt','fano26-heuristic-actual.json'],stdout=out,stderr=err)
 report['decoder_returncode']=dec.returncode
 if dec.returncode==0:
  data=json.loads(Path('fano26-heuristic-actual.json').read_text())
  for key in ['actual_size','is_ao2','verified_rows','errors','not_read1_edges','candidate_refutation']:report[key]=data[key]
Path('fano26-heuristic.result.json').write_text(json.dumps(report,indent=2))
print(json.dumps(report),flush=True)
