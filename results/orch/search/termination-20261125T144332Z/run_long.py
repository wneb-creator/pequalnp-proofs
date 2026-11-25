import sys,subprocess,json,hashlib
from datetime import datetime,timezone
from pathlib import Path
solver,cnf,log,status=sys.argv[1:]
args=[solver,'-t','3600','--unsat','--seed=302',cnf]
record={'started_at':datetime.now(timezone.utc).isoformat(),'command':args,'cnf_sha256':hashlib.sha256(Path(cnf).read_bytes()).hexdigest(),'status':'running'}
with Path(log).open('w') as f:
 p=subprocess.Popen(args,stdout=f,stderr=subprocess.STDOUT)
 record['pid']=p.pid
 Path(status).write_text(json.dumps(record,indent=2)+'\n')
 result=p.wait()
record['ended_at']=datetime.now(timezone.utc).isoformat()
record['status']='completed'
record['exit_code']=result
record['log_sha256']=hashlib.sha256(Path(log).read_bytes()).hexdigest()
Path(status).write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
