from pathlib import Path
import datetime,hashlib,json,os,signal,subprocess,time
B=Path('/tmp/oec/pequalnp-pilot-21/search')
root=B/'disconnected-rup-0459';root.mkdir(exist_ok=False)
source=B/'lrat-rup-replay.py'
assert hashlib.sha256(source.read_bytes()).hexdigest()=='0f1aba1fe39efaed530fcbff6c0ef71ba0ba9a7ec8e5097c8ba7b26f63c10ab6'
argv=['python',str(source),'--cnf',str(B/'disconnected-five-supported/query.cnf'),'--proof',str(B/'disconnected-five-supported/query.lrat.gz'),'--outdir',str(root/'checked'),'--max-address-space-mib','1024']
started=time.monotonic();record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'argv':argv,'wall_budget_seconds':120,'nice':10,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'scope':'external RUP-only replay of restricted disconnected2+3 template, not Lean or full-gap proof'}
with (root/'checker.log').open('xb') as log:
 p=subprocess.Popen(argv,stdout=log,stderr=subprocess.STDOUT,preexec_fn=lambda:os.setpriority(os.PRIO_PROCESS,0,10))
 record['pid']=p.pid;(root/'launch.json').write_text(json.dumps(record,indent=2)+'\n')
 timedout=False
 try:code=p.wait(timeout=120)
 except subprocess.TimeoutExpired:
  timedout=True;p.terminate()
  try:code=p.wait(timeout=5)
  except subprocess.TimeoutExpired:p.kill();code=p.wait()
record.update({'exit_code':code,'wall_timeout':timedout,'elapsed_seconds':time.monotonic()-started,'status':'PASSED' if code==0 and not timedout else 'STOPPED_OR_FAILED'})
(root/'status.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record),flush=True)
