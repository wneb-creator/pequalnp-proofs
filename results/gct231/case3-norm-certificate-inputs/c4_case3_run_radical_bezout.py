from pathlib import Path
import json,resource,subprocess,time
p=Path(__file__).parent
def limit():
 resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
 resource.setrlimit(resource.RLIMIT_CORE,(0,0))
start=time.monotonic()
with (p/'c4-case3-radical-bezout.log').open('w') as out:
 try:
  q=subprocess.run([str(p/'univariate_bezout'),str(p/'c4-case3-radical-bezout.in'),str(p/'c4-case3-radical-bezout.out')],stdout=out,stderr=subprocess.STDOUT,timeout=120,preexec_fn=limit)
  status='PASS' if q.returncode==0 else 'FAIL';code=q.returncode
 except subprocess.TimeoutExpired:
  status='UNKNOWN_TIME_LIMIT';code=None
r={'status':status,'returncode':code,'wall_seconds':time.monotonic()-start,'seconds_limit':120,'memory_mib_limit':512}
(p/'c4-case3-radical-bezout-run.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r),flush=True)
