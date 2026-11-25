import argparse
import json
from pathlib import Path
import resource
import subprocess
import time

p = argparse.ArgumentParser(description='Run isolated exact QQ trace under hard time and memory bounds.')
p.add_argument('input')
p.add_argument('prefix')
p.add_argument('--seconds',type=int,default=30)
p.add_argument('--memory-mib',type=int,default=2048)
p.add_argument('--batch',type=int,default=32)
a = p.parse_args()
base = Path(__file__).parent
prefix = Path(a.prefix)
def limits():
    memory = a.memory_mib*1024**2
    resource.setrlimit(resource.RLIMIT_AS,(memory,memory))
    resource.setrlimit(resource.RLIMIT_CORE,(0,0))
start = time.monotonic()
with prefix.with_suffix('.log').open('w') as out:
    try:
        result = subprocess.run([str(base/'openf4_qq_trace'),a.input,str(prefix.with_suffix('.trace')),str(a.batch)],
                                stdout=out,stderr=subprocess.STDOUT,preexec_fn=limits,timeout=a.seconds)
        status = {'status':'COMPLETED' if result.returncode == 0 else 'FAILED_NO_VERDICT',
                  'returncode':result.returncode}
    except subprocess.TimeoutExpired:
        status = {'status':'UNKNOWN_TIME_LIMIT'}
status.update({'wall_seconds':time.monotonic()-start,'seconds_limit':a.seconds,
               'memory_mib_limit':a.memory_mib,'batch_limit':a.batch,'input':a.input,'characteristic':0})
prefix.with_suffix('.run.json').write_text(json.dumps(status,indent=2)+'\n')
print(json.dumps(status),flush=True)
