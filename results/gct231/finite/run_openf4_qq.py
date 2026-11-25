import argparse,subprocess,resource,time,json
from pathlib import Path
parser=argparse.ArgumentParser(description='Run exact QQ OpenF4 with hard process time/memory boundaries and complete logs.')
parser.add_argument('input');parser.add_argument('prefix');parser.add_argument('--seconds',type=int,default=120);parser.add_argument('--memory-mib',type=int,default=2048);a=parser.parse_args()
base=Path(__file__).parent;prefix=Path(a.prefix)
def limits():
 memory=a.memory_mib*1024**2
 resource.setrlimit(resource.RLIMIT_AS,(memory,memory));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
start=time.monotonic()
with prefix.with_suffix('.log').open('w') as out:
 try:
  r=subprocess.run([str(base/'openf4_qq'),a.input],stdout=out,stderr=subprocess.STDOUT,preexec_fn=limits,timeout=a.seconds)
  result={'status':'COMPLETED' if r.returncode==0 else 'FAILED_NO_VERDICT','returncode':r.returncode}
 except subprocess.TimeoutExpired:result={'status':'UNKNOWN_TIME_LIMIT'}
result.update({'wall_seconds':time.monotonic()-start,'seconds_limit':a.seconds,'memory_mib_limit':a.memory_mib,'input':a.input,'characteristic':0})
prefix.with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result),flush=True)
