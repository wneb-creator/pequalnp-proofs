import argparse,subprocess,time,json,hashlib,resource
from pathlib import Path
p=argparse.ArgumentParser(description='Bound an exact OpenF4 batch run and preserve all diagnostics.')
p.add_argument('input');p.add_argument('prefix');p.add_argument('--seconds',type=int,default=120)
p.add_argument('--memory-mib',type=int,default=4096)
a=p.parse_args();base=Path(__file__).parent;pref=Path(a.prefix);start=time.monotonic()
def limits():
 resource.setrlimit(resource.RLIMIT_CORE,(0,0))
 resource.setrlimit(resource.RLIMIT_AS,(a.memory_mib*1024*1024,a.memory_mib*1024*1024))
with pref.with_suffix('.log').open('w') as log:
 try:
  r=subprocess.run([str(base/'openf4_batch32'),a.input],stdout=log,stderr=subprocess.STDOUT,timeout=a.seconds,preexec_fn=limits)
  status='COMPLETED' if r.returncode==0 else 'UNKNOWN_ERROR';code=r.returncode
 except subprocess.TimeoutExpired:status='UNKNOWN_TIME_LIMIT';code=None
meta={'status':status,'returncode':code,'seconds':time.monotonic()-start,'limit_seconds':a.seconds,'memory_limit_mib':a.memory_mib,'input':a.input,'input_sha256':hashlib.sha256(Path(a.input).read_bytes()).hexdigest(),'binary_sha256':hashlib.sha256((base/'openf4_batch32').read_bytes()).hexdigest(),'selected_pairs_per_batch':32,'scope':'Exact finite-field calculation; not a characteristic-zero certificate.'}
pref.with_suffix('.run.json').write_text(json.dumps(meta,indent=2)+'\n');print(json.dumps(meta))
