from pathlib import Path
import argparse,resource,subprocess,time,json,hashlib
B=Path('/tmp/oec/pequalnp-pilot-78')
LEAN=B/'elan/toolchains/leanprover--lean4---v4.36.0/bin/lean'
ap=argparse.ArgumentParser(description='Run direct Lean inside an already established lake env; apply resource caps only to the Lean child.')
ap.add_argument('source');ap.add_argument('--cpu',type=int,default=30);ap.add_argument('--wall',type=int,default=60);ap.add_argument('--tag',required=True)
a=ap.parse_args();src=Path(a.source).resolve();out=B/'grind-review'/a.tag
assert src.is_relative_to(B) and LEAN.is_file()
def limits():
 resource.setrlimit(resource.RLIMIT_AS,(1024*2**20,1024*2**20));resource.setrlimit(resource.RLIMIT_CPU,(a.cpu,a.cpu+5));resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_FSIZE,(8*2**20,8*2**20))
start=time.monotonic()
with out.with_suffix('.stdout').open('w') as stdout,out.with_suffix('.stderr').open('w') as stderr:
 try:r=subprocess.run([str(LEAN),'-j1','-o',str(out.with_suffix('.olean')),str(src)],stdout=stdout,stderr=stderr,preexec_fn=limits,timeout=a.wall);code=r.returncode
 except subprocess.TimeoutExpired:code='wall_timeout'
u=resource.getrusage(resource.RUSAGE_CHILDREN)
report={'exit':code,'source':str(src),'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'wall_seconds':time.monotonic()-start,'cpu_seconds':u.ru_utime+u.ru_stime,'max_rss_kib':u.ru_maxrss,'address_cap_bytes':1024*2**20,'cpu_cap':a.cpu,'wall_cap':a.wall,'threads':1,'scope':'Normal kernel-checked Lean compilation with direct1GiB-capped Lean child after supported lake env initialization; no environment dump, checker modification or Mathlib source build.'}
out.with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)
