from pathlib import Path
import subprocess,resource,json,time,sys
base=Path('/tmp/oec/pequalnp-pilot-78');job=base/'construct_search';char=int(sys.argv[1]) if len(sys.argv)>1 else 101;budget=int(sys.argv[2]) if len(sys.argv)>2 else 60;stem=f'tracezero-hadamard-{char}'
def limits():
 resource.setrlimit(resource.RLIMIT_AS,(512*2**20,512*2**20));resource.setrlimit(resource.RLIMIT_CPU,(budget,budget+5));resource.setrlimit(resource.RLIMIT_FSIZE,(2*2**20,2*2**20));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
start=time.monotonic()
with (job/f'{stem}.stdout').open('w') as out,(job/f'{stem}.stderr').open('w') as err:
 try:
  p=subprocess.run([str(base/'numeric/singular/bin/Singular'),'--quiet','--no-tty','--no-rc','--no-shell','--cpus=1','--threads=1','--flint-threads=1',str(job/f'{stem}.sing')],stdin=subprocess.DEVNULL,stdout=out,stderr=err,env={'LD_LIBRARY_PATH':str(base/'numeric/singular/lib')+':'+str(base/'numeric/cas/lib'),'OMP_NUM_THREADS':'1','OPENBLAS_NUM_THREADS':'1'},preexec_fn=limits,timeout=budget+20);code=p.returncode
 except subprocess.TimeoutExpired:code='wall_timeout'
record={'characteristic':char,'cpu_budget':budget,'memory_mib':512,'wall_seconds':time.monotonic()-start,'exit':code};(job/f'{stem}.result.json').write_text(json.dumps(record)+'\n');print(json.dumps(record),flush=True)
