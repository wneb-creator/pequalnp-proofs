from pathlib import Path
import subprocess,resource,json,time
base=Path('/tmp/oec/pequalnp-pilot-78');job=base/'construct_search';stem='rank1-incident-opposite-lift-Q'
def limits():
 resource.setrlimit(resource.RLIMIT_AS,(1280*2**20,1280*2**20));resource.setrlimit(resource.RLIMIT_CPU,(1200,1205));resource.setrlimit(resource.RLIMIT_FSIZE,(64*2**20,64*2**20));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
start=time.monotonic()
with (job/f'{stem}.stdout').open('w') as out,(job/f'{stem}.stderr').open('w') as err:
 try:
  p=subprocess.run([str(base/'numeric/singular/bin/Singular'),'--quiet','--no-tty','--no-rc','--no-shell','--cpus=1','--threads=1','--flint-threads=1',str(job/f'{stem}.sing')],stdin=subprocess.DEVNULL,stdout=out,stderr=err,env={'LD_LIBRARY_PATH':str(base/'numeric/singular/lib')+':'+str(base/'numeric/cas/lib'),'OMP_NUM_THREADS':'1','OPENBLAS_NUM_THREADS':'1'},preexec_fn=limits,timeout=1300);code=p.returncode
 except subprocess.TimeoutExpired:code='wall_timeout'
record={'engine':'Singular_direct_modular_lift','cpu_budget':1200,'memory_mib':1280,'wall_seconds':time.monotonic()-start,'exit':code,'scope':'Exact identity required before interpreting as a proof'};(job/f'{stem}.result.json').write_text(json.dumps(record)+'\n');print(json.dumps(record),flush=True)
