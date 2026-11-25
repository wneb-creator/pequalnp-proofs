from pathlib import Path
import subprocess,resource,json,time
base=Path('/tmp/oec/pequalnp-pilot-78');job=base/'geometry_search/tracezero_Bzero_generic'
def limits():
 resource.setrlimit(resource.RLIMIT_AS,(256*2**20,256*2**20));resource.setrlimit(resource.RLIMIT_CPU,(60,65));resource.setrlimit(resource.RLIMIT_FSIZE,(16*2**20,16*2**20));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
env={'LD_LIBRARY_PATH':str(base/'numeric/singular/lib')+':'+str(base/'numeric/cas/lib'),'OMP_NUM_THREADS':'1','OPENBLAS_NUM_THREADS':'1'}
for name in ('identity','swap-pair','swap-cross','cycle'):
 start=time.monotonic()
 with (job/(name+'.stdout')).open('wb') as out,(job/(name+'.stderr')).open('wb') as err:
  try:
   p=subprocess.run([str(base/'numeric/singular/bin/Singular'),'--quiet','--no-tty','--no-rc','--no-shell','--cpus=1','--threads=1','--flint-threads=1',str(job/(name+'.sing'))],stdin=subprocess.DEVNULL,stdout=out,stderr=err,env=env,preexec_fn=limits,timeout=75);code=p.returncode
  except subprocess.TimeoutExpired:code='timeout'
 raw=(job/(name+'.stdout')).read_bytes();r={'name':name,'exit':code,'seconds':time.monotonic()-start,'memory_mib':256,'cpu_seconds':60,'completed':b'COMPLETED_EXACT_RUN' in raw,'scope':'ExactQ standard basis attempt; incomplete output gives no conclusion.'}
 (job/(name+'.result.json')).write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r),flush=True)
