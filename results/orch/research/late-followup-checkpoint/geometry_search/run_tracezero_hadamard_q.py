from pathlib import Path
import json,resource,subprocess,time,hashlib

base=Path('/tmp/oec/pequalnp-pilot-78');job=base/'geometry_search/tracezero_hadamard_q';name='hadamard-rank2-Q-std'
source=(base/'construct_search/tracezero-hadamard-0.sing').read_text()
script=source.replace('option(redSB);','option(redSB);\noption(prot);').replace('print("BASIS");G;','int unitIndex=0;int ii;for(ii=1;ii<=size(G);ii++){if(G[ii]!=0 && deg(G[ii])==0){unitIndex=ii;break;}}\nprint("UNIT_IDEAL");(unitIndex!=0);\nprint("BASIS");short=0;G;')
(job/(name+'.sing')).write_text(script)
def limit():
 resource.setrlimit(resource.RLIMIT_AS,(1536*2**20,1536*2**20));resource.setrlimit(resource.RLIMIT_CPU,(1800,1805));resource.setrlimit(resource.RLIMIT_FSIZE,(16*2**20,16*2**20));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
start=time.monotonic()
env={'LD_LIBRARY_PATH':str(base/'numeric/singular/lib')+':'+str(base/'numeric/cas/lib'),'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1'}
with (job/(name+'.stdout')).open('wb') as out,(job/(name+'.stderr')).open('wb') as err:
 try:
  p=subprocess.run([str(base/'numeric/singular/bin/Singular'),'--quiet','--no-tty','--no-rc','--no-shell','--cpus=1','--threads=1','--flint-threads=1',str(job/(name+'.sing'))],stdin=subprocess.DEVNULL,stdout=out,stderr=err,env=env,preexec_fn=limit,timeout=1860)
  result=p.returncode
 except subprocess.TimeoutExpired:result='wall_timeout'
r={'name':name,'exit':result,'seconds':time.monotonic()-start,'memory_mib':1536,'cpu_limit_seconds':1800,'scope':'Exact rational standard basis attempt in independently audited Hadamard coordinates; timeout or memory termination gives no conclusion'}
for ext in ('stdout','stderr'):
 path=job/(name+'.'+ext);r[ext+'_sha256']=hashlib.sha256(path.read_bytes()).hexdigest();r[ext+'_bytes']=path.stat().st_size
 if path.stat().st_size>0:
  subprocess.run(['zstd','-q','-f',str(path),'-o',str(path)+'.zst'],check=True,stdin=subprocess.DEVNULL)
  raw=subprocess.check_output(['zstd','-q','-d','-c',str(path)+'.zst'])
  assert hashlib.sha256(raw).hexdigest()==r[ext+'_sha256'];path.unlink()
(job/(name+'.result.json')).write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r),flush=True)
