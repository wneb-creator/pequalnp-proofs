from pathlib import Path
import json,resource,subprocess,time,hashlib
base=Path('/tmp/oec/pequalnp-pilot-78');job=base/'geometry_search/tracezero_rankdrop';name='rank3-incidence-shifted-Q-slimgb'
source=(job/'rank3-incidence-shifted-Q.sing').read_text()
assert source.count('std(I)')==1
script=source.replace('std(I)','slimgb(I)').replace('print("BASIS");G;','print("BASIS");short=0;G;print("COMPLETED_EXACT_RUN");')
(job/(name+'.sing')).write_text(script)
def limit():
 resource.setrlimit(resource.RLIMIT_AS,(1536*2**20,1536*2**20));resource.setrlimit(resource.RLIMIT_CPU,(1800,1805));resource.setrlimit(resource.RLIMIT_FSIZE,(16*2**20,16*2**20));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
start=time.monotonic();env={'LD_LIBRARY_PATH':str(base/'numeric/singular/lib')+':'+str(base/'numeric/cas/lib'),'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1'}
timed_out=False
with (job/(name+'.stdout')).open('wb') as out,(job/(name+'.stderr')).open('wb') as err:
 p=subprocess.Popen([str(base/'numeric/singular/bin/Singular'),'--quiet','--no-tty','--no-rc','--no-shell','--cpus=1','--threads=1','--flint-threads=1',str(job/(name+'.sing'))],stdin=subprocess.DEVNULL,stdout=out,stderr=err,env=env,preexec_fn=limit)
 (job/(name+'.pid')).write_text(str(p.pid)+'\n')
 try:result=p.wait(timeout=1860)
 except subprocess.TimeoutExpired:
  timed_out=True;p.kill();p.wait();result='wall_timeout'
r={'name':name,'exit':result,'seconds':time.monotonic()-start,'memory_mib':1536,'cpu_limit_seconds':1800,'scope':'Guard-free necessary first-variation system for diagonal-rank-three candidates; not sufficient for a full flat. Timeout or memory termination gives no conclusion.'}
for ext in ('stdout','stderr'):
 path=job/(name+'.'+ext);raw=path.read_bytes();r[ext+'_sha256']=hashlib.sha256(raw).hexdigest();r[ext+'_bytes']=len(raw)
 if ext=='stdout':r['completed_marker_present']=b'COMPLETED_EXACT_RUN' in raw
 if raw:
  subprocess.run(['zstd','-q','-f',str(path),'-o',str(path)+'.zst'],check=True,stdin=subprocess.DEVNULL)
  check=subprocess.check_output(['zstd','-q','-d','-c',str(path)+'.zst']);assert hashlib.sha256(check).hexdigest()==r[ext+'_sha256'];path.unlink()
r['conclusion']='Completed; inspect exact basis and independently certify it before drawing a mathematical conclusion.' if r['completed_marker_present'] else 'INCONCLUSIVE'
(job/(name+'.result.json')).write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r),flush=True)
