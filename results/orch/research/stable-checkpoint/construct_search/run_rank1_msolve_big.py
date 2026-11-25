from pathlib import Path
import subprocess,resource,json,time
base=Path('/tmp/oec/pequalnp-pilot-78');job=base/'construct_search';stem='rank1-incident-opposite-msolve-Q1280'
def limits():
 resource.setrlimit(resource.RLIMIT_AS,(1280*2**20,1280*2**20));resource.setrlimit(resource.RLIMIT_CPU,(1200,1205));resource.setrlimit(resource.RLIMIT_FSIZE,(2*2**20,2*2**20));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
start=time.monotonic()
with (job/f'{stem}.stdout').open('w') as out,(job/f'{stem}.stderr').open('w') as err:
 try:
  p=subprocess.run([str(base/'numeric/cas-avx2/bin/msolve'),'-f',str(job/'rank1-incident-opposite-nonzero-Q.ms'),'-o',str(job/f'{stem}.out'),'-t','1','-v','2','-l','2','-q','0','-m','512','-P','1','-s','12'],stdin=subprocess.DEVNULL,stdout=out,stderr=err,env={'LD_LIBRARY_PATH':str(base/'numeric/cas-avx2/lib')+':'+str(base/'numeric/cas/lib'),'OMP_NUM_THREADS':'1','OPENBLAS_NUM_THREADS':'1'},preexec_fn=limits,timeout=1300);code=p.returncode
 except subprocess.TimeoutExpired:code='wall_timeout'
record={'engine':'msolve_AVX2_exact_sparse_Q','cpu_budget':1200,'memory_mib':1280,'wall_seconds':time.monotonic()-start,'exit':code,'scope':'Saturated opposite-edge nonzero branch only'};(job/f'{stem}.result.json').write_text(json.dumps(record)+'\n');print(json.dumps(record),flush=True)
