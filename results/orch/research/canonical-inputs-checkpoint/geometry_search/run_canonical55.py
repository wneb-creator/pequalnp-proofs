from pathlib import Path
import datetime,hashlib,json,resource,subprocess,time
base=Path('/tmp/oec/pequalnp-pilot-78')
job=base/'geometry_search/canonical55'
name='canonical55-modGB';source=job/(name+'.sing')
def limit():
    resource.setrlimit(resource.RLIMIT_AS,(1536*2**20,1536*2**20))
    resource.setrlimit(resource.RLIMIT_CPU,(1200,1205))
    resource.setrlimit(resource.RLIMIT_FSIZE,(16*2**20,16*2**20))
    resource.setrlimit(resource.RLIMIT_CORE,(0,0))
start=time.monotonic();utc=datetime.datetime.now(datetime.timezone.utc).isoformat()
env={'LD_LIBRARY_PATH':str(base/'numeric/singular/lib')+':'+str(base/'numeric/cas/lib'),'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1'}
with (job/(name+'.stdout')).open('wb') as out,(job/(name+'.stderr')).open('wb') as err:
    p=subprocess.Popen([str(base/'numeric/singular/bin/Singular'),'--quiet','--no-tty','--no-rc','--no-shell','--cpus=1','--threads=1','--flint-threads=1',str(source)],stdin=subprocess.DEVNULL,stdout=out,stderr=err,env=env,preexec_fn=limit)
    (job/(name+'.pid')).write_text(str(p.pid)+'\n')
    try:code=p.wait(timeout=1500)
    except subprocess.TimeoutExpired:p.kill();p.wait();code='wall_timeout'
result={'started_utc':utc,'exit':code,'seconds':time.monotonic()-start,
        'memory_mib':1536,'cpu_limit_seconds':1200,'wall_limit_seconds':1500,
        'input_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
        'scope':'Modular55 candidate needs exact rational identity and independent verification. Failure/timeout is inconclusive.'}
for ext in ['stdout','stderr']:
    p=job/(name+'.'+ext);raw=p.read_bytes()
    result[ext+'_sha256']=hashlib.sha256(raw).hexdigest();result[ext+'_bytes']=len(raw)
    if ext=='stdout':
        for label in ['MODULAR_BASIS_COMPLETE','EXACT_LIFT_COMPLETE','COMPLETED_EXACT_RUN']:
            result[label.lower()]=label.encode() in raw
    if raw:
        subprocess.run(['zstd','-q','-f',str(p),'-o',str(p)+'.zst'],stdin=subprocess.DEVNULL,check=True)
        check=subprocess.check_output(['zstd','-q','-d','-c',str(p)+'.zst'])
        assert hashlib.sha256(check).hexdigest()==result[ext+'_sha256'];p.unlink()
result['conclusion']='Await independent exact certificate audit' if result['exact_lift_complete'] else 'INCONCLUSIVE'
(job/(name+'.result.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result),flush=True)
