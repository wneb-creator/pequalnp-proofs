from pathlib import Path
import subprocess,resource,time,json,hashlib,os,sys
resource.setrlimit(resource.RLIMIT_CORE,(0,0))
job=Path('/tmp/oec/pequalnp-pilot-79');label=sys.argv[1];assert label in ['base','path','triangle','path-qq','triangle-qq'];seconds=int(sys.argv[2]);assert seconds<=90;stem='frame-gram-localized-'+label;source=job/(stem+'.msolve');digest=hashlib.sha256(source.read_bytes()).hexdigest();env={k:v for k,v in os.environ.items() if k in {'PATH','LANG','LC_ALL','TMPDIR'}};env.update(OMP_NUM_THREADS='1',OPENBLAS_NUM_THREADS='1')
def limits():
 resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(int(2.5*1024**3),int(2.5*1024**3)));resource.setrlimit(resource.RLIMIT_CPU,(seconds,seconds+1))
start=time.monotonic();status={}
with (job/(stem+'.log')).open('w') as log:
 p=subprocess.Popen(['python',str(job/('neogb-run-rational.py' if label.endswith('-qq') else 'neogb-run.py')),'-f',str(source),'-o',str(job/(stem+'-gb.json')),'-t','1','--info','2'],cwd='/workspace/pequalnp-proofs',env=env,stdout=log,stderr=subprocess.STDOUT,preexec_fn=limits)
 try:p.wait(timeout=seconds+5)
 except subprocess.TimeoutExpired:p.kill();p.wait();status['limit']='wall'
status.update(exit_code=p.returncode,seconds=time.monotonic()-start,source_sha256=digest,source_unchanged=hashlib.sha256(source.read_bytes()).hexdigest()==digest);assert status['source_unchanged'];result=job/(stem+'-gb.json')
if p.returncode==0:
 data=json.loads(result.read_text());status['basis_size']=len(data['basis']);status['unit_ideal']=any(len(q)==1 and q[0]['coefficient'] and not any(q[0]['exponents']) for q in data['basis'])
(job/(stem+'-status.json')).write_text(json.dumps(status,indent=2)+'\n');print(json.dumps(status),flush=True)
