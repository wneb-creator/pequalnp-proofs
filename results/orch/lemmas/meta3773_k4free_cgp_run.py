from pathlib import Path
import subprocess,resource,time,json,hashlib,os,sys
resource.setrlimit(resource.RLIMIT_CORE,(0,0));job=Path('/tmp/oec/pequalnp-pilot-79');seed=int(sys.argv[1]);seconds=int(sys.argv[2]);assert 0<seconds<=180;source=job/'meta3773_k4free_cgp.cpp';binary=job/'meta3773_k4free_cgp';digests={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [source,binary]};env={k:v for k,v in os.environ.items() if k in ['PATH','LANG','LC_ALL','TMPDIR']};stem='meta3773-k4free-cgp-'+str(seed)
def limits():
 resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(seconds+5,seconds+5))
start=time.monotonic()
with (job/(stem+'.log')).open('w') as log:
 try:p=subprocess.run([str(binary),str(seconds),str(seed)],cwd='/workspace/pequalnp-proofs',env=env,preexec_fn=limits,stdout=log,stderr=subprocess.STDOUT,timeout=seconds+10);code=p.returncode
 except subprocess.TimeoutExpired:code='wall_timeout'
assert all(hashlib.sha256((job/name).read_bytes()).hexdigest()==digest for name,digest in digests.items());result={'exit_code':code,'seconds':time.monotonic()-start,'bound_hashes':digests};(job/(stem+'-status.json')).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
