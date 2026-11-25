from pathlib import Path
import subprocess,resource,time,sys,json
job=Path('/tmp/oec/pequalnp-pilot-79');index=int(sys.argv[1]);assert 0<=index<4
name='centered-two-coordinate-'+str(index)+'-rational'
args=['python3',str(job/'neogb-run-rational.py'),'-f',str(job/(name+'.msolve')),'-o',str(job/(name+'-basis.json')),'-t','1','--info','2','--max-pairs','256','--la','2']
def limits():
 resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(120,120))
start=time.monotonic();expired=False
with (job/(name+'-f4.log')).open('w') as log:
 proc=subprocess.Popen(args,stdout=log,stderr=subprocess.STDOUT,preexec_fn=limits)
 while proc.poll() is None:
  if time.monotonic()-start>120:expired=True;proc.kill();break
  time.sleep(0.5)
 code=proc.wait()
meta={'chart':index,'exit':code,'timeout':expired,'seconds':time.monotonic()-start,'memory_limit_bytes':1024**3,'classification':'CAS computation; not Lean checked'}
(job/(name+'-run.json')).write_text(json.dumps(meta,indent=2)+'\n');print(json.dumps(meta),flush=True)
