from pathlib import Path
import subprocess,resource,time,sys,json
job=Path('/tmp/oec/pequalnp-pilot-79');mode=sys.argv[1]
assert mode in ['mod97','rational']
variant=sys.argv[2] if len(sys.argv)>2 else 'natural'
assert variant in ['natural','eliminated']
base='centered-two-'+variant+'-'+mode
la1=len(sys.argv)>3 and sys.argv[3]=='la1'
name=base+('-la1' if la1 else '')
args=['python3',str(job/('neogb-run.py' if mode=='mod97' else 'neogb-run-rational.py')),'-f',str(job/(base+'.msolve')),'-o',str(job/(name+'-basis.json')),'-t','1','--info','2','--max-pairs',('128' if la1 else '256'),'--la',('1' if la1 else '2')]
def limits():
 resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3))
 resource.setrlimit(resource.RLIMIT_CPU,(120,120))
start=time.monotonic();expired=False
with (job/(name+'-f4.log')).open('w') as log:
 proc=subprocess.Popen(args,stdout=log,stderr=subprocess.STDOUT,preexec_fn=limits)
 while proc.poll() is None:
  if time.monotonic()-start>120:
   expired=True;proc.kill();break
  time.sleep(0.5)
 code=proc.wait()
meta={'mode':mode,'exit':code,'timeout':expired,'seconds':time.monotonic()-start,'memory_limit_bytes':1024**3,'classification':'CAS computation; not Lean checked'}
(job/(name+'-run.json')).write_text(json.dumps(meta,indent=2)+'\n');print(json.dumps(meta),flush=True)
