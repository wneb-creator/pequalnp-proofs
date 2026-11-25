from pathlib import Path
import resource,subprocess,time,json,sys
job=Path('/tmp/oec/pequalnp-pilot-79');chart=int(sys.argv[1]);degree=int(sys.argv[2]);prime=int(sys.argv[3]) if len(sys.argv)>3 else 1000000007
base='centered-two-macaulay-'+str(chart)+'-d'+str(degree);name=base+'-p'+str(prime)
def limits():resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(120,120))
start=time.monotonic();expired=False
with (job/(name+'.log')).open('w') as log:
 proc=subprocess.Popen([str(job/'macaulay_witness'),str(job/(base+'.matrix')),str(job/(name+'-witness.json')),str(prime)],stdout=log,stderr=subprocess.STDOUT,preexec_fn=limits)
 while proc.poll() is None:
  if time.monotonic()-start>120:expired=True;proc.kill();break
  time.sleep(.1)
 code=proc.wait()
meta={'classification':'Modular CAS certificate search, not Lean checked','chart':chart,'degree':degree,'prime':prime,'exit':code,'timeout':expired,'seconds':time.monotonic()-start};(job/(name+'-run.json')).write_text(json.dumps(meta)+'\n');print(json.dumps(meta),flush=True)
