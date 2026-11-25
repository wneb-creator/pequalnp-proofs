from pathlib import Path
import subprocess,os,resource,time,json,hashlib,datetime
out=Path('/tmp/oec/pequalnp-pilot-87/proof_structure/petersen-and5-long')
solver=Path('/tmp/oec/pequalnp-pilot-87/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical')
cmd=[str(solver),'-t','900','--seed=0','--binary=true','-w',str(out/'model.out'),str(out/'problem.cnf'),str(out/'proof.drat')]
def limits():
 os.sched_setaffinity(0,{3})
 resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3))
 resource.setrlimit(resource.RLIMIT_FSIZE,(1024**3,1024**3))
start=time.monotonic();utc=datetime.datetime.now(datetime.timezone.utc).isoformat()
meta={'argv':cmd,'start_utc':utc,'cpu_affinity':[3],'address_limit_bytes':1024**3,'proof_file_limit_bytes':1024**3,'solver_sha256':hashlib.sha256(solver.read_bytes()).hexdigest(),'solver_version':'2.1.2','scope':'Bounded computational search; UNKNOWN is not exclusion. DRAT trace is preserved even if incomplete.'}
(out/'launch.json').write_text(json.dumps(meta,indent=2)+'\n')
with (out/'solver.stdout-stderr.txt').open('wb') as log:
 p=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,preexec_fn=limits)
 (out/'pid.json').write_text(json.dumps({'launcher':os.getpid(),'solver':p.pid})+'\n')
 try:code=p.wait(timeout=915)
 except subprocess.TimeoutExpired:
  p.terminate()
  try:code=p.wait(timeout=5)
  except subprocess.TimeoutExpired:p.kill();code=p.wait()
meta.update({'end_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'wall_seconds':time.monotonic()-start,'returncode':code,'maxrss_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,'status':{10:'SAT',20:'UNSAT',0:'UNKNOWN'}.get(code,'PROCESS_FAILURE'),'proof_bytes':(out/'proof.drat').stat().st_size if (out/'proof.drat').exists() else 0})
(out/'status.json').write_text(json.dumps(meta,indent=2)+'\n');print(json.dumps(meta,indent=2))
