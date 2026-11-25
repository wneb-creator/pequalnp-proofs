from pathlib import Path
import subprocess,resource,time,json,os,signal,sys
job=Path('/tmp/oec/pequalnp-pilot-79');mode=sys.argv[1];assert mode in ['elab','complex','mod97']
source={'elab':'CenteredTwoElab.lean','complex':'CenteredTwoChart.lean','mod97':'CenteredTwoChart97.lean'}[mode]
settings=json.loads((job/'lean-path-settings.json').read_text());allowed={'LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH'}
assert set(settings)==allowed
environment={k:v for k,v in settings.items() if isinstance(v,str)}
environment['PATH']=str(job/'elan/toolchains/leanprover--lean4---v4.36.0/bin')+':/usr/bin:/bin'
environment['LC_ALL']='C.UTF-8'
args=[str(job/'elan/toolchains/leanprover--lean4---v4.36.0/bin/lean'),'--threads=1','--memory=4096',str(job/source)]
limit=4*1024**3;start=time.monotonic();expired=False;over_memory=False;peak=0
logname='centered-two-direct4-'+mode
def limits():resource.setrlimit(resource.RLIMIT_CPU,(120,120))
def rss_tree(pid,seen=None):
 seen=set() if seen is None else seen
 if pid in seen:return 0
 seen.add(pid);base=Path('/proc')/str(pid);status=base/'status';rss=0;children=set()
 try:
  if status.is_file():
   for line in status.read_text().splitlines():
    if line.startswith('VmRSS:'):rss=int(line.split()[1])*1024
  task=base/'task'
  if task.is_dir():
   for thread in task.iterdir():
    childfile=thread/'children'
    if childfile.is_file():children.update(map(int,childfile.read_text().split()))
  for child in children:rss+=rss_tree(child,seen)
 except (FileNotFoundError,ProcessLookupError):pass
 return rss
with (job/(logname+'.log')).open('w') as log:
 proc=subprocess.Popen(args,cwd='/workspace/pequalnp-proofs/lean',env=environment,stdout=log,stderr=subprocess.STDOUT,preexec_fn=limits,start_new_session=True)
 pid=proc.pid
 (job/(logname+'.pid.json')).write_text(json.dumps({'pid':pid,'mode':mode}))
 while proc.poll() is None:
  peak=max(peak,rss_tree(pid));expired=time.monotonic()-start>120;over_memory=peak>limit
  if expired or over_memory:os.killpg(pid,signal.SIGKILL);break
  time.sleep(.1)
 code=proc.wait()
meta={'pid':pid,'mode':mode,'exit':code,'timeout':expired,'over_memory':over_memory,'peak_rss_bytes':peak,'seconds':time.monotonic()-start,'memory_limit_bytes':limit};(job/(logname+'-run.json')).write_text(json.dumps(meta,indent=2));print(json.dumps(meta),flush=True)
