import subprocess,time,json,os,signal,resource,psutil,sys
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-75/gct231/fresh');source=sys.argv[1];tag=sys.argv[2];start=time.monotonic();peak=0;reason=None;rootdir=Path('/workspace/pequalnp-proofs/lean');packages=['Cli','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','mathlib'];tool='/tmp/oec/pequalnp-pilot-75/lean-tools/lean-4.36.0-linux';env={};env['LEAN_PATH']=':'.join([str(rootdir/'.lake/packages'/n/'.lake/build/lib/lean') for n in packages]+[str(rootdir/'.lake/build/lib/lean'),tool+'/lib/lean'])
with (base/(tag+'.log')).open('w') as f:
 p=subprocess.Popen([tool+'/bin/lean','-j1',str(base/source)],stdout=f,stderr=subprocess.STDOUT,start_new_session=True,env=env)
 while p.poll() is None:
  try:
   proc=psutil.Process(p.pid);peak=max(peak,sum(x.memory_info().rss for x in [proc]+proc.children(recursive=True) if x.is_running())//1024)
  except psutil.Error:pass
  if peak>4*1024**2:reason='RSS_LIMIT';os.killpg(p.pid,signal.SIGKILL);break
  if time.monotonic()-start>100:reason='TIME_LIMIT';os.killpg(p.pid,signal.SIGKILL);break
  time.sleep(.2)
 code=p.wait()
record={'exit_code':code,'seconds':time.monotonic()-start,'peak_rss_kib':peak,'resource_rss_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,'reason':reason};(base/(tag+'.json')).write_text(json.dumps(record,indent=2));print(record)
