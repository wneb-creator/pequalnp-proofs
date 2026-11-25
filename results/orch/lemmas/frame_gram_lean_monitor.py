from pathlib import Path
import subprocess,time,psutil,os,signal,json,sys
source=Path(sys.argv[1]);stem=sys.argv[2];job=Path('/tmp/oec/pequalnp-pilot-79');start=time.monotonic();peak=0;reason=None
with (job/(stem+'.log')).open('w') as log:
 p=subprocess.Popen(['lake','env','lean',str(source)],cwd='/workspace/pequalnp-proofs/lean',stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
 while p.poll() is None:
  try:
   root=psutil.Process(p.pid);rss=sum(q.memory_info().rss for q in [root,*root.children(recursive=True)] if q.is_running());peak=max(peak,rss)
  except (psutil.NoSuchProcess,psutil.AccessDenied):rss=0
  if rss>2.6*1024**3:reason='rss_limit'
  elif time.monotonic()-start>90:reason='time_limit'
  if reason:
   os.killpg(p.pid,signal.SIGKILL);p.wait();break
  time.sleep(0.5)
 result={'source':str(source),'exit_code':p.wait(),'seconds':time.monotonic()-start,'peak_rss_bytes':peak,'reason':reason}
(job/(stem+'.status.json')).write_text(json.dumps(result,indent=2));print(json.dumps(result))
