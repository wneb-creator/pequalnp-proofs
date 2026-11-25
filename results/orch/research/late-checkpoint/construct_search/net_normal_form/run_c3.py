from pathlib import Path
import subprocess,resource,json,time,sys
p=Path('/tmp/oec/pequalnp-pilot-78/numeric');job=Path('/tmp/oec/pequalnp-pilot-78/construct_search/net_normal_form');tag=sys.argv[1];stem='c3-'+tag

def limit():
 resource.setrlimit(resource.RLIMIT_AS,(512*2**20,512*2**20));resource.setrlimit(resource.RLIMIT_CPU,(120,123));resource.setrlimit(resource.RLIMIT_FSIZE,(2*2**20,2*2**20));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
start=time.monotonic();before=resource.getrusage(resource.RUSAGE_CHILDREN)
with (job/(stem+'.stdout')).open('w') as out,(job/(stem+'.stderr')).open('w') as err:
 try:
  proc=subprocess.run([str(p/'singular/bin/Singular'),'--quiet','--no-tty','--no-rc','--no-shell','--cpus=1','--threads=1','--flint-threads=1',str(job/(stem+'.sing'))],stdin=subprocess.DEVNULL,stdout=out,stderr=err,env={'LD_LIBRARY_PATH':str(p/'singular/lib')+':'+str(p/'cas/lib')},preexec_fn=limit,timeout=140)
  exitcode=proc.returncode
 except subprocess.TimeoutExpired:exitcode='timeout'
after=resource.getrusage(resource.RUSAGE_CHILDREN);r={'tag':tag,'exit':exitcode,'wall_seconds':time.monotonic()-start,'cpu_seconds':after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime,'max_rss_kib':after.ru_maxrss,'stdout_bytes':(job/(stem+'.stdout')).stat().st_size,'stderr_bytes':(job/(stem+'.stderr')).stat().st_size};(job/(stem+'.result.json')).write_text(json.dumps(r,indent=2));print(json.dumps(r),flush=True)
