from pathlib import Path
import subprocess,resource,json,time,sys
job=Path('/tmp/oec/pequalnp-pilot-78/construct_search/net_normal_form');prime=int(sys.argv[1]);stem='tracezero-f'+str(prime)
def limit():
 resource.setrlimit(resource.RLIMIT_AS,(256*2**20,256*2**20));resource.setrlimit(resource.RLIMIT_CPU,(900,903));resource.setrlimit(resource.RLIMIT_FSIZE,(2*2**20,2*2**20));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
start=time.monotonic();before=resource.getrusage(resource.RUSAGE_CHILDREN)
with (job/(stem+'.stdout')).open('w') as out,(job/(stem+'.stderr')).open('w') as err:
 try:
  proc=subprocess.run([str(job/'tracezero_census'),str(prime),str(job/stem)],stdin=subprocess.DEVNULL,stdout=out,stderr=err,env={'OMP_NUM_THREADS':'4','OMP_STACKSIZE':'1M'},preexec_fn=limit,timeout=420)
  code=proc.returncode
 except subprocess.TimeoutExpired:code='timeout'
after=resource.getrusage(resource.RUSAGE_CHILDREN);r={'prime':prime,'exit':code,'wall_seconds':time.monotonic()-start,'cpu_seconds':after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime,'max_rss_kib':after.ru_maxrss,'stdout_bytes':(job/(stem+'.stdout')).stat().st_size,'stderr_bytes':(job/(stem+'.stderr')).stat().st_size};(job/(stem+'.result.json')).write_text(json.dumps(r,indent=2));print(json.dumps(r),flush=True)
