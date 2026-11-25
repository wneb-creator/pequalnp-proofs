from pathlib import Path
import subprocess,resource,time,json,os,sys,signal,hashlib
job=Path('/tmp/oec/pequalnp-pilot-79');seed=int(sys.argv[1]);nodes=int(sys.argv[2]);duration=float(sys.argv[3]) if len(sys.argv)>3 else 112
assert nodes==63 or 64<=nodes<=140
assert 0<duration<=112
prefix=f'meta3773-cgp-{seed}-{nodes}'
datafile=job/(sys.argv[5] if len(sys.argv)>5 else 'meta3773-synthesis-data.txt');assert datafile.resolve().parent==job
source_before=hashlib.sha256((job/'meta3773_cgp.cpp').read_bytes()).hexdigest()
args=[str(job/'meta3773_cgp'),str(datafile),str(seed),str(duration),str(nodes),str(job/(prefix+'-best.json'))]
if len(sys.argv)>4:
 warm=job/sys.argv[4];assert warm.resolve().parent==job;args.append(str(warm))
resource.setrlimit(resource.RLIMIT_CORE,(0,0))
def limits():
 resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(118,119))
start=time.monotonic();timeout=False;peak=0
with (job/(prefix+'.log')).open('w')as log:
 p=subprocess.Popen(args,cwd=str(job),env={'PATH':'/usr/local/bin:/usr/bin:/bin','LC_ALL':'C'},stdout=log,stderr=subprocess.STDOUT,preexec_fn=limits,start_new_session=True)
 while p.poll() is None:
  try:
   for line in(Path('/proc')/str(p.pid)/'status').read_text().splitlines():
    if line.startswith('VmRSS:'):peak=max(peak,int(line.split()[1])*1024)
  except FileNotFoundError:pass
  if time.monotonic()-start>120:timeout=True;os.killpg(p.pid,signal.SIGKILL);break
  time.sleep(.1)
 code=p.wait()
meta={'seed':seed,'genotype':nodes,'data':datafile.name,'data_sha':hashlib.sha256(datafile.read_bytes()).hexdigest(),'source_sha_before':source_before,'binary_sha':hashlib.sha256((job/'meta3773_cgp').read_bytes()).hexdigest(),'warm_seed':sys.argv[4] if len(sys.argv)>4 else None,'exit':code,'seconds':time.monotonic()-start,'timeout':timeout,'peak_rss_bytes':peak,'source_sha':hashlib.sha256((job/'meta3773_cgp.cpp').read_bytes()).hexdigest()}
assert meta['source_sha']==source_before
(job/(prefix+'-status.json')).write_text(json.dumps(meta,indent=2)+'\n');print(json.dumps(meta))
