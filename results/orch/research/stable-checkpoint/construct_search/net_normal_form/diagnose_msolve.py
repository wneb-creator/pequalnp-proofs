from pathlib import Path
import subprocess,resource,json,time,sys,hashlib
ROOT=Path('/tmp/oec/pequalnp-pilot-78');OUT=ROOT/'construct_search/net_normal_form';architecture,mode,cap=sys.argv[1],sys.argv[2],int(sys.argv[3]);stem=f'msolve-diagnosis-{architecture}-{mode}-{cap}'+('-trace' if len(sys.argv)>4 else '')
exe=ROOT/('numeric/cas-avx2/bin/msolve' if architecture=='avx2' else 'numeric/cas/bin/msolve');source=ROOT/'construct_search/msolve-smoke.ms'
lib=str(ROOT/'numeric/cas/lib')
if architecture=='avx2':lib=str(ROOT/'numeric/cas-avx2/lib')+':'+lib
options={}
if mode=='fixed':options['env']={'LD_LIBRARY_PATH':lib,'OMP_NUM_THREADS':'1','OPENBLAS_NUM_THREADS':'1'}
# In inherited mode env is deliberately omitted; no environment is inspected or copied.
def limits():
 resource.setrlimit(resource.RLIMIT_AS,(cap*2**20,cap*2**20));resource.setrlimit(resource.RLIMIT_CPU,(20,22));resource.setrlimit(resource.RLIMIT_FSIZE,(2*2**20,2*2**20));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
start=time.monotonic();before=resource.getrusage(resource.RUSAGE_CHILDREN)
with (OUT/(stem+'.stdout')).open('w') as stdout,(OUT/(stem+'.stderr')).open('w') as stderr:
 try:
  child=subprocess.run((['/usr/bin/strace','-f','-e','trace=mmap,munmap,mremap,brk','-o',str(OUT/(stem+'.memory-trace'))] if len(sys.argv)>4 else [])+[str(exe),'-f',str(source),'-o',str(OUT/(stem+'.out')),'-t','1','-v','2','-l','2','-q','0','-m','512','-P','1','-s','12'],stdin=subprocess.DEVNULL,stdout=stdout,stderr=stderr,preexec_fn=limits,timeout=25,**options);code=child.returncode
 except subprocess.TimeoutExpired:code='wall_timeout'
after=resource.getrusage(resource.RUSAGE_CHILDREN);report={'architecture':architecture,'environment_mode':mode,'address_space_mib':cap,'exit':code,'wall_seconds':time.monotonic()-start,'cpu_seconds':after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime,'max_rss_kib':after.ru_maxrss,'stdout_bytes':(OUT/(stem+'.stdout')).stat().st_size,'stderr_bytes':(OUT/(stem+'.stderr')).stat().st_size,'input_sha256':hashlib.sha256(source.read_bytes()).hexdigest()}
(OUT/(stem+'.json')).write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)
