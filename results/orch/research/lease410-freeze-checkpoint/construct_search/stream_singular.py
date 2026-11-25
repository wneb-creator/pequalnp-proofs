from pathlib import Path
import argparse, datetime, gzip, hashlib, json, os, resource, shutil
import signal, subprocess, threading, time

parser=argparse.ArgumentParser()
parser.add_argument('--source',required=True)
parser.add_argument('--stem',required=True)
parser.add_argument('--memory-mib',type=int,default=2048)
parser.add_argument('--cpu-seconds',type=int,default=1200)
parser.add_argument('--wall-seconds',type=int,default=2400)
args=parser.parse_args()
base=Path('/tmp/oec/pequalnp-pilot-78');job=base/'construct_search'
source=Path(args.source).resolve();assert source.is_file()
assert source.is_relative_to(base) and '/' not in args.stem
stem=job/args.stem
def named(suffix):return Path(str(stem)+suffix)
def limits():
 resource.setrlimit(resource.RLIMIT_AS,(args.memory_mib*2**20,)*2)
 resource.setrlimit(resource.RLIMIT_CPU,(args.cpu_seconds,args.cpu_seconds+5))
 resource.setrlimit(resource.RLIMIT_FSIZE,(64*2**20,)*2)
 resource.setrlimit(resource.RLIMIT_CORE,(0,0))
ending=threading.Event();done=threading.Event();errors=[]
raw_hash=hashlib.sha256();counts={'raw_bytes':0};started=time.monotonic()
with named('.stderr').open('wb') as err,named('.progress.jsonl').open('w') as progress:
 def note(event,**kwargs):
  progress.write(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'event':event,**kwargs})+'\n');progress.flush()
 proc=subprocess.Popen([str(base/'numeric/singular/bin/Singular'),'--quiet','--no-tty','--no-rc','--no-shell','--cpus=1','--threads=1','--flint-threads=1',str(source)],stdin=subprocess.DEVNULL,stdout=subprocess.PIPE,stderr=err,env={'LD_LIBRARY_PATH':str(base/'numeric/singular/lib')+':'+str(base/'numeric/cas/lib'),'OMP_NUM_THREADS':'1','OPENBLAS_NUM_THREADS':'1'},preexec_fn=limits)
 note('started',pid=proc.pid,source_sha256=hashlib.sha256(source.read_bytes()).hexdigest())
 def capture():
  partial=b'';oversize=False
  try:
   with gzip.open(named('.stdout.gz'),'wb',compresslevel=6) as out:
    while True:
     chunk=os.read(proc.stdout.fileno(),65536)
     if not chunk:break
     if shutil.disk_usage(job).free<8*2**20 and proc.poll() is None and not ending.is_set():
      os.kill(proc.pid,signal.SIGSTOP);note('disk_pause',free_bytes=shutil.disk_usage(job).free)
      while shutil.disk_usage(job).free<16*2**20 and not ending.is_set():time.sleep(1)
      if proc.poll() is None:os.kill(proc.pid,signal.SIGCONT)
      note('disk_resume',free_bytes=shutil.disk_usage(job).free)
     out.write(chunk);out.flush();raw_hash.update(chunk);counts['raw_bytes']+=len(chunk)
     pieces=chunk.split(b'\n')
     for index,piece in enumerate(pieces):
      if not oversize:
       if len(partial)+len(piece)<=512:partial+=piece
       else:oversize=True;partial=b''
      if index<len(pieces)-1:
       if not oversize and partial:note('stdout_line',line=partial.decode('utf-8','replace'),raw_bytes=counts['raw_bytes'])
       partial=b'';oversize=False
     if ending.is_set() and proc.poll() is not None:pass
    if partial and not oversize:note('stdout_line',line=partial.decode('utf-8','replace'),raw_bytes=counts['raw_bytes'])
  except BaseException as exc:
   errors.append(type(exc).__name__+': '+str(exc));ending.set()
   if proc.poll() is None:
    proc.terminate();os.kill(proc.pid,signal.SIGCONT)
  finally:done.set()
 worker=threading.Thread(target=capture);worker.start();termination=None
 while True:
  try:code=proc.wait(timeout=1);break
  except subprocess.TimeoutExpired:
   if errors or time.monotonic()-started>=args.wall_seconds:
    termination='capture_error' if errors else 'wall_timeout';ending.set();proc.terminate();os.kill(proc.pid,signal.SIGCONT)
    try:code=proc.wait(timeout=5)
    except subprocess.TimeoutExpired:proc.kill();code=proc.wait()
    break
 worker.join();proc.stdout.close();note('completed',exit=code,termination=termination)
verified=False;decoded=hashlib.sha256();decoded_count=0
if not errors:
 try:
  with gzip.open(named('.stdout.gz'),'rb') as f:
   while True:
    chunk=f.read(65536)
    if not chunk:break
    decoded.update(chunk);decoded_count+=len(chunk)
  verified=decoded.digest()==raw_hash.digest() and decoded_count==counts['raw_bytes']
 except BaseException as exc:errors.append(type(exc).__name__+': '+str(exc))
usage=resource.getrusage(resource.RUSAGE_CHILDREN)
record={'engine':'Singular_focused_liftstd_12_streaming','source':str(source),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'cpu_budget':args.cpu_seconds,'wall_budget':args.wall_seconds,'memory_mib':args.memory_mib,'wall_seconds':time.monotonic()-started,'exit':code,'termination':termination,'errors':errors,'raw_stdout_bytes':counts['raw_bytes'],'raw_stdout_sha256':raw_hash.hexdigest(),'gzip_bytes':named('.stdout.gz').stat().st_size,'lossless_roundtrip_verified':verified,'child_user_cpu':usage.ru_utime,'child_system_cpu':usage.ru_stime,'child_maxrss_kib':usage.ru_maxrss,'scope':'Complete stdout retained in lossless gzip. Exact polynomial identity still required before any proof claim.'}
named('.result.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record),flush=True)
