from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import collections,fcntl,hashlib,json,os,shutil,signal,subprocess,sys,time
ROOT=Path('/tmp/oec/pequalnp-pilot-94')
SERVICE=ROOT/'memory-cache';SERVICE.mkdir(exist_ok=True)
REPO=Path('/workspace/pequalnp-proofs');WORK=REPO/'lean'
LEAN_TAR=ROOT/'toolchain/toolchains/leanprover--lean4---v4.36.0/bin/leantar'
MAX_BYTES=int(4.25*1024**3)

def worker():
 fds=[];links=[];stored=0
 try:
  for line in sys.stdin:
   task=json.loads(line)
   if task.get('stop'):break
   folder=Path(task['folder']);row=task['row'];package=Path(row['package'])
   assert package.is_relative_to(WORK/'.lake/packages')
   files=[p for p in folder.rglob('*') if p.is_file()]
   suffix='.lake/build/lib/lean/'+row['module'].replace('.','/')+'.olean'
   public=[p for p in files if str(p).endswith(suffix)]
   assert len(public)==1,(row['module'],public)
   stage_package=Path(str(public[0])[:-len(suffix)])
   manifest=[];added=0
   for source in files:
    relative=source.relative_to(stage_package)
    assert relative.parts[:2]==('.lake','build')
    destination=package/relative
    assert destination.is_relative_to(package/'.lake/build')
    stat=source.stat();digest=hashlib.sha256(source.read_bytes()).hexdigest()
    if destination.exists() or destination.is_symlink():
     assert destination.is_file() and hashlib.sha256(destination.read_bytes()).hexdigest()==digest,str(destination)
     continue
    fd=os.memfd_create('pilot94-'+source.name,os.MFD_CLOEXEC|os.MFD_ALLOW_SEALING)
    with source.open('rb') as src,os.fdopen(os.dup(fd),'wb') as dst:shutil.copyfileobj(src,dst,1024*1024)
    os.fchmod(fd,stat.st_mode&0o777);os.utime(fd,ns=(stat.st_atime_ns,stat.st_mtime_ns))
    # Linux constants verified from installed linux/fcntl.h and asm-generic/fcntl.h.
    fcntl.fcntl(fd,1024+9,0x0001|0x0002|0x0004|0x0008)
    destination.parent.mkdir(parents=True,exist_ok=True)
    target='/proc/'+str(os.getpid())+'/fd/'+str(fd)
    destination.symlink_to(target)
    fds.append(fd);links.append((destination,target));added+=stat.st_size;stored+=stat.st_size
    manifest.append({'path':str(destination),'bytes':stat.st_size,'sha256':digest,'holder_pid':os.getpid(),'fd':fd})
   with (SERVICE/'artifacts.jsonl').open('a') as out:
    out.write(json.dumps({'module':row['module'],'official_source_hash':row['hash'],'artifacts':manifest})+'\n')
   print(json.dumps({'ok':True,'added_bytes':added,'stored_bytes':stored,'fds':len(fds),'pid':os.getpid()}),flush=True)
 except BaseException as error:
  print(json.dumps({'ok':False,'error':repr(error)}),flush=True)
  raise
 finally:
  for path,target in links:
   if path.is_symlink() and os.readlink(path)==target:path.unlink()
  for fd in fds:os.close(fd)

def memory():
 values={line.split()[0]:int(line.split()[1]) for line in Path('/sys/fs/cgroup/memory.stat').read_text().splitlines()}
 return {k:values.get(k,0) for k in ['anon','shmem','kernel','file']}

def main():
 rows=json.loads((ROOT/'cache-hash-inventory.json').read_text())
 rows=[row for row in rows if not Path(row['olean']).is_file()]
 # Finish tiny Batteries roots early; all paths derive from official cache hashes.
 rows.sort(key=lambda row:(not row['module'].startswith('Batteries'),row['module']))
 archives=SERVICE/'archives';archives.mkdir(exist_ok=True)
 staging=SERVICE/'staging';staging.mkdir(exist_ok=True)
 workers=[];current=None;count=0;stored=0;failure=None;started=time.time()
 log=(SERVICE/'diagnostics.log').open('a')
 def save(status,**extra):
  state={'status':status,'pid':os.getpid(),'completed':count,'total':len(rows),'stored_bytes':stored,'holders':[w.pid for w in workers],'elapsed_seconds':time.time()-started,'memory':memory(),**extra}
  temp=SERVICE/'status.next.json';temp.write_text(json.dumps(state,indent=2)+'\n');temp.replace(SERVICE/'status.json')
 def download(row):
  archive=archives/(row['hash']+'.ltar')
  old=ROOT/'cache-memory-sample'/(row['hash']+'.ltar')
  if old.is_file():shutil.copyfile(old,archive)
  else:
   url='https://cache.mathlib.org/mathlib4-master/f/'+row['hash']+'.ltar'
   result=subprocess.run(['curl','--fail','--silent','--show-error','--max-time','30','--output',str(archive),url],capture_output=True)
   if result.stdout or result.stderr:
    with (SERVICE/'download.log').open('ab') as out:
     out.write((row['module']+'\n').encode());out.write(result.stdout);out.write(result.stderr)
   if result.returncode:raise RuntimeError('Official cache download failed '+row['module']+' code='+str(result.returncode))
  return row,archive
 try:
  save('loading')
  with ThreadPoolExecutor(max_workers=8) as pool:
   for start in range(0,len(rows),16):
    batch=list(pool.map(download,rows[start:start+16]))
    for row,archive in batch:
     if (SERVICE/'STOP').exists():raise RuntimeError('Stop requested')
     m=memory()
     if m['anon']+m['shmem']+m['kernel']>int(5.5*1024**3):raise RuntimeError('Non-reclaimable memory safety threshold reached')
     if shutil.disk_usage(WORK).free<32*1024**2:raise RuntimeError('Scratch disk safety threshold reached')
     folder=staging/row['hash'];folder.mkdir(exist_ok=True)
     result=subprocess.run([str(LEAN_TAR),'-C',str(folder),'-x',str(archive)],capture_output=True)
     if result.stdout or result.stderr:
      log.write(row['module']+'\n'+result.stdout.decode(errors='replace')+result.stderr.decode(errors='replace'));log.flush()
     if result.returncode:raise RuntimeError('Official cache unpack failed '+row['module'])
     size=sum(p.stat().st_size for p in folder.rglob('*') if p.is_file())
     if stored+size>MAX_BYTES:raise RuntimeError('Memfd storage safety threshold reached')
     if current is None or current['fds']>10000:
      proc=subprocess.Popen([sys.executable,__file__,'worker'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=log,text=True,bufsize=1)
      workers.append(proc);current={'proc':proc,'fds':0}
     proc=current['proc'];proc.stdin.write(json.dumps({'folder':str(folder),'row':row})+'\n');proc.stdin.flush()
     response=proc.stdout.readline()
     if not response:raise RuntimeError('Artifact holder exited unexpectedly')
     answer=json.loads(response)
     if not answer['ok']:raise RuntimeError(answer['error'])
     current['fds']=answer['fds'];stored+=answer['added_bytes'];count+=1
     shutil.rmtree(folder);archive.unlink()
     if count%100==0 or count==len(rows):
      save('loading');print(json.dumps({'completed':count,'total':len(rows),'stored_MiB':stored//1048576,'elapsed_seconds':round(time.time()-started,1)}),flush=True)
  save('ready');print('GENUINE_CACHE_READY',flush=True)
 except BaseException as error:
  failure=repr(error);save('incomplete',error=failure);print('CACHE_LOAD_STOPPED '+failure,flush=True)
 finally:
  while not (SERVICE/'STOP').exists():
   if any(w.poll() is not None for w in workers):save('holder_failed',error='An artifact holder exited');break
   time.sleep(10)
  for proc in workers:
   if proc.poll() is None:
    proc.stdin.write('{"stop":true}\n');proc.stdin.flush()
  for proc in workers:proc.wait()
  save('stopped',error=failure);log.close()

if __name__=='__main__':
 if len(sys.argv)>1 and sys.argv[1]=='worker':worker()
 else:main()
