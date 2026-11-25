from pathlib import Path
import os,sys,time,json,hashlib,shutil,subprocess,multiprocessing as mp,fcntl,signal,datetime
BASE=Path('/tmp/oec/pequalnp-pilot-104')
REPO=Path('/workspace/pequalnp-proofs')
LEAN=REPO/'lean'
WORK=BASE/'7794-memory-cache'
WORK.mkdir(exist_ok=True)
ROOTS={'Mathlib':'mathlib','Batteries':'batteries','Aesop':'aesop','Qq':'Qq','ImportGraph':'importGraph','ProofWidgets':'proofwidgets','Plausible':'plausible','LeanSearchClient':'LeanSearchClient'}
LEANTAR=str(BASE/'toolchain/lean-4.36.0-linux/bin/leantar')
LIMIT=int(7.5*1024**3)
RESERVE=200*1024**2
DEADLINE=time.monotonic()+max(0,datetime.datetime(2026,11,25,16,50,tzinfo=datetime.timezone.utc).timestamp()-time.time())
F_ADD_SEALS=1024+9
F_GET_SEALS=1024+10
ALL_SEALS=0x0001|0x0002|0x0004|0x0008
stop=mp.Event()
lock=mp.Lock()
counts=mp.Array('q',4*4)
def memory():return int(Path('/sys/fs/cgroup/memory.current').read_text())
def digest_stream(f):
 h=hashlib.sha256()
 while b:=f.read(1024*1024):h.update(b)
 return h.hexdigest()
def destbase(mod):return LEAN/'.lake/packages'/ROOTS[mod.split('.')[0]]/'.lake/build/lib/lean'
def worker(index,rows):
 held=[];links=[]
 log=(WORK/f'worker-{index}.jsonl').open('w',buffering=1)
 try:
  for ordinal,(mod,archive) in enumerate(rows):
   if stop.is_set():raise RuntimeError('preparation stopped')
   if time.monotonic()>DEADLINE:raise RuntimeError('preparation time cap reached')
   if memory()>=LIMIT:raise RuntimeError('preparation memory threshold reached')
   stage=WORK/f'stage-{index}';stage.mkdir(exist_ok=True)
   arc=stage/archive
   with (WORK/f'worker-{index}-transport.log').open('ab') as transport:
    transport.write((mod+' '+archive+'\n').encode())
    r=subprocess.run(['curl','-f','-s','-S','https://cache.mathlib.org/mathlib4-master/f/'+archive,'-o',str(arc)],stdout=transport,stderr=transport,timeout=60)
    if r.returncode:raise RuntimeError(mod+' fetch returned '+str(r.returncode))
    r=subprocess.run([LEANTAR,'-f','-x',str(arc)],cwd=stage,stdout=transport,stderr=transport,timeout=60)
    if r.returncode:raise RuntimeError(mod+' extraction returned '+str(r.returncode))
   package=ROOTS[mod.split('.')[0]]
   prefix=stage/'.lake/build/lib/lean' if package=='mathlib' else stage/'.lake/packages'/package/'.lake/build/lib/lean'
   stem=Path(*mod.split('.'))
   primary=prefix/Path(str(stem)+'.olean')
   if not primary.is_file():raise RuntimeError(mod+' official archive lacks expected olean')
   for suffix in ['.olean','.olean.server','.olean.private','.ir','.ir.sig']:
    src=prefix/Path(str(stem)+suffix)
    if not src.is_file():continue
    if stop.is_set() or memory()>=LIMIT:raise RuntimeError('memory threshold or requested stop')
    dst=destbase(mod)/Path(str(stem)+suffix)
    dst.parent.mkdir(parents=True,exist_ok=True)
    size=src.stat().st_size
    with src.open('rb') as f:sha=digest_stream(f)
    if dst.exists():
     with dst.open('rb') as f:actual=digest_stream(f)
     if actual!=sha:raise RuntimeError('existing artifact checksum mismatch')
     backing='existing'
    else:
     with lock:
      disk=shutil.disk_usage(LEAN).free>=RESERVE
      if disk:os.replace(src,dst)
     if disk:
      with dst.open('rb') as f:actual=digest_stream(f)
      if actual!=sha:raise RuntimeError('disk artifact checksum mismatch')
      fd=os.open(dst,os.O_RDONLY);os.fsync(fd);os.posix_fadvise(fd,0,0,os.POSIX_FADV_DONTNEED);os.close(fd)
      backing='disk'
      with counts.get_lock():counts[index*4+2]+=size
     else:
      fd=os.memfd_create('official-cache-'+mod+suffix,os.MFD_ALLOW_SEALING)
      with src.open('rb') as f:
       while b:=f.read(1024*1024):
        view=memoryview(b)
        while view:
         n=os.write(fd,view);view=view[n:]
      os.lseek(fd,0,os.SEEK_SET)
      with os.fdopen(os.dup(fd),'rb') as f:actual=digest_stream(f)
      if actual!=sha:raise RuntimeError('memfd artifact checksum mismatch')
      os.fchmod(fd,0o444)
      fcntl.fcntl(fd,F_ADD_SEALS,ALL_SEALS)
      if fcntl.fcntl(fd,F_GET_SEALS)!=ALL_SEALS:raise RuntimeError('memfd sealing failed')
      dst.symlink_to(f'/proc/{os.getpid()}/fd/{fd}')
      held.append(fd);links.append(dst)
      backing='memfd'
      with counts.get_lock():counts[index*4+3]+=size
      src.unlink()
    log.write(json.dumps({'module':mod,'archive':archive,'path':str(dst.relative_to(LEAN)),'bytes':size,'sha256':sha,'backing':backing,'holder':os.getpid() if backing=='memfd' else None})+'\n')
    with counts.get_lock():counts[index*4+1]+=1
   shutil.rmtree(stage)
   with counts.get_lock():counts[index*4]+=1
  (WORK/f'worker-{index}.ready').write_text(str(os.getpid())+'\n')
  while not stop.wait(0.5):pass
 except Exception as e:
  log.write(json.dumps({'error':str(e),'worker':index})+'\n')
  (WORK/f'worker-{index}.error').write_text(str(e)+'\n')
  stop.set()
 finally:
  for p in links:
   if p.is_symlink() and os.readlink(p).startswith(f'/proc/{os.getpid()}/fd/'):p.unlink()
  for fd in held:os.close(fd)
  log.close()
def complete(mod):
 p=destbase(mod)/Path(*mod.split('.'))
 if not Path(str(p)+'.olean').exists():return False
 trace=Path(str(p)+'.trace')
 expected=['.olean','.olean.server','.olean.private','.ir','.ir.sig']
 if trace.exists():
  o=json.loads(trace.read_text()).get('outputs') or {}
  expected=['.olean']
  if o.get('m'):expected+=['.olean.server','.olean.private']
  if o.get('r'):expected+=['.ir']
  if o.get('rs'):expected+=['.ir.sig']
 return all(Path(str(p)+s).exists() for s in expected)
def main():
 allrows=[line.split() for line in (BASE/'2962-cache-hashes.stdout').read_text().splitlines()]
 rows=[(m,h) for m,h in allrows if not complete(m)]
 rows.sort(key=lambda x:(x[0].split('.')[0]=='Mathlib',x[0]))
 print(json.dumps({'event':'starting','modules':len(rows),'memoryLimit':LIMIT,'reserveDisk':RESERVE,'pid':os.getpid()}),flush=True)
 (WORK/'holder.pid').write_text(str(os.getpid())+'\n')
 procs=[mp.Process(target=worker,args=(i,rows[i::4])) for i in range(4)]
 for p in procs:p.start()
 last=0;ready=False;checker=None
 try:
  while not stop.is_set():
   now=time.monotonic();mem=memory()
   if now-last>=15:
    values=list(counts)
    print(json.dumps({'event':'status','ready':ready,'done':sum(values[0::4]),'files':sum(values[1::4]),'diskBytes':sum(values[2::4]),'memfdBytes':sum(values[3::4]),'memory':mem,'diskFree':shutil.disk_usage(LEAN).free}),flush=True)
    last=now
   if mem>=LIMIT:
    print(json.dumps({'event':'memory-limit','memory':mem}),flush=True)
    if checker is not None and checker.poll() is None:os.killpg(checker.pid,signal.SIGTERM)
    stop.set();break
   if not ready and all((WORK/f'worker-{i}.ready').exists() for i in range(4)):
    ready=True
    (WORK/'READY').write_text(json.dumps({'modules':len(rows),'time':time.time()})+'\n')
    print(json.dumps({'event':'READY','modules':len(rows),'memory':mem}),flush=True)
   if not ready and now>DEADLINE:
    print(json.dumps({'event':'preparation-time-cap'}),flush=True);stop.set();break
   if ready and checker is None and (WORK/'RUN_CHECKER').exists():
    env=os.environ.copy()
    env['PATH']=str(BASE/'toolchain/lean-4.36.0-linux/bin')+':'+env.get('PATH','')
    env['PEQUALNP_REAL_LAKE']=str(BASE/'toolchain/lean-4.36.0-linux/bin/lake')
    env['PEQUALNP_HOME']=str(BASE/'7794-checker-queue')
    out=(BASE/'7794-checker-memory.stdout').open('wb');err=(BASE/'7794-checker-memory.stderr').open('wb')
    checker=subprocess.Popen(['node','tools/check-lean.mjs','lean/PEqualNP/Outside/L_meta_7794.lean',str(BASE/'7794-statement.txt'),'check'],cwd=REPO,env=env,stdout=out,stderr=err,start_new_session=True)
    (WORK/'checker.pid').write_text(str(checker.pid)+'\n')
    print(json.dumps({'event':'checker-started','pid':checker.pid}),flush=True)
   if checker is not None and checker.poll() is not None and not (WORK/'CHECKER_DONE').exists():
    (WORK/'CHECKER_DONE').write_text(str(checker.returncode)+'\n')
    print(json.dumps({'event':'checker-done','exit':checker.returncode,'memory':mem}),flush=True)
   if (WORK/'STOP').exists():stop.set();break
   time.sleep(0.2)
 finally:
  stop.set()
  if checker is not None and checker.poll() is None:
   os.killpg(checker.pid,signal.SIGTERM)
   try:checker.wait(timeout=10)
   except subprocess.TimeoutExpired:print('Checker is still terminating',flush=True)
  for p in procs:p.join(timeout=65)
  for p in procs:
   if p.is_alive():p.terminate();p.join()
  print(json.dumps({'event':'holder-stopped','memory':memory()}),flush=True)
if __name__=='__main__':main()
