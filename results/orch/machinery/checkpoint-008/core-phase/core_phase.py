import argparse,fcntl,hashlib,importlib.util,json,os,stat,subprocess,sys
from pathlib import Path
BASE=Path('/tmp/oec/pequalnp-pilot-45')
spec=importlib.util.spec_from_file_location('reviewed_storage',BASE/'resource-wrapper/storage_phase.py')
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
def report(action,**data):print(json.dumps(dict(core_phase=action,**data)),file=sys.stderr,flush=True)
def sync_dir(path):
 fd=os.open(path,os.O_RDONLY|os.O_DIRECTORY)
 try:os.fsync(fd)
 finally:os.close(fd)
def atomic_json(path,data):
 tmp=path.with_name(path.name+'.new')
 try:pending=tmp.lstat()
 except FileNotFoundError:pending=None
 if pending is not None:
  if not stat.S_ISREG(pending.st_mode) or pending.st_uid!=os.getuid():raise RuntimeError('unexpected pending JSON file')
  tmp.unlink();sync_dir(tmp.parent)
 with tmp.open('x') as f:json.dump(data,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
 os.replace(tmp,path);sync_dir(path.parent)
def digest(path):
 h=hashlib.sha256()
 with Path(path).open('rb') as f:
  for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
 return h.hexdigest()
def no_lean_processes():
 r=subprocess.run(['ps','-eo','pid,stat,comm'],capture_output=True,text=True,check=True)
 live=[line for line in r.stdout.splitlines()[1:] if line.split()[-1] in ('lake','lean','checklemma') and not line.split()[1].startswith('Z')]
 if live:raise RuntimeError('a Lean, Lake, or verifier process is still alive')
def no_backing_mappers(rows):
 targets={(os.major(x['fd_dev']),os.minor(x['fd_dev']),x['fd_ino']) for x in rows}
 result=subprocess.run(['ps','-eo','pid,uid'],capture_output=True,text=True,check=True)
 for line in result.stdout.splitlines()[1:]:
  pid,uid=map(int,line.split())
  if uid!=os.getuid():continue
  try:maps=(Path('/proc')/str(pid)/'maps').read_text()
  except FileNotFoundError:continue
  for entry in maps.splitlines():
   fields=entry.split(maxsplit=5);major,minor=(int(x,16) for x in fields[3].split(':'))
   if (major,minor,int(fields[4])) in targets:raise RuntimeError(f'core backing remains mapped by owned process {pid}')
class CorePhase:
 def __init__(self,c):
  self.c=c;self.state=Path(c['state_dir']);self.state.mkdir(parents=True,exist_ok=True)
  self.prepared=self.state/'prepared.json';self.journal=self.state/'transaction.json';self.pack=self.state/'excluded.zstpack';self.codec=module.Codec()
 def validate_path(self,row):
  p=Path(row['path']);root=Path(self.c['toolchain_root'])/'lib/lean'
  if not p.is_relative_to(root) or not any(p.name.endswith(s) for s in ('.olean','.olean.private','.olean.server','.ir')):raise RuntimeError('ineligible core runtime path')
  if row['target']!=f"/proc/{row['pid']}/fd/{row['fd']}":raise RuntimeError('invalid backing target')
  return p
 def backing(self,row,size=None):
  st=Path(row['target']).stat()
  if (st.st_dev,st.st_ino)!=(row['fd_dev'],row['fd_ino']):raise RuntimeError('backing identity changed')
  if size is not None and st.st_size!=size:raise RuntimeError('unexpected backing size')
  return st
 def decoded(self,row):
  with self.pack.open('rb') as f:f.seek(row['offset']);compressed=f.read(row['compressed'])
  raw=self.codec.decompress(compressed,row['size'])
  if hashlib.sha256(raw).hexdigest()!=row['sha256']:raise RuntimeError('backup hash mismatch')
  return raw
 def prepare(self):
  if digest(self.c['excluded_manifest'])!=self.c['excluded_manifest_sha256']:raise RuntimeError('reviewed exclusion manifest changed')
  if self.prepared.exists():
   data=json.loads(self.prepared.read_text())
   for row in data['files']:self.validate_path(row);self.decoded(row)
   report('already_prepared',files=len(data['files']),bytes=data['bytes']);return
  assert not self.pack.exists()
  source=json.loads(Path(self.c['excluded_manifest']).read_text());rows=source['files'];result=[]
  with self.pack.open('xb') as pack:
   for original in rows:
    row=dict(original);row.update(size=row['bytes'],fd_dev=row['device'],fd_ino=row['inode'])
    p=self.validate_path(row);st=self.backing(row,row['size'])
    if not p.is_symlink() or os.readlink(p)!=row['target']:raise RuntimeError('unexpected core runtime link')
    if stat.S_IMODE(st.st_mode)!=row['mode'] or st.st_mtime_ns!=row['mtime_ns']:raise RuntimeError('metadata changed since exclusion audit')
    raw=p.read_bytes()
    if hashlib.sha256(raw).hexdigest()!=row['sha256']:raise RuntimeError('live core hash mismatch')
    compressed=self.codec.compress(raw)
    if os.statvfs(self.state).f_bavail*os.statvfs(self.state).f_frsize < len(compressed)+100*1024*1024:raise RuntimeError('insufficient backup disk reserve')
    row['offset']=pack.tell();row['compressed']=len(compressed);pack.write(compressed);result.append(row)
   pack.flush();os.fsync(pack.fileno())
  sync_dir(self.state)
  data={'files':result,'bytes':sum(x['size'] for x in result),'source_manifest_sha256':digest(self.c['excluded_manifest'])}
  for row in result:self.decoded(row)
  atomic_json(self.prepared,data)
  report('prepared',files=len(result),bytes=data['bytes'],compressed_bytes=self.pack.stat().st_size)
 def enter(self):
  no_lean_processes()
  base=json.loads(Path(self.c['base_journal']).read_text())
  if base['status']!='entered':raise RuntimeError('base storage phase must be entered first')
  if self.journal.exists() and json.loads(self.journal.read_text())['status']!='restored':raise RuntimeError('unfinished core transaction')
  data=json.loads(self.prepared.read_text())
  if data['source_manifest_sha256']!=self.c['excluded_manifest_sha256']:raise RuntimeError('unreviewed prepared exclusions')
  base_paths={x['path'] for kind in ('build','ram') for x in base[kind]}
  base_backings={(x['fd_dev'],x['fd_ino']) for x in base['ram']}
  if any(x['path'] in base_paths or (x['fd_dev'],x['fd_ino']) in base_backings for x in data['files']):raise RuntimeError('core and base phases overlap')
  no_backing_mappers(data['files'])
  for row in data['files']:
   p=self.validate_path(row);st=self.backing(row,row['size']);self.decoded(row)
   if not p.is_symlink() or os.readlink(p)!=row['target'] or digest(p)!=row['sha256']:raise RuntimeError('core artifact changed before enter')
   if stat.S_IMODE(st.st_mode)!=row['mode'] or st.st_mtime_ns!=row['mtime_ns']:raise RuntimeError('core metadata changed before enter')
  plan=dict(data,status='planned');atomic_json(self.journal,plan)
  no_lean_processes();no_backing_mappers(plan['files'])
  for row in plan['files']:
   p=Path(row['path']);self.backing(row,row['size']);p.unlink();sync_dir(p.parent)
   fd=os.open(row['target'],os.O_RDWR)
   try:
    st=os.fstat(fd)
    if (st.st_dev,st.st_ino,st.st_size)!=(row['fd_dev'],row['fd_ino'],row['size']):raise RuntimeError('core backing changed before truncate')
    os.ftruncate(fd,0)
   finally:os.close(fd)
  plan['status']='entered';atomic_json(self.journal,plan);report('entered',files=len(plan['files']),released_bytes=plan['bytes'])
 def restore(self):
  if not self.journal.exists():report('restore_no_transaction');return
  plan=json.loads(self.journal.read_text())
  if plan['status']=='restored':report('already_restored');return
  no_lean_processes();no_backing_mappers(plan['files']);errors=[]
  for row in plan['files']:
   try:
    p=self.validate_path(row);st=self.backing(row)
    if p.exists() or p.is_symlink():
     if not p.is_symlink() or os.readlink(p)!=row['target']:raise RuntimeError('unexpected existing core path')
    if st.st_size!=row['size'] or digest(row['target'])!=row['sha256']:
     raw=self.decoded(row);fd=os.open(row['target'],os.O_RDWR)
     try:
      current=os.fstat(fd)
      if (current.st_dev,current.st_ino)!=(row['fd_dev'],row['fd_ino']):raise RuntimeError('restore backing changed')
      os.ftruncate(fd,0);offset=0
      while offset<len(raw):
       written=os.pwrite(fd,raw[offset:],offset)
       if written<=0:raise RuntimeError('core backing write made no progress')
       offset+=written
     finally:os.close(fd)
    # A previous restore can stop after writing the bytes but before metadata.
    fd=os.open(row['target'],os.O_RDWR)
    try:
     current=os.fstat(fd)
     if (current.st_dev,current.st_ino)!=(row['fd_dev'],row['fd_ino']):raise RuntimeError('metadata backing changed')
     os.fchmod(fd,row['mode']);os.utime(fd,ns=(row['mtime_ns'],row['mtime_ns']));os.fsync(fd)
    finally:os.close(fd)
    st=self.backing(row,row['size'])
    if digest(row['target'])!=row['sha256'] or stat.S_IMODE(st.st_mode)!=row['mode'] or st.st_mtime_ns!=row['mtime_ns']:raise RuntimeError('restored core bytes or metadata mismatch')
    if not p.is_symlink():
     temp=p.with_name(p.name+'.core-phase-new')
     if temp.exists() or temp.is_symlink():
      if not temp.is_symlink() or os.readlink(temp)!=row['target']:raise RuntimeError('unexpected pending core symlink')
     else:temp.symlink_to(row['target'])
     if 'symlink_mtime_ns' in row:os.utime(temp,ns=(row['symlink_mtime_ns'],row['symlink_mtime_ns']),follow_symlinks=False)
     os.replace(temp,p);sync_dir(p.parent)
    if 'symlink_mtime_ns' in row:
     os.utime(p,ns=(row['symlink_mtime_ns'],row['symlink_mtime_ns']),follow_symlinks=False);sync_dir(p.parent)
     if p.lstat().st_mtime_ns!=row['symlink_mtime_ns']:raise RuntimeError('restored symlink metadata mismatch')
   except Exception as error:errors.append(str(p)+': '+str(error));report('restore_error',error=errors[-1])
  if errors:raise RuntimeError(f'core restoration incomplete: {len(errors)} files')
  plan['status']='restored';atomic_json(self.journal,plan);report('restored',files=len(plan['files']),bytes=plan['bytes'])
def main():
 parser=argparse.ArgumentParser();parser.add_argument('--config',default=str(BASE/'core-phase/config.json'));parser.add_argument('action',choices=('prepare','enter','restore'));args=parser.parse_args()
 try:
  c=json.loads(Path(args.config).read_text());state=Path(c['state_dir']);state.mkdir(parents=True,exist_ok=True)
  with Path(c['phase_lock']).open('a') as lock:
   fcntl.flock(lock.fileno(),fcntl.LOCK_EX|fcntl.LOCK_NB);getattr(CorePhase(c),args.action)()
  return 0
 except Exception as error:report('failed',action=args.action,error=str(error));return 1
if __name__=='__main__':sys.exit(main())
