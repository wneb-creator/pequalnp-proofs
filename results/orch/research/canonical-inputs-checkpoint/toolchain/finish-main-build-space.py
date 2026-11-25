from pathlib import Path
import hashlib,json,os,socket,stat,fcntl,datetime
B=Path('/tmp/oec/pequalnp-pilot-78/toolchain')
old=json.loads((B/'main-2629-backup-validation.json').read_text())
space=json.loads((B/'main-build-space-validation.json').read_text())
p=Path(old['source']);archive=Path(old['backup'])
def digest(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  while b:=f.read(1024**2):h.update(b)
 return h.hexdigest()
def call(data):
 with socket.socket(socket.AF_UNIX,socket.SOCK_STREAM) as s:
  s.connect(str(B/'memfd.sock'));s.sendall(json.dumps(data).encode()+b'\n')
  with s.makefile('rb') as f:r=json.loads(f.readline())
 assert r['ok'];return r
def free():
 fs=os.statvfs(B);return fs.f_bavail*fs.f_frsize
assert p.is_file() and not p.is_symlink() and p.stat().st_size==125550912
new_sha=digest(p);assert new_sha!=old['source_sha256']
assert archive.stat().st_size==old['backup_bytes'] and digest(archive)==old['backup_sha256']
before=call({'op':'status'});before_free=free()
archive.unlink()
restored=[];total=0
for row in space['files']:
 if total>=40_000_000:break
 if free()-row['bytes']<50*2**20:break
 q=Path(row['path']);assert q.is_symlink() and q.stat().st_size==row['bytes'] and digest(q)==row['sha256']
 with q.open('rb') as f:assert fcntl.fcntl(f.fileno(),1034)==15
 result=call({'op':'release','paths':[str(q)]})
 assert q.is_file() and not q.is_symlink() and digest(q)==row['sha256']
 os.chmod(q,row['mode']);os.utime(q,ns=(row['atime_ns'],row['mtime_ns']))
 st=q.stat();assert st.st_size==row['bytes'] and stat.S_IMODE(st.st_mode)==row['mode'] and st.st_mtime_ns==row['mtime_ns']
 restored.append(row);total+=row['bytes']
 with (B/'main-build-space-restored-events.jsonl').open('a') as out:out.write(json.dumps(row)+'\n')
after=call({'op':'status'});assert before['bytes']-after['bytes']==total and before['count']-after['count']==len(restored)
assert free()>=50*2**20
report={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'After root confirmed new main build and preservation push, discarded only the SHA-verified obsolete binary backup, then restored authentic private artifacts to disk with exact SHA/mode/mtime verification. New main artifact was read only.','old_backup_removed':str(archive),'old_backup_sha256':old['backup_sha256'],'new_main_sha256':new_sha,'new_main_bytes':p.stat().st_size,'before':before,'after':after,'disk_free_before':before_free,'disk_free_after':free(),'restored_bytes':total,'restored_files':restored}
(B/'main-build-space-completion.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='restored_files'},indent=2))
