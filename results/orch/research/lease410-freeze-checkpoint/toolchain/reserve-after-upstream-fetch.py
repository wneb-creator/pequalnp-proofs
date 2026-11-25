from pathlib import Path
import hashlib,json,os,stat,socket,fcntl,datetime
B=Path('/tmp/oec/pequalnp-pilot-78/toolchain')
j=json.loads((B/'main-build-space-completion.json').read_text());rows=j['restored_files']
assert len(rows)==22 and sum(r['bytes'] for r in rows)==40531464
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(1024**2):h.update(b)
 return h.hexdigest()
def call(data):
 with socket.socket(socket.AF_UNIX,socket.SOCK_STREAM) as s:
  s.connect(str(B/'memfd.sock'));s.sendall(json.dumps(data).encode()+b'\n')
  with s.makefile('rb') as f:r=json.loads(f.readline())
 assert r['ok'];return r
before=call({'op':'status'})
for row in rows:
 p=Path(row['path']);assert p.is_file() and not p.is_symlink();st=p.stat()
 assert st.st_size==row['bytes'] and stat.S_IMODE(st.st_mode)==row['mode'] and st.st_mtime_ns==row['mtime_ns'] and digest(p)==row['sha256']
reply=call({'op':'store','paths':[r['path'] for r in rows]})
(B/'reserve-after-upstream-holder-reply.json').write_text(json.dumps(reply,indent=2)+'\n')
for row in rows:
 p=Path(row['path']);assert p.is_symlink();st=p.stat()
 assert st.st_size==row['bytes'] and stat.S_IMODE(st.st_mode)==row['mode'] and st.st_mtime_ns==row['mtime_ns'] and digest(p)==row['sha256']
 with p.open('rb') as f:assert fcntl.fcntl(f.fileno(),1034)==15
after=call({'op':'status'});assert after['bytes']-before['bytes']==40531464 and after['count']-before['count']==22
fs=os.statvfs(B)
result={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'At root request, reversed only the last22 authentic private-artifact disk restorations to reserve space after upstream fetch. FullSHA/mode/mtime/seals verified; existing holder policy unchanged; no research or runtime bytes discarded.','before':before,'after':after,'files':rows,'disk_free_bytes':fs.f_bavail*fs.f_frsize}
(B/'reserve-after-upstream-validation.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='files'},indent=2))
