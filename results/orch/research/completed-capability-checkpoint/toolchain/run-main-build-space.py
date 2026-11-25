from pathlib import Path
import hashlib,json,os,socket,stat,fcntl,time
B=Path('/tmp/oec/pequalnp-pilot-78/toolchain')
plan=B/'main-build-space-private-plan.json'
assert hashlib.sha256(plan.read_bytes()).hexdigest()=='a40a2e14537478e107b9b34a714996d3ecba05163b6d0963f84afa67f669d751'
j=json.loads(plan.read_text())
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
before=call({'op':'status'});states=[]
for row in j['files']:
 p=Path(row['path']);assert p.is_file() and not p.is_symlink()
 st=p.stat();assert st.st_size==row['bytes'] and digest(p)==row['sha256']
 assert stat.S_IMODE(st.st_mode)==row['mode'] and st.st_mtime_ns==row['mtime_ns']
 states.append({'path':str(p),'bytes':st.st_size,'sha256':row['sha256'],'mode':stat.S_IMODE(st.st_mode),'mtime_ns':st.st_mtime_ns,'atime_ns':st.st_atime_ns})
result=call({'op':'store','paths':[r['path'] for r in states]})
(B/'main-build-space-holder-reply.json').write_text(json.dumps(result,indent=2)+'\n')
for row in states:
 p=Path(row['path']);assert p.is_symlink() and p.stat().st_size==row['bytes'] and digest(p)==row['sha256']
 st=p.stat();assert stat.S_IMODE(st.st_mode)==row['mode'] and st.st_mtime_ns==row['mtime_ns']
 with p.open('rb') as f:assert fcntl.fcntl(f.fileno(),1034)==15
after=call({'op':'status'});assert after['bytes']-before['bytes']==j['bytes'] and after['count']-before['count']==j['count']
fs=os.statvfs(B)
out={'status':'PASS','scope':'Temporary main-build disk reserve: authentic private artifacts returned to existing sealed holder, every full SHA/mode/mtime/seal verified before and after; no checker/runtime bytes changed.','before':before,'after':after,'files':states,'disk_free_bytes':fs.f_bavail*fs.f_frsize,'plan_sha256':hashlib.sha256(plan.read_bytes()).hexdigest()}
(B/'main-build-space-validation.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='files'},indent=2))
