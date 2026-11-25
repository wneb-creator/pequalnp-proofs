import os,socket,json,hashlib,fcntl,threading,sys
from pathlib import Path
p=Path('/tmp/oec/pequalnp-pilot-182')
slot=sys.argv[1]
sockpath=p/('ram-cache-'+slot+'.sock')
if sockpath.exists(): sockpath.unlink()
srv=socket.socket(socket.AF_UNIX,socket.SOCK_STREAM);srv.bind(str(sockpath));srv.listen(64)
fds=[]
lock=threading.Lock()
(p/('ram-cache-'+slot+'.pid')).write_text(str(os.getpid()))
def handle(c):
 with c:
  try:
   f=c.makefile('rb');d=json.loads(f.readline())
   src=Path(d['source']);dst=Path(d['destination'])
   assert src.is_relative_to(p/'cache-staging')
   assert dst.is_relative_to(Path('/workspace/pequalnp-proofs/lean/.lake/packages'))
   assert not dst.exists()
   fd=os.memfd_create('pnp-official-cache',os.MFD_CLOEXEC|os.MFD_ALLOW_SEALING)
   h=hashlib.sha256();size=0
   with src.open('rb') as inp:
    while chunk:=inp.read(1024*1024):
     h.update(chunk);size+=len(chunk)
     view=memoryview(chunk)
     while view: view=view[os.write(fd,view):]
   assert h.hexdigest()==d['sha256']
   os.fchmod(fd,0o400)
   dst.parent.mkdir(parents=True,exist_ok=True)
   os.symlink('/proc/'+str(os.getpid())+'/fd/'+str(fd),dst)
   with lock: fds.append(fd)
   c.sendall((json.dumps({'ok':True,'bytes':size,'sha256':h.hexdigest()})+'\n').encode())
  except Exception as e:
   c.sendall((json.dumps({'ok':False,'error':str(e)})+'\n').encode())
print('RAM cache keeper ready',flush=True)
while True:
 c,_=srv.accept();threading.Thread(target=handle,args=(c,),daemon=True).start()
