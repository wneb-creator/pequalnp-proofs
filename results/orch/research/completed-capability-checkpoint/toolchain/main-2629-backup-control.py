from pathlib import Path
import argparse,hashlib,json,os,subprocess
BASE=Path('/tmp/oec/pequalnp-pilot-78/toolchain')
j=json.loads((BASE/'main-2629-backup-validation.json').read_text())
p=Path(j['source']);backup=Path(j['backup'])
def digest(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  while b:=f.read(1024*1024):h.update(b)
 return h.hexdigest()
ap=argparse.ArgumentParser(description='Remove or restore only the SHA-verified generated main2629 olean; caller must coordinate idle Lean imports.')
ap.add_argument('operation',choices=['check','remove','restore'])
a=ap.parse_args()
assert digest(backup)==j['backup_sha256']
if a.operation=='check':
 assert p.is_file() and not p.is_symlink() and digest(p)==j['source_sha256']
elif a.operation=='remove':
 assert p.is_file() and not p.is_symlink() and digest(p)==j['source_sha256']
 p.unlink()
else:
 assert not p.exists(), 'Refuse to replace an existing new artifact; root must inspect/remove it separately.'
 fs=os.statvfs(p.parent);assert fs.f_bavail*fs.f_frsize>j['source_bytes']+10*2**20
 tmp=p.with_name(p.name+'.main2629-restore')
 assert not tmp.exists()
 with tmp.open('xb') as out,(BASE/'main-2629-restore.stderr').open('wb') as err:
  subprocess.run(['zstd','-dc',str(backup)],stdout=out,stderr=err,check=True)
 assert tmp.stat().st_size==j['source_bytes'] and digest(tmp)==j['source_sha256']
 os.chmod(tmp,j['source_mode']);os.utime(tmp,ns=(j['source_atime_ns'],j['source_mtime_ns']))
 os.replace(tmp,p)
fs=os.statvfs(BASE)
print(json.dumps({'operation':a.operation,'source':str(p),'source_exists':p.exists(),'backup_sha256':j['backup_sha256'],'free_bytes':fs.f_bavail*fs.f_frsize}))
