from pathlib import Path
import hashlib,json,os,stat,subprocess,time
BASE=Path('/tmp/oec/pequalnp-pilot-78/toolchain')
SOURCE=Path('/workspace/pequalnp-proofs/lean/.lake/build/lib/lean/PEqualNP/Outside/L_gct_231.olean')
BACKUP=BASE/'main-2629.olean.zst'
assert SOURCE.is_file() and not SOURCE.is_symlink() and not BACKUP.exists()
def digest(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  while b:=f.read(1024*1024):h.update(b)
 return h.hexdigest()
st=SOURCE.stat();sha=digest(SOURCE);start=time.monotonic()
with (BASE/'main-2629-compress.stdout').open('wb') as out,(BASE/'main-2629-compress.stderr').open('wb') as err:
 r=subprocess.run(['zstd','-3','--single-thread','--keep','--no-progress',str(SOURCE),'-o',str(BACKUP)],stdout=out,stderr=err,check=True)
h=hashlib.sha256();n=0
with (BASE/'main-2629-decompress.stderr').open('wb') as err:
 p=subprocess.Popen(['zstd','-dc',str(BACKUP)],stdout=subprocess.PIPE,stderr=err)
 while b:=p.stdout.read(1024*1024):h.update(b);n+=len(b)
 assert p.wait()==0
assert n==st.st_size and h.hexdigest()==sha and digest(SOURCE)==sha
after=SOURCE.stat();assert after.st_size==st.st_size and after.st_mtime_ns==st.st_mtime_ns
fs=os.statvfs(BASE)
report={'status':'PASS','source':str(SOURCE),'source_bytes':st.st_size,'source_sha256':sha,'source_mode':stat.S_IMODE(st.st_mode),'source_mtime_ns':st.st_mtime_ns,'source_atime_ns':st.st_atime_ns,'backup':str(BACKUP),'backup_bytes':BACKUP.stat().st_size,'backup_sha256':digest(BACKUP),'roundtrip_sha256':h.hexdigest(),'disk_free_bytes':fs.f_bavail*fs.f_frsize,'seconds':time.monotonic()-start,'source_retained':True,'scope':'Lossless backup only. No generated artifact removed or changed; root must coordinate idle imports before replacement/build.'}
(BASE/'main-2629-backup-validation.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
