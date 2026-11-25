import argparse,fcntl,hashlib,json,os,re,subprocess
from pathlib import Path
BASE=Path('/tmp/oec/pequalnp-pilot-45/resource-wrapper')
STATE=Path('/tmp/oec/pequalnp-pilot-45/build-cache-compaction/generation-002/state')
def sync_dir(path):
 fd=os.open(path,os.O_RDONLY|os.O_DIRECTORY)
 try:os.fsync(fd)
 finally:os.close(fd)
def digest(path):
 h=hashlib.sha256()
 with path.open('rb') as stream:
  for chunk in iter(lambda:stream.read(1024*1024),b''):h.update(chunk)
 return h.hexdigest()
parser=argparse.ArgumentParser();parser.add_argument('label');args=parser.parse_args()
assert re.fullmatch(r'[a-z0-9_-]+',args.label)
with (STATE/'phase.lock').open('a') as lock:
 fcntl.flock(lock.fileno(),fcntl.LOCK_EX|fcntl.LOCK_NB)
 source=STATE/'transaction.json';data=json.loads(source.read_text());assert data['status']=='restored'
 st=source.stat();raw_hash=digest(source)
 archive=STATE/f'transaction-{args.label}.json.zst';temporary=archive.with_name(archive.name+'.new')
 assert not archive.exists() and not temporary.exists()
 with temporary.open('xb') as stream:
  result=subprocess.run(['zstd','-q','-c',str(source)],stdout=stream,stderr=subprocess.PIPE)
  if result.returncode:raise RuntimeError(result.stderr.decode(errors='replace'))
  stream.flush();os.fsync(stream.fileno())
 os.replace(temporary,archive);sync_dir(STATE)
 h=hashlib.sha256();size=0
 process=subprocess.Popen(['zstd','-q','-d','-c',str(archive)],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 for chunk in iter(lambda:process.stdout.read(1024*1024),b''):h.update(chunk);size+=len(chunk)
 stderr=process.stderr.read();assert process.wait()==0,stderr.decode(errors='replace')
 assert h.hexdigest()==raw_hash and size==st.st_size and digest(source)==raw_hash
 metadata={'source':str(source),'archive':str(archive),'status':'restored','uncompressed_bytes':size,'sha256':raw_hash,'archive_sha256':digest(archive),'archive_bytes':archive.stat().st_size,'source_mode':st.st_mode&0o777,'source_mtime_ns':st.st_mtime_ns}
 record=archive.with_name(archive.name+'.metadata.json')
 with record.open('x') as stream:json.dump(metadata,stream,indent=2);stream.write('\n');stream.flush();os.fsync(stream.fileno())
 sync_dir(STATE)
 source.unlink();sync_dir(STATE)
 print(json.dumps(dict(metadata,disk_free=os.statvfs(BASE).f_bavail*os.statvfs(BASE).f_frsize)))
