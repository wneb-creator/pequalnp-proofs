from pathlib import Path
import hashlib, json, os, subprocess, time, datetime
BASE=Path('/tmp/oec/pequalnp-pilot-61')
OUT=BASE/'archive6349'
RAW=BASE/'canonical6349.lrat'
DEST=OUT/'canonical6349.lrat.zst'
BLOCK=1024*1024
LIMIT=40*BLOCK
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as src:
  for b in iter(lambda:src.read(BLOCK),b''):h.update(b)
 return h.hexdigest()
start=time.monotonic();stat0=RAW.stat();rawhash=sha(RAW)
with (OUT/'compression.log').open('wb') as log, DEST.open('wb') as dest:
 process=subprocess.Popen(['zstd','-10','--single-thread','-c',str(RAW)],stdout=dest,stderr=log)
 pid,status,rusage=os.wait4(process.pid,0);process.returncode=os.waitstatus_to_exitcode(status)
assert process.returncode==0,process.returncode
compression_end=time.monotonic();compressedhash=sha(DEST)
with (OUT/'decompression-verification.log').open('wb') as log:
 process=subprocess.Popen(['zstd','-d','-c',str(DEST)],stdout=subprocess.PIPE,stderr=log)
 h=hashlib.sha256();total=0
 while True:
  b=process.stdout.read(BLOCK)
  if not b:break
  h.update(b);total+=len(b)
 process.stdout.close();rc=process.wait()
assert rc==0,rc
decompressedhash=h.hexdigest()
assert total==stat0.st_size and decompressedhash==rawhash,(total,decompressedhash)
stat1=RAW.stat();assert (stat0.st_size,stat0.st_mtime_ns)==(stat1.st_size,stat1.st_mtime_ns)
chunks=[]
if DEST.stat().st_size>LIMIT:
 with DEST.open('rb') as src:
  part=0
  while True:
   first=src.read(BLOCK)
   if not first:break
   path=OUT/f'canonical6349.lrat.zst.part-{part:03d}';hh=hashlib.sha256();size=0
   with path.open('wb') as dst:
    b=first
    while b:
     dst.write(b);hh.update(b);size+=len(b)
     if size==LIMIT:break
     b=src.read(min(BLOCK,LIMIT-size))
   chunks.append({'path':str(path),'bytes':size,'sha256':hh.hexdigest()});part+=1
else:
 chunks=[{'path':str(DEST),'bytes':DEST.stat().st_size,'sha256':compressedhash}]
h=hashlib.sha256();count=0
for item in chunks:
 with Path(item['path']).open('rb')as src:
  for b in iter(lambda:src.read(BLOCK),b''):h.update(b);count+=len(b)
assert h.hexdigest()==compressedhash and count==DEST.stat().st_size
result={'createdUtc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'purpose':'Lossless preservation of raw solver LRAT, not a kernel verification claim','raw':{'path':str(RAW),'bytes':stat0.st_size,'sha256':rawhash,'mtimeNs':stat0.st_mtime_ns,'unchangedDuringArchival':True},'compressed':{'path':str(DEST),'bytes':DEST.stat().st_size,'sha256':compressedhash,'codec':'zstd','level':10,'singleThread':True,'exitCode':0,'secondsIncludingRawHash':compression_end-start,'userSeconds':rusage.ru_utime,'systemSeconds':rusage.ru_stime,'maxRssKiB':rusage.ru_maxrss},'verification':{'decompressionExitCode':0,'decompressedBytes':total,'decompressedSha256':decompressedhash,'rawShaMatchesDecompressed':True,'concatenatedChunkShaMatchesCompressed':True},'chunkLimitBytes':LIMIT,'chunks':chunks,'fullCompressedStreamNeededWhenSplit':False,'totalSeconds':time.monotonic()-start,'restore':'Concatenate chunks in listed order, then zstd-decompress; verify raw sha256 before use.'}
(OUT/'raw-lrat-archive-manifest.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result),flush=True)
