import hashlib,json,subprocess,threading,time
from pathlib import Path
BASE=Path('/tmp/oec/pequalnp-pilot-45')
STATE=BASE/'resource-wrapper/storage-state'
OUT=BASE/'journal-census'
LABELS=('metadata-smoke','checker004','combined-smoke001','checker005','diagnostic001','checker006','checker007')
rows=[]
for label in LABELS:
 p=STATE/f'transaction-{label}.json.zst'
 m=json.loads(p.with_name(p.name+'.metadata.json').read_text())
 assert m['status']=='restored' and m['archive']==str(p)
 raw=p.read_bytes();assert len(raw)==m['archive_bytes'] and hashlib.sha256(raw).hexdigest()==m['archive_sha256']
 rows.append((p,m))
print(json.dumps({'archives':len(rows),'source_compressed_bytes':sum(m['archive_bytes'] for _,m in rows),'source_raw_bytes':sum(m['uncompressed_bytes'] for _,m in rows)}),flush=True)

def measure(label,flags,decompress=True,selected=None):
 selected=rows if selected is None else selected
 stats={'label':label,'compressed_bytes':0};h=hashlib.sha256();start=time.monotonic()
 with (OUT/f'{label}.stderr').open('wb') as err:
  proc=subprocess.Popen(['zstd','-q','-c',*flags],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=err)
  def drain():
   for chunk in iter(lambda:proc.stdout.read(1024*1024),b''):
    stats['compressed_bytes']+=len(chunk);h.update(chunk)
  reader=threading.Thread(target=drain);reader.start()
  source_reports=[]
  for i,(p,m) in enumerate(selected):
   ih=hashlib.sha256();size=0
   if decompress:
    with (OUT/f'{label}-input-{i}.stderr').open('wb') as de:
     child=subprocess.Popen(['zstd','-q','-d','-c',str(p)],stdout=subprocess.PIPE,stderr=de)
     for chunk in iter(lambda:child.stdout.read(1024*1024),b''):
      ih.update(chunk);size+=len(chunk);proc.stdin.write(chunk)
     assert child.wait()==0
    assert size==m['uncompressed_bytes'] and ih.hexdigest()==m['sha256']
   else:
    with p.open('rb') as f:
     for chunk in iter(lambda:f.read(1024*1024),b''):
      ih.update(chunk);size+=len(chunk);proc.stdin.write(chunk)
    assert size==m['archive_bytes'] and ih.hexdigest()==m['archive_sha256']
   source_reports.append({'name':p.name,'input_bytes':size,'input_sha256':ih.hexdigest()})
  proc.stdin.close();code=proc.wait();reader.join();assert code==0
 stats.update(output_sha256=h.hexdigest(),elapsed_seconds=time.monotonic()-start,source_reports=source_reports,exit_code=code)
 print(json.dumps(stats),flush=True)
 return stats
results=[]
results.append(measure('logical-concat-long27',['--long=27','--single-thread','-3']))
results.append(measure('compressed-concat-long27',['--long=27','--single-thread','-3'],decompress=False))
first=rows[0]
r=measure('reconstruct-first-compressed',['--stream-size='+str(first[1]['uncompressed_bytes'])],selected=[first]);r['exact_original_compressed_bytes']=r['compressed_bytes']==first[1]['archive_bytes'] and r['output_sha256']==first[1]['archive_sha256'];results.append(r)
summary={'archives':len(rows),'old_compressed_bytes':sum(m['archive_bytes'] for _,m in rows),'raw_bytes':sum(m['uncompressed_bytes'] for _,m in rows),'logical_concat_saving':sum(m['archive_bytes'] for _,m in rows)-results[0]['compressed_bytes'],'compressed_concat_saving':sum(m['archive_bytes'] for _,m in rows)-results[1]['compressed_bytes'],'first_recompression_exact':r['exact_original_compressed_bytes'],'measurements':results,'source_archives_changed':False}
for p,m in rows:
 assert p.stat().st_size==m['archive_bytes']
(OUT/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k!='measurements'}),flush=True)
