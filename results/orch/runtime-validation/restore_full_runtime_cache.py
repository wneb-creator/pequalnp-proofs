import os,json,subprocess,hashlib,socket,shutil,time,concurrent.futures,threading
from pathlib import Path
p=Path('/tmp/oec/pequalnp-pilot-182');lean=Path('/workspace/pequalnp-proofs/lean')
leantar=p/'lean-4.36.0-linux/bin/leantar'
rows=[]
for line in (p/'full-cache-hashes.tsv').read_text().splitlines():
 mod,archive,source=line.split('\t')
 src=lean/source;pkg=lean/Path(*Path(source).parts[:3])
 rel=src.relative_to(pkg).with_suffix('')
 target=pkg/'.lake/build/lib/lean'/rel
 if not target.with_suffix('.olean').exists(): rows.append((mod,archive,pkg,rel))
(p/'runtime-cache-needed.json').write_text(json.dumps([{'module':a,'archive':b,'package':str(c),'relative':str(d)} for a,b,c,d in rows],indent=2)+'\n')
lock=threading.Lock();done=0;total_bytes=0;started=time.monotonic()
manifest=(p/'runtime-cache-installed.jsonl').open('a',buffering=1)
def work(item):
 global done,total_bytes
 idx,(mod,archive,pkg,rel)=item
 d=p/'cache-staging'/str(idx);d.mkdir(parents=True,exist_ok=True)
 a=d/archive
 url='https://cache.mathlib.org/mathlib4-master/f/'+archive
 r=subprocess.run(['curl','-f','-sS','--retry','2','--retry-delay','1','-o',str(a),url],capture_output=True,text=True)
 if r.returncode: raise RuntimeError(mod+': '+r.stderr)
 archive_sha=hashlib.sha256(a.read_bytes()).hexdigest()
 r=subprocess.run([str(leantar),'-x','-C',str(d),str(a)],capture_output=True,text=True)
 if r.returncode: raise RuntimeError(mod+': '+r.stdout+r.stderr)
 installed=[]
 for suffix in ['.olean','.olean.server','.olean.private','.ir','.ir.sig']:
  base=d if mod=='Mathlib' or mod.startswith('Mathlib.') else d/pkg.relative_to(lean)
  source=base/'.lake/build/lib/lean'/(str(rel)+suffix)
  if not source.exists():
   if suffix=='.olean': raise RuntimeError('missing olean in archive '+mod)
   continue
  dst=pkg/'.lake/build/lib/lean'/(str(rel)+suffix)
  if dst.exists(): continue
  h=hashlib.sha256(source.read_bytes()).hexdigest()
  with socket.socket(socket.AF_UNIX,socket.SOCK_STREAM) as c:
   c.connect(str(p/('ram-cache-'+str(idx%3)+'.sock')))
   c.sendall((json.dumps({'source':str(source),'destination':str(dst),'sha256':h})+'\n').encode())
   ans=json.loads(c.makefile('rb').readline())
   if not ans['ok']: raise RuntimeError(str(ans))
  installed.append({'path':str(dst),'bytes':source.stat().st_size,'sha256':h})
 record={'module':mod,'archive':archive,'url':url,'archive_sha256':archive_sha,'files':installed}
 with lock:
  manifest.write(json.dumps(record)+'\n');done+=1;total_bytes+=sum(x['bytes'] for x in installed)
  if done%100==0: print(json.dumps({'done':done,'total':len(rows),'runtime_bytes':total_bytes,'elapsed_seconds':round(time.monotonic()-started,1)}),flush=True)
 shutil.rmtree(d)
print('Restoring '+str(len(rows))+' missing modules from official pinned cache',flush=True)
with concurrent.futures.ThreadPoolExecutor(max_workers=12) as pool:
 list(pool.map(work,enumerate(rows)))
print(json.dumps({'done':done,'total':len(rows),'runtime_bytes':total_bytes,'elapsed_seconds':time.monotonic()-started,'complete':True}),flush=True)
