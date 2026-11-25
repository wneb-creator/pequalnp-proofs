from pathlib import Path
import concurrent.futures,json,random,subprocess,shutil
base=Path('/tmp/oec/pequalnp-pilot-104')
package=Path('/workspace/pequalnp-proofs/lean/.lake/packages/mathlib')
rows=dict(line.split() for line in (base/'2962-cache-hashes.stdout').read_text().splitlines())
missing=[m for m in rows if m.startswith('Mathlib.') and not (package/'.lake/build/lib/lean'/Path(*m.split('.')).with_suffix('.olean')).exists()]
random.Random(7794).shuffle(missing)
work=base/'7794-runtime-sample';work.mkdir(exist_ok=True)
leantar='/tmp/oec/pequalnp-pilot-104/toolchain/lean-4.36.0-linux/bin/leantar'
def sample(m):
 d=work/m;d.mkdir(exist_ok=True);arc=d/rows[m]
 with (work/(m+'.log')).open('wb') as log:
  r=subprocess.run(['curl','-f','-s','-S','https://cache.mathlib.org/mathlib4-master/f/'+arc.name,'-o',str(arc)],stdout=log,stderr=log)
  if r.returncode:raise RuntimeError(m+' fetch failure')
  n=arc.stat().st_size
  r=subprocess.run([leantar,'-f','-x',str(arc)],cwd=d,stdout=log,stderr=log)
  if r.returncode:raise RuntimeError(m+' extraction failure')
 sizes={}
 for p in d.rglob('*'):
  if p.is_file() and p!=arc:
   k='.olean.private' if p.name.endswith('.olean.private') else '.olean.server' if p.name.endswith('.olean.server') else '.ir.sig' if p.name.endswith('.ir.sig') else p.suffix
   sizes[k]=sizes.get(k,0)+p.stat().st_size
 shutil.rmtree(d)
 return {'module':m,'archiveBytes':n,'sizes':sizes}
print(json.dumps({'totalMissingMathlib':len(missing),'samples':100}),flush=True)
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
 for r in pool.map(sample,missing[:100]):print(json.dumps(r),flush=True)
