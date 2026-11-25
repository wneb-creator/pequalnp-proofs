from pathlib import Path
import subprocess,json,time,random
root=Path('/tmp/oec/pequalnp-pilot-184/petersen-search')
seed=json.loads((root/'repair-seed.json').read_text());base=(root/'repair-base.cnf').read_text().splitlines();header=base[0].split();nv,nc=int(header[2]),int(header[3]);body='\n'.join(base[1:])+'\n'
n,s,A=11,18,1055
ix=lambda kd,j,a:(kd*(s+1)+j)*A+a+1
variants=[{9,12,14,16,17},{0,4,9,12,14,17},{4,7,9,10,12,14,17},{1,6,9,12,14,16,17},{4,7,9,12,14,15,17},{0,1,3,9,12,14,17},{2,7,9,10,12,14,17},{4,6,7,9,12,14,17}]
rng=random.Random(1890)
variants += [set(rng.sample(range(17),6))|{17} for _ in range(12)]
results=[]
for index,free in enumerate(variants):
 units=[ix(6,0,seed['output'])]
 for j,g in enumerate(seed['gates']):
  if j in free:continue
  op={'and':0,'or':1,'not':3}[g[0]];a=g[1];b=g[2] if len(g)>2 else a
  units.extend(ix(0,j,k)*(1 if k==op else -1) for k in range(4))
  units.extend(ix(1,j,k)*(1 if k==a else -1) for k in range(n+j+1))
  units.extend(ix(2,j,k)*(1 if k==b else -1) for k in range(n+j+1))
 cnf=root/'repair-active.cnf';cnf.write_text(f'p cnf {nv} {nc+len(units)}\n'+body+''.join(f'{v} 0\n' for v in units))
 out=root/f'repair-{index:03d}.stdout';err=root/f'repair-{index:03d}.stderr';started=time.monotonic()
 with out.open('w') as o,err.open('w') as e:
  p=subprocess.Popen(['/tmp/oec/pequalnp-pilot-184/replacement/cadical/build/cadical','--sat','-t','10',str(cnf)],stdout=o,stderr=e)
  peak=0;memory_stop=False
  while p.poll() is None:
   r=subprocess.run(['ps','-o','rss=','-p',str(p.pid)],text=True,capture_output=True)
   rss=int(r.stdout.strip() or 0);peak=max(peak,rss)
   if rss>300*1024:p.terminate();memory_stop=True
   time.sleep(.5)
 status=[l for l in out.read_text().splitlines() if l.startswith('s ') or l=='c UNKNOWN']
 row={'index':index,'free':sorted(free),'exit':p.returncode,'status':status,'seconds':time.monotonic()-started,'peak_KiB':peak,'memory_stop':memory_stop}
 if p.returncode==10:
  with (root/f'repair-{index:03d}.validation').open('w') as v:
   subprocess.run(['python3',str(root/'decode-seeded.py'),str(out)],stdout=v,stderr=subprocess.STDOUT,check=True)
  witness=json.loads(out.with_suffix('.witness.json').read_text())
  row['false_positives']=len(witness['false_positives']);row['false_negatives']=len(witness['false_negatives'])
  if not witness['false_positives'] and not witness['false_negatives']:
   (root/'COUNTEREXAMPLE.json').write_text(json.dumps(witness,indent=2));row['FOUND']=True
 results.append(row);(root/'repair-results.json').write_text(json.dumps(results,indent=2));print(row,flush=True)
 if row.get('FOUND'):break
