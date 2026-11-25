from pathlib import Path
import json,subprocess,time
out=Path('results/orch9775/projection');solver='/tmp/oec/pequalnp-pilot-103/setup/lean-4.36.0-linux/bin/cadical'
for I in [111,4757,2213]:
 d=json.loads((out/f'code-{I}.json').read_text());k=d['k'];rs=[r for r in d['relations']if not I>>r['c']&1];calls=0
 def solve(rs):
  global calls
  calls+=1;cs=[];nv=14*k
  def var(x,t):return 1+x*k+t
  for r in rs:
   x,c=r['x'],r['c'];diff=[]
   for t in range(k):
    nv+=1;v=nv;diff.append(v);cs += [[-v,var(x,t)],[-v,-var(c,t)],[v,-var(x,t),var(c,t)]]
   if r['strict']:cs.append(diff)
   else:
    for t in range(k):cs.append([-var(x,t)]+diff)
  cnf=Path(f'/tmp/oec/pequalnp-pilot-103/9775-minimize-code-{I}.cnf');cnf.write_text(f'p cnf {nv} {len(cs)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in cs))
  with(out/f'minimize-{I}.stdout').open('a')as f,(out/f'minimize-{I}.stderr').open('a')as g:cp=subprocess.run([solver,'-t','2',str(cnf)],stdout=f,stderr=g)
  return cp.returncode
 assert solve(rs)==20
 # Remove whole vertex families first, then individual relations.
 for v in sorted({r['x']for r in rs}|{r['c']for r in rs}):
  trial=[r for r in rs if v not in [r['x'],r['c']]]
  if solve(trial)==20:rs=trial
 for r in rs[:]:
  trial=[q for q in rs if q is not r]
  if solve(trial)==20:rs=trial
 assert solve(rs)==20
 d['relations']=rs;d['calls']=calls;d['variables']=sorted({r['x']for r in rs}|{r['c']for r in rs});(out/f'code-{I}-minimal.json').write_text(json.dumps(d,indent=2)+'\n');print(I,k,'vertices',d['variables'],'relations',len(rs),'calls',calls,flush=True)
