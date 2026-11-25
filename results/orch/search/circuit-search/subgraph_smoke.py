import json,subprocess,sys
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-70/circuit-search')
for name in ['subgraph-3-0','subgraph-3-1','subgraph-4-0','subgraph-4-1']:
 graph=json.loads((base/f'{name}.json').read_text());n=graph['ninputs'];edges=graph['edges']
 old=[];terms=[]
 for a in sorted({e[0] for e in edges}):
  neighbors=sorted(b for aa,b in edges if aa==a)
  wire=neighbors[0]
  for b in neighbors[1:]:
   old.append(('or',wire,b));wire=n-1+len(old)
  terms.append(n+len(old));old.append(('and',a,wire))
 out=terms[0]
 for t in terms[1:]:old.append(('or',out,t));out=n-1+len(old)
 mapping={i:i for i in range(n)};pending=set(range(len(old)));gates=[]
 while pending:
  choices=[]
  for i in pending:
   op,a,b=old[i]
   if a in mapping and b in mapping:
    a,b=sorted([mapping[a],mapping[b]])
    choices.append(((a,b,op=='or'),i,(op,a,b)))
  _,i,g=min(choices);mapping[n+i]=n+len(gates);gates.append(g);pending.remove(i)
 assert len(gates)==graph['target_gates']+1
 cnf=base/f'{name}-baseline.cnf'
 with (base/f'{name}-baseline-encode.log').open('w') as log:
  subprocess.run([sys.executable,str(base/'synthesize.py'),'--gates',str(len(gates)),'--edge-file',str(base/f'{name}.json'),'--no-canon','--output',str(cnf)],stdout=log,stderr=subprocess.STDOUT,check=True)
 meta=json.loads(cnf.with_suffix('.map.json').read_text());units=[]
 for (op,a,b),s in zip(gates,meta['structure']):units.extend([s['left'][a],s['right'][b],s['op'] if op=='or' else -s['op']])
 lines=cnf.read_text().splitlines();fields=lines[0].split();fields[-1]=str(int(fields[-1])+len(units));lines[0]=' '.join(fields)
 lines.extend(str(v)+' 0' for v in units);cnf.write_text('\n'.join(lines)+'\n')
 solve=base/f'{name}-baseline-solve.log'
 with solve.open('w') as log:
  rc=subprocess.run([str(base/'cadical/build/cadical'),'-t','10',str(cnf)],stdout=log,stderr=subprocess.STDOUT).returncode
 assert rc==10,(name,rc)
 with (base/f'{name}-baseline-verified.log').open('w') as log:
  subprocess.run([sys.executable,str(base/'decode.py'),str(cnf.with_suffix('.map.json')),str(solve)],stdout=log,stderr=subprocess.STDOUT,check=True)
 print(name,'baseline SAT and independently verified all',1<<n,'inputs',flush=True)
