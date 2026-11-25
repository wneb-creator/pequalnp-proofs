import json,time,subprocess,sys
from pathlib import Path
from itertools import combinations
from datetime import datetime,timezone
base=Path('/tmp/oec/pequalnp-pilot-152/gap-3754')
source=Path('/workspace/pequalnp-proofs/results/orch/forest-formulas-3754/forest6-formula-search.log')
rows=[json.loads(x) for x in source.read_text().splitlines()];results=[]
print(datetime.now(timezone.utc).isoformat(),'forest circuit census',len(rows),'graphs,5000ms per graph',flush=True)
for i,row in enumerate(rows,1):
 edges=row['edges'];n=6;colors=[None]*n;neighbors=[[] for _ in range(n)]
 for a,b in edges:neighbors[a].append(b);neighbors[b].append(a)
 for v in range(n):
  if colors[v] is not None:continue
  colors[v]=0;todo=[v]
  while todo:
   a=todo.pop()
   for b in neighbors[a]:
    if colors[b] is None:colors[b]=1-colors[a];todo.append(b)
    assert colors[b]!=colors[a]
 name='forest6case'+str(i).zfill(2);spec=base/(name+'.json');m=row['star_bound']
 spec.write_text(json.dumps(dict(name=name,n=n,edges=edges,colors=colors)))
 log=base/(name+str(n)+'-size'+str(m)+'-dirty.log');start=time.monotonic()
 with log.open('w') as out:
  proc=subprocess.run([sys.executable,str(base/'dirty-graph-synth.py'),str(spec),str(m),'5000','dirty'],stdout=out,stderr=subprocess.STDOUT)
 text=log.read_text();matches=[x for x in text.splitlines() if x.startswith('RESULT ') or x.startswith('REASON ')]
 result=dict(case=i,edges=edges,gates=m,returncode=proc.returncode,result=matches,seconds=time.monotonic()-start)
 results.append(result);print(json.dumps(result),flush=True)
 assert proc.returncode==0
 if any(x.startswith('RESULT sat ') for x in matches):print('SAT_CANDIDATE',str(log),flush=True)
(base/'forest-circuit-batch-results.json').write_text(json.dumps(results,indent=2)+'\n')
print('COMPLETED',len(results),datetime.now(timezone.utc).isoformat(),flush=True)
