import json
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-42/sat');ls=(base/'circuit-14-share.cnf').read_text().splitlines();head=ls[0].split();counter=int(head[2]);extra=[]
vs=json.loads((base/'vars-14.json').read_text());rows=json.loads((base/'rows-14.json').read_text())
def add(xs):extra.append(' '.join(map(str,xs))+' 0')
for k in range(13,27):
 for j in range(k):
  witnesses=[]
  for r,(p,t) in enumerate(rows):
   f=vs[f'v{k}_{r}']*(1 if t else -1)
   if j<13:
    goodg=bool(p>>j&1)==bool(t)
    if not goodg:witnesses.append(f)
   else:
    g=vs[f'v{j}_{r}']*(1 if t else -1)
    counter+=1;witnesses.append(counter);add([-counter,f]);add([-counter,-g])
  add(witnesses)
head[2]=str(counter);head[3]=str(int(head[3])+len(extra));(base/'circuit-14-dom.cnf').write_text(' '.join(head)+'\n'+'\n'.join(ls[1:]+extra)+'\n');print('variables',counter,'extra clauses',len(extra))
