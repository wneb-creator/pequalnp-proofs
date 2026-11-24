import json
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-42/sat');ls=(base/'free-and-10.cnf').read_text().splitlines();head=ls[0].split();counter=int(head[2]);extra=[]
vs=json.loads((base/'free-and-vars-10.json').read_text());rows=json.loads((base/'rows-14.json').read_text())
def add(xs):extra.append(' '.join(map(str,xs))+' 0')
for k in range(10):
 first=[];second=[]
 for r,(p,t) in enumerate(rows):
  if not t:continue
  a=vs[f'm{k}_0_{r}'];b=vs[f'm{k}_1_{r}']
  counter+=1;x=counter;counter+=1;y=counter;first.append(x);second.append(y)
  add([-x,a]);add([-x,-b]);add([-y,-a]);add([-y,b])
 add(first);add(second)
 add([-vs[f'v{k}_{r}'] for r,(p,t) in enumerate(rows) if not t])
head[2]=str(counter);head[3]=str(int(head[3])+len(extra));(base/'free-and-10-prune.cnf').write_text(' '.join(head)+'\n'+'\n'.join(ls[1:]+extra)+'\n');print('variables',counter,'extra clauses',len(extra))
