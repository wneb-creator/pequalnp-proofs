import json
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-42/sat');ls=(base/'circuit-14-dom.cnf').read_text().splitlines();head=ls[0].split();counter=int(head[2]);extra=[]
vs=json.loads((base/'vars-14.json').read_text());rows=json.loads((base/'rows-14.json').read_text())
def add(xs):extra.append(' '.join(map(str,xs))+' 0')
for k in range(13,27):
 sets={(t,d):[] for t in [0,1] for d in [0,1]}
 for r,(p,t) in enumerate(rows):
  a=vs[f'av{k}_{r}'];b=vs[f'bv{k}_{r}'];counter+=1;x=counter;counter+=1;y=counter
  sets[t,0].append(x);sets[t,1].append(y)
  add([-x,a]);add([-x,-b]);add([-y,-a]);add([-y,b])
 for d in [0,1]:
  add([-vs[f'o{k}']]+sets[1,d]);add([vs[f'o{k}']]+sets[0,d])
head[2]=str(counter);head[3]=str(int(head[3])+len(extra));(base/'circuit-14-useful.cnf').write_text(' '.join(head)+'\n'+'\n'.join(ls[1:]+extra)+'\n');print('variables',counter,'extra clauses',len(extra))
