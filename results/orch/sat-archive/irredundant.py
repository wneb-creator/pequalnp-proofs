import json
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-42/sat')
ls=(base/'circuit-14-sym.cnf').read_text().splitlines();head=ls[0].split();counter=int(head[2]);extra=[]
vs=json.loads((base/'vars-14.json').read_text());rows=json.loads((base/'rows-14.json').read_text())
def new():
 global counter
 counter+=1;return counter
def add(xs):extra.append(' '.join(map(str,xs))+' 0')
for k in range(13,27):
 first=[];second=[]
 for r in range(len(rows)):
  a=vs[f'av{k}_{r}'];b=vs[f'bv{k}_{r}'];x=new();y=new()
  first.append(x);second.append(y)
  add([-x,a]);add([-x,-b]);add([-y,-a]);add([-y,b])
 add(first);add(second)
 add([vs[f'v{k}_{r}'] for r,(p,t) in enumerate(rows) if t])
 add([-vs[f'v{k}_{r}'] for r,(p,t) in enumerate(rows) if not t])
head[2]=str(counter);head[3]=str(int(head[3])+len(extra))
(base/'circuit-14-irr.cnf').write_text(' '.join(head)+'\n'+'\n'.join(ls[1:]+extra)+'\n')
print('vars',counter,'extra clauses',len(extra))
