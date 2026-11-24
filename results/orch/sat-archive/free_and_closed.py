import json
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-42/sat');ls=(base/'free-and-10.cnf').read_text().splitlines();head=ls[0].split();counter=int(head[2]);extra=[]
ns=json.loads((base/'free-and-vars-10.json').read_text());rows=json.loads((base/'rows-14.json').read_text())
def add(xs):extra.append(' '.join(map(str,xs))+' 0')
for k in range(11):
 for arg in ([0,1] if k<10 else [0]):
  for j in range(14+k):
   s=ns[f's{k}_{arg}_{j}'];w=[]
   for r,(p,t) in enumerate(rows):
    if not t:continue
    operand=ns[f'm{k}_{arg}_{r}']
    if j<14:
     val=False if j==13 else bool(p>>j&1)
     if not val:w.append(operand)
    else:
     val=ns[f'v{j-14}_{r}'];counter+=1;bad=counter;w.append(bad)
     add([-bad,operand]);add([-bad,-val])
   add([s]+w)
head[2]=str(counter);head[3]=str(int(head[3])+len(extra));(base/'free-and-10-closed.cnf').write_text(' '.join(head)+'\n'+'\n'.join(ls[1:]+extra)+'\n');print('variables',counter,'extra clauses',len(extra))
