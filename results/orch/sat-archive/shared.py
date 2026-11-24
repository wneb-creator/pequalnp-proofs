import json,itertools
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-42/sat');ls=(base/'circuit-14-irr.cnf').read_text().splitlines();head=ls[0].split();counter=int(head[2]);extra=[];pairs=[]
vs=json.loads((base/'vars-14.json').read_text())
for k in range(13,26):
 for j,l in itertools.combinations(range(k+1,27),2):
  counter+=1;pairs.append(counter)
  for h in [j,l]:
   refs=[vs[f'b{h}_{k}']]
   if k<h-1:refs.append(vs[f'a{h}_{k}'])
   extra.append(' '.join(map(str,[-counter]+refs))+' 0')
extra.append(' '.join(map(str,pairs))+' 0');head[2]=str(counter);head[3]=str(int(head[3])+len(extra))
(base/'circuit-14-share.cnf').write_text(' '.join(head)+'\n'+'\n'.join(ls[1:]+extra)+'\n');print('extra clauses',len(extra))
