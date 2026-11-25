import json
from pathlib import Path
prefix='/tmp/oec/pequalnp-pilot-157/sat_full_subK4_14'
d=json.loads(Path(prefix+'.map.json').read_text());n=d['p']+d['l'];cs=[];nv=d['variables']
for j in range(1,d['k']):
 dep=d['sel'][j][1][-1];prev=d['ops'][j-1];cur=d['ops'][j]
 cs.append([dep,-prev,cur])
 aa=d['sel'][j-1][0];bb=d['sel'][j][0]
 nv+=1;eq=nv
 for a,b in zip(aa,bb):
  cs.extend([[-a,-b,eq],[-eq,-a,b],[-eq,-b,a]])
 cs.append([-eq,-bb[-1]])
 for i in range(n+j-1):
  for h in range(i):
   for guard in ([prev,cur],[-prev,-cur]):
    cs.append([dep,*guard,-aa[i],-bb[h]])
    cs.append([dep,*guard,-eq,-d['sel'][j-1][1][i],-d['sel'][j][1][h]])
lines=Path(prefix+'.cnf').read_text().splitlines();head=lines[0].split();head[2]=str(nv);head[3]=str(int(head[3])+len(cs))
Path(prefix+'.ordered.cnf').write_text(' '.join(head)+'\n'+'\n'.join(lines[1:])+'\n'+''.join(' '.join(map(str,c))+' 0\n' for c in cs))
print('Added independent-adjacent gate-order clauses:',len(cs),'variables:',nv)
