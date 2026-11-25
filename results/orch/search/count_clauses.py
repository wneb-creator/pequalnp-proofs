from pathlib import Path
from itertools import combinations
import sys
p=Path(sys.argv[1]);ls=p.read_text().splitlines();h=ls[0].split();s=19;A=1055
v=[j*A+4 for j in range(19)]
for num in [1,2,3,4]:
 extra=[]
 for vs in combinations(v,num+1):extra.append(' '.join(str(-x) for x in vs)+' 0')
 for vs in combinations(v,19-num+1):extra.append(' '.join(map(str,vs))+' 0')
 q=p.with_name(p.stem+f'-n{num}.cnf');q.write_text(f'p cnf {h[2]} {int(h[3])+len(extra)}\n'+'\n'.join(ls[1:]+extra)+'\n')
 print(q.name,int(h[3])+len(extra))
