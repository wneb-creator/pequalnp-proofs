import sys,json,itertools
from pathlib import Path
base=Path(sys.argv[1]);limit=int(sys.argv[2]);out=Path(sys.argv[3]);m=json.loads(base.with_suffix('.meta.json').read_text());n,s,A=m['n'],m['s'],m['A'];ix=lambda kd,j,a:(kd*(s+1)+j)*A+a+1
phase=lambda a:ix(6,0,a);invert=lambda a:ix(7,0,a)
F=[]
for a in range(n):F.append([-phase(a)])
F.append([invert(n+s-1),-phase(n+s-1)])
for cs in itertools.combinations(range(n+s),limit+1):F.append([-invert(a) for a in cs])
params=[(1,1,0),(1,0,0),(0,1,0),(0,0,0),(1,1,1),(1,0,1),(0,1,1),(0,0,1)]
for j in range(s):
 for sd in [1,2]:
  for k in range(n+j):
   for op,ps in enumerate(params):
    parity=ps[sd-1]^ps[2];prefix=[-ix(sd,j,k),-ix(0,j,op),invert(k)];a,b=phase(k),phase(n+j)
    if parity:F.extend([prefix+[a,b],prefix+[-a,-b]])
    else:F.extend([prefix+[a,-b],prefix+[-a,b]])
ls=base.read_text().splitlines();h=ls[0].split();out.write_text(f'p cnf {8*(s+1)*A} {int(h[3])+len(F)}\n'+'\n'.join(ls[1:])+'\n'+''.join(' '.join(map(str,c))+' 0\n' for c in F));m['inversion_budget']=limit;out.with_suffix('.meta.json').write_text(json.dumps(m)+'\n');print('extra_clauses',len(F),'total',int(h[3])+len(F))
