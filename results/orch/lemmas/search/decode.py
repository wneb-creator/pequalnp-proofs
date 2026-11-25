import re,json,sys
from pathlib import Path
p=Path(sys.argv[1]); text=p.read_text()
status=[r for r in text.splitlines() if r.startswith('s ')]
print('status',status)
if 's SATISFIABLE' not in status: raise SystemExit(0)
M=set(int(v) for row in text.splitlines() if row.startswith('v ') for v in row.split()[1:] if int(v)>0)
n=7;s=13;A=2**n+n+s+1
ix=lambda kd,j,a:(kd*(s+1)+j)*A+a+1
g=[]
for j in range(s):
 op=next(o for o in range(3) if ix(0,j,o) in M)
 a=next(k for k in range(n+j+1) if ix(1,j,k) in M)
 b=next(k for k in range(n+j+1) if ix(2,j,k) in M)
 g.append((op,a,b))
o=next(k for k in range(n+s+1) if ix(6,0,k) in M)
E=[(0,2),(1,3),(0,4),(1,4),(2,4),(0,5),(1,5),(3,5),(0,6),(2,6),(3,6),(5,6)]
err=[]
for x in range(2**n):
 w=[bool(x>>i&1) for i in range(n)]
 for op,a,b in g:
  va=w[a] if a<len(w) else False;vb=w[b] if b<len(w) else False
  w.append((va and vb) if op==0 else (va or vb) if op==1 else True)
 y=w[o] if o<len(w) else False
 f=any(w[a] and w[b] for a,b in E)
 if y!=f:err.append(x)
print('gates',g,'output',o,'errors',err)
p.with_suffix('.witness.json').write_text(json.dumps({'gates':g,'output':o,'errors':err},indent=2))
