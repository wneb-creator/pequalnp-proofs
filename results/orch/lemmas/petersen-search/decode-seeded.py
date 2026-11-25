from pathlib import Path
import json,sys
p=Path(sys.argv[1]);text=p.read_text()
status=[s for s in text.splitlines() if s.startswith('s ')]
print('status',status)
if 's SATISFIABLE' not in status:raise SystemExit(0)
M=set(int(v) for row in text.splitlines() if row.startswith('v ') for v in row.split()[1:] if int(v)>0)
n=11;s=18;A=1024+n+s+2
ix=lambda kd,j,a:(kd*(s+1)+j)*A+a+1
g=[]
for j in range(s):
 op=next(o for o in range(4) if ix(0,j,o) in M)
 a=next(k for k in range(n+j+1) if ix(1,j,k) in M)
 b=next(k for k in range(n+j+1) if ix(2,j,k) in M)
 g.append((op,a,b))
o=next(k for k in range(n+s+1) if ix(6,0,k) in M)
E=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
fp=[];fn=[]
for x in range(1024):
 w=[bool(x>>i&1) for i in range(10)];w.append(w[0] and w[2])
 for op,a,b in g:
  va=w[a] if a<len(w) else False;vb=w[b] if b<len(w) else False
  w.append((va and vb) if op==0 else (va or vb) if op==1 else True if op==2 else not va)
 y=w[o] if o<len(w) else False
 f=any(w[a] and w[b] for a,b in E)
 if y and not f:fp.append(x)
 if not y and f:fn.append(x)
result={'gates':g,'output':o,'false_positives':fp,'false_negatives':fn}
p.with_suffix('.witness.json').write_text(json.dumps(result,indent=2))
print('gates',g,'output',o,'false_positive_count',len(fp),'false_negative_count',len(fn))
