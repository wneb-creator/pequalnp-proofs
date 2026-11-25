import sys,json
from pathlib import Path
base=Path(sys.argv[1]);m=json.loads(base.with_suffix('.meta.json').read_text());n,s,A=m['n'],m['s'],m['A'];val=set()
for line in Path(sys.argv[2]).read_text().splitlines():
 if line.startswith('v '):val.update(int(x) for x in line.split()[1:] if int(x)>0)
T=lambda kd,j,a:(kd*(s+1)+j)*A+a+1 in val
cir=[]
for j in range(s):
 op=next(a for a in range(8) if T(0,j,a));a=next(a for a in range(n+j) if T(1,j,a));b=next(a for a in range(n+j) if T(2,j,a));cir.append((m['ops'][op],a,b))
bad=[]
for r in range(1<<n):
 w=[bool(r>>i&1) for i in range(n)]
 for mask,a,b in cir:w.append(bool(mask>>(2*w[a]+w[b])&1))
 want=any((r>>a&1) and (r>>b&1) for a,b in m['edges'])
 if w[-1]!=want:bad.append(r)
r={'gates':cir,'bad_rows':bad,'n':n,'s':s}
base.with_suffix('.decoded.json').write_text(json.dumps(r,indent=2)+'\n')
print('failure_count',len(bad),'first',bad[:20]);print('gates',cir)
