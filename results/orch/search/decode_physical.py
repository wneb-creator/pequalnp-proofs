import sys,json
from pathlib import Path
base=Path(sys.argv[1]);m=json.loads(base.with_suffix('.meta.json').read_text());n,s,A=m['n'],m['s'],m['A'];val=set()
for line in Path(sys.argv[2]).read_text().splitlines():
 if line.startswith('v '):val.update(int(x) for x in line.split()[1:] if int(x)>0)
T=lambda kd,j,a:(kd*(s+1)+j)*A+a+1 in val
phase=[int(T(6,0,i)) for i in range(n+s)];invert=[T(7,0,i) for i in range(n+s)];assert not any(phase[:n]);assert sum(invert)<=m['inversion_budget']
params=[(1,1,0),(1,0,0),(0,1,0),(0,0,0),(1,1,1),(1,0,1),(0,1,1),(0,0,1)]
cir=[];wire={i:i for i in range(n)};comp={}
def add(op,ins):cir.append((op,ins));return n+len(cir)-1
for i in range(n):
 if invert[i]:comp[i]=add('not',[wire[i]])
for j in range(s):
 op=next(a for a in range(8) if T(0,j,a));a=next(a for a in range(n+j) if T(1,j,a));b=next(a for a in range(n+j) if T(2,j,a));ca,cb,co=params[op]
 na=phase[a]^ca^co^phase[n+j];nb=phase[b]^cb^co^phase[n+j]
 aa=comp[a] if na else wire[a];bb=comp[b] if nb else wire[b]
 wire[n+j]=add('or' if co^phase[n+j] else 'and',[aa,bb])
 if invert[n+j]:comp[n+j]=add('not',[wire[n+j]])
out=comp[n+s-1] if phase[-1] else wire[n+s-1]
bad=[]
for r in range(1<<n):
 w=[bool(r>>i&1) for i in range(n)]
 for op,ins in cir:
  vs=[w[i] for i in ins];w.append(not vs[0] if op=='not' else all(vs) if op=='and' else any(vs))
 want=any((r>>a&1) and (r>>b&1) for a,b in m['edges'])
 if w[out]!=want:bad.append(r)
r={'n':n,'gates':cir,'output':out,'not_count':sum(invert),'bad_rows':bad}
base.with_suffix('.physical.json').write_text(json.dumps(r,indent=2)+'\n')
print('physical gates',len(cir),'NOTs',sum(invert),'bad_count',len(bad),'first_bad',bad[:20]);print('gates',cir,'output',out)
