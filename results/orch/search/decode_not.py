import sys,json
from pathlib import Path
n,s=10,19; A=(1<<n)+n+s+2
p=Path(sys.argv[1]); val=set()
for line in p.read_text().splitlines():
 if line.startswith('v '): val.update(int(x) for x in line.split()[1:] if int(x)>0)
def T(k,j,a):return (k*(s+1)+j)*A+a+1 in val
cir=[]
for j in range(s):
 ops=[a for a in range(4) if T(0,j,a)];aa=[a for a in range(n+j+1) if T(1,j,a)];bb=[a for a in range(n+j+1) if T(2,j,a)]
 assert ops and aa and bb,(j,ops,aa,bb)
 op=3 if 3 in ops else ops[0]
 cir.append((op,aa[0],bb[0]))
out=next(a for a in range(n+s+1) if T(6,0,a))
edges=[(i,(i+1)%5) for i in range(5)]+[(i,i+5) for i in range(5)]+[(5,7),(7,9),(9,6),(6,8),(8,5)]
bad=[]
for r in range(1<<n):
 w=[bool(r>>i&1) for i in range(n)]
 for op,a,b in cir:
  va=w[a] if a<len(w) else False;vb=w[b] if b<len(w) else False
  w.append(va and vb if op==0 else va or vb if op==1 else True if op==2 else not va)
 got=w[out] if out<len(w) else False;want=any((r>>a&1) and (r>>b&1) for a,b in edges)
 if got!=want:bad.append(r)
r={'gates':cir,'out':out,'bad_rows':bad,'nots':sum(op==3 for op,a,b in cir)}
p.with_suffix('.decoded.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2))
