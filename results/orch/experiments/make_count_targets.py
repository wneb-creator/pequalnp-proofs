from pathlib import Path
from itertools import combinations

def build(n,kind):
 edges=list(combinations(range(n),2));atoms=[sum(1<<x for x in range(1<<n) if x>>i&1) for i in range(n)];full=(1<<(1<<n))-1
 rows=[]
 for em in range(1<<len(edges)):
  es=[e for i,e in enumerate(edges) if em>>i&1];E=set(es)
  adj=lambda a,b:tuple(sorted((a,b))) in E
  if any(adj(a,b) and adj(b,c) and adj(c,a) for a,b,c in combinations(range(n),3)):continue
  square=False
  for a,b,c,d in combinations(range(n),4):
   if any(adj(p,q) and adj(q,r) and adj(r,s) and adj(s,p) for p,q,r,s in [(a,b,c,d),(a,b,d,c),(a,c,b,d)]):square=True;break
  if square:continue
  if kind=='B' and len(es)>4:continue
  t=sum(1<<x for x in range(1<<n) if any((x>>a&1) and (x>>b&1) for a,b in es))
  if kind=='A':
   bound=min(s.bit_count() for s in range(1<<n) if all((s>>a&1) or (s>>b&1) for a,b in es))
  else:
   bound=max(0,len(es)-1)
   t=sum(1<<x for x in range(1<<n) if not(t>>(((1<<n)-1)^x)&1))
  linear=0
  for a in atoms:
   if a&~t==0:linear|=a
  if bound:rows.append((t,bound,linear,em))
 path=Path(f'/tmp/oec/pequalnp-pilot-43/count_targets_{kind}_{n}.txt')
 path.write_text('\n'.join(' '.join(map(str,r)) for r in rows)+'\n')
 print(kind,n,'graphs',len(rows),'max_bound',max(r[1] for r in rows))
build(6,'A');build(5,'B')
