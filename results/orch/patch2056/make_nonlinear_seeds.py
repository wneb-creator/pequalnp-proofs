from pathlib import Path
from itertools import combinations
import json
b=Path(__file__).resolve().parent;d=json.loads((b/'collinear6-data.json').read_text());N=len(d['points']);n=d['inputs'];rows=d['rows'];E=len(d['edges']);target=(1<<E)-1;mask=(1<<len(rows))-1;negative=mask^target
inputs=[sum(((r>>i)&1)<<k for k,r in enumerate(rows)) for i in range(n)]
seeds=[]
for p,q in combinations(range(N),2):
 gs=[]
 def gate(op,a,c):gs.append([op,a,c]);return n+len(gs)-1
 def fold(xs):
  out=xs[0]
  for c in xs[1:]:out=gate(1,out,c)
  return out
 R=fold([c for a,c in d['edges'] if a==p]);S=fold([c for a,c in d['edges'] if a==q])
 pq=gate(1,p,q);RS=gate(1,R,S);pS=gate(1,p,S);qR=gate(1,q,R);a=gate(0,pq,RS);c=gate(0,pS,qR);block=gate(0,a,c)
 roots=[block]
 for r in range(N):
  if r not in (p,q):roots.append(gate(0,r,fold([c for a,c in d['edges'] if a==r])))
 out=fold(roots);vs=inputs[:];clean=[False]*n;P=[v&target if i<N else 0 for i,v in enumerate(inputs)];L=[v&target if i>=N else 0 for i,v in enumerate(inputs)];G=[0]*n;violations=0;dominated=0;uses=[0]*(n+len(gs))
 for op,x,y in gs:
  value=vs[x]|vs[y] if op else vs[x]&vs[y]
  violations+=(clean[x]!=clean[y]) if op else (clean[x] or clean[y])
  dominated+=any((value&target&~av)==0 and (av&negative&~value)==0 for av in vs)
  vs.append(value);clean.append(value&negative==0);P.append(P[x]|P[y] if op else 0);L.append(L[x]|L[y] if op else 0);G.append(G[x]|G[y] if op else (P[x]&L[y])|(L[x]&P[y]));uses[x]+=1;uses[y]+=1
 violations+=sum(max(0,uses[i]-1) for i in range(n,n+len(gs)) if clean[i])
 assert vs[out]==target and len(gs)==33
 seeds.append({'pair':[p,q],'gates':gs,'output':out,'size':len(gs),'normalization_violations':int(violations),'dominated_gates':int(dominated),'accepted_without_read1':(target&~G[out]).bit_count()})
(b/'collinear6-nonlinear-seeds.json').write_text(json.dumps(seeds,indent=2)+'\n')
print(json.dumps({'seeds':len(seeds),'sizes':sorted(set(s['size'] for s in seeds)),'normalization_violations':sorted(set(s['normalization_violations'] for s in seeds)),'dominated_gates':sorted(set(s['dominated_gates'] for s in seeds)),'accepted_without_read1':sorted(set(s['accepted_without_read1'] for s in seeds))}),flush=True)
