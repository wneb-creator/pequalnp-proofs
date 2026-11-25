from itertools import permutations,combinations
from pathlib import Path
import json
n=4;diag=sum(1<<(4*a+a) for a in range(4));others=[k for k in range(16) if k%5];valid=[]
for t in range(1<<12):
 mask=diag|sum(1<<k for j,k in enumerate(others) if t>>j&1);rows=[(mask>>(4*a))&15 for a in range(4)]
 if all((rows[a]&rows[b]).bit_count()<=1 for a,b in combinations(range(4),2)):valid.append(mask)
perms=list(permutations(range(4)));reps={}
for mask in valid:
 orbit=[]
 for p in perms:
  a=sum(1<<(4*p[i]+p[j]) for i in range(4) for j in range(4) if mask>>(4*i+j)&1);orbit.append(a);orbit.append(sum(1<<(4*j+i) for i in range(4) for j in range(4) if a>>(4*i+j)&1))
 rep=min(orbit);reps.setdefault(rep,[]).append(mask)
out=dict(valid=len(valid),maximum_edges=max(x.bit_count() for x in valid),orbits=[dict(rep=x,edges=x.bit_count(),orbit=len(ys)) for x,ys in sorted(reps.items())]);Path('/tmp/oec/pequalnp-pilot-71/core-counterexample/graph44-orbits.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
