import json,itertools,collections,sys
from pathlib import Path
p=int(sys.argv[1]);base=Path('/tmp/oec/pequalnp-pilot-78/finitefield')
planes=json.loads((base/f'f{p}-2planes.json').read_text())
ijs=[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)];index={pair:i for i,pair in enumerate(ijs)}
diag=[0,4,7,9]
def norm(v):
 v=[x%p for x in v];k=next(i for i,x in enumerate(v) if x);r=pow(v[k],-1,p);return tuple(x*r%p for x in v)
def canon(v):
 return min(norm([v[index[tuple(sorted((s[i],s[j])))]] for i,j in ijs]) for s in itertools.permutations(range(4)))
bykernel=collections.Counter();orbits=collections.defaultdict(set)
for a,b in planes:
 i=next((i for i in diag if a[i] or b[i]),None)
 if i is None:continue
 h=[(b[i]*x-a[i]*y)%p for x,y in zip(a,b)]
 if any(h[j] for j in diag):continue
 hn=norm(h);hc=canon(hn);bykernel[hc]+=1;orbits[hc].add(hn)
for h,n in bykernel.items():print('kernel orbit',h,'planes',n,'distinct kernels',len(orbits[h]))
