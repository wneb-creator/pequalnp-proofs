import itertools,json,time
from pathlib import Path
started=time.monotonic()
n=6
vars=[sum(1<<m for m in range(64) if m>>i&1) for i in range(n)]
ors=[0]*64
for mask in range(1,64):
 b=mask&-mask;ors[mask]=ors[mask^b]|vars[b.bit_length()-1]
first={}
for a in range(64):
 for b in range(a,64):first.setdefault(ors[a]&ors[b],(a,b))
targets={}
for edges in range(512):
 pairs=[(i,3+j) for i in range(3) for j in range(3) if edges>>(3*i+j)&1]
 tt=0
 for a,b in pairs:tt|=vars[a]&vars[b]
 cover=max((len(S) for k in range(4) for S in itertools.combinations(pairs,k) if all(not ((edges>>(3*a+(d-3))&1) and (edges>>(3*c+(b-3))&1)) for (a,b),(c,d) in itertools.combinations(S,2))),default=0)
 targets[tt]=(edges,cover)
found={0:(0,None)}
for g1,ab in first.items():
 if g1 in targets:found.setdefault(g1,(1,ab))
checks=0
for g1,ab in first.items():
 vals=list(set(ors+[v|g1 for v in ors]))
 for a,b in itertools.combinations_with_replacement(vals,2):
  g2=a&b
  for out in (g2,g1|g2):
   if out in targets:found.setdefault(out,(2,ab,a,b))
  checks+=1
bad=[dict(edges=targets[t][0],cover=targets[t][1],witness=v) for t,v in found.items() if t in targets and v[0]<targets[t][1]]
result=dict(graphs=len(targets),first_functions=len(first),second_pairs=checks,found=len(found),counterexamples=bad,elapsed=time.monotonic()-started)
Path('/tmp/oec/pequalnp-pilot-60/and-fooling-small.json').write_text(json.dumps(result,indent=2))
print(json.dumps(result),flush=True)
