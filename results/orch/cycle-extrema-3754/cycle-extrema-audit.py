import json
from pathlib import Path
answers=[]
for n in [6,8,10,12]:
 edges=[(i,(i+1)%n) for i in range(n)]
 def target(x):return any(x>>a&1 and x>>b&1 for a,b in edges)
 maxima=[x for x in range(1<<n) if not target(x) and all(x>>i&1 or target(x|(1<<i)) for i in range(n))]
 assert all(sum(bool(x>>a&1 and x>>b&1) for a,b in edges)<=x.bit_count() for x in range(1<<n))
 neighbors=[{(i-1)%n,(i+1)%n} for i in range(n)]
 assert all(len(neighbors[a]&neighbors[b])<=1 for a in range(n) for b in range(a))
 assert all(a%2!=b%2 for a,b in edges)
 answers.append(dict(n=n,edges=edges,maximal_false_count=len(maxima),maximal_false_masks=maxima,all_induced_edge_le_vertex=True,bipartite=True,no_four_cycle=True,assignments_checked=1<<n))
print(json.dumps(answers,indent=2))
