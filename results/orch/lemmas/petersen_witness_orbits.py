import json
from itertools import combinations, permutations
from pathlib import Path
E=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
B=[50,69,104,116,138,201,208,276,385,402,521,548,554,770,773]
adj=[[False]*10 for _ in range(10)]
for u,v in E:adj[u][v]=adj[v][u]=True
order=[0,1,4,5,2,6,3,7,8,9]
autos=[]
def visit(p,used):
 if len(p)==10:
  autos.append(tuple(p[i] for i in range(10)));return
 u=order[len(p)]
 for v in range(10):
  if v not in used and all(adj[u][a]==adj[v][b] for a,b in p.items()):
   p[u]=v;visit(p,used|{v});del p[u]
visit({},set())
def move(m,p):return sum(1<<p[i] for i in range(10) if m>>i&1)
def bits(m):return [i for i in range(10) if m>>i&1]
pairs={(1<<u|1<<v,b) for u,v in E for b in B}
remaining=set(pairs);orbits=[]
while remaining:
 rep=min(remaining)
 orbit={(move(rep[0],p),move(rep[1],p)) for p in autos}
 assert orbit<=pairs
 remaining-=orbit
 orbits.append(dict(edge=rep[0],blocker=rep[1],edge_vertices=bits(rep[0]),blocker_vertices=bits(rep[1]),intersection_vertices=bits(rep[0]&rep[1]),size=len(orbit),stabilizer=len(autos)//len(orbit)))
assert len(autos)==120
EM={1<<u|1<<v for u,v in E}
for p in autos:
 assert sorted(p)==list(range(10))
 assert {move(m,p) for m in EM}==EM
 assert {move(m,p) for m in B}==set(B)
labels=list(combinations(range(5),2))
labelsets=[set(a) for a in labels]
embedding={}
def embed(used):
 if len(embedding)==10:return True
 u=order[len(embedding)]
 for v in range(10):
  if v not in used and all(adj[u][a]==labelsets[v].isdisjoint(labelsets[b]) for a,b in embedding.items()):
   embedding[u]=v
   if embed(used|{v}):return True
   del embedding[u]
 return False
assert embed(set())
vertex_label=[labels[embedding[i]] for i in range(10)]
reverse={a:i for i,a in enumerate(vertex_label)}
s5autos={tuple(reverse[tuple(sorted(p[j] for j in vertex_label[i]))] for i in range(10)) for p in permutations(range(5))}
assert s5autos==set(autos)
assert sum(o['size'] for o in orbits)==225
result=dict(automorphisms=len(autos),orbits=orbits,permutations=autos,kneser_labels=vertex_label,independent_s5_validation=True)
Path('/tmp/oec/pequalnp-pilot-99/petersen_witness_orbits.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(automorphisms=len(autos),orbits=orbits),indent=2))
