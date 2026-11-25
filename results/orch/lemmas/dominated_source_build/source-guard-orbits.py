from itertools import permutations
from pathlib import Path
import json
edges={(min(a,b),max(a,b)) for a,b in [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]}
adj=lambda a,b:(min(a,b),max(a,b)) in edges
maps=[]
def extend(prefix,unused):
 i=len(prefix)
 if i==10:
  maps.append(tuple(prefix))
  return
 for j in unused:
  if all(adj(i,k)==adj(j,prefix[k]) for k in range(i)):
   extend(prefix+[j],unused-{j})
extend([],set(range(10)))
stab=[p for p in maps if {p[0],p[1]}=={0,1}]
masks={50,69,104,116,138,201,208,276,385,402,521,548,554,770,773}
def move(mask,p):
 return sum(1<<p[i] for i in range(10) if mask>>i&1)
orbits=[]
while masks:
 m=min(masks)
 orbit=sorted({move(m,p) for p in stab})
 assert set(orbit)<=masks
 masks-=set(orbit)
 orbits.append(orbit)
result={'automorphisms':len(maps),'unordered_edge_stabilizer':len(stab),'orbits':orbits,'representatives':[o[0] for o in orbits],'stabilizer_maps':stab,'status':'computed, not Lean-checked'}
print(json.dumps(result,indent=2))
Path(__file__).with_name('source-guard-orbits.json').write_text(json.dumps(result,indent=2)+'\n')
