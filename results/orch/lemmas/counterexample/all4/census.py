from itertools import permutations, combinations
from pathlib import Path
import json
N=4; perms=list(permutations(range(N)))
perm_bits=[[sum(1<<p[i] for i in range(N)if m>>i&1)for m in range(1<<N)]for p in perms]
def canon(rows):
 forms=[]
 cols=tuple(sum(1<<i for i in range(N)if rows[i]>>j&1)for j in range(N))
 for bits in perm_bits:
  forms.append(tuple(sorted(bits[r]for r in rows)))
  forms.append(tuple(sorted(bits[c]for c in cols)))
 return min(forms)
def getprops(rows):
 edges=[(i,j)for i in range(N)for j in range(N)if rows[i]>>j&1]
 active=set(i for i,j in edges)|set(N+j for i,j in edges);seen=set();components=0
 while active-seen:
  todo=[next(iter(active-seen))];components+=1
  while todo:
   v=todo.pop()
   if v in seen:continue
   seen.add(v)
   todo.extend((N+j if v==i else i)for i,j in edges if v==i or v==N+j)
 tau=min((m.bit_count(),m)for m in range(1<<(2*N))if all((m>>i&1)or(m>>(N+j)&1)for i,j in edges))
 degrees=[sum(i==v or N+j==v for i,j in edges)for v in range(2*N)]
 return {'rows':rows,'edges':edges,'edge_count':len(edges),'active_vertices':len(active),'components':components,'cycle_rank':len(edges)-len(active)+components,'hubs':sum(d>=3 for d in degrees),'degrees':degrees,'vertex_cover_size':tau[0],'vertex_cover_mask':tau[1],'clean_upper':len(edges)+tau[0]-1 if edges else 0}
classes={};matrices=0
for mask in range(1<<(N*N)):
 rows=tuple((mask>>(N*i))&((1<<N)-1)for i in range(N))
 if any((rows[i]&rows[j]).bit_count()>1 for i,j in combinations(range(N),2)):continue
 matrices+=1;key=canon(rows);classes[key]=classes.get(key,0)+1
out=[]
for rows,count in classes.items():
 d=getprops(rows);d['orbit_size']=count;d['id']='g'+str(sum(r<<(N*i)for i,r in enumerate(rows)));out.append(d)
out.sort(key=lambda d:(-int(d['components']==1 and d['active_vertices']==8),-d['cycle_rank'],-d['hubs'],-d['edge_count'],d['id']))
p=Path(__file__).resolve().parent;(p/'classes.json').write_text(json.dumps({'N':N,'matrices':matrices,'classes':out},indent=2)+'\n')
print('matrices',matrices,'classes',len(out),'connected_spanning',sum(d['components']==1 and d['active_vertices']==8 for d in out))
for d in out:
 if d['components']==1 and d['active_vertices']==8:print(d['id'],d['rows'],'E',d['edge_count'],'hubs',d['hubs'],'rank',d['cycle_rank'],'upper',d['clean_upper'])
