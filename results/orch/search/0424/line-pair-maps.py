import itertools
import json
from pathlib import Path

HERE=Path('/tmp/oec/pequalnp-pilot-21/search')
lines=[frozenset((w+i)%13 for i in (0,1,3,9)) for w in range(13)]
pairline={frozenset((p,q)):w for w,L in enumerate(lines) for p,q in itertools.combinations(L,2)}
linemeet={frozenset((i,j)):next(iter(lines[i]&lines[j])) for i,j in itertools.combinations(range(13),2)}
def quadrangle(points):
 return all(pairline[frozenset((a,b))]!=pairline[frozenset((a,c))] for a,b,c in itertools.combinations(points,3))
source=next(q for q in itertools.permutations(range(13),4) if quadrangle(q))
maps={};count=0
for target in itertools.permutations(range(13),4):
 if not quadrangle(target):continue
 pm=dict(zip(source,target));lm={}
 for _ in range(13):
  for p,q in itertools.combinations(list(pm),2):
   a=pairline[frozenset((p,q))];b=pairline[frozenset((pm[p],pm[q]))]
   if a in lm:assert lm[a]==b
   lm[a]=b
  for i,j in itertools.combinations(list(lm),2):
   a=linemeet[frozenset((i,j))];b=linemeet[frozenset((lm[i],lm[j]))]
   if a in pm:assert pm[a]==b
   pm[a]=b
  if len(pm)==len(lm)==13:break
 assert len(pm)==len(lm)==13
 assert len(set(pm.values()))==len(set(lm.values()))==13
 assert all(frozenset(pm[p] for p in lines[i])==lines[lm[i]] for i in range(13))
 inverse=[next(j for j in range(13) if pm[j]==i) for i in range(13)]
 maps.setdefault(f'{lm[0]},{lm[1]}',inverse)
 count+=1
assert len(maps)==156
for key,perm in maps.items():
 a,b=map(int,key.split(','))
 assert sorted(perm)==list(range(13))
 assert frozenset(perm[p] for p in lines[a])==lines[0]
 assert frozenset(perm[p] for p in lines[b])==lines[1]
 assert {frozenset(perm[p] for p in L) for L in lines}==set(lines)
(HERE/'line-pair-maps.json').write_text(json.dumps(maps,sort_keys=True)+'\n')
print(json.dumps({'automorphisms_checked':count,'ordered_line_pairs':len(maps),'normal_target_labels':[0,1]},indent=2))
