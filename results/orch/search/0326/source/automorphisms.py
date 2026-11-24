import itertools,json,pathlib
lines=[frozenset((w+i)%13 for i in (0,1,3,9)) for w in range(13)]
pairline={frozenset((p,q)):w for w,L in enumerate(lines) for p,q in itertools.combinations(L,2)}
linemeet={frozenset((i,j)):next(iter(lines[i]&lines[j])) for i,j in itertools.combinations(range(13),2)}
def quadrangle(p):return all(len({pairline[frozenset((a,b))],pairline[frozenset((a,c))]})==2 for a,b,c in itertools.combinations(p,3))
source=next(q for q in itertools.permutations(range(13),4) if quadrangle(q))
autos=[];pointpairs=set();pairmaps={};fanoutmaps={}
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
 assert len(pm)==len(lm)==13 and len(set(pm.values()))==len(set(lm.values()))==13
 assert all(frozenset(pm[p] for p in lines[i])==lines[lm[i]] for i in range(13))
 autos.append(tuple(lm[i] for i in range(13)));pointpairs.add((pm[0],pm[1]))
 inverse=[next(j for j in range(13) if pm[j]==i) for i in range(13)]
 pairmaps.setdefault(f'{pm[0]},{pm[1]}',inverse)
 for case,(a,b) in enumerate([(0,1),(1,3),(1,2)]):
  u,v=sorted([pm[a],pm[b]])
  fanoutmaps.setdefault(f'{pm[0]},{u},{v}',{'case':case,'perm':inverse})
summary={'automorphisms':len(autos),'ordered_point_pair_orbit':len(pointpairs),'source_quadrangle':source,'orbits':{}}
for size in (3,4,5):
 unseen=set(itertools.combinations(range(13),size));orbits=[]
 while unseen:
  rep=min(unseen);orb={tuple(sorted(a[i] for i in rep)) for a in autos}
  assert orb<=unseen
  unseen-=orb;orbits.append({'representative':rep,'size':len(orb)})
 summary['orbits'][size]=orbits
print(json.dumps(summary,indent=2))
pathlib.Path('/tmp/oec/pequalnp-pilot-21/search/automorphisms.json').write_text(json.dumps(summary,indent=2)+'\n')

pathlib.Path('/tmp/oec/pequalnp-pilot-21/search/point-pair-maps.json').write_text(json.dumps(pairmaps,sort_keys=True)+'\n')

pathlib.Path('/tmp/oec/pequalnp-pilot-21/search/fanout-stabilizer-maps.json').write_text(json.dumps(fanoutmaps,sort_keys=True)+'\n')
