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
 autos.append((tuple(pm[i] for i in range(13)),tuple(lm[i] for i in range(13))));pointpairs.add((pm[0],pm[1]))
 inverse=[next(j for j in range(13) if pm[j]==i) for i in range(13)]
 pairmaps.setdefault(f'{pm[0]},{pm[1]}',inverse)
 for case,(a,b) in enumerate([(0,1),(1,3),(1,2)]):
  u,v=sorted([pm[a],pm[b]])
  fanoutmaps.setdefault(f'{pm[0]},{u},{v}',{'case':case,'perm':inverse})

reps=[(0,1,2,3,4),(0,1,2,3,7),(0,1,2,3,9)]
certificates={}
for pointmap,linemap in autos:
 inverse=[pointmap.index(p) for p in range(13)]
 for representative in reps:
  image=tuple(sorted(linemap[w] for w in representative))
  key=','.join(map(str,image))
  certificates.setdefault(key,{'representative':list(representative),'point_map':inverse})
assert set(certificates)=={','.join(map(str,x)) for x in itertools.combinations(range(13),5)}
counts={','.join(map(str,r)):0 for r in reps}
for key,item in certificates.items():
 subset=list(map(int,key.split(',')));permutation=item['point_map'];representative=item['representative']
 assert sorted(permutation)==list(range(13))
 images=[frozenset(permutation[p] for p in line) for line in lines]
 assert set(images)==set(lines)
 assert {images[w] for w in subset}=={lines[w] for w in representative}
 counts[','.join(map(str,representative))]+=1
base=pathlib.Path('/tmp/oec/pequalnp-pilot-21/search')
with (base/'five-line-orbit-maps.json').open('x') as output:output.write(json.dumps(certificates,sort_keys=True)+'\n')
report={'automorphisms':len(autos),'covered_subsets':len(certificates),'orbit_sizes':counts,'all_point_maps_directly_verified':True,'scope':'finite input/output symmetry certificate, not a circuit lower bound'}
(base/'five-line-orbit-maps-summary.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
