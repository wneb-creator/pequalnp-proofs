import argparse,itertools,json
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('prefix');ap.add_argument('--pin-control',action='store_true');args=ap.parse_args();prefix=args.prefix
d=json.loads(Path(prefix+'.map.json').read_text());p=d['p'];l=d['l'];n=p+l;cs=[];nv=d['variables']
for j in range(1,d['k']):
 dep=d['sel'][j][1][-1];prev=d['ops'][j-1];cur=d['ops'][j];cs.append([dep,-prev,cur])
 aa=d['sel'][j-1][0];bb=d['sel'][j][0];nv+=1;eq=nv
 for a,b in zip(aa,bb):cs.extend([[-a,-b,eq],[-eq,-a,b],[-eq,-b,a]])
 cs.append([-eq,-bb[-1]])
 for i in range(n+j-1):
  for h in range(i):
   for guard in ([prev,cur],[-prev,-cur]):
    cs.append([dep,*guard,-aa[i],-bb[h]])
    cs.append([dep,*guard,-eq,-d['sel'][j-1][1][i],-d['sel'][j][1][h]])
lines=[frozenset(a for a,b in d['edges'] if b==j) for j in range(l)];lineids={s:i for i,s in enumerate(lines)};perms=[];E=set(map(tuple,d['edges']))
for pp in itertools.permutations(range(p)):
 images=[frozenset(pp[a] for a in line) for line in lines]
 if not all(s in lineids for s in images):continue
 perm=tuple(pp)+tuple(p+lineids[s] for s in images)
 assert len(set(perm))==n and all((perm[a],perm[p+b]-p) in E for a,b in E)
 perms.append(perm)
seen=set();reps=[]
for a in range(n):
 for b in range(a,n):
  if (a,b) in seen:continue
  orbit={tuple(sorted((perm[a],perm[b]))) for perm in perms};seen|=orbit;reps.append(min(orbit))
assert len(seen)==n*(n+1)//2
choices=[]
for a,b in reps:nv+=1;choices.append(nv);cs.append([-nv,d['sel'][0][0][a]]);cs.append([-nv,d['sel'][0][1][b]])
cs.append(choices)
raw=Path(prefix+'.cnf').read_text().splitlines();head=raw[0].split();head[2]=str(nv);head[3]=str(int(head[3])+len(cs));body='\n'.join(raw[1:])+'\n'+''.join(' '.join(map(str,c))+' 0\n' for c in cs)
Path(prefix+'.sym.cnf').write_text(' '.join(head)+'\n'+body)
Path(prefix+'.sym.json').write_text(json.dumps(dict(automorphisms=perms,first_pair_representatives=reps,pair_configurations=len(seen),new_clauses=len(cs),variables=nv)))
print('automorphisms',len(perms),'first_pair_orbits',len(reps),'new_clauses',len(cs),'variables',nv)
if args.pin_control:
 gates=[];terms=[]
 for a in range(p):
  nb=[p+b for aa,b in d['edges'] if aa==a];r=nb[0]
  for b in nb[1:]:gates.append((1,r,b));r=n+len(gates)-1
  gates.append((0,a,r));terms.append(n+len(gates)-1)
 r=terms[0]
 for t in terms[1:]:gates.append((1,r,t));r=n+len(gates)-1
 assert len(gates)==d['k'];originalout=r
 def canonical(perm):
  mp=dict(enumerate(perm));left=set(range(len(gates)));gs=[]
  while left:
   ready=[]
   for j in left:
    op,a,b=gates[j]
    if a in mp and b in mp:ready.append(((op,*sorted((mp[a],mp[b]))),j))
   key,j=min(ready);gs.append(key);mp[n+j]=n+len(gs)-1;left.remove(j)
  return tuple(gs),mp[originalout]
 cg,out=min(canonical(perm) for perm in perms);assert cg[0][1:] in reps
 units=[]
 for j,(op,a,b) in enumerate(cg):
  units.append(d['ops'][j] if op else -d['ops'][j])
  for side,w in enumerate((a,b)):units.extend(v if i==w else -v for i,v in enumerate(d['sel'][j][side]))
 units.extend(v if n+j==out else -v for j,v in enumerate(d['out']))
 head[3]=str(int(head[3])+len(units));Path(prefix+'.sym.pinned.cnf').write_text(' '.join(head)+'\n'+body+''.join(str(x)+' 0\n' for x in units))
 print('Pinned canonical symmetry control',len(cg),'gates')
