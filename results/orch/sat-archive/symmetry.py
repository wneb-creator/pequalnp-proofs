import itertools,json
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-42/sat')
edges=[(0,3),(2,3),(1,2),(1,3),(0,2),(0,1)]
matchings=[frozenset([4,6]),frozenset([5,9]),frozenset([7,8])]
perms=[]
for p in itertools.permutations(range(4)):
 q=list(p)
 q += [4+edges.index(tuple(sorted((p[a],p[b])))) for a,b in edges]
 q += [10+matchings.index(frozenset(q[x] for x in m)) for m in matchings]
 perms.append(q)
reps=set()
for a in range(13):
 for b in range(a+1,13):
  orbit=[tuple(sorted([q[a],q[b]])) for q in perms]
  reps.add(min(orbit,key=lambda z:(z[1],z[0])))
print('representatives',sorted(reps,key=lambda z:(z[1],z[0])))
vs=json.loads((base/'vars-14.json').read_text())
extra=[]
for a in range(12):
 for b in range(a+1,13):
  if (a,b) not in reps:extra.append(f'-{vs[f"a13_{a}"]} -{vs[f"b13_{b}"]} 0')
ls=(base/'circuit-14.cnf').read_text().splitlines();head=ls[0].split();head[-1]=str(int(head[-1])+len(extra))
(base/'circuit-14-sym.cnf').write_text(' '.join(head)+'\n'+'\n'.join(ls[1:]+extra)+'\n')
