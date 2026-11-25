import json,itertools
from pathlib import Path
base=Path(__file__).resolve().parent
stats={}
nonpseudo=[]
for m in range(1<<16):
 adj=[{4+j for j in range(4) if m>>(4*i+j)&1} for i in range(4)]
 if any(len(adj[i]&adj[j])>=2 for i in range(4) for j in range(i)):continue
 es=[(i,j) for i in range(4) for j in adj[i]]
 stats[len(es)]=stats.get(len(es),0)+1
 unseen=set(range(8));bad=False
 while unseen:
  comp={unseen.pop()}
  while True:
   nex=comp|{v for e in es if set(e)&comp for v in e}
   if nex==comp:break
   comp=nex
  unseen-=comp
  if sum(a in comp and b in comp for a,b in es)>len(comp):bad=True
 if bad:nonpseudo.append(es)
es=[(0,5),(0,6),(0,7),(1,4),(2,4),(3,4),(1,5),(2,6),(3,7)]
positive=[(1<<a)|(1<<b) for a,b in es]
negative=[m for m in range(256) if not any(m>>a&1 and m>>b&1 for a,b in es)]
maxind=[m for m in negative if all(m>>i&1 or m|(1<<i) not in negative for i in range(8))]
for relaxed in [False,True]:
 rows=positive+(maxind if not relaxed else [0]+[1<<i for i in range(8)]+[ (1<<i)|(1<<j) for i in range(8) for j in range(i) if (j,i) not in es and (i,j) not in es])
 profile={'preds':list(range(8)),'window_budget':15,'and_count':8,'values':[[int(m>>i&1) for i in range(8)] for m in rows],'targets':[int(m in positive) for m in rows],'dx':[0]*8,'dy':[0]*8,'base_channels':[0,0],'graph_edges':es,'assignment_masks':rows,'relaxed':relaxed}
 (base/('theta3-or7-'+('shadow' if relaxed else 'full')+'.profile.json')).write_text(json.dumps(profile,indent=2)+'\n')
print(json.dumps({'C4free_census':stats,'nonpseudoforest_count':len(nonpseudo),'nonpseudo_edge_counts':sorted(set(map(len,nonpseudo))),'all_nonpseudo_degree_multisets':sorted(set(tuple(sorted(sum(v in e for e in g) for v in range(8))) for g in nonpseudo)),'theta3_edges':es,'theta3_maximal_independent':maxind,'theta3_rows':len(positive)+len(maxind)},indent=2))
