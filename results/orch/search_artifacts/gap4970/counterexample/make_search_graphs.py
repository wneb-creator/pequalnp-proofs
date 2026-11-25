import itertools
import json
from pathlib import Path

P=Path(__file__).resolve().parent/'stochastic'
P.mkdir(exist_ok=True)
graphs=[]
graphs.append(('subk4',4,6,[(v,4+j) for j,e in enumerate(itertools.combinations(range(4),2)) for v in e]))
blocks=[(0,1,2),(0,3,4),(1,3),(1,4),(2,3),(2,4)]
graphs.append(('irregular11',5,6,[(v,5+j) for j,b in enumerate(blocks) for v in b]))
fano=[(v,l) for l in range(7) for v in range(7) if (v-l)%7 in (0,1,3)]
for gone_line in (0,2):
    left=[v for v in range(7) if v!=0];right=[l for l in range(7) if l!=gone_line]
    es=[(left.index(v),6+right.index(l)) for v,l in fano if v in left and l in right]
    graphs.append(('fano_minus_'+('incident' if gone_line==0 else 'nonincident'),6,6,es))
raw=[(i,(i+1)%8) for i in range(8)]+[(8+i,8+(i+3)%8) for i in range(8)]+[(i,8+i) for i in range(8)]
left=[0,2,4,6,9,11,13,15];right=[i for i in range(16) if i not in left]
edges=[]
for a,b in raw:
    if a not in left:a,b=b,a
    assert a in left and b in right
    edges.append((left.index(a),8+right.index(b)))
graphs.append(('cubic16',8,8,edges))
report=[]
for name,p,l,edges in graphs:
    n=p+l;edges=sorted(set(edges));adj=[set() for _ in range(n)]
    for a,b in edges:adj[a].add(b);adj[b].add(a)
    assert all(len(adj[i])>=2 for i in range(p))
    assert all(len(adj[a]&adj[b])<=1 for a,b in itertools.combinations(range(n),2))
    covers=[r for r in range(1<<n) if all((r>>a&1) or (r>>b&1) for a,b in edges)]
    tau=min(map(int.bit_count,covers));assert tau==p
    target=lambda r:any((r>>a&1) and (r>>b&1) for a,b in edges)
    ind=[r for r in range(1<<n) if not target(r)]
    mis=[r for r in ind if all(target(r|(1<<i)) for i in range(n) if not r>>i&1)]
    stars={sum(1<<v for v in sub) for ns in adj for k in range(2,len(ns)+1) for sub in itertools.combinations(ns,k)}
    rows=set(mis)|{(1<<a)|(1<<b) for a,b in edges}|{((1<<n)-1)^q for q in stars}
    assert len(rows)<=256
    with (P/(name+'.dat')).open('w') as f:
        f.write(f'{n} {p} {len(edges)} {len(edges)+tau-1}\n')
        for a,b in edges:f.write(f'{a} {b}\n')
    info={'name':name,'n':n,'p':p,'l':l,'edges':edges,'tau':tau,'bound':len(edges)+tau-1,'target_gates':len(edges)+tau-2,'independent_sets':len(ind),'maximal_independent_sets':len(mis),'star_supports':len(stars),'evaluation_rows':len(rows),'no_four_cycle':True}
    (P/(name+'.json')).write_text(json.dumps(info,indent=2)+'\n');report.append(info)
(P/'graphs.json').write_text(json.dumps(report,indent=2)+'\n')
for g in report:print(g['name'],'n',g['n'],'edges',len(g['edges']),'tau',g['tau'],'target',g['target_gates'],'rows',g['evaluation_rows'])
