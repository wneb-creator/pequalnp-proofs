from collections import deque
from itertools import combinations
from pathlib import Path
import json

dest=Path('results/orch/lemmas')
plane=json.loads((dest/'counterexample_2583_data.json').read_text())
coords=[tuple(v) for v in plane['coordinates']]
lookup={v:i for i,v in enumerate(coords)}
matrices=[[[0,1,0],[1,0,0],[0,0,1]],[[1,0,0],[0,0,1],[0,1,0]],
          [[1,1,0],[0,1,0],[0,0,1]],[[2,0,0],[0,1,0],[0,0,1]]]
def project(M,v):
    u=[sum(a*b for a,b in zip(row,v))%3 for row in M]
    c=pow(next(a for a in u if a),-1,3)
    return tuple(a*c%3 for a in u)
perms=[[lookup[project(M,v)] for v in coords] for M in matrices]
assert all(sorted(p)==list(range(13)) for p in perms)
def action(mask,perm):
    return sum(1<<perm[i] for i in range(13) if mask&(1<<i))
manifest=[]
for k in [4,5,6,7]:
    unseen={sum(1<<i for i in v) for v in combinations(range(13),k)}
    repnum=0
    while unseen:
        representative=min(unseen);orbit={representative};queue=deque([representative])
        while queue:
            v=queue.popleft()
            for perm in perms:
                w=action(v,perm)
                if w not in orbit:orbit.add(w);queue.append(w)
        assert orbit<=unseen
        unseen-=orbit
        points=[p for p in range(13) if representative&(1<<p)]
        lines=[l for l in range(13) if any(plane['incidence_rows'][p][l] for p in points)]
        E=[(i,k+j) for i,p in enumerate(points) for j,l in enumerate(lines) if plane['incidence_rows'][p][l]]
        assert len(E)==4*k
        inc=[[plane['incidence_rows'][p][l] for l in lines] for p in points]
        false=[]
        for S in range(1<<k):
            T=sum(1<<j for j in range(len(lines)) if all(not(S&(1<<i)) or not inc[i][j] for i in range(k)))
            close=sum(1<<i for i in range(k) if all(not(T&(1<<j)) or not inc[i][j] for j in range(len(lines))))
            if close==S:false.append(S|(T<<k))
        rows=[[(1<<a)|(1<<b),1] for a,b in E]+[[v,0] for v in false]
        globalmap=points+[13+l for l in lines]
        degrees=[sum(plane['incidence_rows'][p][l] for p in points) for l in range(13)]
        hist=[degrees.count(i) for i in range(5)]
        core={'q':3,'point_count':k,'line_count':len(lines),'input_count':len(globalmap),
              'point_subset':points,'line_subset':lines,'global_input_map':globalmap,
              'edges':E,'incidence_rows':inc,'maximal_independent_masks':false,'boundary_rows':rows,
              'read1_star_gate_count':5*k-1,'target_gate_count':5*k-2,
              'orbit_size':len(orbit),'line_intersection_histogram':hist}
        name=f'counterexample_2583_core_k{k}_r{repnum}'
        (dest/(name+'.json')).write_text(json.dumps(core,indent=2)+'\n')
        (dest/(name+'.txt')).write_text(f'{len(globalmap)} {k} {len(E)} {len(rows)}\n'+''.join(f'{a} {b}\n' for a,b in E)+''.join(f'{v} {b}\n' for v,b in rows))
        (dest/(name+'.map.txt')).write_text(f'{k} {len(globalmap)} {5*k-2}\n'+' '.join(map(str,points))+'\n'+' '.join(map(str,globalmap))+'\n')
        manifest.append({key:core[key] for key in ['point_count','input_count','point_subset','target_gate_count','orbit_size','line_intersection_histogram']}|{'file':name+'.json','row_count':len(rows)})
        print(name,'points',points,'inputs',len(globalmap),'gates',5*k-2,'rows',len(rows),'orbit',len(orbit),'linehist',hist)
        repnum+=1
(dest/'counterexample_2583_core_manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
