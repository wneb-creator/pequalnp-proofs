from collections import deque, Counter
from itertools import combinations
from pathlib import Path
import json

base=Path('/tmp/oec/pequalnp-pilot-62')
raw=[int(x) for x in (base/'singleton-packing-input.txt').read_text().split()]
rows=raw[2:470]
edges=raw[470:]
lines=[{p for p in range(13) if (p-l)%13 in (0,1,3,9)} for l in range(13)]

def norm(v):
    v=tuple(x%3 for x in v)
    a=next(x for x in v if x)
    return tuple(x*a%3 for x in v)

def cross(u,v):
    return norm((u[1]*v[2]-u[2]*v[1],u[2]*v[0]-u[0]*v[2],u[0]*v[1]-u[1]*v[0]))

points={0:(1,0,0),1:(0,1,0),2:(0,0,1),5:(1,1,1)}
duals={}
while len(points)<13 or len(duals)<13:
    before=(len(points),len(duals))
    for l,ps in enumerate(lines):
        known=sorted(ps&points.keys())
        if l not in duals and len(known)>=2:
            duals[l]=cross(points[known[0]],points[known[1]])
    for p in range(13):
        known=[l for l in duals if p in lines[l]]
        if p not in points and len(known)>=2:
            points[p]=cross(duals[known[0]],duals[known[1]])
    assert before!=(len(points),len(duals))
assert len(set(points.values()))==13 and len(set(duals.values()))==13
assert all((sum(a*b for a,b in zip(points[p],duals[l]))%3==0)==(p in lines[l]) for p in range(13) for l in range(13))
inverse={v:p for p,v in points.items()}
line_inverse={frozenset(ps):l for l,ps in enumerate(lines)}
maps=[lambda v:(v[1],v[2],v[0]),lambda v:(v[0]+v[1],v[1],v[2]),lambda v:(-v[0],v[1],v[2])]
generators=[]
for f in maps:
    perm=[inverse[norm(f(points[p]))] for p in range(13)]
    perm += [13+line_inverse[frozenset(perm[p] for p in ps)] for ps in lines]
    generators.append(perm)
generators.append([13+(-p)%13 for p in range(13)]+[(-l)%13 for l in range(13)])
def act(mask,perm):
    return sum(1<<perm[v] for v in range(26) if mask>>v&1)
for perm in generators:
    assert sorted(perm)==list(range(26))
    assert {act(e,perm) for e in edges}==set(edges)
    assert {act(r,perm) for r in rows}==set(rows)
pairs=[(1<<a)|(1<<b) for a,b in combinations(range(26),2)]
pair_index={v:i for i,v in enumerate(pairs)}
pair_perms=[[pair_index[act(b,g)] for b in pairs] for g in generators]
pending={(i,j) for i in range(325) for j in range(i+1,325) if not pairs[i]&pairs[j]}
assert len(pending)==44850
orbits=[]
certificate=[]
while pending:
    rep=min(pending)
    seen={rep}
    todo=deque([rep])
    position={rep:len(certificate)}
    certificate.append([rep[0],rep[1],-1,-1])
    while todo:
        x=todo.popleft()
        for gi,perm in enumerate(pair_perms):
            y=tuple(sorted((perm[x[0]],perm[x[1]])))
            if y not in seen:
                seen.add(y)
                todo.append(y)
                position[y]=len(certificate)
                certificate.append([y[0],y[1],position[x],gi])
    assert seen<=pending
    pending-=seen
    orbits.append({'pair_indices':list(rep),'block_masks':[pairs[i] for i in rep],'orbit_size':len(seen),'certificate_root':position[rep]})
result={'generators':generators,'points':points,'lines':duals,'two_pair_orbit_count':len(orbits),'two_pair_total':sum(x['orbit_size'] for x in orbits),'orbits':orbits}
(base/'packing-capacity3-orbit-certificate.txt').write_text(str(len(certificate))+'\n'+'\n'.join(' '.join(str(v) for v in row) for row in certificate)+'\n')
(base/'packing-capacity3-two-pair-roots.txt').write_text(str(len(orbits))+'\n'+'\n'.join('2 '+' '.join(str(v) for v in x['block_masks']) for x in orbits)+'\n')
for label,bs in [('singletons',[1<<v for v in range(26)]),('pairs',pairs)]:
    remaining=set(bs)
    small_orbits=[]
    small_certificate=[]
    while remaining:
        rep=min(remaining)
        seen={rep}
        todo=deque([rep])
        position={rep:len(small_certificate)}
        small_certificate.append([rep,-1,-1])
        while todo:
            x=todo.popleft()
            for gi,g in enumerate(generators):
                y=act(x,g)
                if y not in seen:
                    seen.add(y)
                    todo.append(y)
                    position[y]=len(small_certificate)
                    small_certificate.append([y,position[x],gi])
        assert seen<=remaining
        remaining-=seen
        small_orbits.append({'block':rep,'size':len(seen),'certificate_root':position[rep]})
    result[label+'_orbits']=small_orbits
    (base/('packing-capacity3-'+label+'-roots.txt')).write_text(str(len(small_orbits))+'\n'+'\n'.join('1 '+str(x['block']) for x in small_orbits)+'\n')
    (base/('packing-capacity3-'+label+'-certificate.txt')).write_text(str(len(small_certificate))+'\n'+'\n'.join(' '.join(str(v) for v in row) for row in small_certificate)+'\n')
(base/'packing-capacity3-symmetries.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'two_pair_orbit_count':len(orbits),'two_pair_total':sum(x['orbit_size'] for x in orbits),'orbit_size_histogram':dict(Counter(x['orbit_size'] for x in orbits))},indent=2))
