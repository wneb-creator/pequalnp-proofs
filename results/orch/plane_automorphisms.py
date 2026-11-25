import itertools, json
from pathlib import Path

def incident(p,l):return (p-l)%13 in (0,1,3,9)
def norm(v):
    q=next(x for x in v if x)
    return tuple(x*pow(q,-1,3)%3 for x in v)
def cross(a,b):
    return norm(((a[1]*b[2]-a[2]*b[1])%3,
                 (a[2]*b[0]-a[0]*b[2])%3,
                 (a[0]*b[1]-a[1]*b[0])%3))
def dot(a,b):return sum(x*y for x,y in zip(a,b))%3
points={0:(1,0,0),1:(0,1,0),2:(0,0,1),5:(1,1,1)}
lines={}
while len(points)<13 or len(lines)<13:
    previous=len(points)+len(lines)
    for p,q in itertools.combinations(list(points),2):
        l,= [l for l in range(13) if incident(p,l) and incident(q,l)]
        v=cross(points[p],points[q])
        assert l not in lines or lines[l]==v
        lines[l]=v
    for l,m in itertools.combinations(list(lines),2):
        p,= [p for p in range(13) if incident(p,l) and incident(p,m)]
        v=cross(lines[l],lines[m])
        assert p not in points or points[p]==v
        points[p]=v
    assert previous<len(points)+len(lines)
assert all(incident(p,l)==(dot(points[p],lines[l])==0) for p in range(13) for l in range(13))

def frame(p,l):
    u=points[p]
    v=next(points[q] for q in range(13) if q!=p and incident(q,l))
    w=next(points[q] for q in range(13) if not incident(q,l))
    return u,v,w
def lincomb(coefs,basis):return tuple(sum(a*v[i] for a,v in zip(coefs,basis))%3 for i in range(3))
target=frame(0,0)
autos=[]
for p in range(13):
    for l in range(13):
        if not incident(p,l):continue
        source=frame(p,l)
        transforms={lincomb(c,source):lincomb(c,target) for c in itertools.product(range(3),repeat=3)}
        assert len(transforms)==27
        point_perm=[next(q for q in range(13) if points[q]==norm(transforms[points[r]])) for r in range(13)]
        line_perm=[]
        for r in range(13):
            image={point_perm[q] for q in range(13) if incident(q,r)}
            s,=[s for s in range(13) if {q for q in range(13) if incident(q,s)}==image]
            line_perm.append(s)
        assert sorted(point_perm)==list(range(13)) and sorted(line_perm)==list(range(13))
        assert point_perm[p]==0 and line_perm[l]==0
        assert all(incident(q,r)==incident(point_perm[q],line_perm[r]) for q in range(13) for r in range(13))
        autos.append(dict(edge=[p,l],points=point_perm,lines=line_perm))
output=dict(points=[points[p] for p in range(13)],lines=[lines[l] for l in range(13)],automorphisms=autos)
Path('/tmp/oec/pequalnp-pilot-60/plane-flag-automorphisms.json').write_text(json.dumps(output,indent=2))
print(json.dumps(dict(automorphisms=len(autos),incidence_checks=169*len(autos))))
