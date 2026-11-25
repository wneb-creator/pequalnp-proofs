from pathlib import Path
from itertools import permutations,combinations
from collections import Counter
import json,sys,hashlib
raw=Path(sys.argv[1]).read_bytes();data=json.loads(raw);rows=data['examples'];assert len(rows)==342 and data['complete']
N=[{0,1,3},{0,2,6},{1,5,6},{0,4,5},{3,4,6},{2,3,5},{1,2,4}];I={0,1,2,3};required=[N[i] for i in [0,1,3]];M={2,4,5,6};E={4,5,6}
def bits(S):return sum(1<<x for x in S)
def decode(m):return {i for i in range(7) if m>>i&1}
def key(row):return tuple(row['r'])+(row['strict_mask'],)+tuple(row['family'])
indexed={key(row):row for row in rows};assert len(indexed)==342
linegroup=[]
for e in permutations(range(7)):
    images=[{e[x] for x in T} for T in N]
    if any(T not in N for T in images):continue
    pp=[N.index(T) for T in images]
    if {pp[i] for i in I}==I and pp[2]==2:linegroup.append((e,pp))
assert len(linegroup)==6
unitgroup=list(permutations(range(3)))
def transform(row,e,unit):
    r=[0]*7
    for t,m in enumerate(row['r']):r[e[t]]=sum(1<<unit[j] for j in range(3) if m>>j&1)
    flip=lambda m:sum(1<<e[t] for t in range(7) if m>>t&1)
    return tuple(r)+(flip(row['strict_mask']),)+tuple(sorted(flip(m) for m in row['family']))
orbits={}
for row in rows:
    transformed={transform(row,e,u) for e,pp in linegroup for u in unitgroup}
    assert transformed<=indexed.keys()
    canonical=min(transformed);orbits.setdefault(canonical,set()).add(key(row))
for row in rows:
    r=[{j for j in range(3) if row['r'][t]>>j&1} for t in range(7)]
    units=[{t for t in range(7) if j in r[t]} for j in range(3)]
    Y=[decode(m) for m in row['family']];S=decode(row['strict_mask'])
    assert len({frozenset(y) for y in Y})==7 and N[2]<S and S in Y
    assert all(t in Y for t in required)
    assert all(len(y)>=2 and (len(y)!=2 or any(y<=t for t in required)) for y in Y)
    assert all(not any(u==N[i] for i in M) for u in units)
    assert all(u in Y for u in units if len(u)>=3 or len(u)==2 and any(u<=t for t in required))
    for t in required:
        assert any(len(y)==2 and y<=t or len(y)==4 and t<=y for y in Y) or any(len(a)==len(b)==5 and a&b==t for a,b in combinations(Y,2))
    exact={i for i in [0,1,3] if any(sum(x in N[j] for j in I)>=2 and len(r[x])<=1 for x in N[i])}
    A={i:set(N[i]) for i in I};A[2]=S.copy()
    while True:
        shared=units+Y+list(A.values())
        updated={i:A[i]|{t for x in N[i] for t in range(7) if r[x]<=r[t] and any(x in w and t in w for w in shared)} for i in I}
        if updated==A:break
        A=updated
    assert A[2]==S and all(A[i]<=N[i] for i in exact)
    assert all(any(A[i]<=y for y in Y) for i in I)
    assert [bits(A[i]) for i in range(4)]==row['assigned']
    assert all(sum(t in A[i] for i in I)+int(any(t in N[j] for j in E))<=2+len(r[t]) for t in range(7))
    costs=[len(r[c])+sum(x!=c and r[x]<=r[c] and any(x in w and c in w for w in shared) for x in range(7)) for c in range(7)]
    assert costs==row['costs'] and costs[0]<=5 and max(costs)<=6
canonical=[]
for ck,members in sorted(orbits.items()):
    row=indexed[ck];orbit={transform(row,e,u) for e,pp in linegroup for u in unitgroup};assert orbit==members
    R=[sorted(t for t in range(7) if row['r'][t]>>j&1) for j in range(3)]
    canonical.append({'orbit_size':len(members),'representative':row,'unit_supports_local_lines':R})
out={'scope':'Independent verification and symmetry classification of342 abstract q2 residual/family survivors. Not circuits or a proof of feasibility. New count-saturation consequences and the combined finite-to-circuit transfer are not yet Lean packaged.','input_sha256':hashlib.sha256(raw).hexdigest(),'states_verified':342,'line_automorphisms':[{'line_positions':list(e),'point_permutation':pp} for e,pp in linegroup],'unit_permutation_count':6,'group_size':36,'orbit_count':len(canonical),'orbit_size_histogram':dict(Counter(x['orbit_size'] for x in canonical)),'canonical':canonical}
Path(sys.argv[2]).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'states':342,'orbits':len(canonical),'sizes':out['orbit_size_histogram'],'representatives':canonical}))
