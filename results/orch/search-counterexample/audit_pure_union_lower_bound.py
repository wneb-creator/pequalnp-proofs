from collections import Counter
from hashlib import sha256
from itertools import combinations, combinations_with_replacement
import json
from pathlib import Path

base=Path('/tmp/oec/pequalnp-pilot-62')
data=json.loads((base/'geometry-data.json').read_text())
line_points=data['lines']
pencils=[sum(1<<l for l in range(13) if line_points[l]>>p&1) for p in range(13)]
assert all(x.bit_count()==4 for x in pencils)
assert all((a&b).bit_count()==1 for a,b in combinations(pencils,2))
caps=sorted({r['D'] for r in data['generic'] if r['D'].bit_count()==4})
assert len(caps)==234
avoiding={n:sum(1<<p for p in range(13) if not pencils[p]&n) for n in caps}
assert all(x.bit_count()==3 for x in avoiding.values())
guards=[]
guard_hist=Counter()
for mask in range(8192):
    contained=[p for p,t in enumerate(pencils) if mask&t==t]
    if not contained:continue
    missed=[n for n in caps if not mask&n]
    if not missed:continue
    assert 1<=len(contained)<=3
    guard_hist[(mask.bit_count(),len(contained))]+=1
    guards.append((mask,contained,missed))
row_bijection_checks=0
private_incidence_checks=0
shared_incidence_checks=0
residual_cases=Counter()
for p,t in enumerate(pencils):
    rays=[line_points[l]^(1<<p) for l in range(13) if t>>l&1]
    assert len(rays)==4 and all(x.bit_count()==3 for x in rays)
    assert sum(rays)==8191^(1<<p)
    cap_edges={}
    for n in caps:
        if n&t:continue
        others=avoiding[n]^(1<<p)
        assert others.bit_count()==2
        assert all((others&ray).bit_count()<=1 for ray in rays)
        assert others not in cap_edges
        cap_edges[others]=n
    expected={(1<<a)|(1<<b) for a,b in combinations([v for v in range(13) if v!=p],2)
              if not any((ray>>a&1) and (ray>>b&1) for ray in rays)}
    assert set(cap_edges)==expected and len(expected)==54
    row_bijection_checks+=len(expected)
    outside_lines=[l for l in range(13) if not t>>l&1]
    for a in range(3):
        choices=[()] if a==0 else combinations_with_replacement(outside_lines,a)
        for chosen in choices:
            removed=0
            for l in chosen:removed|=line_points[l]
            remaining=(8191^(1<<p))&~removed
            parts=[(remaining&ray).bit_count() for ray in rays]
            expected_cover=remaining.bit_count()-max(parts)
            assert expected_cover>=9-3*a
            # Independently enumerate independent sets of this at-most12
            # vertex multipartite graph rather than assume its formula.
            maximum_independent=0
            sub=remaining
            while True:
                if not any(edge&sub==edge for edge in expected):
                    maximum_independent=max(maximum_independent,sub.bit_count())
                if not sub:break
                sub=(sub-1)&remaining
            assert expected_cover==remaining.bit_count()-maximum_independent
            residual_cases[(a,tuple(sorted(parts)),expected_cover)]+=1
    for mask,contained,missed in guards:
        if p not in contained:continue
        if len(contained)==1:
            if mask==t:continue
            extras=[l for l in outside_lines if mask>>l&1]
            assert extras
            for l in extras:
                for n in missed:
                    assert cap_edges.get(avoiding[n]^(1<<p))==n
                    assert line_points[l]&(avoiding[n]^(1<<p))
                    private_incidence_checks+=1
        else:
            for q in contained:
                if q==p:continue
                for n in missed:
                    assert avoiding[n]>>q&1
                    shared_incidence_checks+=1
result={
    'status':'All finite geometric ingredients of the restricted39 charging proof passed independent audit.',
    'useful_union_supports':len(guards),
    'guard_histogram':[{'support_size':s,'contained_pencils':r,'count':n} for (s,r),n in sorted(guard_hist.items())],
    'cap_edge_bijection_checks':row_bijection_checks,
    'private_extra_line_incidence_checks':private_incidence_checks,
    'shared_other_pencil_incidence_checks':shared_incidence_checks,
    'residual_vertex_cover_cases':[{'private_count':a,'part_sizes':list(parts),'minimum_cover':m,'count':n} for (a,parts,m),n in sorted(residual_cases.items())],
    'scope':'Supports a mathematical39-OR lower bound only for internal pure unions and final free intersections; not Lean checked and not the arbitrary-AND51 target.',
}
print(json.dumps(result,indent=2))
(base/'pure-union-lower-bound-independent-audit.json').write_text(json.dumps(result,indent=2)+'\n')
