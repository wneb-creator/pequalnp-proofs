#!/usr/bin/env python3
"""Short finite probes for AND-root and unique-input semantic architectures."""
from collections import Counter
from itertools import combinations
import json

E=[(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),
 (3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),
 (6,8),(6,9),(6,11)]
ALL=(1<<14)-1
adj=[sum(1<<(b if a==v else a) for a,b in E if v in (a,b)) for v in range(14)]
truth=[any(m&(1<<a) and m&(1<<b) for a,b in E) for m in range(1<<14)]
independent=[m for m in range(1<<14) if not truth[m]]
mis=[m for m in independent if all(m&(1<<v) or m&adj[v] for v in range(14))]
assert len(mis)==37
shapes=Counter(((m&127).bit_count(),(m>>7).bit_count()) for m in mis)
linear=[]
identities=0
for I in mis:
    S=ALL^I
    additions=[]
    part=I
    while True:
        if all(not(S&(1<<v)) or part&adj[v] for v in range(14)):
            additions.append(part)
        if not part:break
        part=(part-1)&I
    minima=[p for p in additions if not any(q!=p and (q&p)==q for q in additions)]
    # Maximal superfunction B allowed by G=OR(S) AND B is G plus these terms.
    for mask in range(1<<14):
        B=truth[mask] or any((mask&p)==p for p in minima)
        assert (bool(mask&S) and B)==truth[mask]
        identities+=1
    assert [m for m in mis if not(m&S)]==[I]
    linear.append(dict(I=I,cover=S,independent_shape=[(I&127).bit_count(),(I>>7).bit_count()],
        cover_size=S.bit_count(),minimum_tree_new_gate_budget=26-S.bit_count(),
        minimal_added_terms=minima,added_term_degrees=sorted(p.bit_count() for p in minima)))

critical_false=[m for m in mis if not(m&1)]
critical_true=[(1<<a)|(1<<b) for a,b in E if 0 in (a,b)]
assert len(critical_false)==25 and len(critical_true)==3
assert all(truth[m|1] for m in critical_false)
N=adj[0]
partner_min=[]
allowed=[]
for m in independent:
    if m&1 or m&N:continue
    if all(not(N&(1<<v)) or m&adj[v] for v in range(14)):allowed.append(m)
partner_min=[p for p in allowed if not any(q!=p and (q&p)==q for q in allowed)]
assert len(partner_min)==8 and all(p.bit_count()==3 for p in partner_min)
groups=((1,3),(2,6),(4,5))
expected={sum(1<<v for v in chosen) for chosen in __import__('itertools').product(*groups)}
assert set(partner_min)==expected
for m in independent:
    if m&1:continue
    influence_extension=any((N&(1<<v)) and not truth[m|(1<<v)] for v in range(14))
    P=all(any(m&(1<<v) for v in group) for group in groups)
    assert influence_extension == (not P)

support_pairs=Counter()
for a in range(1,1<<14):
    common=ALL
    for v in range(14):
        if a&(1<<v):common&=adj[v]
    b=common
    while b:
        assert not(a&b)
        assert min(a.bit_count(),b.bit_count())==1
        support_pairs[(a.bit_count(),b.bit_count())]+=1
        b=(b-1)&common

print(json.dumps(dict(status='PASS',maximal_false_sets=37,
    maximal_false_shapes={str(k):v for k,v in sorted(shapes.items())},
    linear_factor_cases=linear,linear_factor_truth_checks=identities,
    unique0_critical_false_masks=critical_false,unique0_critical_positive_masks=critical_true,
    unique_OR_partner_allowed_independent_minimal_terms=partner_min,
    unique_OR_partner_product_groups=groups,
    nonempty_AND_root_singleton_support_pairs={str(k):v for k,v in sorted(support_pairs.items())},
    scope='Finite semantic architecture checks only; no circuit witness or lower-bound certificate'),indent=2,sort_keys=True))
