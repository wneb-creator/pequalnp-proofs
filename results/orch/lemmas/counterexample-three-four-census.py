"""Exhaustive C4-free graph census on the fixed 3+4 bipartition."""
from itertools import permutations
import json

p,l=3,4
edges=[(a,p+b) for a in range(p) for b in range(l)]
perms=[(a,b) for a in permutations(range(p)) for b in permutations(range(l))]
def c4free(mask):
    return all(not all(mask>>(u*l+v)&1 for u in [a,aa] for v in [b,bb])
               for a in range(p) for aa in range(a+1,p)
               for b in range(l) for bb in range(b+1,l))
def cover(mask):
    return min(s.bit_count() for s in range(1<<(p+l))
               if all(not(mask>>e&1) or s>>a&1 or s>>b&1 for e,(a,b) in enumerate(edges)))
def canon(mask):
    return min(sum(1<<(aa[a]*l+bb[b]) for a in range(p) for b in range(l) if mask>>(a*l+b)&1)
               for aa,bb in perms)
def decode(mask): return [e for k,e in enumerate(edges) if mask>>k&1]
records=[];hist={};classes={}
for mask in range(1<<(p*l)):
    if not c4free(mask):continue
    e=mask.bit_count();tau=cover(mask)
    hist[(e,tau)]=hist.get((e,tau),0)+1
    if e+tau>=10:
        c=canon(mask);classes[c]=classes.get(c,0)+1
        records.append(dict(mask=mask,edges=e,tau=tau,canonical=c))
expected_edges=[(a,3+b) for a in range(3) for b in range(3) if a!=b]+[(0,6)]
expected=sum(1<<(a*4+b-3) for a,b in expected_edges)
assert c4free(expected) and expected.bit_count()==7 and cover(expected)==3
assert max(e for e,tau in hist)==7
assert max(e+tau for e,tau in hist)==10
assert set(classes)=={canon(expected)}
report=dict(all_masks=1<<(p*l),c4_free_masks=sum(hist.values()),maximum_edges=max(e for e,tau in hist),
            maximum_edges_plus_cover=max(e+tau for e,tau in hist),
            histogram=[dict(edges=e,tau=tau,count=c) for (e,tau),c in sorted(hist.items())],
            target_masks=len(records),target_isomorphism_classes=len(classes),
            classes=[dict(canonical=key,count=value,edges=decode(key)) for key,value in classes.items()],
            expected_pendant_edges=expected_edges,expected_mask=expected,expected_canonical=canon(expected),
            conclusion='Every C4-free3+4 graph with |E|+tau(E)>=10 is isomorphic, preserving the bipartition, to C6 plus one pendant edge.',
            scope='Finite exhaustive Python calculation, not Lean verification.',target_records=records)
print(json.dumps(report,indent=2))
