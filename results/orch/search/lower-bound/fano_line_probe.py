#!/usr/bin/env python3
"""Tiny exact Fano-line identities and interface-antichain checks."""
from itertools import combinations
from collections import Counter
import json

lines=[(0,1,3),(0,2,6),(1,5,6),(0,4,5),(3,4,6),(2,3,5),(1,2,4)]
def D(mask):return any(all(mask&(1<<v) for v in line) for line in lines)
gates=[]
def gate(op,a,b):
    gates.append([op,a,b]);return 6+len(gates)
# x0*(x1*x3 + x2*x6 + x4*x5), plus two factored transversal pairs.
t1=gate('or',gate('and',1,2),gate('and',3,6))
t1=gate('and',4,t1)
t2=gate('or',gate('and',1,6),gate('and',3,2))
t2=gate('and',5,t2)
t=gate('or',t1,t2)
q=gate('or',gate('and',1,3),gate('and',2,6))
q=gate('or',q,gate('and',4,5))
out=gate('or',t,gate('and',0,q))
assert len(gates)==16 and out==22
weights=Counter()
for mask in range(128):
    vals=[bool(mask&(1<<v)) for v in range(7)]
    for op,a,b in gates:vals.append(vals[a] and vals[b] if op=='and' else vals[a] or vals[b])
    assert vals[-1]==D(mask)
    assert D(mask)==(not D(mask^127))
    neighborhood_ors=[any(mask&(1<<v) for v in line) for line in lines]
    assert D(mask)==all(neighborhood_ors)
    weights[sum(neighborhood_ors)]+=1
    for line in lines:
        assert not D(mask) or any(mask&(1<<v) for v in line)

max_antichain={}
for k in range(1,5):
    points=list(range(1<<k))
    largest=0
    for family in range(1<<(1<<k)):
        if family.bit_count()<=largest:continue
        selected=[x for x in points if family&(1<<x)]
        if all((x&y)!=x and (x&y)!=y for x,y in combinations(selected,2)):
            largest=len(selected)
    max_antichain[k]=largest
assert max_antichain=={1:1,2:2,3:3,4:6}

print(json.dumps(dict(status='PASS',fano_lines=lines,formula_gates=gates,
    formula_gate_count=16,truth_assignments_checked=128,self_dual=True,
    conjunction_of_line_sums=True,line_sum_weight_distribution=dict(weights),
    largest_boolean_antichains=max_antichain,
    scope='Upper bound and semantic interface observations; no optimum claim'),indent=2,sort_keys=True))
