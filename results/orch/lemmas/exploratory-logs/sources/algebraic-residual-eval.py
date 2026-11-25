import itertools,json

n=6
edges={(0,3),(1,3),(2,3),(0,4),(0,5)}
gates=[('or',0,1),('or',3,4),('and',6,7),('or',2,8),('and',9,3),('or',5,8),('and',11,0),('or',10,12)]
output=13
rows=[]
for x in range(1<<n):
    vals=[bool(x>>i&1) for i in range(n)]
    for op,a,b in gates: vals.append(vals[a] and vals[b] if op=='and' else vals[a] or vals[b])
    goal=any((x>>a&1) and (x>>b&1) for a,b in edges)
    rows.append((vals,goal))
assert all(vals[output]==goal for vals,goal in rows)
reach=[{i} for i in range(n)]
closure=[set() for _ in range(n)]
cone=[set() for _ in range(n)]
for j,(op,a,b) in enumerate(gates):
    reach.append(reach[a]|reach[b] if op=='or' else set())
    closure.append({j}|closure[a]|closure[b] if op=='or' else {j})
    cone.append(({a-n} if a>=n else set())|({b-n} if b>=n else set())|cone[a]|cone[b])
below={j for j in range(len(gates)) if all(not v[n+j] or goal for v,goal in rows)}
tops={j for j,(op,a,b) in enumerate(gates) if op=='and' and j in below}
junk={j for j,(op,a,b) in enumerate(gates) if op=='and' and j not in below}
orn={j for j,(op,a,b) in enumerate(gates) if op=='or' and j not in below}
centreless={j for j in tops if not reach[gates[j][1]] or not reach[gates[j][2]]}
star=set()
for j in tops:
    _,a,b=gates[j]
    star|={tuple(sorted((u,v))) for u in reach[a] for v in reach[b]}
U=edges-star
lam=set()
for j in orn:
    _,a,b=gates[j]
    if not reach[a] or not reach[b]: continue
    for t in tops:
        _,c,d=gates[t]
        if len(reach[d])==1 and j in closure[c]: lam.add(j)
        if len(reach[c])==1 and j in closure[d]: lam.add(j)
T={j for j,(op,a,b) in enumerate(gates) if op=='or' and any(i<3 for i in reach[n+j]) and any(i>=3 for i in reach[n+j])}
topform=all(i not in cone[n+j] for i in tops for j,(op,_,_) in enumerate(gates) if op=='and')
pair_active=all(any(rows[(1<<a)|(1<<b)][0][n+j] for a,b in edges) for j in range(len(gates)))
def tau(es):
    return min(mask.bit_count() for mask in range(1<<n) if all(mask>>a&1 or mask>>b&1 for a,b in es))
result={'gates':gates,'edges':sorted(edges),'tops':sorted(tops),'junk':sorted(junk),'orN':sorted(orn),'centreless':sorted(centreless),'lambda':sorted(lam),'Ustar':sorted(U),'twoColour':sorted(T),'TopForm':topform,'pair_active':pair_active,'tau_E':tau(edges),'tau_U':tau(U),'residual_left':len(U)+tau(U),'residual_right':2*len(centreless)+len(junk)+len(orn-lam)}
print(json.dumps(result,indent=2))
assert topform and pair_active and not T
assert result['residual_left']==result['residual_right']==5
