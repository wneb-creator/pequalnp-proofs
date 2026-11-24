from itertools import combinations
from collections import defaultdict

def closure(seed, op):
    values=set(seed)
    changed=True
    while changed:
        changed=False
        v=list(values)
        for a in v:
            for b in v:
                c=op(a,b)
                if c not in values:
                    values.add(c)
                    changed=True
    return values

def truth(n, edges):
    return sum(1<<bits for bits in range(1<<n) if any(bits>>a&bits>>b&1 for a,b in edges))

def cover(n,edges):
    return min(s.bit_count() for s in range(1<<n) if all((s>>a|s>>b)&1 for a,b in edges))

def girth5(n,edges):
    e={frozenset(x) for x in edges}
    adj=lambda a,b: frozenset((a,b)) in e
    return all(not(adj(a,b) and adj(b,c) and adj(c,a)) for a,b,c in combinations(range(n),3)) and all(sum(adj(a,c) and adj(b,c) for c in range(n))<2 for a,b in combinations(range(n),2))

for n in range(1,5):
    allmask=(1<<(1<<n))-1
    variables=[sum(1<<bits for bits in range(1<<n) if bits>>v&1) for v in range(n)]
    operations={'and':(lambda a,b:a&b),'or':(lambda a,b:a|b)}
    outputs={}
    for paid,free in [('and','or'),('or','and')]:
        base=closure([0,allmask]+variables,operations[free])
        vals=set(base)
        for a,b in combinations(sorted(base),2):
            vals.update(closure(base|{operations[paid](a,b)},operations[free]))
        outputs[paid]=vals
        print('inputs',n,'paid',paid,'one-paid-gate functions',len(vals))
    pairs=list(combinations(range(n),2))
    checked=0
    for bits in range(1<<len(pairs)):
        edges=[e for i,e in enumerate(pairs) if bits>>i&1]
        if not girth5(n,edges):continue
        checked+=1; f=truth(n,edges); tau=cover(n,edges)
        if tau>=2: assert f not in outputs['and'], (n,edges,'AND violated')
        if len(edges)>=3: assert f not in outputs['or'], (n,edges,'OR violated')
    print('girth>=5 graph checks',checked,'pass')

n=9
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
owners=[(1,[0,2,6]),(2,[3,7]),(4,[3,0]),(5,[0,7,8]),(8,[3,6])]
gates=[]
blocks=[]
for v,neighbors in owners:
    acc=neighbors[0]
    for w in neighbors[1:]:
        gates.append(('or',acc,w));acc=n+len(gates)-1
    gates.append(('and',v,acc));blocks.append(n+len(gates)-1)
acc=blocks[0]
for b in blocks[1:]:
    gates.append(('or',acc,b));acc=n+len(gates)-1
for bits in range(1<<n):
    wires=[bool(bits>>i&1) for i in range(n)]
    for op,a,b in gates:
        wires.append((wires[a] and wires[b]) if op=='and' else (wires[a] or wires[b]))
    assert wires[acc]==any((bits>>a&1) and (bits>>b&1) for a,b in edges)
print('target witness full truth table pass',1<<n,'rows')
print('target cover number',cover(n,edges),'girth>=5',girth5(n,edges),'gates',len(gates),'AND',sum(x[0]=='and' for x in gates),'OR',sum(x[0]=='or' for x in gates))
print('gates',gates,'output',acc)
