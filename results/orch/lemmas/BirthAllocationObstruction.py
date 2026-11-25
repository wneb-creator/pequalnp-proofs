import json

p = l = 4
n = p + l
edges = {(0,4),(0,5),(0,6),(1,4),(1,7),(2,5),(2,7),(3,6),(3,7)}
gates = [
    ('or',0,1), ('or',8,2), ('or',9,3),
    ('or',4,5), ('or',11,6), ('or',12,7),
    ('and',0,13), ('and',1,13), ('and',2,13), ('and',3,13),
    ('and',10,4), ('and',10,5), ('and',10,6), ('and',10,7),
    ('or',18,19), ('or',22,20), ('and',14,23),
    ('or',18,21), ('and',15,25),
    ('or',19,21), ('and',16,27),
    ('or',20,21), ('and',17,29),
    ('or',24,26), ('or',31,28), ('or',32,30),
]
assert all(a < n+k and b < n+k for k, (_,a,b) in enumerate(gates))

def evaluate(x):
    values = [bool(x & (1 << i)) for i in range(n)]
    for op,a,b in gates:
        values.append(values[a] and values[b] if op == 'and' else values[a] or values[b])
    return values

for x in range(1 << n):
    target = any(x & (1<<a) and x & (1<<b) for a,b in edges)
    assert evaluate(x)[-1] == target
for a in range(p):
    for a2 in range(a+1,p):
        common = {b for b in range(p,n) if (a,b) in edges and (a2,b) in edges}
        assert len(common) <= 1
or_reach = [{i} for i in range(n)]
for op,a,b in gates:
    reach = or_reach[a] | or_reach[b] if op == 'or' else set()
    assert not (any(i<p for i in reach) and any(i>=p for i in reach))
    or_reach.append(reach)
onehot_values = [evaluate(1<<i) for i in range(n)]
supports = [{i for i in range(n) if onehot_values[i][w]} for w in range(n+len(gates))]
assert all(not supports[n+k] for k,(op,_,_) in enumerate(gates) if op == 'and')
reachable = set()
def visit(w):
    if w < n or w-n in reachable:
        return
    k = w-n
    reachable.add(k)
    _,a,b = gates[k]
    visit(a)
    visit(b)
visit(n+len(gates)-1)
births = [k for k in sorted(reachable) if gates[k][0]=='and' and supports[gates[k][1]] and supports[gates[k][2]]]
assert births == list(range(6,14))

def adjacent(a,b):
    return (a,b) in edges or (b,a) in edges
candidates = {}
for k in births:
    options = []
    for center in range(n):
        for leaf_wire in gates[k][1:]:
            leaves = supports[leaf_wire]
            if all(adjacent(center,v) for v in leaves):
                covered = {tuple(sorted((center,v))) for v in leaves}
                assert len(covered) <= 1
                options.append({'center':center,'wire':leaf_wire,'covered':sorted(covered)})
    candidates[k] = options
assert len(edges) > len(births)
print(json.dumps({'status':'exact Python checks passed; not Lean checked',
    'vertices':n,'edges':len(edges),'gates':len(gates),'births':births,
    'all_inputs_checked':1<<n,'tCount':0,'all_AND_singleton_supports_empty':True,
    'max_edges_per_whole_slot_star':1,
    'birth_star_cover_impossible':len(edges)>len(births),
    'candidates':candidates}, indent=2))
