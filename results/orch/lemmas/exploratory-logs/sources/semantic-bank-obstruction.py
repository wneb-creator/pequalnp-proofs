from pathlib import Path
import json

n = 7
names = ['a', 'b', 'c', 'u', 'v', 'z1', 'z2']
gates = [('and', 6, 6), ('and', 5, 5), ('or', 3, 7), ('or', 4, 8),
         ('and', 9, 10), ('or', 3, 4), ('and', 11, 12), ('or', 0, 13),
         ('or', 14, 1), ('or', 14, 2), ('and', 5, 15), ('and', 6, 16), ('or', 17, 18)]
edges = [(0,5),(1,5),(3,5),(0,6),(2,6),(4,6)]
full = (1 << (1 << n)) - 1
inputs = [sum(1 << x for x in range(1 << n) if x >> i & 1) for i in range(n)]
target = 0
for a,b in edges:
    target |= inputs[a] & inputs[b]

def run(kill=None, redirect=None):
    values = inputs[:]
    for j,(op,a,b) in enumerate(gates):
        if kill == j:
            value = 0
        elif redirect is not None and redirect[0] == j:
            value = values[(a,b)[redirect[1]]]
        elif op == 'and':
            value = values[a] & values[b]
        else:
            value = values[a] | values[b]
        values.append(value)
    return values

values = run()
assert values[-1] == target
assert all(not (set(a for a,b in edges if b==5) & set(a for a,b in edges if b==6)) - {0} for _ in [0])
reach = [{i} for i in range(n)]
cone = [set() for _ in range(n)]
for j,(op,a,b) in enumerate(gates):
    reach.append((reach[a] | reach[b]) if op == 'or' else set())
    cone.append(cone[a] | cone[b] | ({a-n} if a>=n else set()) | ({b-n} if b>=n else set()))
    if op == 'or':
        assert len({i < 5 for i in reach[-1]}) <= 1
clean_and = [j for j,(op,_,_) in enumerate(gates) if op=='and' and values[n+j] & ~target == 0]
junk = [j for j,(op,_,_) in enumerate(gates) if op=='and' and values[n+j] & ~target != 0]
assert clean_and == [10,11]
assert all(not any(i in cone[n+j] for i in clean_and) for j,(op,_,_) in enumerate(gates) if op=='and')
pivotal = {}
or_essential = {}
for j,(op,a,b) in enumerate(gates):
    killed = run(kill=j)[-1]
    pivotal[j] = [(u,v) for u,v in edges if not (killed >> ((1<<u)|(1<<v))) & 1]
    assert pivotal[j]
    if op=='or':
        or_essential[j] = []
        for side in range(2):
            redirected = run(redirect=(j,side))[-1]
            witnesses = [(u,v) for u,v in edges if not (redirected >> ((1<<u)|(1<<v))) & 1]
            assert witnesses
            or_essential[j].append(witnesses)
star_edges = set()
lam = set()
for t in clean_and:
    _,a,b = gates[t]
    for u in reach[a]:
        for v in reach[b]:
            star_edges.add(tuple(sorted((u,v))))
    for leaf,centre in [(a,b),(b,a)]:
        if len(reach[centre]) == 1:
            todo=[leaf]
            seen=set()
            while todo:
                w=todo.pop()
                if w<n or w in seen:
                    continue
                seen.add(w)
                op,aa,bb=gates[w-n]
                if op!='or':
                    continue
                if reach[aa] and reach[bb] and values[w] & ~target:
                    lam.add(w-n)
                todo += [aa,bb]
orN = {j for j,(op,a,b) in enumerate(gates) if op=='or' and values[n+j] & ~target}
U = set(tuple(sorted(e)) for e in edges)-star_edges
report = {'n':n,'input_names':names,'gates':gates,'edges':edges,'size':len(gates),
          'tCount':0,'tops':clean_and,'junk':junk,'lambda':sorted(lam),'orN_outside_lambda':sorted(orN-lam),
          'Ustar':sorted(U),'top_form':True,'all_gate_edge_pivotal':pivotal,
          'all_or_branches_essential':or_essential,
          'note':'Not a minimum circuit and not a counterexample to L-meta-4675. Obstructs unconditional per-centre bank factoring.'}
print(json.dumps(report,indent=2))
