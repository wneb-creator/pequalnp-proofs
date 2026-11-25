import hashlib
import itertools
import json
from pathlib import Path

def outputs(n, depth, pruned):
    initial = [sum(1 << x for x in range(1 << n) if x >> i & 1) for i in range(n)]
    reached = {w: 0 for w in initial}
    counts = [0] * depth
    def visit(wires, d):
        for a in range(len(wires)):
            for b in range(a + int(pruned), len(wires)):
                for op in range(2):
                    w = wires[a] | wires[b] if op else wires[a] & wires[b]
                    if pruned and (w in wires or (d and b < len(wires)-1 and w < wires[-1])):
                        continue
                    counts[d] += 1
                    reached[w] = min(reached.get(w, d+1), d+1)
                    if d+1 < depth:
                        visit(wires + [w], d+1)
    visit(initial, 0)
    return reached, counts

for n,d in [(3,4),(4,3)]:
    brute,bc = outputs(n,d,False)
    reduced,rc = outputs(n,d,True)
    assert brute == reduced, (n,d,brute.keys()-reduced.keys())
    print('Canonicalization validation',n,d,'all min costs match',len(brute),'brute',bc,'pruned',rc)

P=L=3
n=P+L
initial = [sum(1 << x for x in range(1 << n) if x >> i & 1) for i in range(n)]
checked=0
for mask in range(1,1<<(P*L)):
    edges=[(p,P+l) for p in range(P) for l in range(L) if mask>>(p*L+l)&1]
    if any(sum((p,P+l) in edges and (q,P+l) in edges for l in range(L))>1 for p in range(P) for q in range(p+1,P)):
        continue
    covers=[s for s in range(1<<n) if all(s>>p&1 or s>>l&1 for p,l in edges)]
    cover=min(covers,key=int.bit_count)
    groups={v:[] for v in range(n) if cover>>v&1}
    for p,l in edges:
        if cover>>p&1: groups[p].append(l)
        else: groups[l].append(p)
    assert all(groups.values())
    wires=list(initial)
    polynomials=[{(i,)} for i in range(n)]
    gates=[]
    def add(a,b,op):
        gates.append((a,b,op))
        wires.append(wires[a]|wires[b] if op else wires[a]&wires[b])
        polynomials.append(polynomials[a]|polynomials[b] if op else {tuple(sorted(x+y)) for x in polynomials[a] for y in polynomials[b]})
        return len(wires)-1
    roots=[]
    for centre,leaves in groups.items():
        root=leaves[0]
        for v in leaves[1:]:root=add(root,v,1)
        roots.append(add(centre,root,0))
    root=roots[0]
    for v in roots[1:]:root=add(root,v,1)
    target=0
    for p,l in edges:target|=initial[p]&initial[l]
    assert wires[root]==target
    assert polynomials[root]=={tuple(sorted(e)) for e in edges}
    assert len(gates)==len(edges)+cover.bit_count()-1
    checked+=1
print('Verified explicit star witnesses, exact truth tables and squarefree edge polynomials:',checked)
p=Path('/tmp/oec/pequalnp-pilot-86/counterexample/small_search.cpp')
print('Search source SHA256:',hashlib.sha256(p.read_bytes()).hexdigest())
