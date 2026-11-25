import json
from pathlib import Path


base = Path('/tmp/oec/pequalnp-pilot-76/fano27')
d = json.loads(base.with_suffix('.json').read_text())
nodes = []
stars = []
for l in range(7):
    a, b, c = sorted({l, (l+1)%7, (l+3)%7})
    nodes.extend([(False,a,b),(False,14+len(nodes),c),(True,15+len(nodes),7+l)])
    stars.append(14+len(nodes)-1)
o = stars[0]
for s in stars[1:]:
    nodes.append((False,o,s))
    o=14+len(nodes)-1

# Canonicalize a topological order by the largest already-numbered operand.
remaining = set(range(27))
mapping = {i:i for i in range(14)}
canonical = []
while remaining:
    ready = [(max(mapping[a],mapping[b]),min(mapping[a],mapping[b]),i)
             for i in remaining for op,a,b in [nodes[i]] if a in mapping and b in mapping]
    r,l,i=min(ready)
    op,a,b=nodes[i]
    mapping[14+i]=14+len(canonical)
    canonical.append((op,l,r))
    remaining.remove(i)
assert canonical[0][1:]==(0,1)
assert mapping[o]==40
assignment={}
for i,(op,l,r) in enumerate(canonical):
    assignment[d['ops'][i]]=op
    for j,v in enumerate(d['lhs'][i]): assignment[v]=j==l
    for j,v in enumerate(d['rhs'][i]): assignment[v]=j==r
for t,mask in enumerate(d['patterns']):
    ws=[bool(mask>>i&1) for i in range(14)]
    for i,(op,l,r) in enumerate(canonical):
        assignment[d['lv'][i][t]]=ws[l]
        assignment[d['rv'][i][t]]=ws[r]
        v=ws[l] and ws[r] if op else ws[l] or ws[r]
        ws.append(v)
        assignment[d['values'][i][t]]=v
count=0
for line in base.with_suffix('.cnf').read_text().splitlines():
    if line.startswith('p'): continue
    c=[int(x) for x in line.split()[:-1]]
    assert any(assignment[abs(v)] == (v>0) for v in c), (count,c)
    count+=1
for mask in range(1<<14):
    ws=[bool(mask>>i&1) for i in range(14)]
    for op,l,r in canonical: ws.append(ws[l] and ws[r] if op else ws[l] or ws[r])
    target=any((mask>>p)&1 and (mask>>l)&1 for p,l in d['edges'])
    assert ws[-1]==bool(target)
print(json.dumps(dict(clauses_validated=count, full_truth_table_cases=16384, gates=27,
                     circuit=canonical)))
