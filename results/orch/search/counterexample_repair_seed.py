import json
from pathlib import Path

base=Path('/tmp/oec/pequalnp-pilot-76/fano26')
d=json.loads(base.with_suffix('.json').read_text())
nodes=[]
stars=[]
for l in range(7):
    a,b,c=sorted({l,(l+1)%7,(l+3)%7})
    j=len(nodes)
    nodes.extend([(False,a,b),(False,14+j,c),(True,15+j,7+l)])
    stars.append(16+j)
o=stars[0]
for s in stars[1:]:
    nodes.append((False,o,s));o=14+len(nodes)-1
remove=1
replacement=14
shift=lambda w: (replacement if w==14+remove else w) - (w>14+remove)
nodes=[(op,shift(a),shift(b)) for j,(op,a,b) in enumerate(nodes) if j!=remove]
remaining=set(range(26));mapping={i:i for i in range(14)};canonical=[]
while remaining:
    ready=[(max(mapping[a],mapping[b]),min(mapping[a],mapping[b]),i)
           for i in remaining for op,a,b in [nodes[i]] if a in mapping and b in mapping]
    r,l,i=min(ready)
    op,a,b=nodes[i]
    mapping[14+i]=14+len(canonical); canonical.append((op,l,r)); remaining.remove(i)
assert canonical[0][1:]==(0,1)
assignment={}
seed=[]
for i,(op,l,r) in enumerate(canonical):
    assignment[d['ops'][i]]=op
    for j,v in enumerate(d['lhs'][i]):assignment[v]=j==l
    for j,v in enumerate(d['rhs'][i]):assignment[v]=j==r
    seed.append([d['ops'][i] if op else -d['ops'][i],d['lhs'][i][l],d['rhs'][i][r]])
for t,mask in enumerate(d['patterns']):
    ws=[bool(mask>>i&1) for i in range(14)]
    for i,(op,l,r) in enumerate(canonical):
        assignment[d['lv'][i][t]]=ws[l];assignment[d['rv'][i][t]]=ws[r]
        v=ws[l] and ws[r] if op else ws[l] or ws[r];ws.append(v)
        assignment[d['values'][i][t]]=v
base.with_suffix('.seed').write_text('\n'.join(' '.join(map(str,row)) for row in seed)+'\n')
base.with_suffix('.phases').write_text(' '.join(str(v if b else -v) for v,b in sorted(assignment.items()))+'\n')
print(json.dumps(dict(gates=len(canonical),seed=canonical)))
