"""Independent exhaustive semantic/strict-cone replay of a supplied control."""
from pathlib import Path
import json,hashlib
source=Path('/tmp/oec/pequalnp-pilot-62/meta2448/petersenminus-star13-v9-control.witness.json')
w=json.loads(source.read_text())
n=w['input_count']; gates=w['gates']; edges=[tuple(e) for e in w['edges']]
assert n==8 and len(gates)==13
census=json.loads(Path('results/meta2448/petersen-deletions.json').read_text())['classes'][1]
assert edges==[tuple(e) for e in census['edges']]
values=[sum(((assignment>>v)&1)<<assignment for assignment in range(1<<n)) for v in range(n)]
cones=[]
for j,(op,a,b) in enumerate(gates):
    assert op in ('and','or') and 0<=a<n+j and 0<=b<n+j
    cone=set()
    for ref in (a,b):
        if ref>=n:
            gate=ref-n
            cone.add(gate);cone.update(cones[gate])
    cones.append(cone)
    values.append(values[a]&values[b] if op=='and' else values[a]|values[b])
truth=sum(int(any(assignment>>a&1 and assignment>>b&1 for a,b in edges))<<assignment for assignment in range(1<<n))
assert values[-1]==truth
first=next(j for j in range(len(gates)) if values[n+j]==truth)
assert first==12
owners=[];centers={}
for j,(op,a,b) in enumerate(gates):
    owned=[]
    for i,(u,v) in enumerate(edges):
        bit=1<<((1<<u)|(1<<v))
        if op=='and' and values[n+j]&bit and all(gates[k][0]!='and' or not(values[n+k]&bit) for k in cones[j]):
            owned.append(i)
    owners.append(owned)
    if owned:
        common=set(edges[owned[0]])
        for i in owned[1:]:common.intersection_update(edges[i])
        assert common
        centers[str(j)]=sorted(common)
assert owners==w['owned_edge_indices']
assert w['has_star_profile'] and w['effective_prefix_has_star_profile']
report={'verdict':'PASS independent finite replay','source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
 'all_assignments_checked':1<<n,'first_exact_output_gate':first,'AND_count':sum(g[0]=='and' for g in gates),
 'OR_count':sum(g[0]=='or' for g in gates),'strict_cones':[sorted(c) for c in cones],
 'owned_edge_indices':owners,'nonempty_owner_centers':centers,
 'scope':'13-gate star control only; no smaller-circuit impossibility or Lean result.'}
Path('results/meta2448/petersen-minus-control-independent-replay.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
