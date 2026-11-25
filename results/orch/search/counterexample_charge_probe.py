import json
from pathlib import Path

n = 14
edges = {(p,7+l) for l in range(7) for p in {l,(l+1)%7,(l+3)%7}}
original=json.loads(Path('/tmp/oec/pequalnp-pilot-76/fano27-validation.log').read_text())['circuit']
gates=[(False,0,1),(False,0,2),(False,0,4),(True,14,15),(True,17,16)]
shift=lambda w: 18 if w==0 else w+5 if w>=n else w
gates += [(op,shift(a),shift(b)) for op,a,b in original]
values=[sum(1<<s for s in range(1<<n) if (s>>i)&1) for i in range(n)]
target=0
for a,b in edges: target |= values[a]&values[b]
for op,a,b in gates: values.append(values[a]&values[b] if op else values[a]|values[b])
assert values[-1]==target
below=[value & ~target == 0 for value in values]
ors=[{i} for i in range(n)]
closures=[set() for _ in range(n)]
for j,(op,a,b) in enumerate(gates):
    ors.append(set() if op else ors[a]|ors[b])
    closures.append(set() if op else {j}|closures[a]|closures[b])
tops={j for j,(op,a,b) in enumerate(gates) if op and below[n+j]}
junk={j for j,(op,a,b) in enumerate(gates) if op and not below[n+j]}
orn={j for j,(op,a,b) in enumerate(gates) if not op and not below[n+j]}
cent={j for j in tops if not ors[gates[j][1]] or not ors[gates[j][2]]}
stars=set()
lam=set()
for j in tops:
    op,a,b=gates[j]
    stars.update(tuple(sorted((u,v))) for u in ors[a] for v in ors[b])
    for operand,other in ((a,b),(b,a)):
        if len(ors[other])==1:
            for k in closures[operand]:
                _,c,d=gates[k]
                if k in orn and ors[c] and ors[d]:lam.add(k)
uncovered=edges-stars
normal=all((not below[a] and not below[b]) if op else below[a]==below[b] for op,a,b in gates)
useful=all(any((v>>((1<<a)|(1<<b)))&1 for a,b in edges) for v in values[n:])
bad_read=[]
for p,l in sorted(edges):
    R=[(i==p,i==l,False) for i in range(n)]
    for op,a,b in gates:
        x,y=R[a],R[b]
        R.append((False,False,(x[0] and y[1]) or(x[1] and y[0])) if op else tuple(x[k] or y[k] for k in range(3)))
    if not R[-1][2]:bad_read.append((p,l))
report=dict(gates=len(gates),normal=normal,pair_useful=useful,uncovered_edges=sorted(uncovered),
            centreless=len(cent),junk=len(junk),orN_minus_lam=len(orn-lam),bad_read_pairs=bad_read,
            charge_left=4*len(uncovered),charge_right=3*(2*len(cent)+len(junk)+len(orn-lam)),
            all_truth_assignments_checked=1<<n,circuit=gates)
Path('/tmp/oec/pequalnp-pilot-76/fano32-charge-probe.json').write_text(json.dumps(report,indent=2)+'\n')
report.pop('circuit');print(json.dumps(report))
