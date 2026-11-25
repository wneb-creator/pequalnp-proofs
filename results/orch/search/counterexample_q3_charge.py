import json
from pathlib import Path
from counterexample_q3_repair import EDGES, LINES, NEGATIVE, N, NINPUT, POSITIVE

n=NINPUT
edges=set(EDGES)
gates=[]
def gate(op,a,b):
    gates.append((op,a,b));return n+len(gates)-1
others=sorted(LINES[0]-{0})
y=others[0]
for x in others[1:]: y=gate(False,y,x)
g=gate(True,gate(False,0,y),gate(False,0,N))
stars=[]
for l in range(N):
    points=sorted(LINES[l])
    if l==0:
        local=gate(False,g,others[-1])
    else:
        terms=[g if p==0 else p for p in points]
        local=terms[0]
        for x in terms[1:]:local=gate(False,local,x)
    stars.append(gate(True,local,N+l))
output=stars[0]
for star in stars[1:]:output=gate(False,output,star)
patterns=POSITIVE+NEGATIVE+[1<<i for i in range(n)]
values=[sum(1<<t for t,mask in enumerate(patterns) if (mask>>i)&1) for i in range(n)]
for op,a,b in gates:values.append(values[a]&values[b] if op else values[a]|values[b])
target=(1<<len(POSITIVE))-1
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
star_edges=set();lam=set()
for j in tops:
    op,a,b=gates[j]
    star_edges.update(tuple(sorted((u,v))) for u in ors[a] for v in ors[b])
    for operand,other in ((a,b),(b,a)):
        if len(ors[other])==1:
            for k in closures[operand]:
                _,c,d=gates[k]
                if k in orn and ors[c] and ors[d]:lam.add(k)
uncovered=edges-star_edges
normal=all((not below[a] and not below[b]) if op else below[a]==below[b] for op,a,b in gates)
pairsets=[{edge for k,edge in enumerate(EDGES) if (v>>k)&1} for v in values]
useful=all(pairsets[n+j] for j in range(len(gates)))
strict=all(bool(pairsets[a]-pairsets[b]) and bool(pairsets[b]-pairsets[a]) for op,a,b in gates if not op)
single_bad=[(j,i) for j in range(len(gates)) for i in range(n)
            if (values[n+j]>>(len(POSITIVE)+len(NEGATIVE)+i))&1 and not any(i not in (a,b) for a,b in pairsets[n+j])]
bad_read=[]
for p,l in sorted(edges):
    R=[(i==p,i==l,False) for i in range(n)]
    for op,a,b in gates:
        x,y=R[a],R[b]
        R.append((False,False,(x[0] and y[1]) or(x[1] and y[0])) if op else tuple(x[k] or y[k] for k in range(3)))
    if not R[-1][2]:bad_read.append((p,l))
report=dict(q=3,gates=len(gates),normal=normal,pair_useful=useful,or_pair_strict=strict,
            singleton_away=not single_bad,bad_singleton_gates=single_bad,
            uncovered_edges=sorted(uncovered),centreless=len(cent),junk=len(junk),
            orN_minus_lam=len(orn-lam),bad_read_pairs=bad_read,
            charge_left=5*len(uncovered),charge_right=4*(2*len(cent)+len(junk)+len(orn-lam)),
            positive_patterns=len(POSITIVE),maximal_independent_patterns=len(NEGATIVE),
            singleton_patterns=n,all_independent_closure_cases=1<<N,circuit=gates)
Path('/tmp/oec/pequalnp-pilot-76/q3-67-charge-probe.json').write_text(json.dumps(report,indent=2)+'\n')
report.pop('circuit');print(json.dumps(report))
