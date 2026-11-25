from itertools import combinations_with_replacement
from datetime import datetime, timezone
from time import monotonic
p=3
q=4
n=p+q
inp=[sum(1<<x for x in range(1<<n) if x>>i&1) for i in range(n)]
ors=[]
for s in range(1<<n):
    v=0
    for i in range(n):
        if s>>i&1:v|=inp[i]
    ors.append(v)
targets={}
for em in range(1<<(p*q)):
    edges=[(a,b) for a in range(p) for b in range(q) if em>>(a*q+b)&1]
    if any(sum((a,b) in edges and (c,b) in edges for b in range(q))>1 for a in range(p) for c in range(a+1,p)):continue
    tau=next(s.bit_count() for s in sorted(range(1<<n),key=int.bit_count) if all((s>>a&1) or (s>>(p+b)&1) for a,b in edges))
    if tau<3:continue
    f=0
    for a,b in edges:f|=inp[a]&inp[p+b]
    targets[f]=edges
print(datetime.now(timezone.utc).isoformat(),'targets',len(targets),flush=True)
firsts={a&b:(i,j) for i,a in enumerate(ors) for j,b in enumerate(ors[:i+1])}
print('first AND functions',len(firsts),flush=True)
count=0
start=monotonic()
for idx,(g1,ab) in enumerate(firsts.items()):
    closure={f:(s,False) for s,f in enumerate(ors)}
    closure.update({f|g1:(s,True) for s,f in enumerate(ors)})
    signals=list(closure)
    for i,u in enumerate(signals):
        for v in signals[:i+1]:
            g2=u&v
            count+=1
            for out in (g2,g1|g2):
                if out in targets:
                    print('COUNTEREXAMPLE',targets[out],'g1',ab,'g2',closure[u],closure[v],'outputORfirst',out!=g2,flush=True)
                    raise SystemExit(1)
    if idx%100==0:print('progress',idx,'/',len(firsts),'AND2 candidates',count,'seconds',round(monotonic()-start,2),flush=True)
print('PASS: no 3x4 C4-free graph with tau=3 has a circuit with <=2 AND gates, even with unlimited OR gates.',count,flush=True)
