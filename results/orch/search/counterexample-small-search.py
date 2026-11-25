from itertools import combinations_with_replacement
from datetime import datetime, timezone
import json

def run(p, q, maxg):
    n=p+q
    inputs=[sum(1 << x for x in range(1<<n) if x>>i&1) for i in range(n)]
    pure={}
    for s in range(1,1<<n):
        mask=0
        for i in range(n):
            if s>>i&1: mask |= inputs[i]
        pure[mask]=s
    left=(1<<p)-1
    allbits=(1<<n)-1
    right=allbits^left
    # A state records every available (truth-table, OR-reach), and semantic OR witnesses.
    start=(tuple(sorted((v,1<<i) for i,v in enumerate(inputs))),())
    levels={start: []}
    checked=0
    for k in range(maxg+1):
        print(datetime.now(timezone.utc).isoformat(), p,q,k,'states',len(levels),flush=True)
        nextlevel={}
        for (signals,witnesses),hist in levels.items():
            for f,r in signals:
                edges=[(a,b) for a in range(p) for b in range(q) if f>>( (1<<a)|(1<<(p+b)))&1]
                if len(edges)+min(p,q)<=k+1: continue
                if any(sum((a,b) in edges and (c,b) in edges for b in range(q))>1 for a in range(p) for c in range(a+1,p)): continue
                target=0
                for a,b in edges: target |= inputs[a]&inputs[p+b]
                if target!=f: continue
                tau=next(s.bit_count() for s in sorted(range(1<<n),key=int.bit_count) if all((s>>a&1) or (s>>(p+b)&1) for a,b in edges))
                if len(edges)+tau<=k+1: continue
                checked+=1
                covered=True
                for a,b in edges:
                    ok=False
                    for s in witnesses:
                        if s&right==s and s>>(p+b)&1 and all((a,c) in edges for c in range(q) if s>>(p+c)&1): ok=True
                        if s&left==s and s>>a&1 and all((c,b) in edges for c in range(p) if s>>c&1): ok=True
                    if not ok: covered=False;break
                if covered:
                    print('COUNTEREXAMPLE',p,q,k,edges,tau,hist,flush=True)
                    return False
            if k==maxg: continue
            avail=set(signals)
            for (f,r),(g,s) in combinations_with_replacement(signals,2):
                for op in (0,1):
                    z=(f|g) if op else (f&g)
                    reach=(r|s) if op else 0
                    if op and reach&left and reach&right: continue
                    newsig=(z,reach)
                    witness=pure.get(z,0) if op else 0
                    if witness.bit_count()<2: witness=0
                    ws=tuple(sorted(set(witnesses)|({witness} if witness else set())))
                    if newsig in avail and ws==witnesses: continue
                    sigs=tuple(sorted(avail|{newsig}))
                    state=(sigs,ws)
                    if state not in nextlevel:
                        nextlevel[state]=hist+[(op,(f,r),(g,s),newsig)]
        levels=nextlevel
    print('PASS finite bound',p,q,maxg,'challenging candidate outputs',checked,flush=True)
    return True

run(2,2,3)
run(2,3,4)
