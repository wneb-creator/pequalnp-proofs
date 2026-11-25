from CommonFilterSearch import test
from itertools import product
from random import Random
import json

def or_costs(n):
    supports=[s for s in range(1,1<<n) if s.bit_count()>=2]
    index={s:i for i,s in enumerate(supports)}
    pair_reqs=[]
    for s in supports:
        reqs=set()
        for a in range(1,s):
            if a&~s:continue
            for b in range(a+1,s):
                if b&~s or a|b!=s:continue
                req=(1<<index[a] if a in index else 0)|(1<<index[b] if b in index else 0)
                reqs.add(req)
        pair_reqs.append(reqs)
    dp=[n*100]*(1<<len(supports))
    for M in range(len(dp)):
        valid=True
        for j,reqs in enumerate(pair_reqs):
            if M>>j&1 and not any(req&~M==0 for req in reqs):valid=False;break
        if valid:dp[M]=M.bit_count()
    for j in range(len(supports)):
        for M in range(len(dp)):
            if not(M>>j&1):dp[M]=min(dp[M],dp[M|(1<<j)])
    def cost(targets):
        M=0
        for s in targets:
            if s in index:M|=1<<index[s]
        return dp[M]
    return cost

for n,mode,total in [(3,'exhaustive',0),(4,'random',1000000)]:
    cost=or_costs(n);rng=Random(2583+n)
    if mode=='exhaustive':samples=product(range(1,1<<n),range(1,1<<n),range(1,1<<n),range(1,1<<n),range(1,1<<(2*n)))
    else:samples=((rng.randrange(1,1<<n),rng.randrange(1,1<<n),rng.randrange(1,1<<n),rng.randrange(1,1<<n),rng.randrange(1,1<<(2*n))) for i in range(total))
    counts=[0,0];best=None
    for p1,l1,p2,l2,w in samples:
        counts[0]+=1;wp=w&((1<<n)-1);wl=w>>n;t=test(n,[p1,p2],[l1,l2],wp,wl)
        if t is None:continue
        counts[1]+=1
        physical=cost([p1,p2,wp])+cost([l1,l2,wl])+int(wp!=0 and wl!=0)+4
        t['physical']=physical;t['physical_slack']=physical+1-t['edges']-t['tau']
        if best is None or t['physical_slack']<best['physical_slack']:best=t
        if t['physical_slack']<0: print(json.dumps(dict(kind='counterexample',sample=t)),flush=True);break
    else:print(json.dumps(dict(n=n,kind=mode,counts=counts,best=best)),flush=True)
