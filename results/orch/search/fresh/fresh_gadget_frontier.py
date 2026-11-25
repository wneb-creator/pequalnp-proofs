"""Exact monotone boundary search with live-wire excess as parameter."""
from functools import lru_cache
from itertools import combinations
from time import monotonic
import argparse, json, math

def inputs(k, private, pencil, graph=None):
    groups = ([tuple(range(k))] if pencil else list(combinations(range(k), 2))) if graph is None else graph
    if private: groups += [(i,) for i in range(k)]
    n = k + len(groups)
    edges = [(p,k+i) for i,s in enumerate(groups) for p in s]
    positive = [(1<<p)|(1<<j) for p,j in edges]
    gm = [sum(1<<p for p in s) for s in groups]
    negative=[]
    for mask in range(1<<k):
        lines=[i for i,g in enumerate(gm) if not mask&g]
        if all(mask>>p&1 or any(gm[i]>>p&1 for i in lines) for p in range(k)):
            negative.append(mask|sum(1<<(k+i) for i in lines))
    return n,edges,positive,negative

def run(k,private,pencil,limit,maxsec):
    n,edges,positive,negative=inputs(k,private,pencil)
    p=len(positive); z=len(negative); tests=positive+negative
    full=(1<<(p*z))-1; target=(1<<p)-1
    initial=tuple(sorted(sum(1<<j for j,t in enumerate(tests) if t>>i&1) for i in range(n)))
    @lru_cache(maxsize=150000)
    def kw(f):
        accept=f&target
        reject=((1<<z)-1)^(f>>p)
        c=0
        while accept:
            bit=accept&-accept
            c |= reject << ((bit.bit_length()-1)*z)
            accept-=bit
        return c
    start=monotonic(); seen={}; count=0; stats={}
    path=[]
    class Timeout(Exception):pass
    def dfs(ws,s):
        nonlocal count
        if s<0: return False
        if target in ws: return True
        if len(ws)<2:return False
        if seen.get(ws,-1)>=s:return False
        count+=1
        if count%5000==0:
            if monotonic()-start>maxsec:raise Timeout
            if len(seen)>120000:seen.clear()
        stats[(len(ws),s)]=stats.get((len(ws),s),0)+1
        cs=[kw(f) for f in ws]
        pref=[0]
        for c in cs:pref.append(pref[-1]|c)
        suff=[0]*(len(ws)+1)
        for i in reversed(range(len(ws))):suff[i]=suff[i+1]|cs[i]
        if pref[-1]!=full:return False
        options=[]
        for i,a in enumerate(ws):
            rest=pref[i]
            for j in range(i+1,len(ws)):
                b=ws[j]; outside=rest|suff[j+1]; rest|=cs[j]
                must=full ^ outside
                keep=((0,0),(1,0),(0,1),(1,1)) if s>=2 else (((0,0),(1,0),(0,1)) if s else ((0,0),))
                for op,h in (('&',a&b),('|',a|b)):
                    if h in ws or not kw(h):continue
                    gap=must&~kw(h)
                    for ka,kb in keep:
                        if gap & ~((cs[i] if ka else 0)|(cs[j] if kb else 0)):continue
                        nw=tuple(sorted([w for idx,w in enumerate(ws) if (idx!=i or ka) and (idx!=j or kb)]+[h]))
                        options.append((ka+kb,-kw(h).bit_count(),nw,op,a,b,h))
        options.sort(key=lambda op:op[:2])
        for spent,_,nw,op,a,b,h in options:
            path.append((op,a,b,h))
            if dfs(nw,s-spent):return True
            path.pop()
        seen[ws]=max(seen.get(ws,-1),s)
        return False
    try: result='SAT' if dfs(initial,limit-n+1) else 'UNSAT'
    except Timeout:result='UNKNOWN'
    print(json.dumps(dict(k=k,n=n,private=private,pencil=pencil,gates=limit,status=result,states=count,elapsed=monotonic()-start,peaks=sorted(([i,j,v] for (i,j),v in stats.items()),key=lambda a:-a[2])[:10],path=path if result=='SAT' else None)),flush=True)
if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--k',type=int,required=True)
    ap.add_argument('--private',action='store_true')
    ap.add_argument('--pencil',action='store_true')
    ap.add_argument('--gates',type=int,required=True)
    ap.add_argument('--sec',type=int,default=120)
    o=ap.parse_args()
    run(o.k,o.private,o.pencil,o.gates,o.sec)
