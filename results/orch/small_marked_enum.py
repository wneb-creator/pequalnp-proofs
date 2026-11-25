#!/usr/bin/env python3
import json,time
from pathlib import Path

class StopSearch(Exception):pass

def run(n,edges,marked,limit=5,seconds=20):
    full=(1<<(1<<n))-1;d0=1<<(1<<n);d1=d0<<1
    d0shift=(1<<n)-(1<<marked[0]);d1shift=(1<<n)+1-(1<<marked[1])
    values=[sum(1<<r for r in range(1<<n) if r>>i&1) | (d0 if i==marked[1] else 0) | (d1 if i==marked[0] else 0) for i in range(n)]
    target=sum(1<<r for r in range(1<<n) if any((r>>a&1) and (r>>b&1) for a,b in edges))
    attempts=0;start=time.monotonic();done=[];found=None;gates=[]
    def dfs(left):
        nonlocal attempts,found
        if attempts%8192==0 and time.monotonic()-start>seconds:raise StopSearch()
        possibilities={}
        for a in range(len(values)):
            va=values[a]
            for b in range(a+1,len(values)):
                vb=values[b]
                possibilities.setdefault(va|vb,('or',a,b))
                sig=(va&vb&full)|((((va<<d0shift)&vb)|((vb<<d0shift)&va))&d0)|((((va<<d1shift)&vb)|((vb<<d1shift)&va))&d1)
                possibilities.setdefault(sig,('and',a,b))
        for sig,g in possibilities.items():
            attempts+=1
            gates.append(g)
            if sig==target:
                found=list(gates);gates.pop();return True
            if left>1:
                values.append(sig)
                if dfs(left-1):values.pop();gates.pop();return True
                values.pop()
            gates.pop()
        return False
    status='bounded-unsat'
    try:
        for k in range(1,limit+1):
            if dfs(k):status='sat';break
            done.append(k)
    except StopSearch:status='unknown-time-limit'
    return {'n':n,'edges':edges,'marked':marked,'status':status,'exhausted_sizes':done,'gates':found,'attempts':attempts,'seconds':time.monotonic()-start,'method':'All proper earlier distinct-wire AND/OR circuits; equal resulting full truth-and-two-derivative signatures deduplicated only for the next new wire in a fixed prefix.'}

cases=[(3,[(0,1)],(0,1),3),(3,[(0,1),(0,2)],(0,1),4),(4,[(0,1),(2,3)],(0,1),4),(4,[(0,1),(1,2),(2,3)],(0,1),5),(4,[(0,1),(1,2),(2,3)],(1,2),5)]
results=[]
for n,e,m,k in cases:
    r=run(n,e,m,k,20);results.append(r);print(json.dumps(r),flush=True)
Path('/tmp/oec/pequalnp-pilot-60/small-marked-results.json').write_text(json.dumps(results,indent=2)+'\n')
