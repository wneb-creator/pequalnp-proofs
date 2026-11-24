import collections
import itertools
import json
import time
import sys
from pathlib import Path

BASE = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).resolve().parent

def decode(s):
    n=ord(s[0])-63
    assert 0<=n<=62
    bits=[(ord(c)-63>>k)&1 for c in s[1:] for k in range(5,-1,-1)]
    assert len(bits)==6*((n*(n-1)//2+5)//6)
    edges=[];adj=[0]*n;k=0
    for b in range(1,n):
        for a in range(b):
            if bits[k]:edges.append((a,b));adj[a]|=1<<b;adj[b]|=1<<a
            k+=1
    assert not any(bits[k:])
    return n,edges,adj

assert decode('DQc')[1]==[(0,2),(1,3),(0,4),(3,4)]

def components(adj):
    n=len(adj);seen=0;parts=[]
    for i in range(n):
        if seen>>i&1:continue
        front=1<<i;part=0
        while front:
            part|=front
            nxt=0
            for j in range(n):
                if front>>j&1:nxt|=adj[j]
            front=nxt&~part
        seen|=part;parts.append(part)
    return parts

def bipartite(adj):
    n=len(adj);color=[-1]*n
    for i in range(n):
        if color[i]>=0:continue
        color[i]=0;stack=[i]
        while stack:
            a=stack.pop()
            for b in range(n):
                if not (adj[a]>>b&1):continue
                if color[b]<0:color[b]=1-color[a];stack.append(b)
                elif color[b]==color[a]:return False
    return True

def stats(g6,idx):
    n,edges,adj=decode(g6)
    assert all((adj[a]&adj[b]).bit_count()<=1 for a,b in itertools.combinations(range(n),2))
    for a,b,c,d in itertools.combinations(range(n),4):
        for x,y,z,w in [(a,b,c,d),(a,b,d,c),(a,c,b,d)]:
            assert not all(adj[u]>>v&1 for u,v in [(x,y),(y,z),(z,w),(w,x)])
    deg=[a.bit_count() for a in adj]
    ind=[s for s in range(1<<n) if all(not(s&adj[i]) for i in range(n) if s>>i&1)]
    mis=[s for s in ind if all(s>>i&1 or s&adj[i] for i in range(n))]
    alpha=max(s.bit_count() for s in ind)
    covers=[s for s in range(1<<n) if all(s>>a&1 or s>>b&1 for a,b in edges)]
    tau=min(s.bit_count() for s in covers)
    assert tau==n-alpha
    assert max(s.bit_count() for s in mis)==alpha
    assert all(not(adj[a]>>b&1) for s in mis for a,b in itertools.combinations([i for i in range(n) if s>>i&1],2))
    tris=[(a,b,c) for a,b,c in itertools.combinations(range(n),3) if adj[a]>>b&1 and adj[b]>>c&1 and adj[c]>>a&1]
    parts=components(adj)
    cover=next(s for s in covers if s.bit_count()==tau)
    row={
      'id':f'c4-n{n}-{idx:04d}','n':n,'graph6':g6,'edges':edges,'edge_count':len(edges),
      'tau':tau,'alpha':alpha,'minimum_cover':[i for i in range(n) if cover>>i&1],
      'maximal_independent_sets':mis,'mis_count':len(mis),
      'bound':max(0,len(edges)+tau-1),'target_size':len(edges)+tau-2,
      'degrees':deg,'min_degree':min(deg),'max_degree':max(deg),'components':len(parts),
      'connected':len(parts)==1,'bipartite':bipartite(adj),'triangles':len(tris),
      'cyclomatic_number':len(edges)-n+len(parts)
    }
    invariants=[]
    for a in range(n):
        invariants.append((deg[a],tuple(sorted(deg[b] for b in range(n) if adj[a]>>b&1)),sum(a in t for t in tris)))
    return row,adj,invariants

iso_checks=0
def isomorphic(left,right):
    global iso_checks
    iso_checks+=1
    _,a,ia=left;_,b,ib=right;n=len(a)
    candidates=[[j for j in range(n) if ib[j]==ia[i]] for i in range(n)]
    if any(not c for c in candidates):return False
    order=sorted(range(n),key=lambda i:(len(candidates[i]),-a[i].bit_count()))
    image=[-1]*n
    def go(k,used):
        if k==n:return True
        i=order[k]
        for j in candidates[i]:
            if used>>j&1:continue
            if any(((a[i]>>h)&1)!=((b[j]>>image[h])&1) for h in order[:k]):continue
            image[i]=j
            if go(k+1,used|(1<<j)):return True
        image[i]=-1
        return False
    return go(0,0)

summary={'source':'https://github.com/cando-developers/nauty','commit':'4fedb86cbf2f7547ee8ad91245af56d7d3c554bf','families':[]}
start=time.time()
for n in [8,9]:
    lines=sorted((BASE/f'c4-all-{n}.g6').read_text().splitlines())
    assert len(lines)==len(set(lines))
    data=[stats(s,i) for i,s in enumerate(lines)]
    buckets=collections.defaultdict(list)
    for d in data:
        row,adj,inv=d
        key=(tuple(sorted(inv)),row['components'],row['triangles'],row['tau'])
        for previous in buckets[key]:assert not isomorphic(d,previous),(row['id'],previous[0]['id'])
        buckets[key].append(d)
    rows=[d[0] for d in data]
    core=[r for r in rows if r['connected'] and r['min_degree']>=2]
    generated_core=set((BASE/f'c4-core-{n}.g6').read_text().splitlines())
    assert generated_core=={r['graph6'] for r in core}
    for kind,selected in [('all',rows),('core',core)]:
        selected.sort(key=lambda r:(-r['edge_count'],-r['tau'],-r['triangles'],r['id']))
        (BASE/f'c4-{kind}-{n}.json').write_text(json.dumps(selected,indent=2)+'\n')
        dist=collections.Counter((r['edge_count'],r['tau'],r['triangles']) for r in selected)
        meta={'n':n,'family':kind,'count':len(selected),'max_edges':max(r['edge_count'] for r in selected),'max_target_size':max(r['target_size'] for r in selected),'by_edge_tau_triangle':[[*k,v] for k,v in sorted(dist.items())]}
        summary['families'].append(meta)
        print(json.dumps({k:v for k,v in meta.items() if k!='by_edge_tau_triangle'}),flush=True)
summary['independent_isomorphism_pair_checks']=iso_checks
summary['elapsed_seconds']=time.time()-start
(BASE/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
combined=json.loads((BASE/'c4-core-8.json').read_text())+json.loads((BASE/'c4-core-9.json').read_text())
(BASE/'c4-core-8-9.json').write_text(json.dumps(combined,indent=2)+'\n')
print('VALIDATED',json.dumps({'iso_pair_checks':iso_checks,'elapsed':time.time()-start,'core_total':len(combined)}),flush=True)
