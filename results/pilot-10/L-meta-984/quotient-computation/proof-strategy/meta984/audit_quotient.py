#!/usr/bin/env python3
"""Unbounded-integer audit of quotient frontiers, automorphisms and parent witnesses."""
import itertools,json,sys,time
from pathlib import Path
from functools import lru_cache
root=Path(sys.argv[1]);out=Path(sys.argv[2]);indices=list(map(int,sys.argv[3:]))
totalstates=totalcandidates=0
for idx in indices:
    fields=list(map(int,(root/f"graph{idx}.txt").read_text().split()));n,budget,m=fields[:3]
    edges=list(zip(fields[3::2],fields[4::2]));edge_set={frozenset(e) for e in edges}
    meta=json.loads((out/f"quotient{idx}.meta.json").read_text());k=meta["k"]
    assert meta["budget"]==budget and meta["score_order"]=="coverage_then_orientation_then_score"
    em=[(1<<a)|(1<<b) for a,b in edges]
    neg=[x for x in range(1<<n) if not any(x&e==e for e in em)]
    maximal=[x for x in neg if not any(y!=x and x&y==x for y in neg)]
    rows=list(itertools.product(maximal,em));rowidx={p:i for i,p in enumerate(rows)}
    assert len(rows)==k and meta["negative_rows"]==[x for x,y in rows] and meta["positive_rows"]==[y for x,y in rows]
    perms=[p for p in itertools.permutations(range(n)) if {frozenset((p[a],p[b])) for a,b in edges}==edge_set]
    assert meta["vertex_perms"]==[list(p) for p in perms]
    def move_mask(x,p):return sum(1<<p[v] for v in range(n) if x>>v&1)
    rps=[tuple(rowidx[move_mask(x,p),move_mask(y,p)] for x,y in rows) for p in perms]
    assert meta["row_perms"]==[list(p) for p in rps]
    for rp,inv in zip(rps,meta["row_inverse_perms"]):assert sorted(rp)==list(range(k)) and all(inv[rp[i]]==i for i in range(k))
    @lru_cache(maxsize=None)
    def images(w):
        return tuple(sum(((w>>i)&1)<<p[i]|((w>>(k+i))&1)<<(k+p[i]) for i in range(k)) for p in rps)
    def orient(ws):return min((tuple(sorted(images(w)[a] for w in ws)),a) for a in range(len(perms)))
    mask=(1<<k)-1;goal=mask<<k
    def covers(ws):
        c=0
        for w in ws:c|=(w>>k)&~w
        return c&mask==mask
    codes=list(map(int,(root/f"pool{idx}.txt").read_text().split()))
    positions=[tuple((c>>(10*j))&1023 for j in range(6)) for c in codes]
    def value(bits):
        a,b,c,d,e,f=bits;x=b+c;y=2-e-f
        return (y if d else max(x,y,max(0,x+y-1))) if a else (0 if d else x)
    @lru_cache(maxsize=None)
    def scores(w):return tuple(value(tuple((w>>p)&1 for p in ps)) for ps in positions)
    target=scores(goal)
    def blocked(ws,s):return len(ws)==s+1 and any(sum(scores(w)[j] for w in ws)<t for j,t in enumerate(target))
    layers={};parents={}
    for s in range(budget+1):
        layers[s]=[tuple(int(w,16) for w in json.loads(line)) for line in (out/f"quotient{idx}.layer{s}.jsonl").read_text().splitlines()]
        parents[s]=[json.loads(line) for line in (out/f"quotient{idx}.parents{s}.jsonl").read_text().splitlines()]
        assert len(layers[s])==len(parents[s])==len(set(layers[s]))
        for ws in layers[s]:assert orient(ws)[0]==ws and covers(ws) and len(ws)<=s+1 and not blocked(ws,s)
    inputs=tuple(sorted(sum(((x>>v)&1)<<i|((y>>v)&1)<<(k+i) for i,(x,y) in enumerate(rows)) for v in range(n)))
    assert meta["inputs_hex"]==[format(w,"x") for w in inputs]
    assert layers[budget]==[inputs] and (goal,) not in layers[0]
    for s in range(budget):
        for child,r in zip(layers[s],parents[s]):
            ws=layers[s+1][r["parent"]];kind=r["kind"];a=r["a"];b=r["b"];keep=r["keep"]
            slack=s+2-len(ws)
            if kind==1:assert slack>=1;raw=list(ws)
            elif kind==2:assert slack>=2;raw=list(ws)+[ws[a]]
            else:
                assert kind==3 and 0<=a<b<len(ws) and slack>=keep.bit_count()
                assert r["op"] in [0,1] and 0<=keep<4
                raw=[(ws[a]&ws[b]) if r["op"]==0 else (ws[a]|ws[b])]+[w for j,w in enumerate(ws) if j not in (a,b)]
                if keep&1:raw.append(ws[a])
                if keep&2:raw.append(ws[b])
            assert covers(raw)
            assert orient(raw)==(child,r["auto"])
    started=time.monotonic();states=sum(map(len,layers.values()));totalstates+=states
    print("START quotient",idx,"automorphisms",len(perms),"states",states,flush=True)
    for s in range(budget,0,-1):
        generated=set();attempted=0
        def add(raw):
            if len(raw)>s or not covers(raw):return
            ws,_=orient(raw)
            if not blocked(ws,s-1):generated.add(ws)
        for ws in layers[s]:
            slack=s+1-len(ws)
            for a in ws:
                ra=list(ws);ra.remove(a)
                if slack>=1:
                    add([a]+ra);attempted+=1
                    if slack>=2:add([a,a]+ra);attempted+=1
                for b in ra:
                    if a>b:continue
                    rest=ra.copy();rest.remove(b)
                    for w in [a&b,a|b]:
                        add([w]+rest);attempted+=1
                        if slack>=1:add([w,a]+rest);add([w,b]+rest);attempted+=2
                        if slack>=2:add([w,a,b]+rest);attempted+=1
        assert generated==set(layers[s-1]),(idx,s,len(generated),len(layers[s-1]))
        totalcandidates+=attempted
        print("PASS quotient closure",idx,s,"to",s-1,"states",len(generated),"candidates",attempted,"seconds",round(time.monotonic()-started,2),flush=True)
    print("PASS quotient graph",idx,"automorphisms, exact canonical closure and every parent witness",flush=True)
print("PASS selected quotient frontiers",indices,"states",totalstates,"literal candidates",totalcandidates,flush=True)
