#!/usr/bin/env python3
"""Independent unbounded-integer audit of compact monotone frontier certificates."""
import itertools,json,re,sys,time
from functools import lru_cache
from pathlib import Path
root=Path(sys.argv[1]); desk=Path(sys.argv[2]); selected=list(map(int,sys.argv[3:]))
s=json.loads(desk.read_text())["gap"]["statement"]
rowspec=[]
for m in re.finditer(r"Fin (\d+) → Bool.*?→ (\d+) ≤ C\.size",s,re.S):
    n=int(m.group(1));bound=int(m.group(2))
    edges=list(dict.fromkeys((int(a),int(b)) for a,b in re.findall(r"x (\d+) && x (\d+)",m.group(0))))
    rowspec.append((n,bound,edges))
assert len(rowspec)==31

def value(bits):
    a,b,c,d,e,f=bits
    x=b+c; y=(1-e)+(1-f)
    return (y if d else max(x,y,max(0,x+y-1))) if a else (0 if d else x)
patterns=list(itertools.product(range(2),repeat=6))
for p in patterns:
    for q in patterns:
        for op in (lambda a,b:a&b,lambda a,b:a|b):
            assert value(tuple(op(a,b) for a,b in zip(p,q)))<=value(p)+value(q)
print("PASS value6 AND/OR subadditivity: all8192 checks",flush=True)

for idx,(n,bound,edges) in enumerate(rowspec):
    raw=list(map(int,(root/f"graph{idx}.txt").read_text().split()))
    assert raw[:3]==[n,bound-1,len(edges)]
    assert list(zip(raw[3::2],raw[4::2]))==edges
    prefix=root/f"compact{idx}"
    if not prefix.with_suffix(".meta.json").exists():
        print("PENDING compact metadata",idx,flush=True);continue
    meta=json.loads(prefix.with_suffix(".meta.json").read_text())
    edge_masks=[(1<<a)|(1<<b) for a,b in edges]
    negative=[x for x in range(1<<n) if not any(x&e==e for e in edge_masks)]
    maximal=[x for x in negative if not any(x!=y and x&y==x for y in negative)]
    rows=list(itertools.product(maximal,edge_masks));k=len(rows);budget=bound-1
    assert meta["k"]==k and meta["budget"]==budget
    assert meta["negative_rows"]==[a for a,b in rows]
    assert meta["positive_rows"]==[b for a,b in rows]
    inputs=tuple(sum(((a>>v)&1)<<i|((b>>v)&1)<<(k+i) for i,(a,b) in enumerate(rows)) for v in range(n))
    assert sorted(inputs)==[int(w,16) for w in meta["inputs_hex"]]
    codes=list(map(int,(root/f"pool{idx}.txt").read_text().split()))
    assert all(0<=c<1<<60 for c in codes)
    assert all(all(((c>>(10*j))&1023)<2*k for j in range(6)) for c in codes)
    print("PASS mapping",idx,"n",n,"bound",bound,"k",k,"score codes",len(codes),flush=True)
    if idx not in selected:continue
    mask=(1<<k)-1;goal=mask<<k
    def covers(ws):
        cover=0
        for w in ws:cover|=(w>>k)&~w
        return cover&mask==mask
    assert covers(inputs)
    for keep in range((1<<n)-1):assert not covers([v for i,v in enumerate(inputs) if keep>>i&1])
    positions=[tuple((code>>(10*j))&1023 for j in range(6)) for code in codes]
    @lru_cache(maxsize=None)
    def scores(w):return tuple(value(tuple((w>>p)&1 for p in ps)) for ps in positions)
    target=scores(goal)
    def blocked(ws,remaining):
        if len(ws)!=remaining+1:return False
        values=[scores(w) for w in ws]
        return any(sum(v[j] for v in values)<t for j,t in enumerate(target))
    layers={}
    for r in range(budget+1):
        rawstates=[tuple(int(w,16) for w in json.loads(line)) for line in Path(f"{prefix}.layer{r}.jsonl").read_text().splitlines()]
        layers[r]=set(rawstates)
        assert len(rawstates)==len(layers[r])
        for ws in rawstates:
            assert ws==tuple(sorted(ws)) and len(ws)<=r+1 and covers(ws)
            assert not blocked(ws,r)
            assert all(0<=w<1<<(2*k) for w in ws)
    assert layers[budget]=={tuple(sorted(inputs))}
    assert (goal,) not in layers[0]
    print("START closure",idx,"states",sum(map(len,layers.values())),"maxbits",2*k,flush=True)
    started=time.monotonic()
    for r in range(budget,0,-1):
        generated=set();attempted=0
        def add(ws):
            if len(ws)>r or not covers(ws):return
            if blocked(ws,r-1):return
            generated.add(tuple(sorted(ws)))
        for ws in layers[r]:
            slack=r+1-len(ws)
            for a in ws:
                ra=list(ws);ra.remove(a)
                if slack>=1:
                    add([a]+ra);attempted+=1
                    if slack>=2:add([a,a]+ra);attempted+=1
                for b in ra:
                    if a>b:continue
                    rest=ra.copy();rest.remove(b)
                    for w in (a|b,a&b):
                        add([w]+rest);attempted+=1
                        if slack>=1:
                            add([w,a]+rest);add([w,b]+rest);attempted+=2
                        if slack>=2:add([w,a,b]+rest);attempted+=1
        assert generated==layers[r-1],(idx,r,len(generated),len(layers[r-1]),len(generated-layers[r-1]),len(layers[r-1]-generated))
        print("PASS closure",idx,r,"to",r-1,"states",len(generated),"literal candidates",attempted,"elapsed",round(time.monotonic()-started,2),flush=True)
    print("PASS full frontier",idx,"independent Python integer semantics",flush=True)
print("PASS: graph/row/bound mappings and all selected exact successor closures",flush=True)
print("Scope: independent computational audit, not a Lean theorem or local-checker verdict.",flush=True)
