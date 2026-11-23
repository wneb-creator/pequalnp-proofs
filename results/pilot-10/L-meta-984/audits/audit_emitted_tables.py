#!/usr/bin/env python3
"""Independent decoder of emitted Lean tables and coverage-check ranges."""
import json,re,sys
from pathlib import Path
root=Path(sys.argv[1]);emit=Path(sys.argv[2]);total=0;totalchecks=0
for idx in range(31):
    text=(emit/f"Shard{idx}.data.fragment.lean").read_text()
    checks=(emit/f"Shard{idx}.checks.fragment.lean").read_text()
    meta=json.loads((root/f"compact{idx}.meta.json").read_text())
    assert text.startswith(f"namespace Shard{idx}\n")
    assert text.rstrip().endswith(f"end Shard{idx}")
    def table(name):
        body=re.search(r"def "+name+r" : Nat → Nat\n(.*?)(?=\n\ndef |\nend )",text,re.S).group(1)
        entries={int(a):int(b,0) for a,b in re.findall(r"  \| (\d+) => (0x[0-9a-f]+|\d+)",body)}
        assert "  | _ => 0" in body
        return entries
    n,ht,lt,dt=map(table,["N","HT","LT","DT"])
    values=[int(x,16) for x in re.search(r"def V : Array Nat := #\[(.*?)\n\]",text,re.S).group(1).split(",")]
    lb,ib,stride=map(int,re.search(r"List.range \(fld \(LT s\) (\d+) j\)\)\.map \(fun t => V.getD \(fld \(DT s\) (\d+) \((\d+) \* j \+ t\)\) 0\)",text).groups())
    steps=int(re.search(r"def idx.*?bsr \(HT s\) 32 \(hk zs\) (\d+) 0 \(N s\)",text).group(1))
    k=int(re.search(r"def Z.*?barScore (\d+) S N idx pool s",text).group(1))
    assert k==meta["k"]
    pool=list(map(int,re.search(r"def pool : List Nat := \[(.*?)\]",text).group(1).split(",")))
    assert pool==list(map(int,(root/f"pool{idx}.txt").read_text().split()))
    blocks={}
    for r,c,o in re.findall(r"theorem check_\d+_\d+ : span \(Z (\d+)\) (\d+) (\d+) = true := by decide \+kernel",checks):
        r,c,o=map(int,[r,c,o]);blocks.setdefault(r,[]).append((o,c));totalchecks+=1
    for r in range(meta["budget"]+1):
        raw=[tuple(int(w,16) for w in json.loads(line)) for line in (root/f"compact{idx}.layer{r}.jsonl").read_text().splitlines()]
        assert n.get(r,0)==len(raw)
        decoded=[];hashes=[]
        for j in range(len(raw)):
            length=(lt.get(r,0)>>(lb*j))&((1<<lb)-1)
            ws=tuple(values[(dt.get(r,0)>>(ib*(stride*j+t)))&((1<<ib)-1)] for t in range(length))
            h=(ht.get(r,0)>>(32*j))&((1<<32)-1)
            assert h==sum((pow(w%11400714819323198549+317,3,11400714819323198549)+1) for w in ws)%4294967291
            decoded.append(ws);hashes.append(h)
        assert set(decoded)==set(raw) and len(decoded)==len(set(decoded))
        assert hashes==sorted(set(hashes))
        for j,h in enumerate(hashes):
            lo,hi=0,len(raw)
            for _ in range(steps):
                if lo+1<hi:
                    mid=(lo+hi)//2
                    if hashes[mid]<=h:lo=mid
                    else:hi=mid
            assert lo==j
        offset=0
        for o,c in blocks.get(r,[]):assert o==offset and c>0;offset+=c
        assert offset==len(raw)
        total+=len(raw)
    budget=int(re.search(r"theorem checked \(s : Nat\) \(hs : s ≤ (\d+)\)",checks).group(1))
    assert budget==meta["budget"]
    print("PASS emitted tables",idx,"states",sum(n.values()),"budget",budget,"k",k,flush=True)
print("PASS all31 packed Lean table decodings, binary lookup entries, pool mappings and kernel-check range coverage",flush=True)
print("TOTAL states",total,"kernel blocks",totalchecks,flush=True)
print("Scope: data-generation audit only; kernel elaboration remains independently required.",flush=True)
