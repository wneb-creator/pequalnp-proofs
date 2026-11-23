#!/usr/bin/env python3
"""Independent decoder of compact Lean parent records and CHD lookup tables."""
import json,re,sys
from functools import lru_cache
from pathlib import Path
front=Path(sys.argv[1]);emit=Path(sys.argv[2]);total=blocks_total=0
MOD=11400714819323198549
for idx in range(31):
    name=f"G{idx}_";text=(emit/f"G{idx}.data.fragment.lean").read_text()
    checks=(emit/f"G{idx}.checks.fragment.lean").read_text()
    meta=json.loads((front/f"quotient{idx}.meta.json").read_text())
    def table(t):
        body=re.search(r"def "+name+t+r" : Nat → Nat\n(.*?)(?=\n\ndef |$)",text,re.S).group(1)
        assert "  | _ => 0" in body
        return {int(a):int(b,0) for a,b in re.findall(r"  \| (\d+) => (0x[0-9a-f]+|\d+)",body)}
    N,pb,records,buckets,flag,seedBits,seeds=map(table,["N","pb","records","buckets","flag","seedBits","seeds"])
    params=re.search(r"qParentState ([^\n]+)",text).group(1).split()
    cap,k,bw,stride,ob,pairs,mb,ab=[int(x,0) for x in params[:8]]
    assert k==meta["k"] and cap==meta["budget"]
    arr=[int(x.strip(),0) for x in re.search(r"def "+name+r"actionRows : Array Nat := #\[(.*?)\]",text,re.S).group(1).split(",")]
    initial=tuple(int(x.strip(),0) for x in re.search(r"def "+name+r"initial : List Nat := \[(.*?)\]",text,re.S).group(1).split(","))
    assert initial==tuple(int(x,16) for x in meta["inputs_hex"])
    def fld(v,b,i):return (v>>(b*i))&((1<<b)-1)
    maps=[tuple(fld(v,bw,i) for i in range(k)) for v in arr]
    assert [list(m) for m in maps]==meta["row_inverse_perms"]
    @lru_cache(maxsize=None)
    def action(w,a):
        p=maps[a]
        return sum(((w>>p[i])&1)<<i|((w>>(k+p[i]))&1)<<(k+i) for i in range(k))
    def key(ws):return sum(pow(w%MOD+317,3,MOD)+1 for w in ws)%4294967291
    def locate(s,ws):
        h=key(ws);code=fld(seeds.get(s,0),seedBits.get(s,0),h%buckets.get(s,0))
        return code-flag.get(s,0) if code>=flag.get(s,0) else pow(h+code+317,3,MOD)%N.get(s,0)
    decoded={cap:[initial]}
    for s in range(cap,-1,-1):
        raw=[tuple(int(w,16) for w in json.loads(line)) for line in (front/f"quotient{idx}.layer{s}.jsonl").read_text().splitlines()]
        assert len(raw)==N.get(s,0)
        if s<cap:
            decoded[s]=[]
            for j in range(len(raw)):
                entry=fld(records.get(s,0),pb.get(s,0)+mb+ab,j)
                par=entry&((1<<pb.get(s,0))-1)
                code=(entry>>pb.get(s,0))&((1<<mb)-1)
                auto=entry>>(pb.get(s,0)+mb)
                prev=decoded[s+1][par]
                if code==0:ws=list(prev)
                elif code<=stride:ws=[prev[code-1]]+list(prev)
                else:
                    q=code-stride-1;pair=fld(pairs,2*ob,q//8)
                    a=pair&((1<<ob)-1);b=pair>>ob
                    assert 0<=a<b<len(prev)
                    v=(prev[a]&prev[b]) if q//4%2==0 else (prev[a]|prev[b])
                    ws=[v]+([prev[a]] if q%2 else [])+([prev[b]] if q//2%2 else [])
                    ws += [w for pos,w in enumerate(prev) if pos not in (a,b)]
                assert 0<=auto<len(maps)
                decoded[s].append(tuple(sorted(action(w,auto) for w in ws)))
        assert len(set(decoded[s]))==len(raw) and set(decoded[s])==set(raw)
        for j,ws in enumerate(decoded[s]):assert locate(s,ws)==j
        total+=len(raw)
    blocks={}
    pattern=r"theorem "+name+r"check_\d+_\d+ : span \("+name+r"Z (\d+)\) (\d+) (\d+) = true := by decide \+kernel"
    for s,c,o in re.findall(pattern,checks):
        s,c,o=map(int,[s,c,o]);blocks.setdefault(s,[]).append((o,c));blocks_total+=1
    for s in range(cap+1):
        off=0
        for o,c in blocks.get(s,[]):assert o==off and c>0;off+=c
        assert off==N.get(s,0)
    print("PASS parent/CHD",idx,"states",sum(N.values()),"group",len(maps),flush=True)
print("PASS all31 compact parent decodings, exact saved-state sets, every CHD slot and kernel-block coverage",flush=True)
print("TOTAL states",total,"kernel blocks",blocks_total,flush=True)
print("Scope: independent data audit; full Lean elaboration and local checker remain required.",flush=True)
