#!/usr/bin/env python3
"""Independent grouped-state decoder, classifier and offset/CHD audit."""
from pathlib import Path
import ast,json,re,sys
base=Path(sys.argv[1]);new=base/"direct_tight";source=Path(sys.argv[2]);total=groups_total=0;MOD=11400714819323198549

def fld(v,b,i):return (v>>(b*i))&((1<<b)-1)
def hk(ws):return sum((w+317)**3+1 for w in ws)%4294967291
for graph in range(10):
    name=f"C{graph}_";data=json.loads((new/f"C{graph}.data.json").read_text());text=(new/f"C{graph}.data.fragment.lean").read_text()
    initial=data["initial"];K=len(initial);ib=data["dictionary_index_bits"];vb=data["word_bits"];countgroups=data["groups"]
    assert data["word_bits"] == 32 and data["source_mode"] == "tight"
    def constant(n):return int(re.search(r"def "+name+n+r" : Nat := (0x[0-9a-f]+|\d+)",text).group(1),0)
    values=constant("values");patterns=constant("patterns")
    assert values==int(data["packed_values_hex"],0) and patterns==int(data["packed_patterns_hex"],0)
    assert [fld(patterns,2*K,i) for i in range(len(data["pattern_codes"]))]==data["pattern_codes"]
    assert [fld(values,vb,i) for i in range(len(data["noninputs"]))]==data["noninputs"]
    def nat_table(n):
        body=re.search(r"def "+name+n+r" : Nat → Nat\n(.*?)(?=\ndef |$)",text,re.S).group(1)
        assert "| _ => 0" in body
        return {int(a):int(b,0) for a,b in re.findall(r"\| (\d+) => (0x[0-9a-f]+|\d+)",body)}
    def list_table(n):
        body=re.search(r"def "+name+n+r" : Nat → List[^\n]*\n(.*?)(?=\ndef |$)",text,re.S).group(1)
        assert "| _ => []" in body
        return {int(a):ast.literal_eval(b) for a,b in re.findall(r"\| (\d+) => (\[.*\])",body)}
    Ns,counts,specs=map(nat_table,["N","counts","specs"]);seeds,records=map(list_table,["seeds","records"])
    S=re.search(r"def "+name+r"S.*?qGroupedState ([^\n]+)",text,re.S).group(1)
    assert S==f"{name}initial {countgroups} {vb} {ib} {name}patterns {name}values ({name}counts s) ({name}specs s) ({name}records s) j"
    assert f"qGroupedIndex {name}initial ({name}counts s) ({name}specs s) ({name}seeds s) ws" in text
    assert ast.literal_eval(re.search(r"def "+name+r"initial : List Nat := (\[.*?\])",text).group(1))==initial
    for ss,layer in data["layers"].items():
        s=int(ss);N=layer["N"];c=counts[s];sp=specs[s]
        assert N==Ns[s] and c==int(layer["packed_counts_hex"],0) and sp==int(layer["packed_specs_hex"],0)
        assert len(seeds[s])==len(records[s])==countgroups
        sizes=[fld(c,12,g) for g in range(countgroups)];assert sum(sizes)==N
        offsets=[];offset=0
        for g,sz in enumerate(sizes):offsets.append(offset);offset+=sz
        expected=[tuple(int(w,16) for w in json.loads(line)) for line in (new/f"C{graph}.layer{s}.jsonl").read_text().splitlines()]
        prior=[tuple(json.loads(line)) for line in (source/f"{data['source_prefix']}.layer{s}.jsonl").read_text().splitlines()]
        assert len(expected)==len(set(expected))==N and set(expected)==set(prior)
        for gg,info in layer["groups"].items():
            g=int(gg);spec=fld(sp,12,g);cb=spec&3;pb=(spec>>2)&31;sb=(spec>>7)&31;flag=1<<(sb-1)
            assert info["N"]==sizes[g] and info["offset"]==offsets[g]
            assert (cb,pb,sb,flag)==(info["countBits"],info["patternBits"],info["seedBits"],info["flag"])
            assert info["buckets"]==max(1,(sizes[g]+3)//4)
            assert seeds[s][g]==int(info["seeds_hex"],0)
            assert records[s][g]==[int(x,0) for x in info["record_blocks_hex"]]
            groups_total+=1
        decoded=[]
        for j,ws in enumerate(expected):
            g=next(g for g in range(countgroups) if j<offsets[g]+sizes[g]);loc=j-offsets[g]
            spec=fld(sp,12,g);cb=spec&3;pb=(spec>>2)&31;head=pb if pb else cb*K;width=head+ib*g
            assert width==layer["groups"][str(g)]["recordBits"]
            rec=fld(records[s][g][loc//256],width,loc%256)
            inputrec=fld(patterns,2*K,rec&((1<<pb)-1)) if pb else rec
            inputbits=2 if pb else cb
            raw=[w for i,w in enumerate(initial) for _ in range(fld(inputrec,inputbits,i))]
            other=rec>>head
            raw += [fld(values,vb,idx-1) for q in range(g) if (idx:=fld(other,ib,q))]
            assert tuple(sorted(raw))==ws and sum(w not in initial for w in raw)==g
            classified=sum(w not in initial for w in ws);assert classified==g
            sb=(spec>>7)&31;flag=1<<(sb-1);h=hk(raw);code=fld(seeds[s][g],sb,h%max(1,(sizes[g]+3)//4))
            local=code-flag if code>=flag else pow(h+code+317,3,MOD)%sizes[g]
            assert offsets[g]+local==j
            decoded.append(tuple(sorted(raw)))
        assert set(decoded)==set(prior)
        total+=N
    print("PASS grouped direct",graph,"states",sum(Ns.values()),"maxgroups",countgroups,flush=True)
print("PASS all10 actual grouped fragments: exact multiset decoding, group classifier, offsets andCHDslots; same fullstatecollections as independently audited final-tight source layers",flush=True)
print("TOTAL states",total,"nonemptygroups",groups_total,flush=True)
print("Scope: computational source/data audit, not a completed Lean theorem or checker verdict.",flush=True)

assert total == 16611
print("SOURCE SHA256 manifest")
import hashlib
for p in sorted(new.glob("*.lean")):
 print(hashlib.sha256(p.read_bytes()).hexdigest(),p.name)
