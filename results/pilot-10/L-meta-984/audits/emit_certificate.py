#!/usr/bin/env python3
"""Emit untrusted L742-compatible data and kernel-check statements.

Usage: emit_certificate.py PREFIX POOL_FILE OUTPUT_PREFIX NAMESPACE [CHUNK]
The fragments are inserted inside PEqualNP.Outside.L_meta_984.Cert.
"""
import argparse
import hashlib
import json
from pathlib import Path

ap=argparse.ArgumentParser()
ap.add_argument('prefix',type=Path)
ap.add_argument('pool_file',type=Path)
ap.add_argument('output_prefix',type=Path)
ap.add_argument('namespace')
ap.add_argument('chunk',nargs='?',type=int,default=8)
args=ap.parse_args()
meta=json.loads(Path(str(args.prefix)+'.meta.json').read_text())
budget=meta['budget']
k=meta['k']
W=11400714819323198549
P=4294967291
cache={}
def hk(ws):
    for w in ws:
        if w not in cache:
            cache[w]=((w%W+317)**3)%W+1
    return sum(cache[w] for w in ws)%P
def pack(xs,bits):
    ans=0
    for x in reversed(xs):
        assert 0<=x<1<<bits
        ans=(ans<<bits)|x
    return f'0x{ans:x}'
def unpack(value,bits,i):
    return (value>>(bits*i))&((1<<bits)-1)
layers={}
for s in range(budget+1):
    raw=[tuple(int(w,16) for w in json.loads(line)) for line in
         Path(str(args.prefix)+f'.layer{s}.jsonl').read_text().splitlines()]
    assert len(set(raw))==len(raw)
    assert all(ws==tuple(sorted(ws)) for ws in raw)
    ordered=sorted((hk(ws),ws) for ws in raw)
    assert len({h for h,ws in ordered})==len(ordered),('hash collision',s)
    layers[s]=ordered
assert len(layers[budget])==1
assert layers[budget][0][1]==tuple(int(w,16) for w in meta['inputs_hex'])
values=sorted(set(w for layer in layers.values() for h,ws in layer for w in ws))
ids={w:i for i,w in enumerate(values)}
ib=max(1,(len(values)-1).bit_length())
stride=max((len(ws) for layer in layers.values() for h,ws in layer),default=1)
lb=max(1,stride.bit_length())
depth=max((len(layer).bit_length() for layer in layers.values()),default=0)+1
pool=[int(line) for line in args.pool_file.read_text().splitlines() if line.strip()]
assert len(set(pool))==len(pool)
def natfun(name,vals):
    lines=[f'def {name} : Nat → Nat']
    lines += [f'  | {s} => {v}' for s,v in vals.items() if v not in (0,'0x0')]
    return '\n'.join(lines+['  | _ => 0'])
data=[f'namespace {args.namespace}',natfun('N',{s:len(l) for s,l in layers.items()})]
data.append('def V : Array Nat := #[\n  '+',\n  '.join(f'0x{w:x}' for w in values)+'\n]')
hashes={s:pack([h for h,ws in layer],32) for s,layer in layers.items()}
lengths={s:pack([len(ws) for h,ws in layer],lb) for s,layer in layers.items()}
states={s:pack([j for h,ws in layer for j in
               [ids[w] for w in ws]+[0]*(stride-len(ws))],ib) for s,layer in layers.items()}
# Independently check the emitted packed representation and binary lookup.
for s,layer in layers.items():
    ht,lt,dt=int(hashes[s],16),int(lengths[s],16),int(states[s],16)
    for index,(h,ws) in enumerate(layer):
        got=tuple(values[unpack(dt,ib,stride*index+t)] for t in range(unpack(lt,lb,index)))
        assert got==ws
        lo,hi=0,len(layer)
        for _ in range(depth):
            if lo+1<hi:
                mid=(lo+hi)//2
                if unpack(ht,32,mid)<=h: lo=mid
                else: hi=mid
        assert lo==index
data += [natfun('HT',hashes),natfun('LT',lengths),natfun('DT',states)]
data += [f'def S (s j : Nat) : List Nat :=\n  (List.range (fld (LT s) {lb} j)).map '
         f'(fun t => V.getD (fld (DT s) {ib} ({stride} * j + t)) 0)',
         f'def idx (s : Nat) (zs : List Nat) : Nat := bsr (HT s) 32 (hk zs) {depth} 0 (N s)',
         'def pool : List Nat := ['+', '.join(map(str,pool))+']',
         f'def Z (s : Nat) : Nat → Bool := barScore {k} S N idx pool s',
         f'end {args.namespace}']
data_text='\n\n'.join(data)+'\n'
args.output_prefix.parent.mkdir(parents=True,exist_ok=True)
Path(str(args.output_prefix)+'.data.fragment.lean').write_text(data_text)

def declaration(name,s,count,offset):
    return (f'set_option maxRecDepth 32768 in\nset_option maxHeartbeats 0 in\n'
            f'theorem {name} : span (Z {s}) {count} {offset} = true := by decide +kernel\n')
largest=max(layers,key=lambda s:len(layers[s]))
bench=[f'namespace {args.namespace}',declaration('benchmark_one',largest,1,0),
       declaration('benchmark_four',largest,min(4,len(layers[largest])),0),
       f'end {args.namespace}']
Path(str(args.output_prefix)+'.benchmark.fragment.lean').write_text('\n'.join(bench)+'\n')

checks=[f'namespace {args.namespace}']
def balanced(s,blocks):
    if len(blocks)==1:
        offset,count,name=blocks[0]
        return offset,count,name
    cut=len(blocks)//2
    left=balanced(s,blocks[:cut]);right=balanced(s,blocks[cut:])
    assert left[0]+left[1]==right[0]
    return left[0],left[1]+right[1],(
      f'(@span_join (Z {s}) {left[1]} {left[0]} {right[1]} {left[2]} {right[2]})')
for s,layer in layers.items():
    blocks=[]
    for offset in range(0,len(layer),args.chunk):
        count=min(args.chunk,len(layer)-offset)
        name=f'check_{s}_{offset}'
        checks.append(declaration(name,s,count,offset))
        blocks.append((offset,count,name))
    if blocks:
        expression=balanced(s,blocks)[2]
        checks.append(f'theorem checked_{s} : span (Z {s}) {len(layer)} 0 = true :=\n  {expression}')
checks.append(f'theorem checked (s : Nat) (hs : s ≤ {budget}) : ∀ i < N s, Z s i = true := by\n  interval_cases s')
for s,layer in layers.items():
    if not layer:
        checks.append('  · simp [N]')
    else:
        checks.append(f'  · intro i hi\n    exact span_ok checked_{s} i (Nat.zero_le i) (by simpa [N] using hi)')
checks.append(f'end {args.namespace}')
Path(str(args.output_prefix)+'.checks.fragment.lean').write_text('\n\n'.join(checks)+'\n')
summary={'prefix':str(args.prefix),'namespace':args.namespace,'k':k,'budget':budget,
         'states':{s:len(layer) for s,layer in layers.items()},'unique_values':len(values),
         'intern_bits':ib,'length_bits':lb,'stride':stride,'binary_search_steps':depth,
         'pool_size':len(pool),'data_sha256':hashlib.sha256(data_text.encode()).hexdigest()}
Path(str(args.output_prefix)+'.emitter.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
