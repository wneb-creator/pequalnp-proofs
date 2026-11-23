#!/usr/bin/env python3
"""Untrusted O(1)-lookup index for the existing exact isPerm verifier.

State order is increasing L742.hk. Output contains only packed Nat data, and
the generated Lean idx must still be used solely through `found`.
"""
import json
from pathlib import Path
import time

ROOT = Path('/tmp/oec/pequalnp-pilot-10/root984')
OUT = Path('/tmp/oec/pequalnp-pilot-10/fresh-full-proof/meta984')
P = 4294967291
W = 11400714819323198549
cache = {}

def hk(ws):
    for w in ws:
        if w not in cache:
            cache[w] = ((w % W + 317) ** 3) % W + 1
    return sum(cache[w] for w in ws) % P

def pack(xs, bits):
    value = 0
    for x in reversed(xs):
        assert 0 <= x < 1 << bits
        value = (value << bits) | x
    return hex(value)

def unpack(value,bits,i):
    return (value >> (bits*i)) & ((1 << bits)-1)

result = {}
start = time.monotonic()
for remaining in range(12):
    states = [tuple(int(x,16) for x in json.loads(line))
              for line in (ROOT / f'shard28.layer{remaining}.jsonl').read_text().splitlines()]
    ordered = sorted((hk(ws),ws) for ws in states)
    n = len(ordered)
    assert len({h for h,ws in ordered}) == n
    if n == 0:
        result[remaining] = {'n':0,'offset_bits':1,'slot_bits':1,'seed_bits':1,
                             'descriptor_bits':3,'index_bits':1,
                             'descriptors':'0x0','indices':'0x0'}
        continue
    buckets = [[] for _ in range(n)]
    for index,(h,ws) in enumerate(ordered):
        buckets[h % n].append((h,index))
    metadata = []
    indices = []
    for bucket in buckets:
        slots = len(bucket) ** 2
        offset = len(indices)
        if not slots:
            metadata.append((offset,0,0))
            continue
        seed = 1
        while True:
            locations = [(h * seed % P) % slots for h,index in bucket]
            if len(set(locations)) == len(bucket):
                break
            seed += 1
            assert seed < 1000000
        metadata.append((offset,slots,seed))
        indices.extend([n]*slots)
        for (h,index),location in zip(bucket,locations):
            indices[offset+location] = index
    ob = max(1,max(m[0] for m in metadata).bit_length())
    sb = max(1,max(m[1] for m in metadata).bit_length())
    mb = max(1,max(m[2] for m in metadata).bit_length())
    db = ob+sb+mb
    ib = max(1,n.bit_length())
    descriptors = [offset | slots<<ob | seed<<(ob+sb) for offset,slots,seed in metadata]
    # Verify both the logical table and the exact packed-Nat decoder.
    dt = int(pack(descriptors,db),16)
    it = int(pack(indices,ib),16)
    for index,(h,ws) in enumerate(ordered):
        desc = unpack(dt,db,h%n)
        offset = desc & ((1<<ob)-1)
        slots = (desc>>ob) & ((1<<sb)-1)
        seed = desc>>(ob+sb)
        actual = unpack(it,ib,offset+((h*seed)%P)%slots)
        assert actual == index
    result[remaining] = {'n':n,'offset_bits':ob,'slot_bits':sb,'seed_bits':mb,
                         'descriptor_bits':db,'index_bits':ib,
                         'descriptors':hex(dt),'indices':hex(it)}
    print('layer',remaining,'states',n,'slots',len(indices),
          'max bucket',max(map(len,buckets)),'max seed',max(m[2] for m in metadata),
          'packed bytes',(db*n+ib*len(indices)+7)//8,flush=True)
(OUT/'shard28.fks.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
print('PASS all132265 known keys resolve to their exact increasing-hash state index;',
      'elapsed',round(time.monotonic()-start,2),flush=True)
print('This is an untrusted lookup optimization, not a proof. Keep exact isPerm checking.',flush=True)
