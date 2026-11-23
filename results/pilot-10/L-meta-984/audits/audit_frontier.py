#!/usr/bin/env python3
"""Independent literal audit of the L742-compatible shard-28 frontier."""
import itertools
import json
from pathlib import Path
import time

ROOT = Path('/tmp/oec/pequalnp-pilot-10/root984')
meta = json.loads((ROOT / 'shard28.meta.json').read_text())
edges = [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(3,4),(3,6),(5,6)]
edge_masks = [(1 << a) | (1 << b) for a,b in edges]
negative = [x for x in range(128) if all((x & e) != e for e in edge_masks)]
maximal = [x for x in negative if all(y == x or x & y != x for y in negative)]
rows = list(itertools.product(maximal, edge_masks))
assert meta['negative_rows'] == [a for a,b in rows]
assert meta['positive_rows'] == [b for a,b in rows]
k = len(rows)
assert k == meta['k'] == 63
mask = (1 << k) - 1
goal = mask << k
inputs = tuple(sum(((a >> v) & 1) << i | ((b >> v) & 1) << (k+i)
                   for i,(a,b) in enumerate(rows)) for v in range(7))
assert sorted(inputs) == [int(w,16) for w in meta['inputs_hex']]

def covers(ws):
    cover = 0
    for w in ws:
        cover |= (w >> k) & (w ^ mask)
    return cover & mask == mask

assert covers(inputs)
for keep in range(127):
    assert not covers([v for i,v in enumerate(inputs) if keep >> i & 1])

layers = {}
for s in range(12):
    raw = [tuple(int(w,16) for w in json.loads(line))
           for line in (ROOT / f'shard28.layer{s}.jsonl').read_text().splitlines()]
    layers[s] = set(raw)
    assert len(raw) == len(layers[s])
    for ws in raw:
        assert ws == tuple(sorted(ws))
        assert len(ws) <= s + 1
        assert covers(ws)
        assert all(0 <= w < 1 << (2*k) for w in ws)
assert layers[11] == {tuple(sorted(inputs))}
assert (goal,) not in layers[0]
unique = set().union(*(set(ws) for layer in layers.values() for ws in layer))
print('rows', len(rows), 'maximal negatives', maximal, flush=True)
print('input coordinate order', [hex(w) for w in inputs], flush=True)
print('states', sum(map(len,layers.values())), 'unique wire values', len(unique), flush=True)

# Generate L742.next literally by erasing one occurrence of each selected value.
# Duplicate selections are harmless; each candidate is checked modulo permutation.
started = time.monotonic()
for s in range(11,0,-1):
    generated = set()
    attempted = 0
    def add(ws):
        global attempted
        attempted += 1
        if len(ws) <= s and covers(ws):
            generated.add(tuple(sorted(ws)))
    for ws in layers[s]:
        slack = s + 1 - len(ws)
        for a in ws:
            ra = list(ws)
            ra.remove(a)
            if slack >= 1:
                add([a] + ra)
                if slack >= 2:
                    add([a,a] + ra)
            for b in ra:
                if a > b:
                    continue
                rest = ra.copy()
                rest.remove(b)
                for w in (a | b, a & b):
                    add([w] + rest)
                    if slack >= 1:
                        add([w,a] + rest)
                        add([w,b] + rest)
                    if slack >= 2:
                        add([w,a,b] + rest)
    assert generated == layers[s-1], (s,len(generated),len(layers[s-1]),
                                     len(generated-layers[s-1]),len(layers[s-1]-generated))
    print('PASS transition', s, 'to',s-1, 'states', len(generated),
          'literal candidates', attempted, 'elapsed',round(time.monotonic()-started,2), flush=True)
print('PASS: exact L742 successor closure, directed coverage, row encoding, and all proper input subsets', flush=True)
print('Scope: independent finite audit only; the Lean certificate and semantic circuit bridge remain separate obligations.', flush=True)
