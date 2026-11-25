#!/usr/bin/env python3
"""Short prototype: two supergraph factors, shared bicliques and OR subsets."""
import argparse
from collections import Counter
import itertools
import json
from pathlib import Path
import random
import time

EDGES = [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),
         (3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),
         (6,8),(6,9),(6,11)]
N = [sum(1 << (v-7) for u,v in EDGES if u == i) for i in range(7)]
FULL = (1 << 49)-1
TARGET = sum(1 << (u*7+v-7) for u,v in EDGES)

def rectangle(a,b):
    return sum(b << (7*u) for u in range(7) if a >> u & 1)

ROWS = []
for a in range(128):
    b = 127
    for u in range(7):
        if a >> u & 1:
            b &= ~N[u]
    if sum(1 << u for u in range(7) if not N[u] & b) == a:
        ROWS.append((a,b))
MIXED = [(a,b) for a,b in ROWS if a and b]
FORBIDDEN = [rectangle(a,b) for a,b in MIXED]
BOUNDARY = [(1 << u) | (1 << v) for u,v in EDGES] + [a | (b << 7) for a,b in ROWS]
SIGS = [sum(1 << j for j,x in enumerate(BOUNDARY) if x >> i & 1) for i in range(14)]
TARGET_SIG = (1 << len(EDGES))-1
LABEL_MASK = (1 << len(MIXED))-1

def factors(labels):
    h = k = FULL
    for i,forbidden in enumerate(FORBIDDEN):
        if labels >> i & 1:
            h &= ~forbidden
        else:
            k &= ~forbidden
    assert h & k == TARGET
    return h,k

def maximal_rectangles(graph):
    rows = [(graph >> (7*u)) & 127 for u in range(7)]
    result = set()
    for a in range(1,128):
        b = 127
        for u in range(7):
            if a >> u & 1:
                b &= rows[u]
        if b:
            closure = sum(1 << u for u in range(7) if rows[u] & b == b)
            result.add((closure,b))
    result.update((1 << u,b) for u,b in enumerate(rows) if b)
    result.update((sum(1 << u for u in range(7) if rows[u] >> v & 1),1 << v)
                  for v in range(7) if any(rows[u] >> v & 1 for u in range(7)))
    return result

SHARED = maximal_rectangles(TARGET)
for a,b in list(SHARED):
    side = b if a.bit_count() == 1 else a
    subset = side
    while subset:
        SHARED.add((a,subset) if a.bit_count() == 1 else (subset,b))
        subset = (subset-1) & side

def candidates(h,k):
    result = []
    for a,b in maximal_rectangles(h) | maximal_rectangles(k) | SHARED:
        edges = rectangle(a,b)
        flags = (1 if edges & h == edges else 0) | (2 if edges & k == edges else 0)
        cover = (edges if flags & 1 else 0) | ((edges << 49) if flags & 2 else 0)
        result.append((a,b,flags,cover))
    return result

def greedy_cover(h,k,options,mode,rng):
    uncovered = h | (k << 49)
    selected = []
    left_known = set()
    right_known = set()
    while uncovered:
        best = None
        best_score = -1
        for candidate in options:
            a,b,flags,cover = candidate
            gain = (cover & uncovered).bit_count()
            if not gain:
                continue
            if mode == 0:
                cost = a.bit_count()+b.bit_count()
            else:
                cost = 2 + (0 if a in left_known else a.bit_count()-1) \
                         + (0 if b in right_known else b.bit_count()-1)
            if mode >= 2 and flags == 3:
                gain *= .2 if mode == 2 else .02
            score = gain / cost + rng.random()*1e-7
            if score > best_score:
                best_score,best = score,candidate
        assert best is not None
        selected.append(best)
        left_known.add(best[0])
        right_known.add(best[1])
        uncovered &= ~best[3]
    # Delete redundant rectangles, preferring to remove expensive ones.
    for candidate in sorted(selected,key=lambda c:c[0].bit_count()+c[1].bit_count(),reverse=True):
        coverage = 0
        for other in selected:
            if other is not candidate:
                coverage |= other[3]
        if coverage & (h | k << 49) == (h | k << 49):
            selected.remove(candidate)
    return selected

class Circuit:
    def __init__(self):
        self.gates = []
        self.sigs = list(SIGS)
        self.by_sig = {sig:i for i,sig in enumerate(SIGS)}

    def make(self,op,a,b):
        sig = self.sigs[a] & self.sigs[b] if op == 'and' else self.sigs[a] | self.sigs[b]
        if sig in self.by_sig:
            return self.by_sig[sig]
        result = len(self.sigs)
        self.gates.append((op,a,b))
        self.sigs.append(sig)
        self.by_sig[sig] = result
        return result

    def sum(self,values):
        values = list(dict.fromkeys(values))
        if not values:
            return None
        while len(values)>1:
            # Favor ORs already represented on the boundary, then balanced pairs.
            pair = max(itertools.combinations(range(len(values)),2),
                       key=lambda ij: ((self.sigs[values[ij[0]]] | self.sigs[values[ij[1]]])
                                       in self.by_sig,-abs(ij[0]-ij[1])))
            i,j = pair
            value = self.make('or',values[i],values[j])
            values = [v for q,v in enumerate(values) if q not in pair]
            values.append(value)
            values = list(dict.fromkeys(values))
        return values[0]

    def packed(self,out):
        live = set()
        def visit(w):
            if w < 14 or w in live:
                return
            live.add(w)
            _,a,b = self.gates[w-14]
            visit(a)
            visit(b)
        visit(out)
        remap = {i:i for i in range(14)}
        gates = []
        for w in sorted(live):
            op,a,b = self.gates[w-14]
            remap[w] = 14+len(gates)
            gates.append([op,remap[a],remap[b]])
        assert self.sigs[out] == TARGET_SIG
        return {'gates':gates,'output':remap[out],'size':len(gates)}

def shared_sums(circuit,masks,offset):
    expr = {mask:set(offset+i for i in range(7) if mask >> i & 1) for mask in masks}
    while any(len(values)>1 for values in expr.values()):
        frequency = Counter(pair for values in expr.values() for pair in itertools.combinations(sorted(values),2))
        a,b = max(frequency,key=lambda pair:(frequency[pair],-max(pair),-min(pair)))
        w = circuit.make('or',a,b)
        for values in expr.values():
            if a in values and b in values:
                values.difference_update((a,b))
                values.add(w)
    return {mask:next(iter(values)) for mask,values in expr.items()}

def synthesize(selected):
    circuit = Circuit()
    left = shared_sums(circuit,{c[0] for c in selected},0)
    right = shared_sums(circuit,{c[1] for c in selected},7)
    groups = {1:[],2:[],3:[]}
    common_edges = 0
    for a,b,flags,_ in selected:
        groups[flags].append(circuit.make('and',left[a],right[b]))
        if flags == 3:
            common_edges |= rectangle(a,b)
    common = circuit.sum(groups[3])
    if not groups[1] or not groups[2] or common_edges == TARGET:
        assert common is not None
        out = common
    else:
        a = circuit.sum(groups[1])
        b = circuit.sum(groups[2])
        out = circuit.make('and',a,b)
        if common is not None:
            out = circuit.make('or',common,out)
    packed = circuit.packed(out)
    packed['common_edge_count'] = common_edges.bit_count()
    packed['rectangles'] = [[a,b,flags] for a,b,flags,_ in selected]
    return packed

def shadow_count(packed):
    linear = [1 << i for i in range(14)]
    quadratic = [0]*14
    for op,a,b in packed['gates']:
        if op == 'or':
            linear.append(linear[a] | linear[b])
            quadratic.append(quadratic[a] | quadratic[b])
        else:
            linear.append(0)
            quadratic.append(sum(1 << j for j,(u,v) in enumerate(EDGES)
                                 if (linear[a] >> u & 1 and linear[b] >> v & 1)
                                 or (linear[a] >> v & 1 and linear[b] >> u & 1)))
    return quadratic[packed['output']].bit_count()

def evaluate_graphs(h,k,rng):
    options = candidates(h,k)
    variants = [greedy_cover(h,k,options,mode,rng) for mode in range(4)]
    # Four deterministic row/column covers, with exact common rectangle sharing.
    for orient_h,orient_k in itertools.product((0,1),repeat=2):
        selected = set()
        for graph,orientation in [(h,orient_h),(k,orient_k)]:
            for a,b in maximal_rectangles(graph):
                if (a.bit_count() == 1 if orientation == 0 else b.bit_count() == 1):
                    selected.add((a,b))
        chosen = [c for c in options if (c[0],c[1]) in selected]
        if chosen:
            variants.append(chosen)
    results = [synthesize(v) for v in variants]
    for result in results:
        result['factor_edge_counts'] = [h.bit_count(),k.bit_count()]
        result['shadow_edge_count'] = shadow_count(result)
    best = min(results,key=lambda c:(c['size'],-c['shadow_edge_count']))
    alternatives = [result for result in results if result['shadow_edge_count'] <= 18]
    nontrivial = min(alternatives,key=lambda c:(c['size'],-c['shadow_edge_count'])) if alternatives else None
    return best,nontrivial

def evaluate(labels,rng):
    best,nontrivial = evaluate_graphs(*factors(labels),rng)
    best['labels'] = labels
    if nontrivial:
        nontrivial['labels'] = labels
    return best,nontrivial

def full_check(result):
    errors = []
    for assignment in range(1<<14):
        values = [bool(assignment >> i & 1) for i in range(14)]
        for op,a,b in result['gates']:
            values.append(values[a] and values[b] if op == 'and' else values[a] or values[b])
        target = any(assignment >> u & 1 and assignment >> v & 1 for u,v in EDGES)
        if values[result['output']] != target:
            errors.append(assignment)
    assert not errors, errors[:10]
    result['full_truth_table_errors'] = 0

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--seconds',type=float,default=5)
    parser.add_argument('--seed',type=int,default=70)
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    rng = random.Random(args.seed)
    started = time.monotonic()
    structured = [sum(1 << i for i,(a,b) in enumerate(MIXED) if (a | b << 7) >> v & 1)
                  for v in range(14)]
    structured += [sum(1 << i for i,(a,b) in enumerate(MIXED) if a.bit_count() == size)
                   for size in (1,2,4)]
    for mask in range(1,128):
        structured.append(sum(1 << i for i,(a,b) in enumerate(MIXED) if (a & mask).bit_count()%2))
    best = None
    best_nontrivial = None
    tested = 0
    while time.monotonic()-started < args.seconds:
        if tested < len(structured):
            labels = structured[tested]
        elif rng.random() < .7 and best_nontrivial:
            labels = best_nontrivial['labels']
            for _ in range(rng.choice((1,1,2,3,5))):
                labels ^= 1 << rng.randrange(35)
        else:
            probability = rng.uniform(.1,.9)
            labels = sum(1 << i for i in range(35) if rng.random() < probability)
        result,nontrivial = evaluate(labels,rng)
        tested += 1
        if best is None or result['size'] < best['size']:
            best = result
            print(json.dumps({'event':'best','tested':tested,'seconds':time.monotonic()-started,
                              'size':best['size'],'common_edges':best['common_edge_count'],
                              'factors':best['factor_edge_counts']}),flush=True)
        if nontrivial and (best_nontrivial is None or nontrivial['size'] < best_nontrivial['size']):
            best_nontrivial = nontrivial
            print(json.dumps({'event':'nontrivial_best','tested':tested,'seconds':time.monotonic()-started,
                              'size':nontrivial['size'],'common_edges':nontrivial['common_edge_count'],
                              'shadow_edges':nontrivial['shadow_edge_count'],
                              'factors':nontrivial['factor_edge_counts']}),flush=True)
        if result['size'] <= 26:
            break
    full_check(best)
    if best_nontrivial:
        full_check(best_nontrivial)
    output = {'tested':tested,'duration_seconds':time.monotonic()-started,
              'best':best,'best_nontrivial':best_nontrivial,
              'row_types':dict(Counter(f'{a.bit_count()}x{b.bit_count()}' for a,b in MIXED))}
    args.output.write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({'event':'done','tested':tested,'seconds':output['duration_seconds'],
                      'best':best['size'],'best_nontrivial':None if best_nontrivial is None else best_nontrivial['size']}),flush=True)

if __name__ == '__main__':
    main()
