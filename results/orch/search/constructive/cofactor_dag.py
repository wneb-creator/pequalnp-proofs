#!/usr/bin/env python3
"""Short monotone cofactor-DAG search over quadratic-plus-linear states."""
import argparse
from functools import lru_cache
import itertools
import json
from pathlib import Path
import random
import time

from factor_partition import BOUNDARY, EDGES, SIGS, TARGET_SIG, full_check

FULL_EDGES = (1 << len(EDGES))-1
TRUE_SIG = (1 << len(BOUNDARY))-1
INCIDENT = [sum(1 << j for j,e in enumerate(EDGES) if v in e) for v in range(14)]
EDGE_SIGS = [SIGS[u] & SIGS[v] for u,v in EDGES]

@lru_cache(None)
def support(edges):
    return sum(1 << v for v in range(14) if edges & INCIDENT[v])

@lru_cache(None)
def remove_dominated(linear,edges):
    for v in range(14):
        if linear >> v & 1:
            edges &= ~INCIDENT[v]
    return edges

@lru_cache(None)
def state_signature(linear,edges):
    result = 0
    for v in range(14):
        if linear >> v & 1:
            result |= SIGS[v]
    while edges:
        bit = edges & -edges
        result |= EDGE_SIGS[bit.bit_length()-1]
        edges ^= bit
    return result

@lru_cache(None)
def covers(edges):
    if not edges:
        return (0,)
    live_left = support(edges) & 127
    live_right = support(edges) & (127 << 7)
    best_size = 15
    best = []
    subset = live_left
    while True:
        right = 0
        for j,(u,v) in enumerate(EDGES):
            if edges >> j & 1 and not subset >> u & 1:
                right |= 1 << v
        cover = subset | right
        size = cover.bit_count()
        if size < best_size:
            best_size,best = size,[cover]
        elif size == best_size:
            best.append(cover)
        if subset == 0:
            break
        subset = (subset-1) & live_left
    # Both natural orientations plus minimum covers; cap only heuristic choices.
    return tuple(dict.fromkeys([live_left,live_right]+best[:4]+best[-4:]))

class Circuit:
    def __init__(self,rng):
        self.gates = []
        self.sig = {-1:0,-2:TRUE_SIG,**dict(enumerate(SIGS))}
        self.cone = {w:0 for w in self.sig}
        self.by_sig = {s:w for w,s in self.sig.items()}
        self.rng = rng

    def cost(self,w):
        return self.cone[w].bit_count()

    def make(self,op,a,b):
        signature = self.sig[a] & self.sig[b] if op == 'and' else self.sig[a] | self.sig[b]
        if signature == 0:
            return -1
        if signature == TRUE_SIG:
            return -2
        cone = self.cone[a] | self.cone[b]
        previous = self.by_sig.get(signature)
        if previous is not None and self.cost(previous) <= cone.bit_count()+1:
            return previous
        assert a >= 0 and b >= 0
        w = 14+len(self.gates)
        self.gates.append((op,a,b))
        self.sig[w] = signature
        self.cone[w] = cone | (1 << (w-14))
        self.by_sig[signature] = w
        return w

    def join(self,values):
        values = list(dict.fromkeys(v for v in values if v != -1))
        if -2 in values:
            return -2
        if not values:
            return -1
        while len(values)>1:
            choices = []
            for i,j in itertools.combinations(range(len(values)),2):
                a,b = values[i],values[j]
                natural = (self.cone[a] | self.cone[b]).bit_count()+1
                existing = self.by_sig.get(self.sig[a] | self.sig[b])
                saving = 0 if existing is None else natural-self.cost(existing)
                choices.append((saving,-natural,self.rng.random(),i,j))
            _,_,_,i,j = max(choices)
            w = self.make('or',values[i],values[j])
            values = list(dict.fromkeys([v for q,v in enumerate(values) if q not in (i,j)]+[w]))
        return values[0]

    def packed(self,out):
        assert self.sig[out] == TARGET_SIG
        remap = {i:i for i in range(14)}
        gates = []
        live = self.cone[out]
        for i,(op,a,b) in enumerate(self.gates):
            if live >> i & 1:
                remap[14+i] = 14+len(gates)
                gates.append([op,remap[a],remap[b]])
        return {'gates':gates,'output':remap[out],'size':len(gates)}

class Synth:
    def __init__(self,order,depth,rng,deadline,mode):
        self.order = order
        self.depth = depth
        self.rng = rng
        self.deadline = deadline
        self.mode = mode
        self.c = Circuit(rng)
        self.memo = {}
        self.flat_memo = {}
        self.states = 0

    def flat(self,linear,edges):
        key = (linear,edges)
        if key in self.flat_memo:
            old = self.flat_memo[key]
            return min((old,self.c.by_sig[self.c.sig[old]]),key=self.c.cost)
        alternatives = []
        for cover in covers(edges):
            owned = {}
            for j,(u,v) in enumerate(EDGES):
                if not edges >> j & 1:
                    continue
                if cover >> u & 1 and cover >> v & 1:
                    center,leaf = (u,v) if self.rng.randrange(2) else (v,u)
                else:
                    center,leaf = (u,v) if cover >> u & 1 else (v,u)
                owned.setdefault(center,[]).append(leaf)
            terms = [v for v in range(14) if linear >> v & 1]
            for center,leaves in owned.items():
                terms.append(self.c.make('and',center,self.c.join(leaves)))
            alternatives.append(self.c.join(terms))
        result = min(alternatives,key=self.c.cost)
        assert self.c.sig[result] == state_signature(linear,edges)
        self.flat_memo[key] = result
        return result

    def solve(self,linear,edges,depth):
        edges = remove_dominated(linear,edges)
        key = (linear,edges,depth)
        if key in self.memo:
            return self.memo[key]
        self.states += 1
        leaf = self.flat(linear,edges)
        if depth == 0 or not edges or time.monotonic() >= self.deadline:
            self.memo[key] = leaf
            return leaf
        active = linear | support(edges)
        possibilities = [v for v in self.order if active >> v & 1]
        if self.mode == 1:
            v = max(possibilities,key=lambda w:(bool(linear >> w & 1),(edges & INCIDENT[w]).bit_count()))
        elif self.mode == 2:
            v = min(possibilities,key=lambda w:(bool(linear >> w & 1),(edges & INCIDENT[w]).bit_count()))
        else:
            v = possibilities[0]
        if linear >> v & 1:
            zero = self.solve(linear & ~(1 << v),edges,depth-1)
            alternatives = [leaf,self.c.make('or',v,zero)]
        else:
            zero_edges = edges & ~INCIDENT[v]
            neighbors = 0
            for j,(a,b) in enumerate(EDGES):
                if edges >> j & 1:
                    if a == v:
                        neighbors |= 1 << b
                    elif b == v:
                        neighbors |= 1 << a
            one_linear = linear | neighbors
            one_edges = remove_dominated(one_linear,zero_edges)
            zero = self.solve(linear,zero_edges,depth-1)
            one = self.solve(one_linear,one_edges,depth-1)
            alternative_or = self.c.make('or',zero,self.c.make('and',v,one))
            alternative_and = self.c.make('and',self.c.make('or',v,zero),one)
            alternatives = [leaf,alternative_or,alternative_and]
        result = min(alternatives,key=self.c.cost)
        assert self.c.sig[result] == state_signature(linear,edges)
        self.memo[key] = result
        return result

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--seconds',type=float,default=24)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--seed',type=int,default=70)
    args = parser.parse_args()
    rng = random.Random(args.seed)
    started = time.monotonic()
    deadline = started+args.seconds
    best = None
    records = []
    initial_orders = [list(range(14)),list(range(7,14))+list(range(7)),
                      [v for pair in zip(range(7),range(7,14)) for v in pair]]
    while time.monotonic()<deadline:
        trial = len(records)
        order = initial_orders[trial] if trial<len(initial_orders) else rng.sample(range(14),14)
        depth = [2,4,6,8,10,14][trial%6]
        mode = (trial//6)%3
        synth = Synth(order,depth,rng,deadline,mode)
        out = synth.solve(0,FULL_EDGES,depth)
        result = synth.c.packed(out)
        result.update({'order':order,'depth':depth,'mode':mode,'states':synth.states,
                       'allocated_gates':len(synth.c.gates)})
        records.append({k:result[k] for k in ['size','depth','mode','states','allocated_gates']})
        if best is None or result['size']<best['size']:
            best = result
            print(json.dumps({'event':'best','trial':trial,'size':result['size'],'depth':depth,
                              'states':synth.states,'seconds':time.monotonic()-started}),flush=True)
        if best['size']<=26:
            break
    full_check(best)
    output = {'duration_seconds':time.monotonic()-started,'trials':len(records),'records':records,'best':best}
    args.output.write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({'event':'done','seconds':output['duration_seconds'],'trials':len(records),
                      'best':best['size'],'full_truth_table_errors':best['full_truth_table_errors']}),flush=True)

if __name__ == '__main__':
    main()
