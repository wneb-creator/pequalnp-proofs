#!/usr/bin/env python3
"""Experimental soundness-auditable bottom-gate recurrence, not a Lean certificate."""
from functools import cache
from itertools import combinations
from time import monotonic
import json

EDGES = ((0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),
 (3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),
 (6,8),(6,9),(6,11))
INC = [sum(1<<i for i,e in enumerate(EDGES) if v in e) for v in range(14)]
EDGE_VERTICES = [(1<<a)|(1<<b) for a,b in EDGES]
START = monotonic()
CALLS = 0

@cache
def support(e):
    if not e: return 0
    bit = e & -e
    return support(e ^ bit) | EDGE_VERTICES[bit.bit_length()-1]

def restrict(state,v,value):
    if state is None: return None
    linear,edges = state
    bit = 1<<v
    if linear & bit:
        return None if value else (linear ^ bit,edges)
    if not (edges & INC[v]): return state
    new_edges = edges & ~INC[v]
    if not value: return linear,new_edges
    new_linear = linear | (support(edges & INC[v]) & ~bit)
    for w in range(14):
        if new_linear & (1<<w): new_edges &= ~INC[w]
    return new_linear,new_edges

@cache
def lower(state):
    global CALLS
    CALLS += 1
    if CALLS % 10000 == 0:
        print(json.dumps(dict(event='progress',states=CALLS,seconds=monotonic()-START)),flush=True)
        if monotonic()-START > 180: raise TimeoutError('internal 180-second experiment limit')
    if state is None: return 0
    linear,edges = state
    active = linear | support(edges)
    vertices = [v for v in range(14) if active & (1<<v)]
    n = len(vertices)
    if n <= 2: return max(0,n-1)
    child = {v:(restrict(state,v,0),restrict(state,v,1)) for v in vertices}
    child_lb = {v:tuple(lower(s) for s in child[v]) for v in vertices}
    best = 1000
    for x,y in combinations(vertices,2):
        for canalizing in (0,1): # 0 means AND, 1 means OR.
            # Unique occurrence of x through this bottom gate makes x irrelevant
            # whenever y is canalizing, and symmetrically for y.
            fx = 1 + (restrict(child[x][0],y,canalizing) != restrict(child[x][1],y,canalizing))
            fy = 1 + (restrict(child[y][0],x,canalizing) != restrict(child[y][1],x,canalizing))
            value = max(child_lb[x][0]+fx+(canalizing==0),
                        child_lb[x][1]+fx+(canalizing==1),
                        child_lb[y][0]+fy+(canalizing==0),
                        child_lb[y][1]+fy+(canalizing==1))
            best = min(best,value)
    result = max(n-1,best)
    if edges:
        ev = support(edges)
        star = edges.bit_count()+min((ev&127).bit_count(),(ev>>7).bit_count())-1+linear.bit_count()
    else:
        star = linear.bit_count()-1
    assert result <= star,(state,result,star)
    return result

try:
    root = (0,(1<<len(EDGES))-1)
    bound = lower(root)
    summary = dict(event='complete',root_lower_bound=bound,states=CALLS,
        seconds=monotonic()-START,cache=str(lower.cache_info()),
        one_zero_bounds=[lower(restrict(root,v,0)) for v in range(14)],
        one_one_bounds=[lower(restrict(root,v,1)) for v in range(14)])
    print(json.dumps(summary,sort_keys=True),flush=True)
except TimeoutError as exc:
    print(json.dumps(dict(event='incomplete',reason=str(exc),states=CALLS,
        seconds=monotonic()-START)),flush=True)
    raise SystemExit(2)
