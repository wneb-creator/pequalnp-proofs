#!/usr/bin/env python3
"""Exact small checks for the cubic gate-elimination assessment; no SAT claims."""
from itertools import combinations, permutations, product
from collections import Counter, deque
import json

EDGES = frozenset(((0,7),(0,8),(0,10),(1,7),(1,9),(1,13),
    (2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),
    (5,9),(5,10),(5,12),(6,8),(6,9),(6,11)))

# State = free variables, linear minterms, quadratic minterms, constant-one bit.
INITIAL = (frozenset(range(14)), frozenset(), EDGES, False)

def restrict(state, v, value):
    free, linear, edges, one = state
    assert v in free
    free = free - {v}
    if one or (value and v in linear):
        return free, frozenset(), frozenset(), True
    new_linear = linear - {v}
    if value:
        new_linear |= {b if a == v else a for a, b in edges if v in (a,b)}
    new_edges = frozenset((a,b) for a,b in edges
        if v not in (a,b) and a not in new_linear and b not in new_linear)
    return free, frozenset(new_linear), new_edges, False

def function_key(state):
    return state[1:]

def pair_subfunction_counts(state):
    result = []
    for a,b in combinations(sorted(state[0]), 2):
        keys = {function_key(restrict(restrict(state,a,x),b,y))
                for x,y in product((0,1), repeat=2)}
        result.append((a,b,len(keys)))
    return result

def essential(state):
    if state[3]:
        return frozenset()
    return state[1] | frozenset(v for edge in state[2] for v in edge)

def restrict_zeros(vertices):
    state = INITIAL
    for v in vertices:
        state = restrict(state,v,0)
    return state

def cover_number(edges):
    vertices = sorted({v for edge in edges for v in edge})
    for k in range(len(vertices)+1):
        for chosen in combinations(vertices,k):
            cover = set(chosen)
            if all(a in cover or b in cover for a,b in edges):
                return k
    raise AssertionError("unreachable")

adj = {v:{b if a == v else a for a,b in EDGES if v in (a,b)} for v in range(14)}
assert all(len(adj[v]) == 3 for v in adj)
assert all(len(adj[a] & adj[b]) <= 1 for a,b in combinations(range(14),2))

def distance(a,b):
    q = deque([(a,0)])
    seen = {a}
    while q:
        v,d = q.popleft()
        if v == b: return d
        for w in adj[v] - seen:
            seen.add(w)
            q.append((w,d+1))
    raise AssertionError("disconnected")

zero_checks = []
for k in range(4):
    bad_q, nonessential, q_min_counts = [], [], Counter()
    for vertices in combinations(range(14),k):
        state = restrict_zeros(vertices)
        minimum = min(c for _,_,c in pair_subfunction_counts(state))
        q_min_counts[minimum] += 1
        if minimum < 3: bad_q.append(vertices)
        if essential(state) != state[0]: nonessential.append(vertices)
    zero_checks.append(dict(zeros=k, min_pair_count_distribution=dict(q_min_counts),
        failing_Q23=len(bad_q), nonessential_remaining=len(nonessential),
        first_failing_Q23=bad_q[:3]))

one_checks = []
for v in range(14):
    state = restrict(INITIAL,v,1)
    counts = pair_subfunction_counts(state)
    assert essential(state) == state[0]
    assert len(state[1]) == 3 and len(state[2]) == 12
    assert len({w for edge in state[2] for w in edge}) == 10
    one_checks.append(dict(vertex=v, linear=sorted(state[1]), edges=len(state[2]),
        graph_cover=cover_number(state[2]), min_pair_count=min(c for _,_,c in counts),
        count_pairs_below_three=sum(c<3 for _,_,c in counts)))

cofactors = Counter()
for k in (1,2):
    for vertices in combinations(range(14),k):
        state = restrict_zeros(vertices)
        tau = cover_number(state[2])
        kind = "one_zero" if k == 1 else "two_zeros_distance_%d" % distance(*vertices)
        cofactors[(kind,len(state[0]),len(state[2]),tau,len(state[2])+tau-1)] += 1

# Exhaust all labelled Steiner triple systems on seven points by exact cover.
pairs = list(combinations(range(7),2))
pair_index = {p:i for i,p in enumerate(pairs)}
triples = list(combinations(range(7),3))
triple_masks = [sum(1 << pair_index[p] for p in combinations(t,2)) for t in triples]
by_pair = [[i for i,m in enumerate(triple_masks) if m & (1<<j)] for j in range(21)]
full = (1<<21)-1
systems = set()
def exact_cover(used, chosen):
    if used == full:
        systems.add(tuple(sorted(triples[i] for i in chosen)))
        return
    first = ((full ^ used) & -(full ^ used)).bit_length()-1
    for i in by_pair[first]:
        if not (used & triple_masks[i]):
            exact_cover(used | triple_masks[i], chosen+[i])
exact_cover(0,[])
assert len(systems) == 30
representative = next(iter(systems))
orbit = {tuple(sorted(tuple(sorted(p[v] for v in t)) for t in representative))
         for p in permutations(range(7))}
assert orbit == systems
heawood_system = tuple(sorted(tuple(sorted(adj[v])) for v in range(7,14)))
assert heawood_system in systems

# Explicit cheap counterexamples to tempting weakened universal claims.
for bits in product((False,True),repeat=6):
    circuit = ((bits[0] or bits[1]) or bits[2]) and ((bits[3] or bits[4]) or bits[5])
    graph = any(bits[a] and bits[b] for a in range(3) for b in range(3,6))
    assert circuit == graph
for x,y,z in product((False,True),repeat=3):
    four_gate_majority = (x and y) or ((x or y) and z)
    assert four_gate_majority == ((x and y) or (x and z) or (y and z))

report = dict(
    scope="Finite graph/cofactor checks only; no circuit lower-bound certificate",
    vertices=14, edges=len(EDGES), cubic=True, no_C4=True,
    zero_restriction_checks=zero_checks, one_restriction_checks=one_checks,
    cofactor_star_upper_bounds=[dict(kind=k[0],free_variables=k[1],edges=k[2],
        minimum_vertex_cover=k[3],star_upper_bound=k[4],instances=v)
        for k,v in sorted(cofactors.items())],
    seven_point_triple_systems=len(systems), systems_in_one_permutation_orbit=len(orbit),
    smaller_cubic_bipartite_C4free_impossible="3m distinct neighbor pairs <= m(m-1)/2 implies m>=7",
    K33_five_gate_truth_table_inputs=64, majority3_four_gate_truth_table_inputs=8)
print(json.dumps(report,indent=2,sort_keys=True))
