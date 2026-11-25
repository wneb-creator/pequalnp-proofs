import collections
import itertools
import json
from pathlib import Path
import time

base = Path('/tmp/oec/pequalnp-pilot-62')
data = json.loads((base / 'geometry-data.json').read_text())
start = time.monotonic()

def mul(a,b):
    raw = [0]*5
    for i,x in enumerate(a):
        for j,y in enumerate(b): raw[i+j] = (raw[i+j]+x*y)%3
    # alpha^3 = alpha - 1 over F3.
    for i in (4,3):
        raw[i-2] = (raw[i-2]+raw[i])%3
        raw[i-3] = (raw[i-3]+2*raw[i])%3
    return tuple(raw[:3])

def power(a,n):
    out = (1,0,0)
    for _ in range(n): out = mul(out,a)
    return out

alpha = (0,1,0)
powers = [power(alpha,n) for n in range(26)]
assert powers[13] == (2,0,0) and power(alpha,26) == (1,0,0)
assert len(set(powers)) == 26
trace_zero = []
for i,v in enumerate(powers[:13]):
    cube,ninth = power(v,3),power(v,9)
    trace = tuple((a+b+c)%3 for a,b,c in zip(v,cube,ninth))
    if trace == (0,0,0): trace_zero.append(i)
assert trace_zero == [0,1,3,9]
point_of = {}
for p,v in enumerate(powers[:13]):
    point_of[v] = p
    point_of[tuple(2*x%3 for x in v)] = p
assert len(point_of) == 26
line_masks = data['lines']
line_of = {m:i for i,m in enumerate(line_masks)}
matrices = [
    [[0,1,0],[1,0,0],[0,0,1]],
    [[0,1,0],[0,0,1],[1,0,0]],
    [[1,1,0],[0,1,0],[0,0,1]],
    [[2,0,0],[0,1,0],[0,0,1]],
]
generators = []
for matrix in matrices:
    action = [point_of[tuple(sum(row[j]*v[j] for j in range(3))%3 for row in matrix)]
              for v in powers[:13]]
    assert len(set(action)) == 13
    line_action = [line_of[sum((mask>>p&1)<<action[p] for p in range(13))] for mask in line_masks]
    generators.append(action+[13+l for l in line_action])
generators.append([13+(-p)%13 for p in range(13)]+[(-l)%13 for l in range(13)])
positive = [(1<<p)|(1<<(13+l)) for p in range(13) for l in range(13) if line_masks[l]>>p&1]
negative = [q['S']|(q['D']<<13) for q in data['generic']]
positive_index = {q:i for i,q in enumerate(positive)}
def move(mask,action): return sum((mask>>j&1)<<action[j] for j in range(26))
signature_masks = [sum((q>>i&1)<<j for j,q in enumerate(positive)) for i in range(26)]
signature_masks += [1<<i for i in range(52)]
assert len(set(signature_masks)) == 78
signature_generators = []
for action in generators:
    assert sorted(action) == list(range(26))
    assert {move(q,action) for q in positive} == set(positive)
    assert {move(q,action) for q in negative} == set(negative)
    edges = [positive_index[move(q,action)] for q in positive]
    signature_generators.append(action+[26+j for j in edges])
    for i,mask in enumerate(signature_masks):
        moved = sum((mask>>b&1)<<edges[b] for b in range(52))
        assert moved == signature_masks[signature_generators[-1][i]]
pairs = {(a,b) for a,b in itertools.combinations(range(78),2)
         if signature_masks[a]&~signature_masks[b] and signature_masks[b]&~signature_masks[a]}
remaining = set(pairs)
orbits = []
while remaining:
    root = min(remaining)
    orbit = {root}
    queue = collections.deque([root])
    while queue:
        a,b = queue.popleft()
        for action in signature_generators:
            moved = tuple(sorted((action[a],action[b])))
            assert moved in pairs
            if moved not in orbit:
                orbit.add(moved)
                queue.append(moved)
    remaining -= orbit
    orbits.append({'representative_indices':list(root),
                   'representative_masks':sorted([signature_masks[i] for i in root]),
                   'size':len(orbit)})
group = {tuple(range(26))}
queue = collections.deque(group)
while queue:
    action = queue.popleft()
    for generator in generators:
        product = tuple(generator[action[j]] for j in range(26))
        if product not in group:
            group.add(product)
            queue.append(product)
out = {'positive_samples':positive,'negative_samples':negative,
       'input_signature_masks':signature_masks[:26],
       'closed_initial_signature_masks':signature_masks,
       'generators':generators,'group_size':len(group),'first_OR_pairs':len(pairs),
       'first_OR_orbits':orbits,'field_trace_zero_exponents':trace_zero,
       'elapsed_seconds':time.monotonic()-start}
(base / 'global-first-or-symmetry.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'group_size':len(group),'first_OR_pairs':len(pairs),
                  'first_OR_orbits':len(orbits),'orbit_sizes':[o['size'] for o in orbits],
                  'elapsed_seconds':time.monotonic()-start}))
