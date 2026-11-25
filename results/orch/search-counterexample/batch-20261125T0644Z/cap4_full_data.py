import itertools
import json
from pathlib import Path

base = Path('/tmp/oec/pequalnp-pilot-62')
geometry = json.loads((base / 'geometry-data.json').read_text())
points = [0, 1, 2, 5]
lines = [l for l in range(13) if any((p-l) % 13 in (0,1,3,9) for p in points)]
vertices = points + [13+l for l in lines]
nv = len(vertices)
positive = [(1<<i)|(1<<j) for i,p in enumerate(points)
            for j,v in enumerate(vertices) if v >= 13 and (p-(v-13)) % 13 in (0,1,3,9)]
projected = []
for row in geometry['generic']:
    q = row['S'] | (row['D'] << 13)
    projected.append(sum(((q>>v)&1)<<i for i,v in enumerate(vertices)))
all_projected = set(projected)
negative = sorted(q for q in all_projected if not any(q != r and q & ~r == 0 for r in all_projected))
assert len(vertices) == 14 and len(positive) == 16
assert all(any(q & ~r == 0 for r in negative) for q in projected)
neighborhoods = [tuple(i for i,p in enumerate(points) if (p-l)%13 in (0,1,3,9)) for l in lines]
assert len(set(neighborhoods)) == 10
assert sorted(map(len,neighborhoods)) == [1]*4+[2]*6
lookup = {q:i+4 for i,q in enumerate(neighborhoods)}
actions = []
def move(q,action):
    return sum(((q>>i)&1)<<action[i] for i in range(nv))
for perm in itertools.permutations(range(4)):
    action = list(perm) + [lookup[tuple(sorted(perm[i] for i in q))] for q in neighborhoods]
    assert sorted(action) == list(range(nv))
    assert {move(q,action) for q in positive} == set(positive)
    assert {move(q,action) for q in negative} == set(negative)
    actions.append(action)
inputs = [sum(((q>>i)&1)<<j for j,q in enumerate(positive)) for i in range(nv)]
initial = set(inputs)
for bits in range(1,1<<nv):
    mask = (1<<len(positive))-1
    for i in range(nv):
        if bits>>i&1: mask &= inputs[i]
    if mask: initial.add(mask)
initial = sorted(initial)
indices = {q:i for i,q in enumerate(initial)}
edge_index = {q:i for i,q in enumerate(positive)}
signature_actions = []
for action in actions:
    edges = [edge_index[move(q,action)] for q in positive]
    signature_actions.append([indices[sum(((q>>i)&1)<<edges[i] for i in range(len(positive)))] for q in initial])
pairs = {(a,b) for a,b in itertools.combinations(range(len(initial)),2) if initial[a]&~initial[b] and initial[b]&~initial[a]}
remaining = pairs.copy()
orbits = []
while remaining:
    a,b = min(remaining)
    orbit = {tuple(sorted((action[a],action[b]))) for action in signature_actions}
    assert orbit <= pairs
    remaining -= orbit
    orbits.append({'representative_masks':[initial[a],initial[b]],'size':len(orbit)})
truth = {'vertices':vertices,'positive_edges':positive,'maximal_negative_masks':negative,
         'original_projected_negative_masks':projected}
(base/'cap4-full-truth.json').write_text(json.dumps(truth,indent=2)+'\n')
symmetry = {'input_count':nv,'positive_samples':positive,'negative_samples':negative,
            'first_OR_orbits':orbits,'initial_signature_masks':initial,'vertex_actions':actions,
            'pair_count':len(pairs),'vertices':vertices}
(base/'cap4-full-first-or-symmetry.json').write_text(json.dumps(symmetry,indent=2)+'\n')
forced_true = {q for q in range(1<<nv) if any(q&p == p for p in positive)}
forced_false = {q for q in range(1<<nv) if any(q&~r == 0 for r in negative)}
assert not forced_true & forced_false
permitted_minterms=[]
for q in range(1<<nv):
    if q in forced_false: continue
    if all(q^(1<<i) in forced_false for i in range(nv) if q>>i&1): permitted_minterms.append(q)
summary = {'vertices':vertices,'positive_count':len(positive),'projected_negative_count':len(all_projected),
           'negative_maxima':len(negative),'actions':len(actions),'initial_signatures':len(initial),
           'first_pairs':len(pairs),'first_or_orbits':len(orbits),'forced_true_assignments':len(forced_true),
           'forced_false_assignments':len(forced_false),'free_assignments':(1<<nv)-len(forced_true)-len(forced_false),
           'permitted_minterm_degree_counts':{d:sum(q.bit_count()==d for q in permitted_minterms) for d in range(nv+1)}}
(base/'cap4-full-data-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary))
