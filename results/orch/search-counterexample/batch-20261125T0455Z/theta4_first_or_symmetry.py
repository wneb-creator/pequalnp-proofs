import collections
import itertools
import json
from pathlib import Path

base=Path('/tmp/oec/pequalnp-pilot-62')
data=json.loads((base/'theta4-truth.json').read_text())
vertices=data['vertices']
assert vertices==[2,0,1,3,9,13,25,14,15,19]
positive=data['positive_edges']
negative=data['maximal_negative_masks']
nv=10
initial_inputs=[sum((p>>i&1)<<j for j,p in enumerate(positive)) for i in range(nv)]
initial=set()
for chosen in range(1,1<<nv):
 mask=(1<<len(positive))-1
 for i in range(nv):
  if chosen>>i&1:mask &= initial_inputs[i]
 if mask:initial.add(mask)
initial=sorted(initial)
index={mask:i for i,mask in enumerate(initial)}
pos_index={mask:i for i,mask in enumerate(positive)}
def move(mask,action):return sum((mask>>i&1)<<action[i] for i in range(nv))
actions=[]
for permutation in itertools.permutations(range(4)):
 action=[0]+[1+i for i in permutation]+[5]+[6+i for i in permutation]
 actions.append(action)
 dual=[5]+list(range(6,10))+[0]+list(range(1,5))
 actions.append([dual[i] for i in action])
signature_actions=[]
for action in actions:
 assert sorted(action)==list(range(nv))
 assert {move(p,action) for p in positive}==set(positive)
 assert {move(q,action) for q in negative}==set(negative)
 edges=[pos_index[move(p,action)] for p in positive]
 signature_actions.append([index[sum((mask>>i&1)<<edges[i] for i in range(len(positive)))] for mask in initial])
pairs={(a,b) for a,b in itertools.combinations(range(len(initial)),2) if initial[a]&~initial[b] and initial[b]&~initial[a]}
remaining=set(pairs);orbits=[]
while remaining:
 a,b=min(remaining)
 orbit={tuple(sorted((action[a],action[b]))) for action in signature_actions}
 assert orbit<=pairs
 remaining-=orbit
 orbits.append({'representative_masks':sorted([initial[a],initial[b]]),'size':len(orbit)})
out={'input_count':nv,'positive_samples':positive,'negative_samples':negative,
     'first_OR_orbits':orbits,'initial_signature_masks':initial,'vertex_actions':actions,
     'pair_count':len(pairs)}
(base/'theta4-first-or-symmetry.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'actions':len(actions),'initial_signatures':len(initial),'pairs':len(pairs),
                  'first_OR_orbits':len(orbits),'orbit_sizes':[o['size'] for o in orbits]}))
