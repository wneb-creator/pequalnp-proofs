from collections import Counter
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path

base=Path('/tmp/oec/pequalnp-pilot-62')
data=json.loads((base/'theta4-first-or-symmetry.json').read_text())
truth=json.loads((base/'theta4-truth.json').read_text())
geometry=json.loads((base/'geometry-data.json').read_text())
witness=json.loads((base/'direct-theta4-control11.witness.json').read_text())
vertices=truth['vertices']
assert vertices==[2,0,1,3,9,13,25,14,15,19]
positive=data['positive_samples'];negative=data['negative_samples']
assert positive==truth['positive_edges'] and negative==truth['maximal_negative_masks']
def project(mask):return sum((mask>>v&1)<<i for i,v in enumerate(vertices))
universe=sum(1<<v for v in vertices)
global_positive=[(1<<p)|(1<<(13+l)) for l in range(13) for p in range(13) if (p-l)%13 in (0,1,3,9)]
assert set(positive)=={project(e) for e in global_positive if not e&~universe}
projected={project(q['S']|(q['D']<<13)) for q in geometry['generic']}
maximal={q for q in projected if not any(q!=r and q&r==q for r in projected)}
assert maximal==set(negative) and len(negative)==19
input_masks=[sum((p>>i&1)<<j for j,p in enumerate(positive)) for i in range(10)]
closure=set(input_masks)
while True:
    nxt=closure|{a&b for a in closure for b in closure}
    if nxt==closure:break
    closure=nxt
initial=data['initial_signature_masks']
assert len(initial)==22 and set(initial)==closure-{0}
actions=[tuple(g) for g in data['vertex_actions']]
assert len(actions)==len(set(actions))==48
assert all(sorted(g)==list(range(10)) for g in actions)
assert all(tuple(g[h[i]] for i in range(10)) in actions for g in actions for h in actions)
def act(mask,g):return sum(1<<g[i] for i in range(10) if mask>>i&1)
pi={x:i for i,x in enumerate(positive)};si={x:i for i,x in enumerate(initial)}
signature_actions=[]
for g in actions:
    assert {act(p,g) for p in positive}==set(positive)
    assert {act(n,g) for n in negative}==set(negative)
    em=[pi[act(p,g)] for p in positive]
    signature_actions.append([si[sum(1<<em[i] for i in range(12) if s>>i&1)] for s in initial])
pairs={(a,b) for a,b in combinations(range(22),2) if initial[a]&~initial[b] and initial[b]&~initial[a]}
assert len(pairs)==207
remaining=set(pairs);orbits=[]
while remaining:
    a,b=min(remaining)
    orbit={tuple(sorted((g[a],g[b]))) for g in signature_actions}
    assert orbit<=remaining
    remaining-=orbit
    orbits.append({'representative_masks':sorted([initial[a],initial[b]]),'size':len(orbit)})
assert orbits==data['first_OR_orbits'] and len(orbits)==18
def evaluate(q):
    values=[bool(q>>i&1) for i in range(10)]
    for a,b in witness['operand_wire_lists']:
        assert a and b and all(0<=i<len(values) for i in a+b)
        values.append(all(values[i] for i in a) or all(values[i] for i in b))
    return all(values[i] for i in witness['output_wire_list'])
positive_cases=negative_cases=free_cases=0
for q in range(1024):
    wanted_positive=any(p&q==p for p in positive)
    wanted_negative=any(q&n==q for n in negative)
    assert not(wanted_positive and wanted_negative)
    value=evaluate(q)
    if wanted_positive:assert value;positive_cases+=1
    elif wanted_negative:assert not value;negative_cases+=1
    else:free_cases+=1
assert all(not evaluate(q) for q in projected)
bounds=[]
for n in negative:
    sensitive=[i for i in range(10) if not n>>i&1 and any(p&(n|(1<<i))==p for p in positive)]
    bounds.append(len(sensitive)-1)
result={
    'status':'Theta-four adapter, projection, automorphism and baseline checks passed.',
    'source_sha256':sha256((base/'global_or_direct_cnf_v2.py').read_bytes()).hexdigest(),
    'symmetry_source_sha256':sha256((base/'theta4_first_or_symmetry.py').read_bytes()).hexdigest(),
    'symmetry_data_sha256':sha256((base/'theta4-first-or-symmetry.json').read_bytes()).hexdigest(),
    'inputs':10,'positive_edges':12,'maximal_negative_samples':19,
    'distinct_global_negative_projections':len(projected),
    'initial_nonempty_signatures':22,'incomparable_initial_pairs':207,
    'automorphisms':48,'first_OR_orbits':18,
    'baseline_ORs':witness['or_count'],'full_truth_cases':1024,
    'forced_positive_cases':positive_cases,'forced_negative_cases':negative_cases,'free_cases':free_cases,
    'false_OR_bound_histogram':dict(Counter(bounds)),
    'scope':'Finite local model/control only; no ten-OR search or Lean proof.',
}
print(json.dumps(result,indent=2))
(base/'theta4-adapter-independent-audit.json').write_text(json.dumps(result,indent=2)+'\n')
