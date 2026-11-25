from collections import Counter, deque
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path

base=Path('/tmp/oec/pequalnp-pilot-62')
data=json.loads((base/'global-first-or-symmetry.json').read_text())
geometry=json.loads((base/'geometry-data.json').read_text())
known=json.loads((base/'multi-output-baseline39.json').read_text())
positive=data['positive_samples']; negative=data['negative_samples']
assert len(positive)==52 and len(set(positive))==52
assert set(positive)=={(1<<p)|(1<<(13+l)) for l in range(13) for p in range(13) if (p-l)%13 in (0,1,3,9)}
assert negative==[q['S']|(q['D']<<13) for q in geometry['generic']]
assert len(negative)==len(set(negative))==468
input_masks=[sum((p>>i&1)<<j for j,p in enumerate(positive)) for i in range(26)]
assert input_masks==data['input_signature_masks']
closure=set(input_masks)
while True:
    expanded=closure|{a&b for a in closure for b in closure}
    if expanded==closure:break
    closure=expanded
initial=data['closed_initial_signature_masks']
assert len(initial)==78 and set(initial)==closure-{0}
assert set(initial)==set(input_masks)|{1<<i for i in range(52)}
inverse_initial={v:i for i,v in enumerate(initial)}
def act(mask,g):return sum(1<<g[i] for i in range(26) if mask>>i&1)
pos_index={x:i for i,x in enumerate(positive)}
signature_maps=[]
for g in data['generators']:
    assert sorted(g)==list(range(26))
    assert {act(p,g) for p in positive}==set(positive)
    assert {act(n,g) for n in negative}==set(negative)
    edge_action=[pos_index[act(p,g)] for p in positive]
    sig_action=[inverse_initial[sum(1<<edge_action[i] for i in range(52) if sig>>i&1)] for sig in initial]
    assert sorted(sig_action)==list(range(78))
    signature_maps.append(sig_action)
pairs={(a,b) for a,b in combinations(range(78),2) if initial[a]&~initial[b] and initial[b]&~initial[a]}
assert len(pairs)==2899
remaining=set(pairs); orbits=[]
while remaining:
    root=min(remaining);seen={root};todo=deque([root])
    while todo:
        a,b=todo.popleft()
        for g in signature_maps:
            q=tuple(sorted((g[a],g[b])))
            assert q in pairs
            if q not in seen:seen.add(q);todo.append(q)
    assert seen<=remaining
    remaining-=seen
    orbits.append((root,len(seen)))
assert len(orbits)==8
for (root,size),stored in zip(orbits,data['first_OR_orbits']):
    assert list(root)==stored['representative_indices'] and size==stored['size']
    assert sorted(initial[i] for i in root)==stored['representative_masks']
group={tuple(range(26))};todo=deque(group)
while todo:
    g=todo.popleft()
    for h in data['generators']:
        q=tuple(h[g[i]] for i in range(26))
        if q not in group:group.add(q);todo.append(q)
assert len(group)==data['group_size']==11232
sensitivity=[]
for n in negative:
    assert not any(p&n==p for p in positive)
    sensitive=[i for i in range(26) if not n>>i&1 and any(p&(n|(1<<i))==p for p in positive)]
    sensitivity.append(len(sensitive)-1)
assert set(sensitivity)=={18}

# Reconstruct the proposed51-gate baseline from its stated39 shared line
# unions and12 point-star joins, without generating or solving a CNF.
baseline=[];masks=input_masks.copy()
for a,b in known['ors']:
    pair=sorted((masks[a+13],masks[b+13]))
    baseline.append(pair);masks.append(pair[0]|pair[1])
accumulated=input_masks[0]
for p in range(1,13):
    baseline.append(sorted((accumulated,input_masks[p])))
    accumulated|=input_masks[p]
assert len(baseline)==51
samples=positive+negative
truths=[sum((q>>i&1)<<j for j,q in enumerate(samples)) for i in range(26)]
positive_bits=(1<<52)-1
all_bits=(1<<len(samples))-1
operands=[]
for a,b in baseline:
    assert a&~b and b&~a and a<b
    terms=[];chosen_lists=[]
    for sig in (a,b):
        chosen=[i for i,t in enumerate(truths) if t&sig==sig]
        assert chosen
        value=all_bits
        for i in chosen:value&=truths[i]
        assert value&positive_bits==sig
        terms.append(value);chosen_lists.append(chosen)
    truths.append(terms[0]|terms[1]);operands.append(chosen_lists)
outputs=[i for i,t in enumerate(truths) if t&positive_bits==positive_bits]
assert outputs
value=all_bits
for i in outputs:value&=truths[i]
assert value==positive_bits
false_counts=[sum(not(t>>row&1) for t in truths[26:]) for row in range(52,520)]
assert min(false_counts)>=18

# Check the optional final-three-gate cover cut constructively on this
# baseline by reversing the selected false output wire.
prefix=48;cover_sizes=[]
for row in range(52,520):
    chosen={next(i for i in outputs if not(truths[i]>>row&1))}
    for i in range(26+51-1,26+prefix-1,-1):
        if i not in chosen:continue
        chosen.remove(i)
        for branch in operands[i-26]:
            chosen.add(next(j for j in branch if not(truths[j]>>row&1)))
    assert all(i<26+prefix and not(truths[i]>>row&1) for i in chosen)
    covered=0
    for i in chosen:covered|=truths[i]&positive_bits
    assert covered==positive_bits
    future_true=sum(bool(t>>row&1) for t in truths[26+prefix:])
    assert len(chosen)+future_true<=4
    cover_sizes.append(len(chosen))
result={
    'status':'Independent global finite-model, symmetry and canonical51-baseline checks passed.',
    'source_sha256':sha256((base/'global_or_direct_cnf.py').read_bytes()).hexdigest(),
    'symmetry_source_sha256':sha256((base/'global_first_or_symmetry.py').read_bytes()).hexdigest(),
    'symmetry_data_sha256':sha256((base/'global-first-or-symmetry.json').read_bytes()).hexdigest(),
    'positive_samples':52,'negative_samples':468,'nonempty_initial_meets':78,
    'incomparable_first_pairs':2899,'first_pair_orbits':8,'orbit_sizes':[n for _,n in orbits],
    'generated_group_size':len(group),'sensitivity_false_OR_bounds':dict(Counter(sensitivity)),
    'canonical51_baseline_sample_checks':520,'baseline_false_OR_count_histogram':dict(Counter(false_counts)),
    'baseline_final_three_cover_size_histogram':dict(Counter(cover_sizes)),
    'restriction':'Finite model covers arbitrary monotone AND/OR circuits under the stated normalization. No full-budget SAT or UNSAT result and no Lean claim.',
}
print(json.dumps(result,indent=2))
(base/'global-or-independent-audit.json').write_text(json.dumps(result,indent=2)+'\n')
