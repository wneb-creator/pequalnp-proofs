import hashlib
import itertools
import json
from pathlib import Path

B=Path('/tmp/oec/pequalnp-pilot-62')
R=Path('/workspace/pequalnp-proofs')
data=json.loads((B/'multi-output-line-neighborhoods.json').read_text())
mask=lambda xs:sum(1<<x for x in xs)
pencils=[mask(l for l in range(13) if (p-l)%13 in {0,1,3,9}) for p in range(13)]
assert pencils==[t['positive_mask'] for t in data['targets']]
caps={mask(xs) for xs in itertools.combinations(range(13),4) if all((mask(xs)&t).bit_count()<=2 for t in pencils)}
assert len(caps)==234 and caps <= set(data['negative_samples'])
negative=set()
for t in pencils:
    rows=[q for q in data['negative_samples'] if not q&t]
    negative.update(q for q in rows if not any(q!=r and q&~r==0 for r in rows))
assert all(n in negative for n in caps if any(not n&t for t in pencils))

def act(q,a):return mask(a[i] for i in range(13) if q>>i&1)
old_actions=[[(m*i+s)%13 for i in range(13)] for m in [1,3,9] for s in range(13)]
new_actions=[[(m*i)%13 for i in range(13)] for m in [1,3,9]]
for a in old_actions:
    assert sorted(a)==list(range(13))
    assert {act(q,a) for q in pencils}==set(pencils)
    assert {act(q,a) for q in negative}==negative
for p in range(13):
    assert act(pencils[p],[(i-p)%13 for i in range(13)])==pencils[0]
assert all(act(pencils[0],a)==pencils[0] for a in new_actions)
pairs=set(itertools.combinations(range(13),2))
def reps(actions):
    return sorted({min(tuple(sorted((a[i],a[j]))) for a in actions) for i,j in pairs})
old_reps,new_reps=reps(old_actions),reps(new_actions)
assert len(old_reps)==2 and len(new_reps)==26
covered=set()
for i,j in new_reps:
    orbit={tuple(sorted((a[i],a[j]))) for a in new_actions}
    assert not covered&orbit;covered|=orbit
assert covered==pairs

old=(B/'multi_output_direct_cover_cnf.py').read_text()
new=(B/'multi_output_exact_pencil_cnf.py').read_text()
assert old.split('ap = argparse.ArgumentParser()',1)[0]==new.split('ap = argparse.ArgumentParser()',1)[0]
assert old.split('for gate in range(args.or_count):',1)[1].split('actions = []',1)[0] == new.split('for gate in range(args.or_count):',1)[1].split('if args.exact_pencil:',1)[0]
estimate=json.loads((B/'multi-output-exact-pencil-estimate.json').read_text())
assert estimate['old_first_or_representatives']==2 and estimate['new_first_or_representatives']==26
assert estimate['new_first_or_representative_pairs']==[list(p) for p in new_reps]
assert estimate['exact_cut_variables']==38 and estimate['exact_cut_clauses']==38*14+1
delta_vars=38+(26-2)
delta_clauses=38*14+1+(26-2)*27
assert delta_vars==62 and delta_clauses==1181
assert estimate['estimated_new_variables']==estimate['old_variables']+delta_vars
assert estimate['estimated_new_clauses']==estimate['old_clauses']+delta_clauses

names=['multi_output_direct_cover_cnf.py','multi_output_exact_pencil_cnf.py','multi-output-exact-pencil-estimate.json','multi-output-line-neighborhoods.json']
out={'reviewer':'repo_audit','status':'PASS source-only cut, mathematical model bridge, and finite symmetry audit; no Lean, full CNF generation or solver run',
 'scope':'Only the13-output line-input canonical free-AND promise model with all13 targets and all four-cap negatives. This does not establish the unrestricted26-input posted51 theorem.',
 'logical_bridge':['No exact pencil makes all13 targets active; checked local_guard_charge and guard_targets_card plus three_per_active_target yield39<=k, without PureUnionAncestry.Scheme.',
 'A rejected canonical output is an AND with a false input/OR factor whose singleton support contains its four-element pencil. Such a factor cannot be an initial singleton. Monotonicity forces its support to miss the rejected cap. Hence the supports satisfy the separates hypothesis.',
 'For k<=38 there is some OR with exact pencil support. Translate line and output labels simultaneously to send that pencil to P0. The revised first-pair symmetry uses only multipliers1,3,9 with zero shift, all preserving P0. The old translation-normalized first-pair constraint must not also be retained.',
 'The Lean corollary source is UNCOMPILED; the circuit-to-support bridge and symmetry existence argument are reviewed mathematics, not new Lean theorems.'],
 'checks':{'four_caps':len(caps),'encoded_negative_maxima':len(negative),'old_symmetries':len(old_actions),'new_pencil_stabilizing_symmetries':len(new_actions),'all_first_input_pairs':len(pairs),'old_orbits':len(old_reps),'new_disjoint_complete_orbits':len(new_reps),'estimated_added_variables':delta_vars,'estimated_added_clauses':delta_clauses},
 'files':{n:hashlib.sha256((B/n).read_bytes()).hexdigest() for n in names},
 'corollary_sha256':hashlib.sha256((R/'results/orch/lemmas/ExactPencilGuardCut.lean').read_bytes()).hexdigest()}
(B/'exact-pencil-independent-audit.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
