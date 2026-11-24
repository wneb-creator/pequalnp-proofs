import hashlib, importlib.util, json, random
from pathlib import Path

ROOT=Path('/tmp/oec/pequalnp-pilot-18')
spec=importlib.util.spec_from_file_location('cut',ROOT/'add_ancestor_support.py')
cut=importlib.util.module_from_spec(spec);spec.loader.exec_module(cut)
meta=json.loads((ROOT/'tail7-ancestorreverse-onejunk/meet5.json').read_text())
newvars,clauses,flags,some=cut.append_gadget(meta)
supports=meta['prefix_support_tables'][13:30]
adj=[sum(1<<v for v in range(11) if tuple(sorted((u,v))) in cut.EDGES) for u in range(11)]

def valid(clause,assignment):
    return any(assignment[abs(v)]==(v>0) for v in clause)

def assignment_for(masks,ancestors,ops):
    a={}
    for g,mask in enumerate(masks):
        for i,lit in enumerate(supports[g]):a[lit]=bool(mask&(1<<i))
        for h,lit in enumerate(meta['prefix_ancestor_flags'][g]):a[lit]=h in ancestors[g]
        a[meta['ops'][g]]=ops[g]
        for v,lit in enumerate(flags[g]):a[lit]=(mask&~adj[v])==0
        a[some[g]]=any((mask&~n)==0 for n in adj)
    return a

# Exhaustive supports, and rejection of every incorrect helper output bit.
helper_size=(len(clauses)-136*12)//17
assert helper_size*17+136*12==len(clauses)
helper=clauses[:helper_size]
for mask in range(2048):
    a=assignment_for([mask]*17,[set() for _ in range(17)],[False]*17)
    assert all(valid(c,a) for c in clauses)
    for bit in flags[0]+[some[0]]:
        a[bit]=not a[bit]
        assert not all(valid(c,a) for c in helper)
        a[bit]=not a[bit]

# Independently generate structurally clean productive prefixes.
rng=random.Random(134217)
checks=0;and_gates=0;wide_ancestor_pairs=0
for trial in range(1024):
    masks=[1<<i for i in range(11)]+[0,2047]
    cones=[set() for _ in masks];ops=[]
    for g in range(17):
        choices=[]
        for a in range(len(masks)):
            if not masks[a]:continue
            for b in range(a,len(masks)):
                if masks[b] and all(masks[b]&~adj[v]==0 for v in range(11) if masks[a]&(1<<v)):
                    choices.append((a,b))
        is_and=bool(choices) and rng.randrange(3)==0
        if is_and:
            a,b=rng.choice(choices);out=0;and_gates+=1
        else:
            a=rng.randrange(len(masks));b=rng.randrange(len(masks));out=masks[a]|masks[b]
        cone=cones[a]|cones[b]
        if a>=13:cone=cone|{a-13}
        if b>=13:cone=cone|{b-13}
        masks.append(out);cones.append(cone);ops.append(is_and)
        for h in cone:
            old=masks[13+h]
            if all(old&~n for n in adj):
                wide_ancestor_pairs+=1
                assert not is_and and old&~out==0
        checks+=1
    assignment=assignment_for(masks[13:],cones[13:],ops)
    assert all(valid(c,assignment) for c in clauses)

cases={}
for name in cut.CASES:
    parent=ROOT/'tail7-ancestorreverse-onejunk'/(name+'.cnf')
    child=ROOT/'tail7-ancestor-support'/(name+'.cnf')
    p=parent.read_text().splitlines();c=child.read_text().splitlines()
    m=json.loads(child.with_suffix('.json').read_text())
    assert c[1:len(p)]==p[1:]
    assert c[len(p):]==[' '.join(map(str,row))+' 0' for row in clauses]
    assert hashlib.sha256(child.read_bytes()).hexdigest()==m['sha256']
    assert int(c[0].split()[2])==newvars
    assert len(c)-len(p)==len(clauses)
    cases[name]=m['sha256']
report={'status':'PASS_SELF_CONTROLS_AWAITING_INDEPENDENT_REVIEW',
 'source_sha256':hashlib.sha256((ROOT/'add_ancestor_support.py').read_bytes()).hexdigest(),
 'support_masks':2048,'wrong_helper_output_rejections':2048*12,
 'random_prefixes':1024,'random_gates':checks,'productive_ANDs':and_gates,
 'no_common_neighbor_ancestor_pairs':wide_ancestor_pairs,
 'added_variables':newvars-meta['variables'],'added_clauses':len(clauses),
 'cases':cases,'claim':'Necessary encoding consequence; no production SAT/UNSAT verdict.'}
(ROOT/'ancestor-support-self-controls.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
