"""Independent joint-prefix geometry, semantics, and cost checks."""
import importlib.util,itertools,json
from pathlib import Path

HERE=Path(__file__).resolve().parent
SEARCH=HERE.parent/'circuit_search'
case=json.loads((SEARCH/'joint-four-owner-packet.json').read_text())[0]
spec=importlib.util.spec_from_file_location('reviewed_joint_assembler',SEARCH/'assemble_joint_four.py')
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
assemble=module.assemble_joint
raw=case['input_original'];groups=case['optional_prefix_groups']
assert case['raw_inputs']==14 and case['inputs']==41 and len(case['features'])==27
assert len(groups)==6 and all(len(g)==3 for g in groups)
assert len(set(sum(groups,[])))==18
all_edges={(p,13+l) for p in range(13) for l in range(13) if (p+l)%13 in (0,1,3,9)}
outside_edges={e for e in all_edges if e[0] not in raw[:4]}
assert len(outside_edges)==36
core_edges={(raw.index(a),raw.index(b)) for a,b in all_edges if a in raw[:4]}
assert set(map(tuple,case['edges']))==core_edges and len(core_edges)==16
def positive(mask):return any(mask>>a&1 and mask>>b&1 for a,b in core_edges)
positive_boundary={1<<a|1<<b for a,b in core_edges}
negative_boundary={x for x in range(1<<14) if not positive(x) and
    all(positive(x|(1<<i)) for i in range(14) if not x>>i&1)}
assert set(map(tuple,case['raw_tests']))=={(x,1) for x in positive_boundary}|{(x,0) for x in negative_boundary}
for (x,y),(encoded,want) in zip(case['raw_tests'],case['tests'],strict=True):
    mask=x
    for j,feature in enumerate(case['features']):
        if any(x>>i&1 for i in feature['raw_indices']):mask|=1<<(14+j)
    assert encoded==mask and want==y
owners=case['outside_owners']
assert {x['outside_point'] for x in owners}==set(range(13))-set(raw[:4])
seen_pairs=set()
for owner in owners:
    p=owner['outside_point']
    neighbors={b for a,b in all_edges if a==p}
    core_lines=neighbors&set(raw[4:])
    assert set(owner['original_neighbors'])==neighbors
    assert set(owner['core_lines'])==core_lines
    whole=case['features'][owner['whole_input']-14]
    assert set(whole['original_lines'])==core_lines
    assert len(core_lines) in (2,3)
    if len(core_lines)==3:
        pairs={tuple(sorted(case['features'][j-14]['original_lines'])) for j in owner['optional_inputs']}
        assert pairs==set(itertools.combinations(sorted(core_lines),2))
        assert owner['optional_inputs'] in groups
        assert not seen_pairs&pairs
        seen_pairs|=pairs
for feature in case['features']:
    assert set(feature['original_lines'])=={raw[i] for i in feature['raw_indices']}
    assert {p for p in range(13) if set(feature['original_lines'])<={l for a,l in all_edges if a==p}}=={feature['outside_owner']}
def encode(mask):
    ans=mask
    for j,feature in enumerate(case['features']):
        if any(mask>>i&1 for i in feature['raw_indices']):ans|=1<<(14+j)
    return ans
essential_witnesses=[]
for i in range(14):
    if i<4:
        line=next(b for a,b in core_edges if a==i)
        mask=1<<line
    else:
        point=next(a for a,b in core_edges if b==i)
        neighbors={b for a,b in core_edges if a==point}
        mask=(1<<point)|sum(1<<j for j in range(4,14) if j not in neighbors)
    changed=mask^(1<<i)
    assert not positive(mask) and positive(changed)
    assert encode(mask)^encode(changed)==1<<i
    essential_witnesses.append({'raw_input':i,'false_mask':mask,'true_mask':changed})

def reduced(terms):
    ans=[]
    for x in sorted(set(terms),key=lambda x:(x.bit_count(),x)):
        if not any(y&x==y for y in ans):ans.append(x)
    return ans
def semantics(inputs,gates):
    values=[list(x) for x in inputs]
    for op,a,b in gates:
        assert op in (0,1) and 0<=a<len(values) and 0<=b<len(values)
        values.append(reduced(values[a]+values[b] if op else [x|y for x in values[a] for y in values[b]]))
    return values
encoded=[[1<<i] for i in raw]+[[1<<i for i in f['original_lines']] for f in case['features']]
outside_terms=[1<<a|1<<b for a,b in outside_edges]
fixtures=[]
def check(name,gates,output=None,expected_extra=None,expected_gates=None):
    output=41+len(gates)-1 if output is None else output
    full,meta=assemble(case,gates,output)
    actual=semantics([[1<<i] for i in range(26)],full)[-1]
    expected=reduced(outside_terms+semantics(encoded,gates)[output])
    assert actual==expected,name
    assert len(full)==meta['outside_gates']+meta['core_gates']+1
    actual_used=set(meta['used_optional_inputs'])
    extra=sum(max(0,len(actual_used&set(g))-1) for g in groups)
    assert extra==meta['prefix_extra_cost'] and meta['outside_gates']==44+extra
    if expected_extra is not None:assert extra==expected_extra,(name,meta)
    if expected_gates is not None:assert len(full)==expected_gates,(name,meta)
    return meta
def combine(inputs,with_point=False):
    gates=[];w=inputs[0]
    for b in inputs[1:]:gates.append([1,w,b]);w=41+len(gates)-1
    if with_point:gates.append([0,0,w])
    return gates

# Every one-of-three choice at all six owners, with all six chosen pairs active.
for choice in itertools.product(*groups):
    check('one_per_owner',combine(choice,True),expected_extra=0)
conflict_count=0
for i,group in enumerate(groups):
    for pair in itertools.combinations(group,2):
        choice=[g[0] for j,g in enumerate(groups) if j!=i]+list(pair)
        check('one_conflict',combine(choice,True),expected_extra=1)
        conflict_count+=1

# Explicit boundary budgets:18+0 and17+1 both assemble to63.
unconditional=[14+i for i,f in enumerate(case['features']) if f['kind']!='optional_pair']
no_conflict=list(range(13))+[g[0] for g in groups]
fixtures.append(check('18_core_zero_conflict',combine(no_conflict),expected_extra=0,expected_gates=63))
one_conflict=list(range(14))+groups[0][:2]+unconditional[:2]
fixtures.append(check('17_core_one_conflict',combine(one_conflict),expected_extra=1,expected_gates=63))
# Dead optional-pair gates must not create a charge after compaction.
dead=[[1,groups[0][0],groups[0][1]],[1,0,0],[1,1,1],[0,42,43]]
fixtures.append(check('inactive_conflict_removed',dead,expected_extra=0,expected_gates=46))
report={'verdict':'PASS','scope':'Joint-prefix grouping, full symbolic assembly semantics, and exact cost; no exact18 target witness.',
        'one_pair_per_owner_choices_checked':729,'single_conflict_choices_checked':conflict_count,
        'raw_assignments_checked_for_boundary_completeness':16384,
        'boundary_cases':len(positive_boundary)+len(negative_boundary),
        'raw_essentiality_witnesses':essential_witnesses,
        'support_constraint':'A connected c-gate binary DAG that uses f distinct derived features must have c >= 13 + f, because all14 raw coordinates are indispensable.',
        'features':27,'triple_owners':6,'fixed_pair_owners':3,
        'cost_formula':'44 + compacted core gates + sum(max(used optional pairs per owner - 1, 0)) + 1',
        'fixtures':fixtures}
(HERE/'joint-four-independent-review.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
