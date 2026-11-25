"""Prepare sufficient raw/joint five-owner targets and exact assembly calibration."""
import json,itertools
from pathlib import Path
from assemble_five_owner import or_network_table,or_network,assemble_five

HERE=Path(__file__).resolve().parent
points=[0,1,2,5,7]
neighbors={p:{13+l for l in range(13) if (p+l)%13 in (0,1,3,9)} for p in range(13)}
lines=sorted(set.union(*(neighbors[p] for p in points)))
raw=points+lines;assert len(raw)==16
edges=sorted((i,raw.index(l)) for i,p in enumerate(points) for l in neighbors[p])
def positive(mask):return any(mask>>a&1 and mask>>b&1 for a,b in edges)
negatives=[m for m in range(1<<16) if not positive(m) and
           all(positive(m|1<<i) for i in range(16) if not m>>i&1)]
assert len(negatives)==30
tests=[[1<<a|1<<b,1] for a,b in edges]+[[m,0] for m in negatives]
features=[];owners=[]
for point in range(13):
    if point in points:continue
    core_lines=sorted(neighbors[point]&set(lines));arity=len(core_lines)
    composite,index,parent,best=or_network_table(arity)
    feature_inputs=[];mask_to_input={}
    for mask in composite:
        subset=[core_lines[i] for i in range(arity) if mask>>i&1]
        logical=16+len(features);feature_inputs.append(logical);mask_to_input[mask]=logical
        features.append({'original_lines':subset,'raw_indices':[raw.index(x) for x in subset],
                         'outside_owner':point,'local_mask':mask,'kind':'whole' if mask==(1<<arity)-1 else 'optional_prefix'})
    whole=(1<<arity)-1;whole_bit=1<<index[whole]
    templates=[]
    for state in parent:
        if state&whole_bit and state.bit_count()==arity-1:
            templates.append([mask_to_input[m] for i,m in enumerate(composite) if state>>i&1])
    optional=[m for m in composite if m!=whole]
    costs=[]
    for request in range(1<<len(optional)):
        needed=[whole]+[m for j,m in enumerate(optional) if request>>j&1]
        costs.append(len(or_network(arity,needed))-(arity-1))
    owners.append({'outside_point':point,'core_lines':core_lines,'original_neighbors':sorted(neighbors[point]),
        'feature_inputs':feature_inputs,'whole_input':mask_to_input[whole],
        'optional_inputs':[mask_to_input[m] for m in optional],
        'zero_extra_templates':templates,'prefix_extra_cost_table':costs})
assert len(features)==36
joint={'name':'five_owner_0_1_2_5_7_joint','group':points,'raw_inputs':16,'inputs':52,
       'input_original':raw,'features':features,'edges':[list(e) for e in edges],
       'raw_tests':tests,'tests':[],'max_gates':23,'outside_owners':owners,
       'outside_base_cost':39,'final_or_cost':1,'total_if_target_met':63,
       'private_raw_indices':[8,9,10],
       'prefix_rule':'Each owner chooses an OR network containing its whole core-line union and every actively used feature. Extra cost is network size minus (number of core lines minus1).',
       'zero_extra_template_groups':[o['zero_extra_templates'] for o in owners],
       'assembler':'algebra_strategy/assemble_five_owner.py:assemble_five'}
for mask,y in tests:
    encoded=mask
    for j,f in enumerate(features):
        if any(mask>>i&1 for i in f['raw_indices']):encoded|=1<<(16+j)
    joint['tests'].append([encoded,y])

canonical=[]
def add(op,a,b):canonical.append([op,a,b]);return 16+len(canonical)-1
terms=[]
for p in range(5):
    ns=sorted(b for a,b in edges if a==p);w=ns[0]
    for b in ns[1:]:w=add(1,w,b)
    terms.append(add(0,p,w))
output=terms[0]
for b in terms[1:]:output=add(1,output,b)
assert len(canonical)==24
joint_canonical=[[op,a if a<16 else a+36,b if b<16 else b+36] for op,a,b in canonical]
full,meta=assemble_five(joint,joint_canonical,output+36)
assert meta['gates']==64 and meta['prefix_extra_cost']==0
outside,_=assemble_five(joint,[],0)
raw_case={'name':'five_owner_0_1_2_5_7_raw','group':points,'raw_inputs':16,'inputs':16,
          'input_original':raw,'features':[],'edges':[list(e) for e in edges],
          'raw_tests':tests,'tests':tests,'max_gates':23,'outside_gates':outside[:-1],
          'outside_output':outside[-1][1],'outside_cost':39,'final_or_cost':1,
          'total_if_target_met':63,'private_raw_indices':[8,9,10]}
assert len(raw_case['outside_gates'])==39

# Independently evaluate exact monotone prime terms for the full64 calibration.
def minimal(terms):
    ans=[]
    for term in sorted(set(terms),key=lambda x:(x.bit_count(),x)):
        if not any(x&term==x for x in ans):ans.append(term)
    return ans
values=[[1<<i] for i in range(26)]
for op,a,b in full:
    assert 0<=a<len(values) and 0<=b<len(values)
    values.append(minimal(values[a]+values[b] if op else [x|y for x in values[a] for y in values[b]]))
assert set(values[-1])=={1<<p|1<<l for p in range(13) for l in neighbors[p]}
for name,obj in [('five-owner-raw-packet.json',[raw_case]),('five-owner-joint-packet.json',[joint]),
                 ('five-owner-canonical24.json',{'gates':canonical,'output':output,'inputs':16}),
                 ('five-owner-joint-canonical24.json',{'gates':joint_canonical,'output':output+36,'inputs':52}),
                 ('five-owner-full64-calibration.json',full)]:
    (HERE/name).write_text(json.dumps(obj,indent=2)+'\n')
summary={'raw_inputs':16,'edges':20,'maximal_negatives':30,'joint_features':36,
         'template_group_sizes':[len(o['zero_extra_templates']) for o in owners],
         'outside_cost':39,'target_core_gates':23,'full_target_gates':63,
         'exact_calibration':meta,'exact_calibration_minimal_terms':52,
         'status':'Sufficient targets; canonical exact24 calibrates to64. No exact23 witness yet.'}
(HERE/'five-owner-packet-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
