"""Independent exhaustive/antichain review of the sufficient four-owner packet."""
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
SEARCH=HERE.parent/'circuit_search'
case=json.loads((SEARCH/'context-four-owner-packet.json').read_text())[0]
seed=json.loads((HERE/'context19-four-owner-seed.json').read_text())

def reduce_terms(terms):
    ans=[]
    for x in sorted(set(terms),key=lambda x:(x.bit_count(),x)):
        if not any(y&x==y for y in ans):ans.append(x)
    return ans

def add_gate(values,gate):
    op,a,b=gate
    assert op in (0,1) and 0<=a<len(values) and 0<=b<len(values)
    if op:terms=values[a]+values[b]
    else:terms=[x|y for x in values[a] for y in values[b]]
    values.append(reduce_terms(terms))

raw=case['input_original']
assert len(raw)==14 and len(set(raw))==14
assert raw[:4]==case['group']==[0,2,3,7]
edges={(p,13+l) for p in range(13) for l in range(13) if (p+l)%13 in (0,1,3,9)}
core_edges={(raw.index(p),raw.index(l)) for p,l in edges if p in case['group']}
assert set(map(tuple,case['edges']))==core_edges
assert len(core_edges)==16

# Enumerate the exact monotone boundary independently on all 2^14 raw masks.
def positive(mask):return any(mask>>a&1 and mask>>b&1 for a,b in core_edges)
positive_tests={1<<a|1<<b for a,b in core_edges}
negative_tests={x for x in range(1<<14) if not positive(x) and
                all(positive(x|(1<<i)) for i in range(14) if not x>>i&1)}
assert {(x,y) for x,y in case['raw_tests']}=={(x,1) for x in positive_tests}|{(x,0) for x in negative_tests}
for (raw_mask,y),(encoded,z) in zip(case['raw_tests'],case['tests'],strict=True):
    assert y==z
    want=raw_mask
    for j,feature in enumerate(case['features']):
        assert set(feature['original_lines'])=={raw[i] for i in feature['raw_indices']}
        if any(raw_mask>>i&1 for i in feature['raw_indices']):want|=1<<(14+j)
    assert encoded==want

# Exact symbolic semantics checks the complete outside circuit and every exposed feature.
outside=case['outside_gates']
values=[[1<<i] for i in range(26)]
for gate in outside:add_gate(values,gate)
assert len(outside)==case['outside_cost']==44
assert case['outside_output']==69
assert values[69]==reduce_terms([1<<p|1<<l for p,l in edges if p not in case['group']])
for feature in case['features']:
    assert values[feature['outside_wire']]==reduce_terms([1<<raw[i] for i in feature['raw_indices']])
assert len(case['features'])==15 and case['inputs']==29
assert case['max_gates']==18 and case['final_or_cost']==1
assert 44+18+1==case['total_if_target_met']==63

def assemble(gates,output):
    result=[g[:] for g in outside]
    mapping=raw+[f['outside_wire'] for f in case['features']]
    for op,a,b in gates:
        assert a<len(mapping) and b<len(mapping)
        result.append([op,mapping[a],mapping[b]])
        mapping.append(26+len(result)-1)
    result.append([1,69,mapping[output]])
    return result

# A canonical 19-paid-gate core calibrates the full assembly to exact size64.
canonical=[]
terms=[]
for p in range(4):
    nbrs=sorted(b for a,b in core_edges if a==p)
    assert len(nbrs)==4
    w=nbrs[0]
    for b in nbrs[1:]:
        canonical.append([1,w,b]);w=29+len(canonical)-1
    canonical.append([0,p,w]);terms.append(29+len(canonical)-1)
w=terms[0]
for b in terms[1:]:
    canonical.append([1,w,b]);w=29+len(canonical)-1
assert len(canonical)==19
full=assemble(canonical,w)
v=[[1<<i] for i in range(26)]
for gate in full:add_gate(v,gate)
assert len(full)==64 and set(v[-1])=={1<<p|1<<l for p,l in edges}

approx=assemble(seed['gates'],seed['output'])
v=[[1<<i] for i in range(26)]
for gate in approx:add_gate(v,gate)
desired={1<<p|1<<l for p,l in edges}
assert desired<=set(v[-1])
extra=set(v[-1])-desired
report={'verdict':'PASS','scope':'Sufficient packet and assembly independently verified; candidate is approximate.',
 'outside_gates':44,'outside_and_count':sum(g[0]==0 for g in outside),
 'free_feature_count':15,'core_positive_boundary_count':len(positive_tests),
 'core_negative_boundary_count':len(negative_tests),
 'exact_calibration_full_gates':64,'exact_calibration_minimal_terms':52,
 'candidate_full_gates':len(approx),'candidate_full_and_count':sum(g[0]==0 for g in approx),
 'candidate_full_or_count':sum(g[0]==1 for g in approx),
 'candidate_extra_minimal_terms':[[i for i in range(26) if x>>i&1] for x in sorted(extra)]}
(HERE/'context-four-packet-review.json').write_text(json.dumps(report,indent=2)+'\n')
(HERE/'context19-full63-assembled.json').write_text(json.dumps(approx)+'\n')
(HERE/'context-four-full64-calibration.json').write_text(json.dumps(full)+'\n')
print(json.dumps(report,indent=2))
