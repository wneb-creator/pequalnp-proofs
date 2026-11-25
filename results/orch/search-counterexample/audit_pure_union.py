from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path

base=Path('/tmp/oec/pequalnp-pilot-62')
data=json.loads((base/'multi-output-line-neighborhoods.json').read_text())
mapping=json.loads((base/'pure-union-control39.mapping.json').read_text())
witness=json.loads((base/'pure-union-control39.witness.json').read_text())
targets=[x['positive_mask'] for x in data['targets']]
caps=[q for q in range(8192) if not any(q&t==t for t in data['allowed_concurrent_triples'])]
assert len(caps)==560
required=[]
for target in targets:
    disjoint=[q for q in caps if not q&target]
    maximal=[q for q in disjoint if not any(q!=r and q&r==q for r in disjoint)]
    assert len(maximal)==54 and all(q.bit_count()==4 for q in maximal)
    assert all(any(q&r==q for r in maximal) for q in disjoint)
    required.extend((target,q) for q in maximal)
assert len(required)==702
assert set(map(tuple,mapping['requirements']))==set(required)
masks=[1<<i for i in range(13)]
for g,(a,b) in enumerate(witness['ors']):
    assert 0<=a<b<13+g
    assert masks[a]&~masks[b] and masks[b]&~masks[a]
    masks.append(masks[a]|masks[b])
assert len(witness['ors'])==witness['or_count']==39
assert masks[13:]==witness['gate_masks']
assert all(any(mask&target==target and not mask&cap for mask in masks[13:]) for target,cap in required)
outputs=[[i for i,mask in enumerate(masks) if mask&target==target] for target in targets]
assert all(outputs)
checks=0
for cap in caps:
    values=[bool(cap>>i&1) for i in range(13)]
    for a,b in witness['ors']:values.append(values[a] or values[b])
    for target,chosen in zip(targets,outputs):
        assert all(values[i] for i in chosen)==bool(cap&target)
        checks+=1
actions=[[(a*j+c)%13 for j in range(13)] for a in (1,3,9) for c in range(13)]
required_set=set(required)
for action in actions:
    def image(mask):return sum(1<<action[j] for j in range(13) if mask>>j&1)
    assert {(image(t),image(q)) for t,q in required}==required_set
representatives=sorted({min(tuple(sorted((action[a],action[b]))) for action in actions) for a,b in combinations(range(13),2)})
assert representatives==[(0,1),(0,2)]
assert mapping['first_OR_representatives']==[list(x) for x in representatives]
result={
    'status':'Independent pure-union requirement, symmetry and witness checks passed.',
    'source_sha256':sha256((base/'pure_union_cnf.py').read_bytes()).hexdigest(),
    'witness_sha256':sha256((base/'pure-union-control39.witness.json').read_bytes()).hexdigest(),
    'or_count':39,'requirements':702,'cap_assignments':560,'output_comparisons':checks,
    'symmetries':39,'first_OR_representatives':representatives,
    'restriction':'Internal gates compute pure line unions; final output meets are free. UNSAT would concern this restricted architecture only.',
}
print(json.dumps(result,indent=2))
(base/'pure-union-independent-audit.json').write_text(json.dumps(result,indent=2)+'\n')
