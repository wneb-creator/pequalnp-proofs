"""Full raw truth checks, encoded essentiality, and assembly fixtures."""
import json,hashlib
from pathlib import Path
from assemble_five_owner import assemble_five,or_network

HERE=Path(__file__).resolve().parent
case=json.loads((HERE/'five-owner-joint-packet.json').read_text())[0]
N=1<<16
columns=[int(('1'*(1<<i)+'0'*(1<<i))*(N//(2<<i)),2) for i in range(16)]
target=0
for a,b in case['edges']:target|=columns[a]&columns[b]
for feature in case['features']:
    v=0
    for i in feature['raw_indices']:v|=columns[i]
    columns.append(v)
blob=target.to_bytes(N//8,'little')
truth={'assignments':N,'true_assignments':target.bit_count(),
       'encoding':'Bit m is target value on raw assignment mask m; bytes little-endian.',
       'sha256':hashlib.sha256(blob).hexdigest(),'packed_hex':blob.hex()}
(HERE/'five-owner-full-truth.json').write_text(json.dumps(truth,indent=2)+'\n')
def encode(mask):
    out=mask
    for j,f in enumerate(case['features']):
        if any(mask>>i&1 for i in f['raw_indices']):out|=1<<(16+j)
    return out
witnesses=[]
edges=set(map(tuple,case['edges']))
for i in range(16):
    if i<5:mask=1<<next(b for a,b in edges if a==i)
    else:
        point=next(a for a,b in edges if b==i)
        neighbors={b for a,b in edges if a==point}
        mask=(1<<point)|sum(1<<j for j in range(5,16) if j not in neighbors)
    changed=mask^(1<<i)
    assert not(target>>mask&1) and target>>changed&1
    assert encode(mask)^encode(changed)==1<<i
    witnesses.append({'raw_input':i,'false_mask':mask,'true_mask':changed})

seeds=[]
names=['five_owner_filtered23_seed.json','five_owner_algebraic5extra22_seed.json',
       'five_owner_algebraic4extra23_seed.json','five_owner_shared4extra22_seed.json',
       'five_owner_shared2extra23_seed.json']
for name in names:
    source=json.loads((HERE.parent/'reduction_analysis'/name).read_text())
    gates=[[op,a if a<16 else a+36,b if b<16 else b+36] for op,a,b in source['gates']]
    output=source['output']+36 if source['output']>=16 else source['output']
    values=columns[:]
    for op,a,b in gates:values.append(values[a]|values[b] if op else values[a]&values[b])
    actual=values[output]
    assert not(target&~actual)
    full,assembly=assemble_five(case,gates,output)
    assert assembly['prefix_extra_cost']==0 and assembly['gates']==len(gates)+40
    seed={'gates':gates,'output':output,'inputs':52,'raw_inputs':16,'source':name,
          'and_count':sum(g[0]==0 for g in gates),'gate_count':len(gates),
          'false_negatives':0,'false_positives':(actual&~target).bit_count(),
          'boundary_errors':[m for m,y in case['raw_tests'] if (actual>>m&1)!=y],
          'assembly':assembly,'target_met':False}
    seeds.append(seed)

def reduced(terms):
    ans=[]
    for x in sorted(set(terms),key=lambda x:(x.bit_count(),x)):
        if not any(y&x==y for y in ans):ans.append(x)
    return ans
def eval_dnf(inputs,gates):
    values=[x[:] for x in inputs]
    for op,a,b in gates:values.append(reduced(values[a]+values[b] if op else [x|y for x in values[a] for y in values[b]]))
    return values
raw=case['input_original']
encoded=[[1<<i] for i in raw]+[[1<<i for i in f['original_lines']] for f in case['features']]
all_edges={(p,13+l) for p in range(13) for l in range(13) if (p+l)%13 in (0,1,3,9)}
outside=[1<<p|1<<l for p,l in all_edges if p not in case['group']]
fixtures=[]
for logical in range(16,52):
    full,meta=assemble_five(case,[],logical)
    assert meta['prefix_extra_cost']==0
    assert eval_dnf([[1<<i] for i in range(26)],full)[-1]==reduced(outside+encoded[logical])
    fixtures.append(meta)
all_features=[];wire=16
for logical in range(17,52):
    all_features.append([1,wire,logical]);wire=52+len(all_features)-1
full,meta=assemble_five(case,all_features,wire)
assert meta['prefix_extra_cost']==20
assert eval_dnf([[1<<i] for i in range(26)],full)[-1]==reduced(outside+eval_dnf(encoded,all_features)[wire])
for seed in seeds:
    full,meta=assemble_five(case,seed['gates'],seed['output'])
    assert eval_dnf([[1<<i] for i in range(26)],full)[-1]==reduced(outside+eval_dnf(encoded,seed['gates'])[seed['output']])
report={'verdict':'PASS','raw_assignments':N,'essential_raw_witnesses':witnesses,
        'single_feature_assembly_fixtures':36,'all_features_extra_cost':20,
        'seed_summaries':[{k:v for k,v in seed.items() if k not in ('gates','boundary_errors')}|
                          {'boundary_error_count':len(seed['boundary_errors'])} for seed in seeds],
        'scope':'All seeds remain incorrect approximations. Exact core23 with zero prefix overhead would suffice.'}
(HERE/'five-owner-joint-seeds.json').write_text(json.dumps(seeds,indent=2)+'\n')
(HERE/'five-owner-artifact-validation.json').write_text(json.dumps(report,indent=2)+'\n')
print('PASS full65536 truth;16 essential raw inputs;36 feature fixtures;all-feature overhead20')
for seed in seeds:print(seed['source'],seed['gate_count'],seed['and_count'],seed['false_positives'],len(seed['boundary_errors']))
