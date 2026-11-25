"""All42 two-row shared-prefix approximations in the joint four-owner packet."""
import itertools,json
from pathlib import Path

HERE=Path(__file__).resolve().parent
case=json.loads((HERE.parent/'circuit_search/joint-four-owner-packet.json').read_text())[0]
neighbors=[{b for a,b in case['edges'] if a==i} for i in range(4)]
features={frozenset(f['raw_indices']):14+j for j,f in enumerate(case['features']) if len(f['raw_indices'])==2}
N=1<<14
columns=[int(('1'*(1<<i)+'0'*(1<<i))*(N//(2<<i)),2) for i in range(14)]
for feature in case['features']:
    value=0
    for i in feature['raw_indices']:value|=columns[i]
    columns.append(value)
target=0
for a,b in case['edges']:target|=columns[a]&columns[b]
seeds=[]
for p,q in itertools.combinations(range(4),2):
    common=neighbors[p]&neighbors[q];assert len(common)==1
    common=next(iter(common))
    for a in sorted(neighbors[p]-{common}):
        for b in sorted(neighbors[q]-{common}):
            feature=features.get(frozenset((a,b)))
            if feature is None:continue
            gates=[]
            def gate(op,x,y):
                gates.append([op,x,y]);return 41+len(gates)-1
            def OR(ws):
                w=ws[0]
                for v in ws[1:]:w=gate(1,w,v)
                return w
            t=gate(1,common,feature)
            terms=[]
            for owner in range(4):
                if owner==p:line_inputs=[t]+sorted(neighbors[p]-{common,a})
                elif owner==q:line_inputs=[t]+sorted(neighbors[q]-{common,b})
                else:line_inputs=sorted(neighbors[owner])
                terms.append(gate(0,owner,OR(line_inputs)))
            output=OR(terms)
            assert len(gates)==18
            values=columns[:]
            for op,x,y in gates:values.append(values[x]|values[y] if op else values[x]&values[y])
            actual=values[output]
            expected=target|(columns[p]&columns[b])|(columns[q]&columns[a])
            assert actual==expected
            used={x for _,a0,b0 in gates for x in (a0,b0) if x<14}
            seeds.append({'gates':gates,'output':output,'inputs':41,'raw_inputs':14,
                'owners':[p,q],'replaced_lines':[a,b],'used_feature':feature,
                'direct_raw_used':sorted(used),'all_raw_used':len(used)==14,
                'false_negatives':0,'false_positives':(actual&~target).bit_count(),
                'boundary_errors':[x for x,y in case['raw_tests'] if (actual>>x&1)!=y],
                'extra_minimal_terms':[[p,b],[q,a]],
                'status':'Incorrect18-gate shared-prefix approximation; one free feature, no prefix conflict.'})
assert len(seeds)==42
(HERE/'joint-four-shared-prefix-seeds.json').write_text(json.dumps(seeds,indent=2)+'\n')
summary={}
for seed in seeds:
    key=(seed['false_positives'],len(seed['boundary_errors']),seed['all_raw_used'])
    summary[key]=summary.get(key,0)+1
print('all42 seeds verified on all16384 inputs, each18 gates/4AND/one derived feature')
print('profiles FP,boundary_errors,all_raw_used -> count',summary)
