import itertools
import json
import pathlib
import runpy

HERE=pathlib.Path(__file__).resolve().parent
Builder=runpy.run_path(str(HERE/'generate_full_guard_seeds.py'))['Builder']
geometry=json.loads((HERE/'geometry.json').read_text())
neighbors=[{b for a,b in geometry['edges'] if a==p} for p in range(13)]
group_arc=(0,1,2,3,5,6,7,9,11)
known=json.loads((HERE.parent/'algebra_strategy/k9_arc_4_8_10_12.json').read_text())
cases=[]
for shape,group in [('arc9',group_arc)]:
    lines=sorted(set.union(*(neighbors[p] for p in group)))
    originals=list(group)+lines
    local={v:i for i,v in enumerate(originals)}
    edges=[[local[p],local[l]] for p in group for l in sorted(neighbors[p])]
    raw=len(originals)
    assert originals==known['input_original'] and edges==known['edges']
    negatives=[x for x,y in known['tests'] if y==0]
    assert len(negatives)==228
    tests=[[(1<<a)|(1<<b),1] for a,b in edges]+[[mask,0] for mask in negatives]
    for preferred in list(itertools.combinations(range(9),2))+[None]:
        builder=Builder(26)
        outside=[p for p in range(13) if p not in group]
        for p in outside:
            feature=neighbors[p]&set(lines)
            if preferred is not None:
                a,b=(group[i] for i in preferred)
                left=feature&neighbors[a];right=feature&neighbors[b]
                if len(left)==len(right)==1 and left!=right:builder.union(left|right)
            builder.union(feature)
        features=[]
        line_mask=sum(1<<l for l in lines)
        for mask,wire in builder.unions.items():
            if wire>=26 and mask&line_mask==mask and mask.bit_count()>=2:
                features.append({'original_lines':[l for l in lines if mask>>l&1],
                                 'raw_indices':[local[l] for l in lines if mask>>l&1],
                                 'outside_wire':wire})
        features.sort(key=lambda f:f['outside_wire'])
        terms=[builder.gate(0,p,builder.union(neighbors[p])) for p in outside]
        output=terms[0]
        for term in terms[1:]:output=builder.gate(1,output,term)
        assert len(builder.gates)==19
        extended=[]
        for mask,label in tests:
            available=mask
            for i,feature in enumerate(features):
                if any(mask>>v&1 for v in feature['raw_indices']):available|=1<<(raw+i)
            extended.append([available,label])
        cases.append(dict(name=shape+'_'+('sorted' if preferred is None else ''.join(map(str,preferred))),
                          group=list(group),raw_inputs=raw,input_original=originals,
                          inputs=raw+len(features),features=features,edges=edges,raw_tests=tests,
                          tests=extended,max_gates=43,outside_gates=builder.gates,
                          outside_output=output,outside_cost=19,final_or_cost=1,total_if_target_met=63))
(HERE/'nine-owner-gadgets.json').write_text(json.dumps(cases))
print([dict(name=c['name'],raw_inputs=c['raw_inputs'],features=len(c['features']),
            tests=len(c['tests']),outside_gates=len(c['outside_gates'])) for c in cases])
