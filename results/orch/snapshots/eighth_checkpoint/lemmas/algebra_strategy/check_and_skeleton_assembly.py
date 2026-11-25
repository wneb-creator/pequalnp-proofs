"""Independent complete truth checks of bounded random skeletons and every AND prefix."""
import json,random
from pathlib import Path
from assemble_and_skeleton import assemble_skeleton

HERE=Path(__file__).resolve().parent
rng=random.Random(65013);cases=300;checks=0;truth_values=0
for case_index in range(cases):
    n=rng.randrange(2,8);k=rng.randrange(0,7)
    skeleton={'inputs':n,'and_gates':[],'output':[]}
    for i in range(k):
        skeleton['and_gates'].append({side:[x for x in range(n+i) if rng.random()<.32] for side in ('left','right')})
    skeleton['output']=[x for x in range(n+k) if rng.random()<.3]
    outputs=[skeleton['output']]+[[n+i] for i in range(k)]
    for output in outputs:
        source=dict(skeleton,output=output)
        assembled=assemble_skeleton(source)
        assert assembled['all_gate_functions_dnf_verified']
        for mask in range(1<<n):
            original=[bool(mask>>i&1) for i in range(n)]
            for g in source['and_gates']:
                original.append(any(original[x] for x in g['left']) and any(original[x] for x in g['right']))
            want=any(original[x] for x in output)
            if assembled['assembled']:
                actual=[bool(mask>>i&1) for i in range(n)]
                for op,a,b in assembled['gates']:actual.append(actual[a] or actual[b] if op else actual[a] and actual[b])
                got=actual[assembled['output']]
            else:got=False
            assert want==got,(case_index,output,mask)
            truth_values+=1
        checks+=1
report={'verdict':'PASS','random_seed':65013,'skeletons':cases,
        'outputs_including_every_AND_prefix':checks,'complete_truth_assignments_checked':truth_values,
        'scope':'Independent Boolean evaluation of original and assembled circuits, including empty/dead/duplicate cases.'}
(HERE/'and-skeleton-random-validation.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
