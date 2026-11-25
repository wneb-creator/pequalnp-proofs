import argparse
import importlib.util
import json
import random
from pathlib import Path

p=argparse.ArgumentParser()
p.add_argument('--source',type=Path,required=True)
p.add_argument('--out',type=Path,required=True)
a=p.parse_args()
spec=importlib.util.spec_from_file_location('plane',a.source)
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
examples=[]
for transpose in [False,True]:
    gates=m.star(random.Random(640139),False,transpose)
    score,mismatches,derivatives=m.evaluate(gates)
    assert len(gates)==64 and mismatches==0
    charges=[]
    for point in range(13):
        vals=[((1<<14)-1) if i==point else 0 for i in range(13)]
        vals += [(1<<line) | ((1<<13) if not ((m.NEIGHBORS[point]>>line)&1) else 0)
                 for line in range(13)]
        charged=[]
        for j,(op,left,right) in enumerate(gates):
            x,y=vals[left],vals[right]
            z=(x|y) if op==0 else (x&y)
            vals.append(z)
            sx,sy=x&8191,y&8191
            if op==0 and not ((z>>13)&1) and (sx&~sy)!=0 and (sy&~sx)!=0:
                charged.append(j)
        assert len(charged)==3
        charges.append(charged)
    distinct=sorted(set().union(*map(set,charges)))
    examples.append({'orientation':'column-stars' if transpose else 'point-stars',
                     'gates':gates,'gate_count':64,'OR_count':sum(op==0 for op,_,_ in gates),
                     'AND_count':sum(op==1 for op,_,_ in gates),
                     'complete_boundary_mismatches':mismatches,'derivative_nonzeros':derivatives,
                     'point_cofactor_charges':charges,'weighted_charges':sum(map(len,charges)),
                     'distinct_productive_OR_gates':distinct,'distinct_count':len(distinct)})
assert examples[0]['distinct_count']==39
assert examples[1]['distinct_count']==12
payload={'claim':'Weighted productive cofactor charges do not imply that many distinct productive OR gates.',
         'verification':'Exact finite monotone edge/maximal-independent boundary check; productive Below test uses the largest assignment outside the row neighborhood and singleton supports.',
         'scope':'Both 64-gate circuits compute incidence but have two nonzero target derivatives; neither refutes the posted gap.',
         'examples':examples}
a.out.write_text(json.dumps(payload,indent=2)+'\n')
print(json.dumps({'examples':[{k:v for k,v in e.items() if k not in ['gates','point_cofactor_charges','distinct_productive_OR_gates']} for e in examples]}))
