import json
from pathlib import Path

r=Path('/workspace/pequalnp-proofs/results/orch1884/search')
g=json.loads((r/'cofactor-baseline16.json').read_text())
E=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
mask=(1<<1024)-1
values=[sum(1<<x for x in range(1024)if x>>i&1)for i in range(10)]
values.append(values[0]^mask)
mapped=[]
for op,a,b in g:
    aa=a+1 if a<9 else a+2
    bb=b+1 if b<9 else b+2
    mapped.append([op,aa,bb])
    values.append((values[aa]|values[bb])if op else(values[aa]&values[bb]))
target=sum(1<<x for x in range(1024)if any(x>>a&1 and x>>b&1 for a,b in E))
# Free constants deliberately relax the two-added-gate search. Any negative
# result therefore also covers the strict actual input set.
values.extend([0,mask])
first={}
for a in range(len(values)):
    first.setdefault(mask^values[a],(2,a,a))
    for b in range(a,len(values)):
        first.setdefault(values[a]&values[b],(0,a,b))
        first.setdefault(values[a]|values[b],(1,a,b))
found=None
for v,gate in first.items():
    if v==target:
        found={'first':gate,'second':None};break
    if mask^v==target:
        found={'first':gate,'second':[2,'new','new']};break
    for b,w in enumerate(values):
        if v&w==target:
            found={'first':gate,'second':[0,'new',b]};break
        if v|w==target:
            found={'first':gate,'second':[1,'new',b]};break
    if found:break
result={'fixed_baseline_gates':16,'mapped_baseline':mapped,'full_assignments':1024,
        'additional_gate_budget':2,'free_negated_x0':True,'free_constants_relaxation':True,
        'distinct_first_gate_functions':len(first),'found_extension':found,
        'scope':'Append at most two AND/OR/NOT gates after the fixed16gate cofactor baseline; earlier gates unchanged.'}
(r/'fixed-two-gate-extension-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k!='mapped_baseline'}))
