import importlib.util
import json
from pathlib import Path
import random

base=Path('/tmp/oec/pequalnp-pilot-96')
spec=importlib.util.spec_from_file_location('ordered',base/'counterexample_sat_ordered.py')
o=importlib.util.module_from_spec(spec)
spec.loader.exec_module(o)
seed=2026112596
rng=random.Random(seed)
tested=0
counts={False:0,True:0}
for normalized in (False,True):
    gates=6
    original,original_choices=o.original_encode([],gates,'any',normalized)
    cnf,choices=o.encode([],gates,'any',normalized)
    assert choices==original_choices and cnf.variables==original.variables
    assert cnf.clauses[:len(original.clauses)]==original.clauses
    added=cnf.clauses[len(original.clauses):]
    stop=gates-1 if normalized else gates-2
    for _ in range(3000):
        circuit=[]
        truth=set()
        for j,(a,b,n,orb) in enumerate(choices):
            operation=rng.randrange(3)
            left=rng.randrange(11+j)
            right=0 if operation==2 else rng.randrange(11+j)
            if operation!=2:left,right=sorted((left,right))
            circuit.append((operation,left,right))
            truth.add(a[left]);truth.add(b[right])
            if operation==2:truth.add(n)
            if operation==1:truth.add(orb)
        actual=all(any(v in truth if v>0 else -v not in truth for v in clause) for clause in added)
        expected=sum(op==2 for op,_,_ in circuit)<=4
        for i in range(stop):
            _,a,b=circuit[i]
            _,aa,bb=circuit[i+1]
            dependent=aa==11+i or bb==11+i
            if not dependent and (aa,bb)<(a,b):expected=False
        assert actual==expected,(normalized,circuit,actual,expected)
        tested+=1
        counts[normalized]+=actual
report={'status':'PASS','seed':seed,'tested_assignments':tested,'generic_accepted':counts[False],'normalized_accepted':counts[True],'scope':'Added at-most4-NOT and independent-adjacent source-pair ordering clauses only; fixed-first and normalized-live classes remain witness-search restrictions, not an exhaustive lower-bound proof.'}
(base/'ordered-reproducible-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
