"""Exact rational checks of roots reconstructed from the two modular bases."""
from pathlib import Path
import json
import sympy as s

base=Path('/tmp/oec/pequalnp-pilot-75/gct231')
values={2:[-2,1,0,6,s.Rational(-1,26)],
        3:[4,s.Rational(1,2),0,-12,s.Rational(1,13)]}
records=[]
for case in (2,3):
    source=base/f'fresh/c4-nonzero-reduced-{case}.json'
    data=json.loads(source.read_text())
    variables=s.symbols(data['variables'])
    namespace=dict(zip(data['variables'],variables))
    substitutions=dict(zip(variables,values[case]))
    evaluated=[s.simplify(s.sympify(poly,locals=namespace).subs(substitutions))
               for poly in data['equations']]
    assert all(value==0 for value in evaluated),(case,evaluated)
    record={'case':case,'variables':data['variables'],
            'exact_values':[str(value) for value in values[case]],
            'verified_equations':len(evaluated),
            'scope':'Exact root of the reduced necessary system only; not a full plane witness.'}
    records.append(record);print('PASS',json.dumps(record),flush=True)
(base/'reduced-c4-exact-roots.json').write_text(json.dumps(records,indent=2)+'\n')
