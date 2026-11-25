"""Exact conditional scalar branches after beta is restricted to -2 or 1/2."""
from pathlib import Path
import json,time
import sympy as S
root=Path(__file__).parent
A,beta,U,V,sat=S.symbols('A beta U V sat');loc={str(x):x for x in [A,beta,U,V,sat]}
source=json.loads((root/'fresh/c4-nonzero-reduced-3.json').read_text())
equations=[S.sympify(x,locals=loc) for x in source['equations']]
output=[];start=time.monotonic()
for b,values in [(S.Integer(-2),[S.Integer(2),S.Rational(3,32)]),
                 (S.Rational(1,2),[S.Integer(4),S.Rational(3,4)])]:
    factored=S.factor(equations[2].subs(beta,b))
    print('BETA',b,'SCALE_CURVE',factored,flush=True)
    for a in values:
        polynomials=[S.expand(p.subs({A:a,beta:b})) for p in equations]
        assert polynomials[2]==0
        basis=S.groebner(polynomials,U,V,sat,order='grevlex',domain=S.QQ)
        record={'A':str(a),'beta':str(b),'variables':['U','V','sat'],
            'equations':list(map(str,polynomials)),
            'nonzero_source_indices':[i for i,p in enumerate(polynomials) if p!=0],
            'groebner_basis':list(map(str,basis.polys)),
            'basis_expressions':[str(p.as_expr()) for p in basis.polys],
            'scope':'Conditional fixed-scalar branch only; requires independently established restriction on beta.'}
        output.append(record)
        print('A',a,'BASIS',record['basis_expressions'],'SECONDS',time.monotonic()-start,flush=True)
(root/'c4-case3-scalar-branches.json').write_text(json.dumps(output,indent=2)+'\n')
