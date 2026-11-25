"""Bounded necessary-equation reduction for C4 case3 over its scale curve."""
from pathlib import Path
import json,time
import sympy as S
base=Path(__file__).parent
A,beta,U,V,sat=S.symbols('A beta U V sat')
local={str(x):x for x in (A,beta,U,V,sat)}
source=json.loads((base/'fresh/c4-nonzero-reduced-3.json').read_text())
equations=[S.sympify(x,locals=local) for x in source['equations']]
F=equations[2];H=beta**2+beta-1
assert S.expand(F-H*((8*A**2-10*A)*beta**2+2*A*beta+6-8*A)-3*A*(2*beta-1))==0
assert S.expand((2*beta+3)*(2*beta-1)-4*H)==1
det=-4*A*beta**2-4*A*beta+5*A+6*beta**2+6*beta-6
safe=A*beta*H*det
field=S.QQ.frac_field(beta,U,V)
modulus=S.Poly(F,A,domain=field)
start=time.monotonic();reductions=[]
def reduce_curve(expression,label):
    quotient,remainder=S.div(S.Poly(expression,A,domain=field),modulus)
    rational=S.cancel(remainder.as_expr())
    numerator,denominator=S.fraction(rational)
    assert denominator.free_symbols <= {beta}
    polynomial=S.Poly(numerator,A,beta,U,V,domain=S.QQ).clear_denoms()[1].primitive()[1].as_expr()
    factors=[]
    while polynomial!=0:
        common=S.gcd(polynomial,safe)
        if S.Poly(common,A,beta,U,V).total_degree()==0:break
        polynomial=S.cancel(polynomial/common);factors.append(str(common))
    reductions.append({'label':label,'denominator':str(denominator),
        'removed_nonzero_factors':factors,'polynomial':str(polynomial)})
    poly=S.Poly(polynomial,A,beta,U,V)
    print(label,{'degree':poly.total_degree(),'terms':len(poly.terms()),
                'seconds':time.monotonic()-start},flush=True)
    (base/'c4-case3-resultant-progress.json').write_text(json.dumps(reductions,indent=2)+'\n')
    return polynomial
q=reduce_curve(equations[0],'q')
c=reduce_curve(equations[1],'c')
r=reduce_curve(equations[3],'linear_r')
l=reduce_curve(equations[4],'quadratic_l')
assert S.degree(r,U)<=1
outputs=[]
for polynomial,label in ((q,'q'),(c,'c'),(l,'l')):
    outputs.append(reduce_curve(S.resultant(r,polynomial,U),'eliminate_U_'+label))
for i,j in ((0,1),(0,2),(1,2)):
    reduce_curve(S.resultant(outputs[i],outputs[j],V),'eliminate_V_'+str(i)+str(j))
(base/'c4-case3-resultants.json').write_text(json.dumps({'source':source,
    'scale_curve':str(F),'known_nonzero_H':str(H),'safe_factors':str(safe),
    'reductions':reductions,'scope':'Necessary resultants only; no branch exclusion until independently checked.'},indent=2)+'\n')
