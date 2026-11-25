"""Reverse elimination and first necessary norm for C4 case3."""
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
    (base/'c4-case3-reverse-progress.json').write_text(json.dumps(reductions,indent=2)+'\n')
    return polynomial
q=reduce_curve(equations[0],'q')
c=reduce_curve(equations[1],'c')
r=reduce_curve(equations[3],'linear_r')
assert S.degree(r,V)<=1
rq=reduce_curve(S.resultant(r,q,V),'eliminate_V_q')
rc=reduce_curve(S.resultant(r,c,V),'eliminate_V_c')
final=reduce_curve(S.resultant(rq,rc,U),'eliminate_U_01')
f=S.Poly(final,A);assert f.degree()==1
a,c=f.all_coeffs();fa,fb,fc=S.Poly(F,A).all_coeffs()
pa,pc,pfa,pfb,pfc=[S.Poly(t,beta,domain=S.QQ) for t in [a,c,fa,fb,fc]]
norm=(pfa*pc*pc-pfb*pa*pc+pfc*pa*pa).primitive()[1]
removed=[]
for safe_factor in [S.Poly(beta,beta),S.Poly(H,beta)]:
    while True:
        quotient,remainder=norm.div(safe_factor)
        if not remainder.is_zero:break
        norm=quotient;removed.append(str(safe_factor.as_expr()))
old=json.loads((base/'c4-case3-norm-gcd.json').read_text())[-1]['gcd_so_far']
combined=norm.gcd(S.Poly(S.sympify(old,locals=local),beta,domain=S.QQ))
factored=S.factor(combined.as_expr())
print('REVERSE_NORM_DEGREE',norm.degree(),'COMBINED_GCD',factored,'SECONDS',time.monotonic()-start,flush=True)
(base/'c4-case3-reverse-firstnorm.json').write_text(json.dumps({'reductions':reductions,
    'norm':str(norm.as_expr()),'removed_nonzero_factors':removed,'combined_gcd':str(combined.as_expr()),
    'combined_gcd_factored':str(factored),'scope':'Necessary elimination/norm constraints only; branch exclusions still require separate proof.'},indent=2)+'\n')
