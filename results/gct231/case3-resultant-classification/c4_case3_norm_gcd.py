"""Necessary scale-curve norms; conjugate roots can introduce spurious branches."""
from pathlib import Path
import json,time
import sympy as S
root=Path(__file__).parent
A,beta,U,V=S.symbols('A beta U V');loc={str(x):x for x in (A,beta,U,V)}
data=json.loads((root/'c4-case3-resultants.json').read_text())
F=S.sympify(data['scale_curve'],locals=loc);H=beta**2+beta-1
fa,fb,fc=S.Poly(F,A).all_coeffs();common=None;output=[];start=time.monotonic()
for row in data['reductions']:
    if not row['label'].startswith('eliminate_V'):continue
    polynomial=S.Poly(S.sympify(row['polynomial'],locals=loc),A)
    assert polynomial.degree()==1
    a,c=polynomial.all_coeffs()
    norm=S.Poly(S.expand(fa*c*c-fb*a*c+fc*a*a),beta,domain=S.QQ).primitive()[1]
    removed=[]
    for safe in (S.Poly(beta,beta),S.Poly(H,beta)):
        while True:
            quotient,remainder=norm.div(safe)
            if not remainder.is_zero:break
            norm=quotient;removed.append(str(safe.as_expr()))
    common=norm if common is None else common.gcd(norm)
    output.append({'label':row['label'],'norm':str(norm.as_expr()),
                   'removed_nonzero_factors':removed,'gcd_so_far':str(common.as_expr())})
    print(row['label'],'normdegree',norm.degree(),'gcddegree',common.degree(),
          'seconds',time.monotonic()-start,flush=True)
    (root/'c4-case3-norm-gcd.json').write_text(json.dumps(output,indent=2)+'\n')
print('factor_final_gcd',S.factor(common.as_expr()),flush=True)
