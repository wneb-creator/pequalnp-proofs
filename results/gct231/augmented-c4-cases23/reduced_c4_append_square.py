"""Append the omitted necessary square-pencil condition to frozen reduced systems."""
import hashlib
import json
from pathlib import Path
import sympy as s
root=Path('/tmp/oec/pequalnp-pilot-75/gct231')
alpha,beta,gamma,u,v=s.symbols('alpha beta gamma u v')
P,B,A,U,V,sat=s.symbols('P B A U V sat')
loc={str(x):x for x in (alpha,beta,gamma,u,v)}
for case in (2,3):
    source=root/'fresh'/f'c4-nonzero-square-{case}.json'
    reduced=root/'fresh'/f'c4-nonzero-reduced-{case}.json'
    full=json.loads(source.read_text())
    data=json.loads(reduced.read_text())
    if case==2:
        sub={alpha:P/beta,gamma:1/P,u:U,v:V/beta}
        power,newpower=beta,B
        variables=(P,B,U,V,sat)
        rootpoint={P:-2,B:1,U:0,V:6,sat:s.Rational(-1,26)}
    else:
        sub={gamma:1/(alpha*beta),u:U,v:V/alpha}
        power,newpower=alpha,A
        variables=(A,beta,U,V,sat)
        rootpoint={A:4,beta:s.Rational(1,2),U:0,V:-12,sat:s.Rational(1,13)}
    original=s.sympify(full['equations'][4],locals=loc)
    value=s.together(original.subs(sub,simultaneous=True))
    numerator,denominator=value.as_numer_denom()
    poly=s.Poly(s.expand(numerator),power)
    assert all(exponent[0]%2==0 for exponent,_ in poly.terms())
    converted=s.expand(sum(coefficient*newpower**(exponent[0]//2)
                           for exponent,coefficient in poly.terms()))
    pol=s.Poly(converted,*variables,domain=s.QQ)
    content,primitive=pol.primitive()
    assert content>0
    square=primitive.as_expr()
    data['equations']=data['equations']+[str(square)]
    data['square_source_sha256']=hashlib.sha256(source.read_bytes()).hexdigest()
    data['reduced_source_sha256']=hashlib.sha256(reduced.read_bytes()).hexdigest()
    data['square_source_index']=4
    data['square_discarded_denominator']=str(denominator)
    data['square_primitive_content']=str(content)
    data['square_at_known_rational_point']=str(square.subs(rootpoint))
    data['scope']='Necessary saturated equations including the square-pencil condition; no solver verdict.'
    target=root/f'c4-nonzero-augmented-{case}.json'
    target.write_text(json.dumps(data,indent=2)+'\n')
    print('CASE',case,'APPENDED_TERMS',len(primitive.terms()),'APPENDED_DEGREE',primitive.total_degree(),
          'CONTENT',content,'DENOMINATOR',denominator,'KNOWN_ROOT_VALUE',square.subs(rootpoint),
          'SHA256',hashlib.sha256(target.read_bytes()).hexdigest(),flush=True)
