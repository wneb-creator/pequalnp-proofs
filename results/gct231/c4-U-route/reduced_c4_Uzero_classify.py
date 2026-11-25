"""Small exact conditional elimination identities assuming U=0; not a proof of U=0."""
import json
from pathlib import Path
import sympy as s
root=Path('/tmp/oec/pequalnp-pilot-75/gct231')
data=json.loads((root/'fresh'/'c4-nonzero-reduced-2.json').read_text())
P,B,U,V,sat=s.symbols(data['variables']);loc=dict(zip(data['variables'],(P,B,U,V,sat)))
e=[s.sympify(t,locals=loc) for t in data['equations']]
first=s.factor(s.resultant(e[0].subs(U,0),e[1].subs(U,0),B))
assert first==-3*V**2*(V-6)**2*(V+2)
print('CASE2 resultant',first,flush=True)
certificates=[]
for b,v,indices in [(s.Rational(1,3),-2,(2,4)),(s.Integer(1),6,(2,3))]:
    f,g=[s.expand(e[i].subs({U:0,B:b,V:v})) for i in indices]
    a,c,h=s.gcdex(f,g,P)
    assert s.expand(a*f+c*g-h)==0
    assert h==(1 if v==-2 else P+2)
    record={'B':str(b),'V':str(v),'indices':list(indices),'polynomials':[str(f),str(g)],
            'multipliers':[str(a),str(c)],'conclusion':str(h)}
    certificates.append(record)
    print(json.dumps(record,sort_keys=True),flush=True)
data3=json.loads((root/'fresh'/'c4-nonzero-reduced-3.json').read_text())
A,beta,U,V,sat=s.symbols(data3['variables']);loc=dict(zip(data3['variables'],(A,beta,U,V,sat)))
e3=[s.sympify(t,locals=loc) for t in data3['equations']]
linear=s.factor(e3[3].subs({U:0,beta:s.Rational(1,2),A:4}))
assert s.expand(linear-s.Rational(169,8)*(V+12))==0
print('CASE3 final linear',linear,flush=True)
(root/'reduced-c4-Uzero-classify.json').write_text(json.dumps({
    'scope':'Exact conditional identities after U=0 and the stated substitutions. U=0 itself remains unproved.',
    'case2_resultant':str(first),'case2_bezout':certificates,'case3_final_linear':str(linear)},indent=2)+'\n')
