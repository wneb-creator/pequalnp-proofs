from pathlib import Path
import hashlib,json
import sympy as S

base=Path('/tmp/oec/pequalnp-pilot-78/geometry_search')
source=base/'full-quartic-correction.json'
data=json.loads(source.read_text())
b=S.symbols('b0:3');r=S.symbols('r0:3');d=S.symbols('d0:3')
sub=dict(zip(b,[0]*3));sub.update({r[i]:-3*d[i] for i in range(3)})
q=S.expand(S.sympify(data['Q']).subs(sub,simultaneous=True))
c=S.expand(S.sympify(data['cubic_actual']).subs(sub,simultaneous=True))
p=S.expand(S.sympify(data['quartic_actual']).subs(sub,simultaneous=True))
assert q==3*sum(x*x for x in d)
assert c==15*d[0]*d[1]*d[2]
assert S.expand(p-(25*sum(x**4 for x in d)+14*sum(d[i]**2*d[j]**2 for i in range(3) for j in range(i+1,3)))/16)==0
for i in range(3):
    j,k=[z for z in range(3) if z!=i]
    assert S.expand(p.subs(d[i],0)-S.Rational(9,4)*d[j]**4-(d[j]**2+d[k]**2)*(25*d[k]**2-11*d[j]**2)/16)==0
report={'status':'PASS','source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
        'all_three_specialized_permanent_coefficients':True,
        'all_three_zero_coordinate_quartic_identities':True,
        'scope':'Independent exact coefficient check and field-theoretic argument review for the nonzero quadratic R pivot. This supplies one linear pivot only; generic B-rank-one remains open.'}
(base/'Bone-q-pivot-independent-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
