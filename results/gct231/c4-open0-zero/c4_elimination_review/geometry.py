"""Recompute selected necessary equations by direct substitution coefficients."""
import json
from pathlib import Path
import sympy as S
base=Path(__file__).resolve().parents[1]
e,f,a,b,H,X,Y,t=S.symbols('e f a b H X Y t')
alpha,beta,gamma,u,v=S.symbols('alpha beta gamma u v')
z=[f,a,b,H,X,Y]; kcoords=[f,a,b,Y]
loc={str(x):x for x in [e,*z,alpha,beta,gamma,u,v]}
q=6*e**2+2*f**2+a**2+b**2-H**2-X**2-Y**2-X*(a+b)+Y*(b-a)
c=2*f*a*b-2*H*X*Y+e*(-4*X**2-4*Y**2+4*X*(a+b)+4*Y*(a-b)-a*a-b*b+4*f*f)-4*e**3
for case,pivot,other in [(0,a,b),(1,b,a)]:
    data=json.loads((base/f'fresh/c4-nonzero-square-{case}.json').read_text())
    equations=dict(zip(data['equation_labels'],[S.sympify(x,locals=loc) for x in data['equations']]))
    w={loc[k]:S.sympify(x,locals=loc) for k,x in data['w'].items()}
    k={e:0,H:alpha*f,X:beta*pivot}
    kvec={x:k.get(x,x) for x in [e,*z]}
    qk=S.expand(q.subs(k,simultaneous=True))
    gram=S.hessian(qk,kcoords)/2
    declared=S.Matrix([[S.sympify(x,locals=loc) for x in row] for row in data['gram_W']])
    assert (gram-declared).applyfunc(S.expand)==S.zeros(4)
    assert S.expand(gram.det()-S.sympify(data['det_W'],locals=loc))==0
    # Verify w is orthogonal to all of W by the mixed coefficient of q.
    qline=S.Poly(S.expand(q.subs({x:kvec[x]+t*w[x] for x in [e,*z]},simultaneous=True)),t)
    assert qline.nth(1)==0
    assert S.expand(qline.nth(2)-equations['q_w'])==0
    cline=S.Poly(S.expand(c.subs({x:kvec[x]+t*w[x] for x in [e,*z]},simultaneous=True)),t)
    assert S.expand(cline.nth(3)-equations['c_w'])==0
    relation=Y-gamma*other
    normal=S.Matrix([S.diff(relation,x) for x in kcoords])
    nv=gram.adjugate()*normal
    assert S.expand((normal.T*nv)[0]-equations['normal_q'])==0
    assert S.expand(cline.nth(1).subs(dict(zip(kcoords,nv)),simultaneous=True)-equations['normal_R'])==0
    assert S.expand(cline.nth(2).subs(dict(zip(kcoords,nv)),simultaneous=True)-equations['normal_L'])==0
    print('PASS',case,'Gram, determinant, orthogonality, direct cubic coefficients, three normal equations',flush=True)
print('PASS: geometric equation formulas; linear-algebra implication reviewed separately.',flush=True)
