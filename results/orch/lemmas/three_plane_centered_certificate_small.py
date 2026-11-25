import sympy as s,itertools
from pathlib import Path
from sympy.polys.matrices import DomainMatrix
x,y,z=s.symbols('x y z');a,b,c,h=s.symbols('a b c h')
K=s.Matrix([[0,a,b],[-a,0,c],[-b,-c,0]]);v=s.Matrix([x,y,z]);d=(s.eye(3)+K)*v;o=h/2*(s.eye(3)-K)*v
red=lambda g:s.rem(s.Poly(s.expand(g),h),s.Poly(h*h+2,h)).as_expr()
f=red(d[0]*d[1]*d[2]+d[0]*o[0]**2+d[1]*o[1]**2+d[2]*o[2]**2+2*o[0]*o[1]*o[2]);gs=s.Poly(f,x,y,z).coeffs()
perms=[]
for p in itertools.permutations(range(3)):
 KP=K.extract(p,p);sub={a:KP[0,1],b:KP[0,2],c:KP[1,2]};mp=[]
 for g in gs:
  gp=s.expand(g.subs(sub,simultaneous=True));mp.append(next(j for j,t in enumerate(gs) if s.expand(gp-t)==0))
 perms.append((sub,mp))
ms=[1,a,b,c,a*a,a*b,a*c,b*b,b*c,c*c];vs=[]
for j in [0,1,4]:
 for m in ms:
  vec=[0]*10
  for sub,mp in perms:vec[mp[j]]+=s.sympify(m).subs(sub,simultaneous=True)
  vec=[s.expand(q) for q in vec]
  if vec not in vs and any(vec):vs.append(vec)
ps=[s.Poly(red(sum(q*g for q,g in zip(v,gs))),a,b,c) for v in vs]
mons=sorted({mon for p in ps for mon in p.monoms()}|{(0,0,0)})
A=s.Matrix([[s.expand(p.coeff_monomial(mon)).coeff(h,0) for p in ps] for mon in mons]);B=s.Matrix([[s.expand(p.coeff_monomial(mon)).coeff(h,1) for p in ps] for mon in mons]);rhs=s.Matrix([int(mon==(0,0,0)) for mon in mons]+[0]*len(mons));Q=A.row_join(-2*B).col_join(B.row_join(A))
print('shape',Q.shape,flush=True)
rr,piv=DomainMatrix.from_Matrix(Q.row_join(rhs)).to_field().rref();R=rr.to_Matrix();print('rank',len(piv),piv,flush=True)
assert Q.cols not in piv
sol=s.zeros(Q.cols,1)
for i,p in enumerate(piv):sol[p]=R[i,-1]
cs=[s.factor(sum((sol[k]+h*sol[len(vs)+k])*vec[j] for k,vec in enumerate(vs))) for j in range(10)]
print('coefficients',cs,flush=True);print('check',red(sum(u*g for u,g in zip(cs,gs))),flush=True)
Path('/tmp/oec/pequalnp-pilot-79/centered-certificate-small.txt').write_text('\n'.join(str(q) for q in cs))
