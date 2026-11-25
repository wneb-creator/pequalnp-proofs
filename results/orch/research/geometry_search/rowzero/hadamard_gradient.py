import sympy as S,itertools
from pathlib import Path
names='a b c d e f x y z'.split();vs=S.symbols(' '.join(names));a,b,c,d,e,f,x,y,z=vs
Q,C,P=[S.sympify(l,locals=dict(zip(names,vs))) for l in Path('/tmp/oec/pequalnp-pilot-78/construct_search/hadamard-polynomials.txt').read_text().splitlines()]
weights=[1,1,1,S.Rational(1,2),S.Rational(1,2),S.Rational(1,2),S.Rational(-1,6),S.Rational(-1,6),S.Rational(-1,6)]
N=S.expand(sum(w*S.diff(C,v)**2 for w,v in zip(weights,vs)))
print('GRADIENT NORM',N,flush=True)
print('LAPLACIAN C',S.expand(sum(w*S.diff(C,v,2) for w,v in zip(weights,vs))),flush=True)
l=a+b+c
invs=[l*l,a*a+b*b+c*c,d*d+e*e+f*f,x*x+y*y+z*z,d*z+e*y+f*x]
bases=[P]+[u*v for i,u in enumerate(invs) for v in invs[i:]]
labels=['P']+[str((i,j)) for i in range(len(invs)) for j in range(i,len(invs))]
monomials=set(S.Poly(N,*vs).monoms())
polys=[S.Poly(S.expand(g),*vs) for g in bases]
for p in polys:monomials.update(p.monoms())
monomials=sorted(monomials)
M=S.Matrix([[p.coeff_monomial(m) for p in polys] for m in monomials])
rhs=S.Matrix([S.Poly(N,*vs).coeff_monomial(m) for m in monomials])
print('INVARIANT PRODUCT SPAN',S.linsolve((M,rhs)),flush=True)
small=[Q*Q,P,Q*l*l,C*l,l**4]
mons=set(S.Poly(N,*vs).monoms());ps=[S.Poly(S.expand(p),*vs) for p in small]
for p in ps:mons.update(p.monoms())
mons=sorted(mons)
M=S.Matrix([[p.coeff_monomial(m) for p in ps] for m in mons]);rhs=S.Matrix([S.Poly(N,*vs).coeff_monomial(m) for m in mons])
print('SMALL SPAN Q²,P,Ql²,Cl,l⁴',S.linsolve((M,rhs)),flush=True)
print('N+32P−3Q²',S.factor(N+32*P-3*Q*Q),flush=True)
