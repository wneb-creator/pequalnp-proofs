from pathlib import Path
from datetime import datetime,timezone
import itertools
import sympy as s

print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
x,y,z,u,v,r,t,c=s.symbols('x y z u v r t c')
N=s.Matrix([[-c,1,0,-1],[1,c,-1,0],[0,-1,-c,1],[-1,0,1,c]])
U=s.Matrix([[s.I*v,-u,0,s.I*u],[-u,-v,-s.I*u,0],[0,-s.I*u,-s.I*v,u],[s.I*u,0,u,v]])
V=s.conjugate(U).subs({s.conjugate(u):r,s.conjugate(v):t})
assert V.free_symbols=={r,t}
T=x*N+y*U+z*V
P=0
for mask in range(1,16):
    size=mask.bit_count()
    P+=(-1)**(4-size)*s.prod(size+sum(T[i,j] for j in range(4) if mask>>j&1) for i in range(4))
P=s.Poly(s.expand(P-24),x,y,z)
q=s.factor(P.coeff_monomial(y*z))
cu=s.factor(P.coeff_monomial(x*y*y))
cv=s.factor(P.coeff_monomial(x*z*z))
print('Q mixed',q,'C_NUU',cu,'C_NVV',cv,flush=True)
assert s.expand(P.coeff_monomial(x*x)-(8-4*c*c))==0
assert all(coef==0 for mon,coef in P.terms() if sum(mon)<4 and mon not in [(2,0,0),(0,1,1),(1,2,0),(1,0,2)])
a=2*u+(2-2*s.I)*v
b=(2+2*s.I)*u+v
assert s.expand(q.subs({r:b,t:-a},simultaneous=True))==0
f=s.expand(cu/(4*s.I))
g=s.expand(cv/(-4*s.I))
h=s.expand(g.subs({r:b,t:-a},simultaneous=True))
res=s.factor(s.resultant(f.subs(v,1),h.subs(v,1),u))
assert s.expand(res-256*(c*c-3*c+1)*(c*c+3*c+1))==0
assert s.rem(res,c*c-2,c)==-2304
print('Closed elimination resultant',res,'mod c^2-2:',-2304,flush=True)
for sign in (1,-1):
    cs=sign*s.sqrt(2)
    pols=[s.expand(p.subs(c,cs)) for p in (q,cu,cv)]
    for uindex in (0,1):
        for vindex in (0,1):
            us=(u,v)[uindex];vs=(r,t)[vindex]
            free=((v,u)[uindex],(t,r)[vindex])
            eq=[s.expand(p.subs({us:1,vs:1})) for p in pols]
            gb=s.groebner(eq,*free,extension=[s.I,s.sqrt(2)])
            print('sign',sign,'normalizations',us,vs,'basis',list(gb),flush=True)
            if list(gb)!=[1]:
                sol=s.solve_poly_system(list(gb),*free)
                print('SOLUTIONS',sol,flush=True)
                for vals in sol:
                    sub={c:cs,us:1,vs:1,**dict(zip(free,vals))}
                    rem=s.Poly(s.expand(P.as_expr().subs(sub)),x,y,z,extension=True)
                    assert all(sum(mon)==4 for mon,coef in rem.terms())
                    print('SEED',sub,'QUARTIC',s.factor(rem.as_expr()),flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True)
