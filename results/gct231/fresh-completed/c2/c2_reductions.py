import itertools
import sympy as s


def per(M):
    return s.expand(sum(s.prod(M[i,p[i]] for i in range(4)) for p in itertools.permutations(range(4))))


a,b,c,h,k = s.symbols('a b c h k')
N = s.Matrix([[a,0,b,c],[0,-a,-b,-c],[b,-b,0,0],[c,-c,0,0]])
minus = s.Poly(per(s.ones(4)+h*N)-24,h)
print('minus_coefficients',[(j,s.factor(minus.nth(j))) for j in (2,4)])
print('minus_quadratic_Gram_determinant',s.det(s.hessian(-minus.nth(2)/2,[a,b,c])/2))

x,y,p,v,w,r = s.symbols('x y p v w r')
z = -2*x-y-2*p-4*v-4*w-2*r
P = s.Matrix([[x,p,v,w],[p,x,v,w],[v,v,y,r],[w,w,r,z]])
for aval in (0,-4):
    NN=N.subs({a:aval,b:1,c:0})
    f=s.Poly(per(s.ones(4)+h*P+k*NN)-24,h,k)
    linear=f.coeff_monomial(h*k*k)
    quadratic=f.coeff_monomial(h*h*k*k)
    xx=s.solve(linear,x)[0]
    print('mixed_line',aval,'linear',s.factor(linear),'x_eliminated',xx,'quartic',s.factor(quadratic.subs(x,xx)))

P0=P.subs(x,p)
assert s.expand(per(s.ones(4)+P0).subs(p,-1)-4*(v+1)**2*(w+1)**2)==0
Q=s.Poly(per(s.ones(4)+h*P0)-24,h).nth(2)
for drop,vars in ((v,[w,r,y]),(w,[v,r,y])):
    qq=s.expand(-Q.subs({p:0,drop:0})/2)
    print('p_zero_and',str(drop)+'_zero','quadratic',qq,'Gram_det',s.det(s.hessian(qq,vars)/2))

A,B,C,L,t=s.symbols('A B C L t')
sub={v:A*p,w:B*p,y:C*p+L*t,r:t}
mat=P0.subs(sub,simultaneous=True)
poly=s.Poly(per(s.ones(4)+mat)-24,p,t)
eq=[]
for mon,coef in poly.terms():
    coef=s.factor(s.rem(coef,L*L+2*L-1,L))
    if coef != 0:
        eq.append(coef)
        print('normalized_mixed0_equation',mon,coef)
gb=s.groebner(eq+[L*L+2*L-1],A,B,C,L,order='grevlex')
print('normalized_mixed0_Groebner',gb)
assert list(gb)==[1]
