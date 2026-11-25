import itertools,json,sympy as s
from pathlib import Path
e,f,a,b,H,X,Y=s.symbols('e f a b H X Y');z=[f,a,b,H,X,Y]
alpha,beta,gamma,t=s.symbols('alpha beta gamma t')
q=6*e**2+2*f**2+a**2+b**2-H**2-X**2-Y**2-X*(a+b)+Y*(b-a)
c=2*f*a*b-2*H*X*Y+e*(-4*X**2-4*Y**2+4*X*(a+b)+4*Y*(a-b)-a*a-b*b+4*f*f)-4*e**3
G=s.hessian(q,z)/2;Gi=G.inv()
S={e:-e,f:-f,a:b,b:a,H:H,X:X,Y:-Y}
T={e:e,f:-f,a:a,b:-b,H:H,X:Y,Y:X}
assert s.expand(q.subs(S,simultaneous=True)-q)==0
assert s.expand(c.subs(S,simultaneous=True)+c)==0
assert s.expand(q.subs(T,simultaneous=True)-q)==0
assert s.expand(c.subs(T,simultaneous=True)-c)==0
print('SYMMETRIES_S_AND_T_PASS',flush=True)
for index,perm in enumerate(itertools.permutations([f,a,b])):
    forms=[H-alpha*perm[0],X-beta*perm[1],Y-gamma*perm[2]]
    N=s.Matrix([[s.diff(ell,w) for w in z] for ell in forms])
    Gram=s.simplify(N*Gi*N.T)
    print('CASE',index,'NORMAL_H_COLUMN',list(Gram[:,0]),flush=True)
    Q3=s.expand(q.subs({e:0,H:alpha*perm[0],X:beta*perm[1],Y:gamma*perm[2]},simultaneous=True))
    M=s.hessian(Q3,[f,a,b])/2
    print('GRAM3',index,M,flush=True)
    if index in [2,3,4,5]:
        minors=[s.expand(M.extract(rows,cols).det()) for rows in itertools.combinations(range(3),2) for cols in itertools.combinations(range(3),2)]
        gro=s.groebner(minors+[alpha*beta*gamma-1],alpha,beta,gamma,order='grevlex',domain=s.QQ)
        assert list(gro)==[1]
        print('RANK_AT_MOST_ONE_IMPOSSIBLE',index,flush=True)
    else:
        assert M[0,1]==M[0,2]==0 and M[0,0]==2-alpha*alpha
print('RANK_ONE_BRANCHES_PASS',flush=True)
we,wf,wa,wb,wH,wX,wY=s.symbols('we wf wa wb wH wX wY')
sub={e:t*we,f:1+t*wf,a:t*wa,b:t*wb,H:alpha+t*wH,X:t*wX,Y:t*wY}
assert s.expand(c.subs(sub,simultaneous=True)).coeff(t,1)==4*we
assert s.expand(q.subs(sub,simultaneous=True)).coeff(t,0)==2-alpha*alpha
print('PURE_fH_DIRECTION_CUBIC_R_SQUARED_W_IS_4e',flush=True)
# Explicit two finite scalar alternatives for the rank-one cases.
for g in [s.Rational(2),s.Rational(-1,2)]:
    aa=1+g/2;bb=4*g/(2*g-1);prod=s.factor(aa*bb*g*g)
    assert prod in [s.Rational(64,3),s.Rational(3,16)]
    print('CASE2_GAMMA',g,'ALPHA2',aa,'BETA2',bb,'SQUARED_PRODUCT',prod,flush=True)
for bval in [s.Rational(1,2),s.Rational(-2)]:
    aa=1-bval/2;gg=4*bval/(2*bval+1);prod=s.factor(aa*bval*bval*gg)
    assert prod in [s.Rational(64,3),s.Rational(3,16)]
    print('CASE3_BETA',bval,'ALPHA2',aa,'GAMMA2',gg,'SQUARED_PRODUCT',prod,flush=True)
print('ALL_BOUNDARY_SCALAR_CHECKS_PASS',flush=True)
