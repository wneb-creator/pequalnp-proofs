import itertools, sympy as s
f,a,b,H,X,Y=s.symbols('f a b H X Y')
alpha,beta,gamma=s.symbols('alpha beta gamma')
q=2*f*f+a*a+b*b-H*H-X*X-Y*Y-X*(a+b)+Y*(b-a)
for perm in itertools.permutations([f,a,b]):
    qp=s.Poly(s.expand(q.subs({H:alpha*perm[0],X:beta*perm[1],Y:gamma*perm[2]})),f,a,b)
    eq=[s.factor(c) for c in qp.coeffs()]+[alpha*beta*gamma-1]
    G=s.groebner(eq,alpha,beta,gamma,order='grevlex',domain=s.QQ)
    print('PERM',perm,'EQUATIONS',eq,'BASIS',list(G),flush=True)
    assert list(G)==[1]
print('ALL_SIX_NONZERO_PRODUCT_CASES_EXCLUDED',flush=True)
