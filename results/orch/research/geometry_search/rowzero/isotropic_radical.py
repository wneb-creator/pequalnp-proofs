import sympy as S,itertools,time

t,a,b,c=S.symbols('t a b c')
h1=S.Matrix([1,1,-1,-1]);h2=S.Matrix([1,-1,1,-1]);h3=S.Matrix([1,-1,-1,1]);one=S.ones(4,1)
u=(1-t*t)*h1+S.I*(1+t*t)*h2+2*t*h3
w=-t*h1+S.I*t*h2+h3
assert S.expand((u.T*u)[0])==0 and S.expand((u.T*w)[0])==0 and S.expand((w.T*w)[0])==4
T=a*u*u.T+b*(u*w.T+w*u.T)+c*(u*one.T+one*u.T)
f=0
for rows in itertools.combinations(range(4),3):
 for cols in itertools.combinations(range(4),3):
  f+=sum(S.prod(T[rows[i],cols[pm[i]]] for i in range(3)) for pm in itertools.permutations(range(3)))
f=S.expand(f)
print('E3u',S.factor(sum(S.prod(u[i] for i in ix) for ix in itertools.combinations(range(4),3))),flush=True)
for mon,co in S.Poly(f,a,b,c).terms():print(mon,S.factor(co),flush=True)
F=t**4-1
A=-1536*t**2*F**2
B=-1536*t*F*(5*t**4-1)
C=-256*(49*t**8-34*t**4+1)
D=-512*t**3*(13*t**4-5)
E=768*S.I*t*F
assert S.expand(f-(A*a**3+B*a*a*b+C*a*b*b+D*b**3+E*b*b*c-E*c**3))==0
P=S.cancel(C-B**2/(3*A))
R=S.cancel(D-B*C/(3*A)+2*B**3/(27*A**2))
assert S.cancel(P-256*(t**8+14*t**4+1))==0
assert S.cancel(R-256*(t**12-33*t**8-33*t**4+1)/(9*t*(t**4-1)))==0
q=S.symbols('q')
K=q*q+14*q+1
H=q**3-33*q*q-33*q+1
assert S.expand(K**3-H**2-108*q*(q-1)**4)==0
assert S.expand(P**3+A*E**2-256**3*((t**8+14*t**4+1)**3+54*t**4*(t**4-1)**4))==0
print('ALL EXACT COEFFICIENT AND OBSTRUCTION IDENTITIES VERIFIED',flush=True)
