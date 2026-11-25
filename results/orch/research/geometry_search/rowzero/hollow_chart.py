import sympy as S,itertools,time

A,B,K,s,t=S.symbols('A B K s t')
z=A*s+B*t
y1=3*A*z+K*t
y2=3*B*z-K*s
a=s+z;b=t+z;d=z;e=y2+z;f=y1+z;c=-s-t-y1-y2-5*z
assert S.expand(a+b+c+d+e+f)==0
assert S.expand(a*f+b*e+c*d)==0
T=S.Matrix([[0,a,b,c],[a,0,d,e],[b,d,0,f],[c,e,f,0]])
cub=0
for rows in itertools.combinations(range(4),3):
 for cols in itertools.combinations(range(4),3):
  cub+=sum(S.prod(T[rows[i],cols[pm[i]]] for i in range(3)) for pm in itertools.permutations(range(3)))
eq=[]
for mon,co in S.Poly(S.expand(cub),s,t).terms():
 co=S.factor(co)
 print('COEFF',mon,co,flush=True)
 eq.append(co)
print('GROEBNER START',time.time(),flush=True)
G=S.groebner(eq,A,B,K,order='grevlex')
print('GROEBNER',G,flush=True)
for g in G.polys:print(g.as_expr(),flush=True)
print('ZERO DIMENSIONAL',G.is_zero_dimensional,flush=True)
if G.is_zero_dimensional:
 L=G.fglm('lex')
 print('LEX',L,flush=True)
 for g in L.polys:print(g.as_expr(),flush=True)
 print('SOLUTIONS',S.solve_poly_system(list(L),A,B,K),flush=True)
