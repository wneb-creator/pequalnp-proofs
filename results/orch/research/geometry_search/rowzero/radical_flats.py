import sympy as S,itertools,time

a,b,c,z,x,y=S.symbols('a b c z x y')
d=1-a-b-c
v=S.Matrix([a,b,c,d])
delta=c-d
h=S.Matrix([delta*x,delta*y,(d-a)*x+(d-b)*y,(a-c)*x+(b-c)*y])
assert S.expand(sum(h))==0 and S.expand((v.T*h)[0])==0
T=v*h.T+h*v.T
norm=S.expand((v.T*v)[0]-1)
print('norm',S.factor(norm),flush=True)
coefficient_sets={}
for degree in [3,4]:
 f=0
 for rows in itertools.combinations(range(4),degree):
  for cols in itertools.combinations(range(4),degree):
   f+=sum(S.prod(T[rows[i],cols[pm[i]]] for i in range(degree)) for pm in itertools.permutations(range(degree)))
 f=S.Poly(S.expand(f),x,y)
 es=[]
 for mon,coef in f.terms():
  coef=S.rem(coef,norm,a)
  coef=S.factor(coef)
  print('degree',degree,'monomial',mon,'coefficient',coef,flush=True)
  es.append(coef)
 coefficient_sets[degree]=es
 if degree==3:
  print('CUBIC GROEBNER START',time.time(),flush=True)
  G=S.groebner([norm,z*delta-1]+es,z,a,b,c,order='grevlex')
  print('CUBIC GROEBNER',G,flush=True)
  for g in G.polys:print(g.as_expr(),flush=True)
print('FULL GROEBNER START',time.time(),flush=True)
G=S.groebner([norm,z*delta-1]+coefficient_sets[3]+coefficient_sets[4],z,a,b,c,order='grevlex')
print('FULL GROEBNER',G,flush=True)
for g in G.polys:print(g.as_expr(),flush=True)
print('LEX START',time.time(),flush=True)
L=G.fglm('lex')
print('FULL LEX',L,flush=True)
for g in L.polys:print(g.as_expr(),flush=True)
print('SOLUTIONS',S.solve_poly_system(list(L),z,a,b,c),flush=True)
