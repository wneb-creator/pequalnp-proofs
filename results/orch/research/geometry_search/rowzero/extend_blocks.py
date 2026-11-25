import sympy as S,itertools

x,y,z=S.symbols('x y z')
h=S.sqrt(2)
A=S.zeros(4); D=S.zeros(4)
B=S.Matrix([[h-1,1],[1,-h-1]])
A[:2,:2]=B;D[2:,2:]=B
u=S.symbols('a b c d e f g h')
aa,bb,cc,dd,ee,ff,gg,hh=u
U=S.Matrix([[aa,0,bb,cc],[0,dd,ee,ff],[bb,ee,gg,0],[cc,ff,0,hh]])
M=S.ones(4)+x*A+y*D+z*U
p=S.Poly(S.expand(sum(S.prod(M[i,pm[i]] for i in range(4)) for pm in itertools.permutations(range(4)))-24),x,y,z)
lin=[co for mon,co in p.terms() if mon[2]==1]
print('linear',lin,flush=True)
ls=S.linsolve(lin,u)
print('linear solutions',ls,flush=True)
sol=list(ls)[0]
eq=[S.factor(co.subs(dict(zip(u,sol)))) for mon,co in p.terms() if mon[2]>1]
eq=[a for a in eq if a!=0]
params=sorted(set().union(*(e.free_symbols for e in eq)),key=str)
print('parameters',params,flush=True)
print('directions',S.simplify(U.subs(dict(zip(u,sol)))),flush=True)
for e in eq:print('equation',e,flush=True)
for param in params:
 print('CHART',param,flush=True)
 es=[S.expand(e.subs(param,1)) for e in eq]
 ps=[v for v in params if v!=param]
 G=S.groebner(es,*ps,extension=h)
 print(G,flush=True)
 for g in G.polys:print(g.as_expr(),flush=True)
 if list(G)!=[1]:print('SOLUTIONS',S.solve_poly_system(list(G),*ps),flush=True)
