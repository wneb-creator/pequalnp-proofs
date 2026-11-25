import sympy as s,itertools,json
from pathlib import Path
a,b,c,d,e,f,u,v=s.symbols('a b c d e f u v');vs=(a,b,c,d,e,f);q=s.sqrt(2)
A=s.Matrix([[0,a,b,c],[a,0,d,e],[b,d,0,f],[c,e,f,0]])
B=s.zeros(4);B[0,0]=-1+q;B[1,1]=-1-q;B[0,1]=B[1,0]=1
M=s.ones(4)+u*A+v*B
F=s.Poly(s.expand(sum(s.prod(M[i,p[i]] for i in range(4)) for p in itertools.permutations(range(4)))-24),u,v)
coeffs=[]
for mon,coef in F.terms():
 coef=s.factor(coef,extension=q)
 print(mon,coef,flush=True);coeffs.append(coef)
linear=[c for c in coeffs if s.Poly(c,*vs,extension=q).total_degree()==1]
print('linear constraints',linear,flush=True)
sol=next(iter(s.linsolve(linear,vs)));print('linear solution',sol,flush=True)
sub=dict(zip(vs,sol));res=sorted(set(s.factor(s.expand(c.subs(sub,simultaneous=True)),extension=q) for c in coeffs)-{s.Integer(0)},key=str)
print('residuals',len(res),flush=True)
for r in res:print(r,flush=True)
free=sorted(set().union(*(r.free_symbols for r in res)),key=str);print('free',free,flush=True)
G=s.groebner(res,*free,extension=q);print('Groebner',G,flush=True)
print('zero dimensional',G.is_zero_dimensional,flush=True)
for name,subst in [('f=0',{f:0,d:-e}),('f=1,S=-1/2',{f:1,d:-e-s.Rational(1,2)}),('f=1,S=(5+3sqrt2)/2',{f:1,d:-e+(5+3*q)/2})]:
 rr=[s.expand(r.subs(subst,simultaneous=True)) for r in res]
 H=s.groebner(rr,c,e,extension=q)
 print('BRANCH',name,'Groebner',list(H),flush=True)
print('COMPLETE PROJECTIVE HOLLOW DIRECTIONS (a,b,c,d,e,f):',flush=True)
for row in [(0,1,-1,0,0,0),(0,0,0,1,-1,0),(0,1,0,1,0,-2),(0,0,1,0,1,-2)]:
 print(row,flush=True)
 assert all(s.simplify(coef.subs(dict(zip(vs,row))))==0 for coef in coeffs)
