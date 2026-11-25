import sympy as s,itertools,time
from sympy.polys.rings import ring
from sympy.polys.domains import QQ_I
t,l=s.symbols('t l')
H=s.Matrix([[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]])
k=H*s.Matrix([0,1-t*t,s.I*(1+t*t),2*t])
v=k.diff(t)+l*k
assert s.expand(sum(k))==0 and s.expand((k.T*k)[0])==0
assert s.expand(sum(v))==0 and s.expand((k.T*v)[0])==0
T=k*v.T+v*k.T
rr,tt,ll=ring('t,l',QQ_I)
M=[[rr.from_expr(s.expand(T[i,j])) for j in range(4)] for i in range(4)]
cubic=rr.zero;quartic=rr.zero
for p in itertools.permutations(range(4)):
 for sel in itertools.combinations(range(4),3):
  prod=rr.one
  for i in sel:prod*=M[i][p[i]]
  cubic+=prod
 prod=rr.one
 for i in range(4):prod*=M[i][p[i]]
 quartic+=prod
C=s.factor(cubic.as_expr());Q=s.factor(quartic.as_expr())
print('cubic',C,flush=True);print('quartic',Q,flush=True)
start=time.monotonic()
result=s.factor(s.resultant(C,Q,l))
print('resultant',result,flush=True)
print('seconds',time.monotonic()-start,flush=True)
G=s.groebner([C,Q],l,t,domain=s.QQ.algebraic_field(s.I),order='grevlex')
print('basis',list(G),flush=True)
print('lex',list(G.fglm('lex')),flush=True)
