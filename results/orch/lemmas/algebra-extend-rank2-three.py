import sympy as s,itertools,json
from pathlib import Path
vs=s.symbols('v:9');coords=[(i,j) for i in range(4) for j in range(i,4)];T=s.zeros(4)
for v,(i,j) in zip(vs,coords[:-1]):T[i,j]=T[j,i]=v
T[3,3]=-sum(T[i,j] for i in range(4) for j in range(4));h,x,y=s.symbols('h x y')
P=s.Poly(s.expand(sum(s.prod(1+h*T[i,pi[i]] for i in range(4)) for pi in itertools.permutations(range(4)))),h)
fs=[P.coeff_monomial(h**d) for d in [2,3,4]]
A=s.Matrix([[0,1,-1,0],[1,-4,0,0],[-1,0,4,0],[0,0,0,0]]);avec=s.Matrix([A[i,j] for i,j in coords[:-1]])
assert all(f.subs(dict(zip(vs,avec)))==0 for f in fs)
M=s.Matrix([[s.diff(f,v).subs(dict(zip(vs,avec))) for v in vs] for f in fs]);print('linear rank',M.rank(),'gradients',M,flush=True)
W=M.nullspace();Q=[];done=avec
for w in W:
 if done.row_join(w).rank()>done.cols:Q.append(w);done=done.row_join(w)
w=s.symbols('w:'+str(len(Q)));bvec=s.Matrix.hstack(*Q)*s.Matrix(w);B=T.subs(dict(zip(vs,bvec)))
print('B',B,'dimension',len(Q),flush=True)
eqs=[]
for d,f in zip([2,3,4],fs):
 p=s.Poly(f.subs(dict(zip(vs,x*avec+y*bvec))),x,y)
 for mon,c in p.terms():
  if c!=0 and c not in eqs:eqs.append(s.factor(c));print(d,mon,s.factor(c),flush=True)
Path('/tmp/oec/pequalnp-pilot-79/rank2-three-extension.json').write_text(json.dumps({'variables':list(map(str,w)),'basis':[list(map(str,q)) for q in Q],'polynomials':list(map(str,eqs))}))
print('starting Groebner',flush=True)
g=s.groebner(eqs,*w,order='grevlex');print('GB',len(g.polys),'zero-dimensional',g.is_zero_dimensional,flush=True)
for p in g.polys:print(s.factor(p.as_expr()),flush=True)
