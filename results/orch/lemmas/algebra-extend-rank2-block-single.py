import sympy as s,itertools,json,time
from pathlib import Path
start=time.time();r=s.sqrt(2);vs=s.symbols('v:9');coords=[(i,j) for i in range(4) for j in range(i,4)];T=s.zeros(4)
for v,(i,j) in zip(vs,coords[:-1]):T[i,j]=T[j,i]=v
T[3,3]=-sum(T[i,j] for i in range(4) for j in range(4));h,x,y=s.symbols('h x y')
P=s.Poly(s.expand(sum(s.prod(1+h*T[i,pi[i]] for i in range(4)) for pi in itertools.permutations(range(4)))),h)
fs=[P.coeff_monomial(h**d) for d in [2,3,4]]
A=s.Matrix([[r-1,1,0,0],[1,-r-1,0,0],[0,0,0,0],[0,0,0,0]]);avec=s.Matrix([A[i,j] for i,j in coords[:-1]])
M=s.Matrix([[s.simplify(s.diff(f,v).subs(dict(zip(vs,avec)))) for v in vs] for f in fs]);print('linear rank',M.rank(),'gradients',M,flush=True)
# Choose B00=0 to fix the A-gauge, and solve linear compatibility for B01.
sol=s.solve([vs[0],(M*s.Matrix(vs))[0]],[vs[0],vs[1]],dict=True)[0];free=[v for v in vs if v not in sol];w=s.symbols('w:'+str(len(free)));bvec=s.Matrix(vs).subs(sol).subs(dict(zip(free,w))).applyfunc(s.simplify);B=T.subs(dict(zip(vs,bvec)))
print('B',B,'dimension',len(w),flush=True)
Q=[]
for wi in w:Q.append(list(map(str,[s.diff(v,wi) for v in bvec])))
eqs=[]
for d,f in zip([2,3,4],fs):
 p=s.Poly(s.expand(f.subs(dict(zip(vs,x*avec+y*bvec)))),x,y,*w,extension=r)
 xyexpr={}
 for mon,c in p.terms():xyexpr[mon[:2]]=xyexpr.get(mon[:2],0)+c*s.prod(v**e for v,e in zip(w,mon[2:]))
 for mon,c in sorted(xyexpr.items()):
  if c!=0:
   c=s.expand(c);eqs.append(c);print(d,mon,c,flush=True)
Path('/tmp/oec/pequalnp-pilot-79/rank2-block-single-extension.json').write_text(json.dumps({'variables':list(map(str,w)),'basis':Q,'polynomials':list(map(str,eqs))}))
print('seconds',time.time()-start,flush=True)
