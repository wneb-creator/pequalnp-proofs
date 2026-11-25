import sympy as s,numpy as np,itertools,json,time
from pathlib import Path
from scipy.optimize import least_squares
base=Path('/tmp/oec/pequalnp-pilot-75/gct231/fresh')
v=s.symbols('v:11');x,y=s.symbols('x y');aa=list(v[:4]);bo=list(v[4:9]);d0,d1=v[9:]
A=s.Matrix([[0,1,aa[0],aa[1]],[1,0,aa[2],aa[3]],[aa[0],aa[2],0,-1-sum(aa)],[aa[1],aa[3],-1-sum(aa),0]])
B=s.Matrix([[1,0,bo[0],bo[1]],[0,d0,bo[2],bo[3]],[bo[0],bo[2],d1,bo[4]],[bo[1],bo[3],bo[4],-1-d0-d1-2*sum(bo)]])
M=s.ones(4)+x*A+y*B
P=s.Poly(s.expand(sum(s.prod(M[i,p[i]] for i in range(4)) for p in itertools.permutations(range(4)))-24),x,y)
rows=[(mon,c) for mon,c in P.terms() if mon!=(4,0)]
assert len(rows)==11
(base/'rank1-general-equations.json').write_text(json.dumps({'parameters':list(map(str,v)),'A':[[str(a) for a in A.row(i)] for i in range(4)],'B':[[str(a) for a in B.row(i)] for i in range(4)],'equations':[{'monomial':mon,'coefficient':str(c)} for mon,c in rows]},indent=2))
expr=[c/max(abs(q) for q in s.Poly(c,*v).coeffs()) for _,c in rows]
print('compiling11 complex equations',flush=True)
fun=s.lambdify(v,s.Matrix(expr),'numpy',cse=True);jac=s.lambdify(v,s.Matrix(expr).jacobian(v),'numpy',cse=True)
cache=None;ans=None
def both(z):
 global cache,ans
 if cache is None or not np.array_equal(cache,z):
  vv=z[:11]+1j*z[11:];ff=np.asarray(fun(*vv),complex).ravel();jj=np.asarray(jac(*vv),complex)
  cache=z.copy();ans=(np.r_[ff.real,ff.imag],np.block([[jj.real,-jj.imag],[jj.imag,jj.real]]))
 return ans
def F(z):return both(z)[0]
def J(z):return both(z)[1]
rng=np.random.default_rng(23121);start=time.monotonic();best=1e99;new=[];count=0
simple=-np.eye(4)
for run in range(1000):
 zz=rng.normal(size=22)*[.1,.3,1,3][run%4]
 out=least_squares(F,zz,jac=J,method='lm',max_nfev=1000,ftol=1e-13,xtol=1e-13,gtol=1e-13)
 err=np.linalg.norm(F(out.x),np.inf);vv=out.x[:11]+1j*out.x[11:]
 dist=min(np.linalg.norm(vv[:4]-a) for a in simple)
 if err<1e-8:count+=1
 print(run,'err',err,'simple_A_distance',dist,'norm',np.linalg.norm(vv),'seconds',time.monotonic()-start,flush=True)
 if err<best:best=err
 if err<1e-10 and dist>1e-3:
  new.append({'run':run,'error':float(err),'distance':float(dist),'real':vv.real.tolist(),'imag':vv.imag.tolist()})
  (base/'rank1-general-new-seeds.json').write_text(json.dumps(new,indent=2))
  print('NEW_NON_SIMPLE_SEED',len(new),flush=True)
  if len(new)>=5:break
 if time.monotonic()-start>90:break
print('DONE roots',count,'best',best,'new_nonsimple',len(new),flush=True)
