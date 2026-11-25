from engine import *
from scipy.linalg import null_space
BASE=Path('/tmp/oec/pequalnp-pilot-78/numeric')
rng=np.random.default_rng(774231)

def full_coeff(U):
 f=np.r_[U.reshape(-1),1][ALLIDX];v=np.prod(f,axis=1)
 return np.bincount(ALLCI,weights=v.real,minlength=35)+1j*np.bincount(ALLCI,weights=v.imag,minlength=35)
U=np.zeros((10,3),complex);U[1,0]=1;U[3,0]=-1;U[2,1]=1;U[3,1]=-1
assert np.max(np.abs(full_coeff(U)[1:]))==0
U=rng.normal(size=(10,3))+1j*rng.normal(size=(10,3));z=rng.normal(size=3)+1j*rng.normal(size=3)
M=np.ones((4,4),complex)
for k,(i,j) in enumerate(coords):M[i,j]=M[j,i]=1+U[k]@z
lhs=sum(np.prod([M[r,p[r]] for r in range(4)]) for p in itertools.permutations(range(4)))
rhs=sum(v*np.prod(z**np.array(e)) for v,e in zip(full_coeff(U),exps))
assert abs(lhs-rhs)<1e-8
print(json.dumps({'star_encoding_passed':True,'direct_permanent_error':abs(lhs-rhs)}),flush=True)

class GeneralChart(Chart):
 def __init__(self):
  tangent=null_space(weights.reshape(1,10))
  Q=np.linalg.qr(rng.normal(size=(9,9))+1j*rng.normal(size=(9,9)))[0]
  frame=tangent@Q;self.U0=frame[:,:3];self.N=frame[:,3:]
  self.last=None;self.idx=ALLIDX;self.ci=ALLCI
  self.deridx=[self.ci*30+np.minimum(self.idx[:,r],29) for r in range(4)]
  self.dermask=[self.idx[:,r]<30 for r in range(4)]
 def matrix(self,x):return self.U0+self.N@(x[:18]+1j*x[18:]).reshape(6,3)
 def calculate(self,x):
  if self.last is not None and np.array_equal(x,self.last):return
  U=self.matrix(x);F=np.r_[U.reshape(-1),1][self.idx];prod=np.prod(F,axis=1)
  vals=np.bincount(self.ci,weights=prod.real,minlength=35)+1j*np.bincount(self.ci,weights=prod.imag,minlength=35)
  deriv=np.zeros(35*30,complex)
  for r in range(4):
   dp=np.prod(F[:,[j for j in range(4) if j!=r]],axis=1);mask=self.dermask[r];ids=self.deridx[r][mask];dp=dp[mask]
   deriv+=np.bincount(ids,weights=dp.real,minlength=35*30)+1j*np.bincount(ids,weights=dp.imag,minlength=35*30)
  D=deriv.reshape(35,10,3)[active]
  J=np.einsum('rsk,si->rik',D,self.N).reshape(31,18)/scales[:,None]
  v=vals[active]/scales
  self.f=np.r_[v.real,v.imag];self.j=np.block([[J.real,-J.imag],[J.imag,J.real]])
  self.vals=vals;self.last=x.copy()

c=GeneralChart();x=rng.normal(size=36)*0.3;v=rng.normal(size=36);eps=1e-6
err=np.max(np.abs((c.fun(x+eps*v)-c.fun(x-eps*v))/(2*eps)-c.jac(x)@v))
assert err<1e-6,err
print(json.dumps({'general_jacobian_error':err}),flush=True)
start=time.monotonic();best=float('inf');charts=list(itertools.combinations(range(10),3));rng.shuffle(charts)
for attempt in range(5000):
 general=attempt%4==0
 chart=GeneralChart() if general else Chart(charts[rng.integers(len(charts))])
 scale=[0.1,0.5,2,5,20,100][(attempt//4)%6]
 x0=rng.normal(size=36)*scale
 result=least_squares(chart.fun,x0,jac=chart.jac,method='lm',max_nfev=1000,ftol=1e-13,xtol=1e-13,gtol=1e-13)
 residual=float(np.max(np.abs(chart.fun(result.x))))
 U=chart.matrix(result.x)
 row={'attempt':attempt,'seconds':round(time.monotonic()-start,3),'general_chart':general,'pivots':None if general else chart.pivots,'scale':scale,'max_residual':residual,'cost':float(result.cost),'nfev':result.nfev,'norm':float(np.linalg.norm(result.x)),'optimality':float(result.optimality),'singular_values':np.linalg.svd(U,compute_uv=False).tolist()}
 if residual<best:
  best=residual;row['U_real']=U.real.tolist();row['U_imag']=U.imag.tolist()
  (BASE/'best-more.json').write_text(json.dumps(row,indent=2));print(json.dumps({'new_best':{k:v for k,v in row.items() if not k.startswith('U_')}}),flush=True)
 if residual<1e-8:
  row['U_real']=U.real.tolist();row['U_imag']=U.imag.tolist()
  (BASE/f'candidate-more-{attempt}.json').write_text(json.dumps(row,indent=2));print(json.dumps({'CANDIDATE':row}),flush=True);break
 if attempt%25==0:print(json.dumps({'progress':row,'best':best}),flush=True)
 with (BASE/'runs-more.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
print(json.dumps({'finished':attempt+1,'seconds':time.monotonic()-start,'best':best}),flush=True)
