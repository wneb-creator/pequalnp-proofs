import sympy as s,numpy as np,itertools,json,time,collections
from pathlib import Path
start=time.time();xs=s.symbols('x:9');h=s.symbols('h');coords=[(i,j) for i in range(4) for j in range(i,4)]
T=s.zeros(4)
for a,(i,j) in zip(xs,coords[:-1]):T[i,j]=T[j,i]=a
T[3,3]=-sum(T[i,j] for i in range(4) for j in range(4))
P=s.Poly(s.expand(sum(s.prod(1+h*T[i,pi[i]] for i in range(4)) for pi in itertools.permutations(range(4)))),h)
polys=[s.Poly(P.coeff_monomial(h**k),*xs) for k in [2,3,4]]
def terms(poly):return [(int(c),[(i,e) for i,e in enumerate(m) if e]) for m,c in poly.terms()]
gtrs=[[terms(f.diff(v)) for v in xs] for f in polys]
def ev(ts,V,p):
 out=np.zeros(len(V),dtype=np.int64)
 for c,mon in ts:
  a=np.full(len(V),c%p,dtype=np.int64)
  for i,e in mon:a*=V[:,i]**e
  out+=a
 return out%p
def rref(rows,p):
 A=np.array(rows,dtype=np.int64,copy=True)%p;i=0;ps=[]
 for j in range(A.shape[1]):
  idx=next((k for k in range(i,len(A)) if A[k,j]),None)
  if idx is None:continue
  A[[i,idx]]=A[[idx,i]];A[i]=A[i]*pow(int(A[i,j]),-1,p)%p
  for k in range(len(A)):
   if k!=i:A[k]=(A[k]-A[k,j]*A[i])%p
  ps.append(j);i+=1
  if i==len(A):break
 return A[:i],ps
def matrix(v,p):
 M=np.zeros((4,4),dtype=np.int64)
 for a,(i,j) in zip(v,coords[:-1]):M[i,j]=M[j,i]=a
 M[3,3]=-M.sum()%p
 return M
perms=list(itertools.permutations(range(4)))
for p in [5,7,11]:
 name=f'finite{p}-planes.json' if p!=11 else 'fixed-row-finite11-planes.json'
 planes=json.loads((Path('/tmp/oec/pequalnp-pilot-79')/name).read_text())
 if p==11:
  planes=[[[(-4*sum(a*b for a,b in zip(v,[7,8,3,4,9,4,5,5])))%p,*v] for v in plane] for plane in planes]
 records=[];counts=collections.Counter();cross=collections.Counter();orbits={}
 for plane in planes:
  A,B=np.array(plane,dtype=np.int64);rows=[];kerrows=[]
  for d,gs in zip([2,3,4],gtrs):
   ts=np.arange(d+1,dtype=np.int64);D=(A[None,:]+ts[:,None]*B)%p
   G=np.stack([ev(g,D,p) for g in gs],axis=1)
   rows.append(np.concatenate([G,ts[:,None]*G%p],axis=1));kerrows.append(G[:d])
  J=np.concatenate(rows);rank=len(rref(J,p)[1]);counts[rank]+=1
  kdim=9-len(rref(np.concatenate(kerrows),p)[1]);cross[(rank,kdim)]+=1
  # Gauge tangent vectors must lie in the Jacobian kernel.
  gauge=np.array([np.concatenate([A,0*A]),np.concatenate([B,0*A]),np.concatenate([0*A,A]),np.concatenate([0*A,B])])
  assert np.all((J@gauge.T)%p==0)
  mats=[matrix(A,p),matrix(B,p)];orbit=[]
  for perm in perms:
   vs=[]
   for M in mats:
    N=M[np.ix_(perm,perm)];vs.append([N[i,j] for i,j in coords[:-1]])
   R,_=rref(vs,p);orbit.append(tuple(tuple(map(int,row)) for row in R))
  key=min(orbit);orbits.setdefault(key,[]).append((rank,kdim))
  records.append({'basis':plane,'jacobian_rank':rank,'grassmann_tangent_dimension':14-rank,'extension_kernel_dimension':kdim,'orbit_representative':key})
 print('CROSS',p,dict(sorted(cross.items())),flush=True)
 print('FIELD',p,'planes',len(planes),'ranks',dict(sorted(counts.items())),'singular',sum(v for k,v in counts.items() if k<12),'orbits',len(orbits),'time',time.time()-start,flush=True)
 for key,ranks in sorted(orbits.items()):
  assert len(set(ranks))==1
  print('ORBIT','size',len(ranks),'rank_and_Kdim',ranks[0],'representative',key,flush=True)
 (Path('/tmp/oec/pequalnp-pilot-79')/f'fano2-jacobian-extension-{p}.json').write_text(json.dumps(records))
