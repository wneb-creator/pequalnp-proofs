import sympy as s, numpy as np,itertools,json,time
from pathlib import Path
start=time.time(); p=5
x=s.symbols('x:9'); h=s.symbols('h');coords=[(i,j) for i in range(4) for j in range(i,4)]
T=s.zeros(4)
for a,(i,j) in zip(x,coords[:-1]):T[i,j]=T[j,i]=a
T[3,3]=-sum(T[i,j] for i in range(4) for j in range(4))
P=s.Poly(s.expand(sum(s.prod((1+h*T[i,pi[i]]) for i in range(4)) for pi in itertools.permutations(range(4)))),h)
polys=[s.Poly(P.coeff_monomial(h**k),*x) for k in [2,3,4]]
def compileterms(poly):return [(int(c)%p,[(i,e) for i,e in enumerate(m) if e]) for m,c in poly.terms()]
terms=[compileterms(f) for f in polys]
gradterms=[[compileterms(f.diff(v)) for v in x] for f in polys]
def evaluate(ts,V):
 out=np.zeros(len(V),dtype=np.int64)
 for c,mon in ts:
  a=np.full(len(V),c,dtype=np.int64)
  for i,e in mon:a*=V[:,i].astype(np.int64)**e
  out+=a
 return (out%p).astype(np.int16)
def value(k,V):return evaluate(terms[k],V)
parts=[]
for i in range(9):
 n=p**(8-i);V=np.zeros((n,9),dtype=np.int16);V[:,i]=1;ns=np.arange(n,dtype=np.int64)
 for j in range(i+1,9):V[:,j]=ns%p;ns//=p
 parts.append(V)
V=np.concatenate(parts)
print('projectivepoints',len(V),'time',time.time()-start,flush=True)
for k in range(3):
 V=V[value(k,V)==0];print('afterconstraint',k,len(V),'time',time.time()-start,flush=True)
N=len(V);print('directions',N,flush=True)
Path('/tmp/oec/pequalnp-pilot-79/finite5-directions.json').write_text(json.dumps(V.tolist()))
G=[np.stack([evaluate(ts,V) for ts in gradterms[k]],axis=1) for k in range(3)]
print('gradientsdone',time.time()-start,flush=True)
adj=np.ones((N,N),dtype=bool)
for k in range(3):
 M=(G[k]@V.T)%p
 adj&=(M==0);adj&=(M.T==0)
 print('adjconstraint',k,int(adj.sum()),'time',time.time()-start,flush=True)
rows,cols=np.where(np.triu(adj,1));keep=value(2,(V[rows]+V[cols])%p)==0
rows=rows[keep];cols=cols[keep]
print('compatiblepairs',len(rows),'time',time.time()-start,flush=True)
def rref(rows):
 A=np.array(rows,dtype=np.int16,copy=True)%p;i=0
 for j in range(A.shape[1]):
  idx=next((k for k in range(i,len(A)) if A[k,j]),None)
  if idx is None:continue
  A[[i,idx]]=A[[idx,i]];A[i]=A[i]*pow(int(A[i,j]),-1,p)%p
  for k in range(len(A)):
   if k!=i:A[k]=(A[k]-A[k,j]*A[i])%p
  i+=1
  if i==len(A):break
 return tuple(tuple(map(int,row)) for row in A[:i])
planes={rref([V[i],V[j]]) for i,j in zip(rows,cols)}
print('distinctplanes',len(planes),flush=True)
Path('/tmp/oec/pequalnp-pilot-79/finite5-planes.json').write_text(json.dumps(list(planes)))
# A third direction C must be compatible with every point of the2-plane.
pointindex={tuple(a):i for i,a in enumerate(V)}
def normalize(a):
 k=next(i for i,v in enumerate(a) if v)
 return tuple((a*pow(int(a[k]),-1,p)%p).tolist())
adj[:]=False;adj[rows,cols]=True;adj[cols,rows]=True;np.fill_diagonal(adj,True)
three=set()
for A,B in planes:
 A=np.array(A,dtype=np.int16);B=np.array(B,dtype=np.int16)
 pis=[pointindex[normalize(B)]]+[pointindex[normalize(A+k*B)] for k in range(p)]
 mask=adj[pis].all(axis=0)
 for ci in np.where(mask)[0]:
  bas=rref([A,B,V[ci]])
  if len(bas)==3:three.add(bas)
print('threeplanes',len(three),'time',time.time()-start,flush=True)
Path('/tmp/oec/pequalnp-pilot-79/finite5-threeplanes.json').write_text(json.dumps(list(three)))
for a in sorted(three)[:10]:print(a,flush=True)
