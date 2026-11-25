from pathlib import Path
import json,numpy as np,itertools,collections,time
start=time.time();coords=[(i,j) for i in range(4) for j in range(i,4)]
def mat(v,p):
 M=np.zeros((4,4),dtype=np.int64)
 for a,(i,j) in zip(v,coords[:-1]):M[i,j]=M[j,i]=a
 M[3,3]=-M.sum()%p
 return M%p
def rank(M,p):
 A=M.copy()%p;i=0
 for j in range(A.shape[1]):
  ind=next((k for k in range(i,len(A)) if A[k,j]),None)
  if ind is None:continue
  A[[i,ind]]=A[[ind,i]];A[i]=A[i]*pow(int(A[i,j]),-1,p)%p
  for k in range(len(A)):
   if k!=i:A[k]=(A[k]-A[k,j]*A[i])%p
  i+=1
  if i==len(A):break
 return i
def normalize(v,p):
 k=next(i for i,a in enumerate(v) if a%p)
 return tuple(int(a*pow(int(v[k]),-1,p)%p) for a in v)
perms=list(itertools.permutations(range(4)))
for p in [5,7]:
 V=json.loads(Path(f'/tmp/oec/pequalnp-pilot-79/finite{p}-directions.json').read_text());counts=collections.Counter();orbits={};records=[]
 for v in V:
  M=mat(v,p);r=rank(M,p)
  if r>2:continue
  star=any(all(M[i,j]==0 for i in range(4) for j in range(4) if i!=c and j!=c) and np.all(M.diagonal()==0) for c in range(4))
  support=sum(any(M[i,j] for j in range(4)) for i in range(4))
  zero_diag=not np.any(M.diagonal());counts[(r,star,support,zero_diag)]+=1
  key=min(normalize([M[np.ix_(pi,pi)][i,j] for i,j in coords[:-1]],p) for pi in perms)
  orbits.setdefault(key,[]).append(v)
  records.append({'direction':v,'rank':r,'star':star,'support_vertices':support,'zero_diagonal':zero_diag})
 print('FIELD',p,'rank2directions',len(records),'types',dict(counts),'orbits',len(orbits),'time',time.time()-start,flush=True)
 for key,vs in sorted(orbits.items()):print('ORBIT',len(vs),'representative',key,flush=True)
 Path(f'/tmp/oec/pequalnp-pilot-79/rank2-directions-{p}.json').write_text(json.dumps(records))
