import json,itertools,collections,numpy as np
from pathlib import Path
p=7
planes=json.loads(Path('/tmp/oec/pequalnp-pilot-79/finite7-planes.json').read_text())
coords=[(i,j) for i in range(4) for j in range(i,4)]
def matrix(v):
 M=np.zeros((4,4),dtype=np.int64)
 for a,(i,j) in zip(v,coords[:-1]):M[i,j]=M[j,i]=a
 M[3,3]=-M.sum()%p
 return M%p
def rref(rows):
 A=np.array(rows,dtype=np.int64,copy=True)%p;i=0
 for j in range(A.shape[1]):
  idx=next((k for k in range(i,len(A)) if A[k,j]),None)
  if idx is None:continue
  A[[i,idx]]=A[[idx,i]];A[i]=A[i]*pow(int(A[i,j]),-1,p)%p
  for k in range(len(A)):
   if k!=i:A[k]=(A[k]-A[k,j]*A[i])%p
  i+=1
  if i==len(A):break
 return tuple(tuple(map(int,row)) for row in A[:i])
def rank(A):return len(rref(A))
perms=list(itertools.permutations(range(4)));orbits={};counts=collections.Counter();mins=collections.Counter();diag=collections.Counter();row=collections.Counter();ranks=collections.Counter();records=[]
for plane in planes:
 A,B=map(matrix,plane)
 ck=4-rank(np.concatenate([A,B]));counts[ck]+=1
 dr=rank([A.diagonal(),B.diagonal()]);diag[dr]+=1
 rr=rank([A.sum(axis=1),B.sum(axis=1)]);row[rr]+=1
 ds=[B]+[(A+k*B)%p for k in range(p)]
 dsr=tuple(sorted(rank(M) for M in ds));mins[min(dsr)]+=1;ranks[dsr]+=1
 orb=[]
 for perm in perms:
  mats=[M[np.ix_(perm,perm)] for M in [A,B]]
  vecs=[[int(M[i,j]) for i,j in coords[:-1]] for M in mats]
  orb.append(rref(vecs))
 key=min(orb);orbits.setdefault(key,[]).append(plane)
 records.append({'basis':plane,'common_kernel_dim':ck,'min_rank':min(dsr),'direction_ranks':dsr,'diag_rank':dr,'row_sum_rank':rr})
print('commonkernel',dict(counts));print('minrank',dict(mins));print('directionranks',dict(ranks));print('diagrank',dict(diag));print('rowsumrank',dict(row));print('S4orbits',len(orbits))
for key,members in orbits.items():
 rec=next(r for r in records if r['basis']==members[0]);print('orbit',len(members),'invariants', {k:v for k,v in rec.items() if k!='basis'},'representative',key)
Path('/tmp/oec/pequalnp-pilot-79/finite7-classification.json').write_text(json.dumps(records))
