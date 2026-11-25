from pathlib import Path
import json,numpy as np,collections
coords=[(i,j) for i in range(4) for j in range(i,4)]
def rref(rows,p):
 A=np.array(rows,dtype=np.int64,copy=True)%p;i=0
 for j in range(A.shape[1]):
  ind=next((k for k in range(i,len(A)) if A[k,j]),None)
  if ind is None:continue
  A[[i,ind]]=A[[ind,i]];A[i]=A[i]*pow(int(A[i,j]),-1,p)%p
  for k in range(len(A)):
   if k!=i:A[k]=(A[k]-A[k,j]*A[i])%p
  i+=1
  if i==len(A):break
 return i
stars=[]
for c in range(4):
 leaves=[j for j in range(4) if j!=c];basis=[]
 for j in leaves[:2]:
  M=np.zeros((4,4),dtype=np.int64);M[c,j]=M[j,c]=1;M[c,leaves[2]]=M[leaves[2],c]=-1
  basis.append([M[i,j] for i,j in coords[:-1]])
 stars.append(basis)
for p in [5,7]:
 rs=json.loads(Path(f'/tmp/oec/pequalnp-pilot-79/fano2-jacobian-extension-{p}.json').read_text())
 table=collections.Counter();miss=[]
 for rec in rs:
  dims=[4-rref(rec['basis']+S,p) for S in stars]
  intersects=any(v>0 for v in dims)
  table[(rec['jacobian_rank'],rec['extension_kernel_dimension'],intersects)]+=1
  if rec['jacobian_rank']<12 and rec['extension_kernel_dimension']>=3 and not intersects:miss.append(rec)
 print('field',p,'table',dict(sorted(table.items())),'combined_nonstar',len(miss))
 Path(f'/tmp/oec/pequalnp-pilot-79/fano2-nonstar-exceptional-{p}.json').write_text(json.dumps(miss))
