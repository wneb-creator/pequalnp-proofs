import numpy as np,json,itertools
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-75/gct231/fresh');rows=json.loads((base/'rank1-general-new-seeds.json').read_text())
coords=list(itertools.combinations_with_replacement(range(4),2));pm=list(itertools.permutations(range(4)))
for row in rows:
 v=np.array(row['real'])+1j*np.array(row['imag']);a=v[:4];b=v[4:9];d=v[9:]
 A=np.array([[0,1,a[0],a[1]],[1,0,a[2],a[3]],[a[0],a[2],0,-1-sum(a)],[a[1],a[3],-1-sum(a),0]])
 B=np.array([[1,0,b[0],b[1]],[0,d[0],b[2],b[3]],[b[0],b[2],d[1],b[4]],[b[1],b[3],b[4],-1-sum(d)-2*sum(b)]])
 mat=[]
 for i in range(4):
  for j in range(4-i):
   M=1+i*A+j*B;grad=np.zeros((4,4),complex)
   for p in pm:
    vals=M[np.arange(4),p]
    for k in range(4):grad[k,p[k]]+=np.prod(np.delete(vals,k))
   mat.append([grad[r,c]+(grad[c,r] if r!=c else 0) for r,c in coords])
 sv=np.linalg.svd(mat,compute_uv=False)
 print(row['run'],'singular values',sv.tolist(),flush=True)
