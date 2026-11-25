from pathlib import Path
import json, itertools, collections
coords=[(i,j) for i in range(4) for j in range(i,4)]
perms=list(itertools.permutations(range(4)))
def mat(v,p):
 M=[[0]*4 for _ in range(4)]
 for a,(i,j) in zip(v,coords[:-1]): M[i][j]=M[j][i]=a
 M[3][3]=-sum(map(sum,M))%p
 return M
def prod(xs):
 o=1
 for x in xs:o*=x
 return o
def gradient(M,p):
 out=[]
 for i,j in coords:
  z=0
  for pi in perms:
   for k in range(4):
    if (k,pi[k]) in [(i,j),(j,i)]:z+=prod(M[l][pi[l]] for l in range(4) if l!=k)
  out.append(z%p)
 return out
for p in [5,7]:
 recs=json.loads(Path(f'/tmp/oec/pequalnp-pilot-79/rank2-directions-{p}.json').read_text())
 tab=collections.Counter()
 for rec in recs:
  M=mat(rec['direction'],p);g=gradient(M,p);tab[(rec['star'],rec['support_vertices'],not any(g))]+=1
  if any(g):print('NONZERO',p,rec['direction'],g)
 print('FIELD',p,'COUNTS',dict(tab))
