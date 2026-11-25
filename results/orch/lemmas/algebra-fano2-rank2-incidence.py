from pathlib import Path
import json,numpy as np,sympy as s,itertools,collections
coords=[(i,j) for i in range(4) for j in range(i,4)]
def mat(v,p):
 M=np.zeros((4,4),dtype=np.int64)
 for a,(i,j) in zip(v,coords[:-1]):M[i,j]=M[j,i]=a
 M[3,3]=-M.sum()%p
 return M%p
def trim(a):
 a=list(a)
 while a and a[-1]==0:a.pop()
 return a
def gcd(a,b,p):
 a=trim(a);b=trim(b)
 while b:
  while len(a)>=len(b):
   c=a[-1]*pow(b[-1],-1,p)%p;k=len(a)-len(b)
   for j in range(len(b)):a[j+k]=(a[j+k]-c*b[j])%p
   a=trim(a)
  a,b=b,a
 if a:a=[v*pow(a[-1],-1,p)%p for v in a]
 return a
perms=list(itertools.permutations(range(3)))
signs=[(-1)**sum(pi[i]>pi[j] for i in range(3) for j in range(i+1,3)) for pi in perms]
def det3(M):return sum(sig*np.prod([M[i,pi[i]] for i in range(3)]) for pi,sig in zip(perms,signs))
for p in [5,7,11]:
 recs=json.loads(Path(f'/tmp/oec/pequalnp-pilot-79/fano2-jacobian-extension-{p}.json').read_text())
 V=s.Matrix([[t**j for j in range(4)] for t in range(4)])
 IV=np.array(V.inv_mod(p)).astype(np.int64)
 table=collections.Counter();miss=[]
 for rec in recs:
  A,B=[mat(v,p) for v in rec['basis']];g=[];infinity=True
  for i in range(4):
   for j in range(4):
    rs=[k for k in range(4) if k!=i];cs=[k for k in range(4) if k!=j]
    vals=[det3(((A+t*B)%p)[np.ix_(rs,cs)])%p for t in range(4)]
    coef=IV@np.array(vals)%p
    g=gcd(g,list(map(int,coef)),p)
    if det3(B[np.ix_(rs,cs)])%p:infinity=False
  has=infinity or len(g)!=1
  rec['rank2_direction_over_algebraic_closure']=has;rec['rank2_gcd']=g;rec['rank2_at_infinity']=infinity
  table[(rec['jacobian_rank'],rec['extension_kernel_dimension'],has)]+=1
  if rec['jacobian_rank']<12 and rec['extension_kernel_dimension']>=3 and not has:miss.append(rec)
 print('FIELD',p,'table',dict(sorted(table.items())),'combined_without_rank2',len(miss),flush=True)
 for rec in miss:print('MISS',rec['basis'],flush=True)
 Path(f'/tmp/oec/pequalnp-pilot-79/fano2-rank2-incidence-{p}.json').write_text(json.dumps(recs))
