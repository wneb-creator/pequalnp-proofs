from pathlib import Path
import json,mpmath as mp,itertools
source=Path('/tmp/oec/pequalnp-pilot-79/boundary_numeric.py').read_text();exec(source.split('for run in range(1000):')[0])
mp.mp.dps=90;data=json.loads((job/'boundary_numeric_best.json').read_text())
A=[mp.mpc(str(r),str(i)) for r,i in zip(data['Areal'],data['Aimag'])];B=[mp.mpc(str(r),str(i)) for r,i in zip(data['Breal'],data['Bimag'])];seed=[B[j] for j in [1,2,3,4,6]]+[A[j] for j in [1,2,4,5,6,7,8]]
DBm=mp.matrix([[int(v.real) for v in row] for row in DB]);DAm=mp.matrix([[int(v.real) for v in row] for row in DA]);B0m=mp.matrix([int(v.real) for v in B0]);A0m=mp.matrix([int(v.real) for v in A0])
def mats(c):return B0m+DBm*mp.matrix(c),A0m+DAm*mp.matrix(c)
def F(*c):
 B,A=mats(c);out=[]
 for k,fn in zip([2,3,4],funs):
  for j in range(k+1):
   q=mp.mpf(j)/k;Z=q*B+(1-q)*A;out.append(fn(*Z))
 return out

def J(*c):
 B,A=mats(c);rows=[]
 for k,df in zip([2,3,4],dfs):
  for j in range(k+1):
   q=mp.mpf(j)/k;Z=q*B+(1-q)*A;G=mp.matrix([df(*Z)]);rows.append(list(G*(q*DBm+(1-q)*DAm)))
 return mp.matrix(rows)
root=mp.findroot(F,tuple(seed),J=J,tol=mp.mpf('1e-80'),maxsteps=30)
B,A=mats(root);print('residual',mp.norm(F(*root)),flush=True)
result={'precision':90,'residual':str(mp.norm(F(*root))),'Areal':[str(mp.re(v)) for v in A],'Aimag':[str(mp.im(v)) for v in A],'Breal':[str(mp.re(v)) for v in B],'Bimag':[str(mp.im(v)) for v in B]}
(job/'boundary_refined.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2),flush=True)
