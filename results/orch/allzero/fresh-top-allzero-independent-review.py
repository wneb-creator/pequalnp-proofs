from pathlib import Path
import itertools,json,hashlib,time,resource
from sympy.polys.rings import ring
from sympy.polys.domains import QQ
import sympy as s
resource.setrlimit(resource.RLIMIT_AS,(700*1024**2,700*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(45,45))
started=time.monotonic();R,*v=ring('w,x,y,z,a,b,c,l,m,n,h',QQ)
w=v[0];t=v[1:4];a=v[4:7];l,m,n=v[7:10];h=v[10];S3=range(3)
Z=[[R.zero,l,m],[-l,R.zero,n],[-m,-n,R.zero]]
ell=sum(a[i]*t[i] for i in S3)
cc=[16*a[i]-2*h-2*sum(a)*a[i]-2*sum(Z[j][i] for j in S3) for i in S3]
bb=[a[i]*ell+sum(Z[i][j]*t[j] for j in S3) for i in S3]
C=[[cc[i]*t[i] if i==j else bb[3-i-j] for j in S3] for i in S3]
S=[[R.zero]+[h*ti for ti in t]]+[[h*t[i]]+C[i] for i in S3]
M=[[h+w*S[i][j] for j in range(4)] for i in range(4)]
# Ryser expansion of per(hJ+wS), with S=hN. Independent of cofactor formulas.
P=R.zero
for mask in range(1,16):
 cols=[j for j in range(4) if mask>>j&1];term=R.one
 for i in range(4):term*=sum(M[i][j] for j in cols)
 P+=(-1)**(4-len(cols))*term
P-=24*(h+w*ell)**4

def reduce_h(poly):
 result=R.zero
 for exp,coef in poly.items():
  e=list(exp);coef*=24**(e[-1]//2);e[-1]%=2;e=tuple(e);result[e]=result.get(e,QQ.zero)+coef
 return R.from_dict({e:c for e,c in result.items() if c})
P=reduce_h(P)

def wcoeff(d):
 result=R.zero
 for exp,coef in P.items():
  if exp[0]==d:
   e=list(exp);e[0]=0;result[tuple(e)]=coef
 return result
assert not wcoeff(0) and not wcoeff(1)
f2=wcoeff(2)/24;f3=reduce_h(h*wcoeff(3))/24
f4=R.zero
for exp,coef in wcoeff(4).items():
 assert min(exp[1:4])>=1
 e=list(exp)
 for i in (1,2,3):e[i]-=1
 f4[tuple(e)]=coef/24
file=Path('/workspace/pequalnp-proofs/results/orch/lemmas/fresh_top_allzero_0.msolve');lines=file.read_text().splitlines();assert lines[:2]==['a,b,c,l,m,n,h','0']
exprs=[R.from_expr(s.sympify(q.replace('^','**'))) for q in ''.join(lines[2:]).split(',') if q]
assert exprs[0]==h*h-24
count=1
for degree,poly in ((2,f2),(3,f3),(1,f4)):
 coeffs={}
 for exp,coef in poly.items():
  alpha=exp[1:4];assert sum(alpha)==degree
  e=list(exp);e[1:4]=[0,0,0];e=tuple(e)
  if alpha not in coeffs:coeffs[alpha]=R.zero
  coeffs[alpha][e]=coeffs[alpha].get(e,QQ.zero)+coef
 actual=[coeffs[alpha] for alpha in sorted(coeffs)]
 assert [reduce_h(e) for e in exprs[count:count+len(actual)]]==actual,(degree,'equation mismatch')
 count+=len(actual)
assert count==len(exprs)==20
print(json.dumps({'independent_ryser_expansion_matches_all_20_input_equations':True,'input_sha256':hashlib.sha256(file.read_bytes()).hexdigest(),'degrees':[2,3,4],'coefficient_counts':[6,10,3],'linear_condition_identically_satisfied':True,'quartic_has_required_xyz_factor':True,'seconds':time.monotonic()-started,'scope':'conditional all-three-complementary-diagonal-restrictions-zero branch; CAS unit result is not a Lean certificate'},indent=2))
