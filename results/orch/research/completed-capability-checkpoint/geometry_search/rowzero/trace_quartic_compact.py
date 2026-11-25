from pathlib import Path
from itertools import permutations
import json
import resource
import time
import sympy as S
from sympy.polys.rings import ring
from sympy.polys.domains import QQ

resource.setrlimit(resource.RLIMIT_AS,(256*2**20,256*2**20))
resource.setrlimit(resource.RLIMIT_CPU,(45,50))
start=time.monotonic()
base=Path('/tmp/oec/pequalnp-pilot-78/geometry_search/rowzero')
ring_,b0,b1,R0,R1,R2,D0,D1,D2=ring('b0,b1,R0,R1,R2,D0,D1,D2',QQ)
B=[b0,b1,-b0-b1];R=[R0,R1,R2];D=[D0,D1,D2]
H=[[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]]
U=[[ring_.zero for _ in range(4)] for _ in range(4)]
for i in range(3):
    U[i+1][i+1]=B[i]
    U[0][i+1]=U[i+1][0]=(R[i]+2*D[i])/2
for i,(j,k) in enumerate([(2,3),(1,3),(1,2)]):
    U[j][k]=U[k][j]=-R[i]/2
T=[[sum(H[i][j]*U[j][k]*H[l][k] for j in range(4) for k in range(4))/4
    for l in range(4)] for i in range(4)]
P=ring_.zero
for perm in permutations(range(4)):
    term=ring_.one
    for i,j in enumerate(perm): term*=T[i][j]
    P+=term
Q=sum(B[i]**2-R[i]**2-6*R[i]*D[i]-6*D[i]**2 for i in range(3))
r=[R[i]+D[i] for i in range(3)]
Srd=sum(r[i]*D[i] for i in range(3));Dsq=sum(d*d for d in D)
Pmod=P-Q**2/16-Q*(Srd/2+Dsq/4)
by_degree={}
for deg in range(5):
    p=ring_.from_dict({m:c for m,c in Pmod.items() if m[0]+m[1]==deg})
    by_degree[deg]=p
assert by_degree[3]==by_degree[4]==0
expected0=(Srd+Dsq/2)**2+sum(D[i]**2*r[i]**2 for i in range(3))/4-sum(D[i]**2*D[j]**2 for i in range(3) for j in range(i+1,3))/4
assert by_degree[0]==expected0
expected1=sum(B[i]*D[i]*R[(i+1)%3]*R[(i+2)%3] for i in range(3))/2
assert by_degree[1]==expected1
expected2=-sum(B[i]**2*D[i]**2 for i in range(3))/4-sum(
    B[i]*B[j]*D[k]*R[k] for i,j,k in [(0,1,2),(0,2,1),(1,2,0)])/2
assert by_degree[2]==expected2
b0s,b1s=S.symbols('b0 b1')
e2=by_degree[2].as_expr()
coeffs={str(m):str(S.factor(S.Poly(e2,b0s,b1s).coeff_monomial(m)))
        for m in [b0s*b0s,b0s*b1s,b1s*b1s]}
report={'status':'PASS','scope':'Exact quartic identity on the trace-zero tangent space; R=P_original-3D. No positivity or dimension conclusion.',
        'Q':str(Q),'Pmod_definition':'per(T)-Q^2/16-Q*(sum((R+D)*D)/2+sum(D^2)/4)',
        'Pmod_B_degree_zero':str(expected0),'Pmod_B_degree_one':str(expected1),
        'Pmod_B_degree_two_symmetric':'-sum(B_i^2*D_i^2)/4-sum_{i<j}(B_i*B_j*D_k*R_k)/2, where {i,j,k}={0,1,2}',
        'Pmod_B_degree_two_coefficients':coeffs,'Pmod_terms':len(Pmod),
        'direct_permanent_terms':len(P),'seconds':time.monotonic()-start}
(base/'trace-quartic-compact.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2),flush=True)
