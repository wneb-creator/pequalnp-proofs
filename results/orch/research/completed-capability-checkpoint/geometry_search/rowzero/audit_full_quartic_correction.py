from pathlib import Path
from itertools import permutations
import hashlib
import json
import resource
import time
import sympy as S
from sympy.polys.rings import ring
from sympy.polys.domains import QQ

resource.setrlimit(resource.RLIMIT_AS,(256*2**20,256*2**20))
resource.setrlimit(resource.RLIMIT_CPU,(30,35))
start=time.monotonic()
parent=Path('/tmp/oec/pequalnp-pilot-78/geometry_search')
base=parent/'rowzero'
source=parent/'full-quartic-correction.json'
data=json.loads(source.read_text())
R,*vars=ring('b0,b1,b2,r0,r1,r2,d0,d1,d2',QQ)
B=vars[:3];rr=vars[3:6];D=vars[6:]
H=[[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]]
U=[[R.zero for _ in range(4)] for _ in range(4)]
for i in range(3):
    U[i+1][i+1]=B[i]
    U[0][i+1]=U[i+1][0]=(rr[i]+2*D[i])/2
for i,(j,k) in enumerate([(2,3),(1,3),(1,2)]):
    U[j][k]=U[k][j]=-rr[i]/2
T=[[sum(H[i][a]*H[j][b]*U[a][b] for a in range(4) for b in range(4))/4
    for j in range(4)] for i in range(4)]
coeff=[R.zero]*5
for perm in permutations(range(4)):
    term=[R.one]
    for i,j in enumerate(perm):
        nxt=[R.zero]*(len(term)+1)
        for degree,c in enumerate(term):
            nxt[degree]+=c
            nxt[degree+1]+=c*T[i][j]
        term=nxt
    for degree,c in enumerate(term):coeff[degree]+=c
assert coeff[0]==24 and coeff[1]==0
def read(key):
    return R.from_expr(S.sympify(data[key]))
Q=read('Q');C=read('cubic_actual');P=read('quartic_actual')
assert coeff[2]==Q and coeff[3]==C and coeff[4]==P
trace=sum(B);rp=[rr[i]+D[i] for i in range(3)]
dot=sum(rp[i]*D[i] for i in range(3));Dsq=sum(d*d for d in D)
C0=B[0]*B[1]*B[2]-rr[0]*rr[1]*rr[2]+sum(B[i]*D[i]**2 for i in range(3))
C0+=2*sum(D[i]*D[j]*rr[k] for i,j,k in [(0,1,2),(0,2,1),(1,2,0)])
C0+=6*D[0]*D[1]*D[2]
assert C==C0+trace*(sum(r*r for r in rr)/2+sum(rr[i]*D[i] for i in range(3)))
K=(dot+Dsq/2)**2+sum(D[i]**2*rp[i]**2 for i in range(3))/4
K-=sum(D[i]**2*D[j]**2 for i in range(3) for j in range(i+1,3))/4
K+=sum(B[i]*D[i]*rr[(i+1)%3]*rr[(i+2)%3] for i in range(3))/2
K-=sum(B[i]**2*D[i]**2 for i in range(3))/4
K-=sum(B[i]*B[j]*D[k]*rr[k] for i,j,k in [(0,1,2),(0,2,1),(1,2,0)])/2
assert K==read('compact_quartic_mod_Q')
E=C/4+trace*Q/16-trace**3/32+trace*dot/2
E-=sum(B[i]*D[i]*rp[i] for i in range(3))/2
E-=((rr[0]+2*D[0])*(rr[1]+2*D[1])*(rr[2]+2*D[2])-rr[0]*rr[1]*rr[2])/4
assert E==read('quartic_trace_correction')
assert P==K+Q**2/16+Q*(dot/2+Dsq/4)+trace*E
report={'status':'PASS','method':'Fresh direct 24-permutation coefficient expansion, independent of the parent Ryser computation.',
        'scope':'Full tangent-space cubic and compact quartic identities, including arbitrary trace. No positivity, infeasibility, or dimension conclusion.',
        'checks':{'all_five_permanent_coefficients':True,'cubic_trace_correction':True,
                  'compact_tracezero_quartic':True,'compact_full_trace_correction':True},
        'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
        'parent_generator_sha256':hashlib.sha256((parent/'derive_full_quartic_correction.py').read_bytes()).hexdigest(),
        'seconds':time.monotonic()-start}
(base/'full-quartic-correction-independent-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report),flush=True)
