from pathlib import Path
import hashlib
import json
import resource
import time
import sympy as S

resource.setrlimit(resource.RLIMIT_AS,(256*2**20,256*2**20))
resource.setrlimit(resource.RLIMIT_CPU,(15,20))
start=time.monotonic()
base=Path('/tmp/oec/pequalnp-pilot-78/geometry_search/rowzero')
source=base.parent/'full-quartic-correction.json'
data=json.loads(source.read_text())
B=S.symbols('b0:3');R=S.symbols('r0:3');D=S.symbols('d0:3')
q=S.sympify(data['Q']);c=S.sympify(data['cubic_actual']);p=S.sympify(data['quartic_actual'])
sub={**{b:0 for b in B},**{r:-3*d for r,d in zip(R,D)}}
specialized=[S.expand(f.subs(sub,simultaneous=True)) for f in [q,c,p]]
q0=3*sum(d*d for d in D)
c0=15*D[0]*D[1]*D[2]
p0=(25*sum(d**4 for d in D)+14*sum(D[i]**2*D[j]**2 for i in range(3) for j in range(i+1,3)))/16
assert all(S.expand(f-g)==0 for f,g in zip(specialized,[q0,c0,p0]))
for i in range(3):
    j,k=[l for l in range(3) if l!=i]
    rhs=S.Rational(9,4)*D[j]**4+(D[j]**2+D[k]**2)*(25*D[k]**2-11*D[j]**2)/16
    assert S.expand(p0.subs(D[i],0)-rhs)==0
assert all(S.diff(q,r)==-2*(r+3*d) for r,d in zip(R,D))
report={'status':'PASS exact identities','source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
        'scope':'Nonvanishing of at least one R-coordinate quadratic first-variation pivot on a nonzero valid B=0 kernel direction. Does not prove the remaining generic B-rank-one exclusion.',
        'specialization':'B=0,R=-3D',
        'quadratic':str(q0),'cubic':str(c0),'quartic':str(S.expand(p0)),
        'zero_coordinate_identity':'If D_i=0 and {i,j,k}={0,1,2}, P=9*D_j^4/4+(D_j^2+D_k^2)*(25*D_k^2-11*D_j^2)/16.',
        'quadratic_R_gradient':[str(S.diff(q,r)) for r in R],
        'argument':['If every R-coordinate pivot vanishes, R=-3D.',
                    'The cubic equation gives a zero D coordinate.',
                    'The quadratic gives that the other two coordinate squares sum to zero.',
                    'The verified quartic identity then gives D_j^4=0, hence D_j=0 and D_k=0 over C.',
                    'Thus D=0 and R=0, contradicting the nonzero kernel direction.'],
        'seconds':time.monotonic()-start}
(base/'trace-Bone-q-pivot.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report),flush=True)
