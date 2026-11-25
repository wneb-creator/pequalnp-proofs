from pathlib import Path
from itertools import combinations
import hashlib,json,resource,time
import sympy as S
from sympy.polys.rings import ring
from sympy.polys.domains import QQ

resource.setrlimit(resource.RLIMIT_AS,(384*2**20,384*2**20))
resource.setrlimit(resource.RLIMIT_CPU,(60,65))
start=time.monotonic()
base=Path('/tmp/oec/pequalnp-pilot-78/geometry_search')
R,*variables=ring('b0,b1,b2,r0,r1,r2,d0,d1,d2',QQ)
B=variables[:3];rr=variables[3:6];D=variables[6:]
H=[[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]]
M=[[R.zero for j in range(4)] for i in range(4)]
for i in range(3):
    M[i+1][i+1]=B[i]
    M[0][i+1]=M[i+1][0]=(rr[i]+2*D[i])/2
for i,(j,k) in enumerate([(2,3),(1,3),(1,2)]):M[j][k]=M[k][j]=-rr[i]/2
T=[[sum(H[i][a]*H[j][b]*M[a][b] for a in range(4) for b in range(4))/4 for j in range(4)] for i in range(4)]
coeff=[R.zero]*5
for size in range(1,5):
    for cols in combinations(range(4),size):
        rowpoly=[R.one]
        for i in range(4):
            linear=sum(T[i][j] for j in cols)
            nxt=[R.zero]*(len(rowpoly)+1)
            for d,a in enumerate(rowpoly):
                nxt[d]+=size*a;nxt[d+1]+=linear*a
            rowpoly=nxt
        for d,a in enumerate(rowpoly):coeff[d]+=(-1)**(4-size)*a
assert coeff[0]==24 and coeff[1]==0
Q=sum(B[i]**2-rr[i]**2-6*rr[i]*D[i]-6*D[i]**2 for i in range(3))
assert coeff[2]==Q
rp=[rr[i]+D[i] for i in range(3)]
dot=sum(rp[i]*D[i] for i in range(3));dsq=sum(d*d for d in D)
compact=(dot+dsq/2)**2+sum(D[i]**2*rp[i]**2 for i in range(3))/4-sum(D[i]**2*D[j]**2 for i in range(3) for j in range(i+1,3))/4
compact+=sum(B[i]*D[i]*rr[(i+1)%3]*rr[(i+2)%3] for i in range(3))/2
compact-=sum(B[i]**2*D[i]**2 for i in range(3))/4
compact-=sum(B[i]*B[j]*D[k]*rr[k] for i,j,k in [(0,1,2),(0,2,1),(1,2,0)])/2
delta=coeff[4]-Q**2/16-Q*(dot/2+dsq/4)-compact
trace=sum(B)
correction,rem=divmod(delta,trace)
assert not rem
cyclic_cubic=B[0]*B[1]*B[2]+sum(B[i]*D[i]**2 for i in range(3))-rr[0]*rr[1]*rr[2]+2*sum(D[i]*D[j]*rr[k] for i,j,k in [(0,1,2),(0,2,1),(1,2,0)])+6*D[0]*D[1]*D[2]
corrC,rem=divmod(coeff[3]-cyclic_cubic,trace)
assert not rem
correction_compact=coeff[3]/4+trace*Q/16-trace**3/32+trace*dot/2
correction_compact-=sum(B[i]*D[i]*rp[i] for i in range(3))/2
correction_compact-=((rr[0]+2*D[0])*(rr[1]+2*D[1])*(rr[2]+2*D[2])-rr[0]*rr[1]*rr[2])/4
assert correction_compact==correction
result={'status':'PASS','Q':str(Q),'cubic_trace_correction':str(corrC),
        'quartic_trace_correction':str(correction),
        'quartic_trace_correction_factor':str(S.factor(correction.as_expr())),
        'cubic_trace_correction_factor':str(S.factor(corrC.as_expr())),
        'cubic_actual':str(coeff[3]),'quartic_actual':str(coeff[4]),
        'compact_quartic_mod_Q':str(compact),
        'compact_trace_correction':'Cfull/4+trace*Q/16-trace^3/32+trace*S/2-sum(B_i*D_i*(R_i+D_i))/2-(prod(R+2D)-prod(R))/4, where S=sum(D_i*(R_i+D_i))',
        'compact_trace_correction_verified':True,
        'cubic_terms':len(coeff[3]),'quartic_terms':len(coeff[4]),
        'quartic_correction_terms':len(correction),
        'scope':'Direct independent Ryser verification of compact tracezero identity plus exact trace corrections on full tangent space. No dimension or infeasibility conclusion.',
        'seconds':time.monotonic()-start}
(base/'full-quartic-correction.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result),flush=True)
