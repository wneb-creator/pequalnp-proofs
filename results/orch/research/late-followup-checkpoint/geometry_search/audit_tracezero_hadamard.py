import json,itertools,time
from pathlib import Path
from sympy.polys.rings import ring
from sympy.polys.domains import QQ

base=Path('/tmp/oec/pequalnp-pilot-78');start=time.monotonic()
data=json.loads((base/'construct_search/tracezero-hadamard.json').read_text())
R,*xs=ring(','.join(data['variables']),QQ);p=xs[:6];bs=xs[6:10];k,l=xs[10:]
D=[(R.one,R.zero),(R.zero,R.one),(k,l)]
P=[tuple(p[2*i:2*i+2]) for i in range(3)]
B=[tuple(bs[:2]),tuple(bs[2:]),(-bs[0]-bs[2],-bs[1]-bs[3])]
zero=(R.zero,R.zero)
Tp=[[zero for j in range(4)] for i in range(4)]
for i in range(3):
 Tp[i+1][i+1]=B[i]
 Tp[0][i+1]=Tp[i+1][0]=tuple((P[i][j]-D[i][j])/2 for j in range(2))
for i,(a,b) in enumerate([(2,3),(1,3),(1,2)]):Tp[a][b]=Tp[b][a]=tuple((3*D[i][j]-P[i][j])/2 for j in range(2))
H=[[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]]
T=[[tuple(sum(H[i][a]*H[j][b]*Tp[a][b][v] for a in range(4) for b in range(4))/4 for v in range(2)) for j in range(4)] for i in range(4)]
assert all(T[i][j]==T[j][i] for i in range(4) for j in range(4))
assert all(sum(T[i][i][v] for i in range(4))==0 and sum(T[i][j][v] for i in range(4) for j in range(4))==0 for v in range(2))
for i,sign in enumerate([(1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1)]):
 assert all(T[i][i][v]==sum(sign[a]*D[a][v] for a in range(3))/2 for v in range(2))
def mul(a,b):
 out={}
 for ea,ca in a.items():
  for eb,cb in b.items():
   e=(ea[0]+eb[0],ea[1]+eb[1]);out[e]=out.get(e,R.zero)+ca*cb
 return out
coeff={}
for perm in itertools.permutations(range(4)):
 term={(0,0):R.one}
 for i in range(4):
  u,v=T[i][perm[i]];term=mul(term,{(0,0):R.one,(1,0):u,(0,1):v})
 for e,c in term.items():coeff[e]=coeff.get(e,R.zero)+c
assert coeff[(0,0)]==24 and coeff[(1,0)]==coeff[(0,1)]==0
for eq,m in zip(data['equations'],data['metadata']):
 exp=(m['degree']-m['t_power'],m['t_power'])
 expected=R.from_expr(__import__('sympy').sympify(eq.replace('^','**')))*QQ(m['content'])/QQ(m['denominator'])
 assert coeff[exp]==expected,exp
report={'status':'PASS','exact_polynomial_coefficients_checked':12,'method':'Independent full24-term permanent expansion using sparse polynomial arithmetic overQQ, no reliance on source Hadamard permanent formulas','symmetry_trace_tangent':True,'diagonal_map':'diag(T)=(D0+D1+D2,D0-D1-D2,-D0+D1-D2,-D0-D1+D2)/2','coverage':'Diagonal-image rank2 is equivalent toD-image rank2. Some pair ofDcoordinate restrictions is independent. TheS4 action contains permutations ofallthreeDaxes; sucha permutation andbasisnormalization giveD=(s,t,k*s+l*t). Thus thischart coversall diagonal-rank2tracezero2planes up tosimultaneousvertexpermutation.','seconds':time.monotonic()-start}
(base/'geometry_search/tracezero_hadamard_q/independent-chart-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
