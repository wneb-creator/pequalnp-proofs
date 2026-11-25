from pathlib import Path
from datetime import datetime, timezone
import itertools, json
import sympy as s

base=Path(__file__).resolve().parent
xs=s.symbols('d1 d2 d3 o1 o2 o3 b1 b2 b3')
d1,d2,d3,o1,o2,o3,b1,b2,b3=xs
H=s.Matrix([[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]])/2
A=s.Matrix([[d1,o3,o2],[o3,d2,o1],[o2,o1,d3]])
bb=s.Matrix([b1,b2,b3])
M=s.zeros(4)
M[1:,1:]=A
M[0,1:]=bb.T
M[1:,0]=bb
T=H*M*H
# Ryser subset formula; compute the three homogeneous pieces directly.
components=[]
for degree in (2,3,4):
    ans=0
    for mask in range(1,16):
        size=mask.bit_count()
        rows=[sum(T[i,j] for j in range(4) if mask>>j&1) for i in range(4)]
        ans+=(-1)**(4-size)*size**(4-degree)*sum(s.prod(rows[i] for i in inds) for inds in itertools.combinations(range(4),degree))
    components.append(s.expand(ans))
Q,C,D=components
G=s.diag(1,1,1,2,2,2,-6,-6,-6)
assert s.expand(Q-(s.Matrix(xs).T*G*s.Matrix(xs))[0])==0
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
print('Q=',Q,flush=True)
print('C=',C,flush=True)
HC=s.hessian(C,xs)
triples=[HC.diff(x) for x in xs]
V=s.Matrix.hstack(*[m.reshape(81,1) for m in triples])
target=G.reshape(81,1)
print('Hessian span dimension',V.rank(),'augmented with Q',V.row_join(target).rank(),flush=True)
print('Hessian E equals Q solutions',s.linsolve((V,target)),flush=True)
Vout=V.row_join(target).rref()
if V.rank()<V.row_join(target).rank():
    # A short rational separating functional on symmetric matrices.
    for l in V.T.nullspace():
        value=(l.T*target)[0]
        if value:
            terms=[(i//9,i%9,str(v/value)) for i,v in enumerate(l) if v]
            print('Separating Hessian functional',terms,flush=True)
            break
data={'variables':list(map(str,xs)),'Q':str(Q),'C':str(C),'D':str(D)}
(base/'homogeneous.json').write_text(json.dumps(data,indent=2)+'\n')
print('C terms',len(s.Poly(C,*xs).terms()),'D terms',len(s.Poly(D,*xs).terms()),flush=True)
e=[s.eye(9)[:,i] for i in range(9)]
gradient=s.Matrix([s.diff(C,x) for x in xs])
point=dict(zip(xs,e[0]))
assert gradient.subs(point)==s.zeros(9,1)
node_hessian=HC.subs(point)
assert node_hessian.rank()==8 and node_hessian.nullspace()==[e[0]]
minor=node_hessian[1:,1:].det()
print('At e_d1: gradient zero; Hessian rank8; radial kernel; transverse determinant',minor,flush=True)
ms=s.symbols('m:9')
N=s.Matrix(3,3,ms)
det=N.det()
detpoint={x:0 for x in ms};detpoint[ms[0]]=1
det_hessian=s.hessian(det,ms).subs(detpoint)
assert det_hessian.rank()==4
print('Generic3x3 determinant at rank-one representative: Hessian rank4',flush=True)

# Define the product by <u*v,w>_Q = D^3 C(u,v,w), without normalization.
def product(u,v):
    return G.inv()*s.Matrix([(u.T*t*v)[0] for t in triples])
for i in range(3):
    assert product(e[i],e[i])==s.zeros(9,1)
for i,j,k in [(0,1,2),(0,2,1),(1,2,0)]:
    assert product(e[i],e[j])==e[k]
xx=e[0]+e[1];yy=e[0]
square=product(xx,xx)
left=product(square,product(xx,yy))
right=product(xx,product(square,yy))
assert left==s.zeros(9,1) and right==2*e[2]
print('Jordan identity failure: left=0, right=2e_d3 for x=e_d1+e_d2,y=e_d1',flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True)
