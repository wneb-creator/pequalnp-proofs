"""Independent Ryser verification of the rank-one-diagonal pencil and extensions."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
import sympy as s
from sympy.polys.rings import ring

base=Path(__file__).resolve().parent
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
x,y,z,a,b=s.symbols('x y z a b');rt=s.sqrt(2)
A=s.Matrix([[0,1,-1,0],[1,0,0,0],[-1,0,0,0],[0,0,0,0]])
Bgen=s.Matrix([[a,0,0,1],[0,0,0,0],[0,0,0,0],[1,0,0,b]])
def ryser(M):
    return s.expand(sum((-1)**(4-mask.bit_count())*s.prod(sum(M[i,j] for j in range(4) if mask>>j&1) for i in range(4)) for mask in range(1,16)))
general=ryser(s.ones(4)+x*A+y*Bgen)
assert s.expand(general-(24+6*(a+b+2)*y+2*(a*b+1)*y*y))==0
print('GENERAL_IDENTITY',general,flush=True)
B=Bgen.subs({a:-1-rt,b:-1+rt})
assert s.expand(general.subs({a:-1-rt,b:-1+rt})-24)==0
assert s.Matrix.hstack(s.Matrix(list(A)),s.Matrix(list(B))).rank()==2
assert s.Matrix.hstack(A.diagonal().T,B.diagonal().T).rank()==1
print('CONSTANT_PERMANENT24; BASIS_RANK2; DIAGONAL_RANK1: PASS',flush=True)

cs=s.symbols('c00 c01 c02 c03 c11 c12 c13 c22 c23 c33')
C=s.zeros(4);idx=0
for i in range(4):
    for j in range(i,4):
        C[i,j]=C[j,i]=cs[idx];idx+=1
domain=s.QQ.algebraic_field(rt)
rr,*gens=ring(','.join(map(str,[x,y,z,*cs])),domain)
M=s.ones(4)+x*A+y*B+z*C
MR=[[rr.from_expr(M[i,j]) for j in range(4)] for i in range(4)]
poly=rr.zero
for mask in range(1,16):
    term=rr.one
    for i in range(4):
        term*=sum((MR[i][j] for j in range(4) if mask>>j&1),rr.zero)
    poly+=(-1)**(4-mask.bit_count())*term
poly-=24
coeff={}
for mon,c in poly.items():
    key=mon[:3]
    term=domain.to_sympy(c)*s.prod(v**e for v,e in zip(cs,mon[3:]))
    coeff[key]=coeff.get(key,0)+term
linear=[p for mon,p in coeff.items() if mon[2]==1]+[cs[1],cs[3]]
sol=next(iter(s.linsolve(linear,cs)))
subs=dict(zip(cs,sol))
expected={cs[0]:-4*rt*cs[7]-8*rt*cs[8]+(-2*rt-1)*cs[9],
          cs[1]:0,cs[2]:(-2+2*rt)*cs[7]+(-2+4*rt)*cs[8]+rt*cs[9],
          cs[3]:0,cs[4]:cs[7],cs[5]:cs[7],cs[6]:cs[8],
          cs[7]:cs[7],cs[8]:cs[8],cs[9]:cs[9]}
assert all(s.expand(subs[v]-expected[v])==0 for v in cs)
print('Normalized first variation matches three-parameter solution',subs,flush=True)
vs=(cs[7],cs[8],cs[9])
residual=list(dict.fromkeys(s.Poly(s.expand(p.subs(subs)),*vs,extension=rt).as_expr() for p in coeff.values()))
residual=[p for p in residual if p!=0]
GB=s.groebner(residual,*vs,extension=rt,order='grevlex')
print('Residual equations',residual,flush=True)
print('GROEBNER',list(GB),flush=True)
for v in vs:
    assert GB.reduce(v**4)[1]==0
    print('NILPOTENT_PARAMETER',v,'power4: PASS',flush=True)
print('This pencil has no independent third direction: PASS',flush=True)

# Set y=0 to independently verify the stronger statement for any space containing A.
star_coeff={(mon[0],mon[2]):p for mon,p in coeff.items() if mon[1]==0}
star_linear=[p for mon,p in star_coeff.items() if mon[1]==1]+[cs[1]]
star_sol=next(iter(s.linsolve(star_linear,cs)))
star_sub=dict(zip(cs,star_sol))
assert s.expand(star_sub[cs[4]]-(-cs[6]+cs[7]+cs[8]))==0
assert s.expand(star_sub[cs[5]]-(-cs[6]/2+cs[7]+cs[8]/2))==0
quartic=s.expand(star_coeff[(2,2)].subs(star_sub))
assert s.expand(quartic-(cs[6]-cs[8])**2)==0
print('STAR first variation',star_sub,flush=True)
print('STAR mixed quartic x2z2',s.factor(quartic),flush=True)
Cstar=C.subs(star_sub).subs(cs[6],cs[8])
adjusted=Cstar+Cstar[0,2]*A/2
swap=[0,2,1,3]
assert adjusted==s.Matrix(4,4,lambda i,j:adjusted[swap[i],swap[j]])
assert A==-s.Matrix(4,4,lambda i,j:A[swap[i],swap[j]])
print('Any constant-permanent space containing A is stable under(12): PASS',flush=True)
print('Combined with the previously reviewed transposition-stable three-plane exclusion, no three-plane contains A',flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True)
print('PASS',flush=True)
