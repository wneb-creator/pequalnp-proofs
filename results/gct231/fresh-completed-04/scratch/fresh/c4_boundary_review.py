"""Exact scalar checks for the boundary reduction, without Groebner calls."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,itertools
import sympy as s

base=Path(__file__).resolve().parent
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
print('Parent source SHA256',hashlib.sha256((base/'c4_boundary_checks.py').read_bytes()).hexdigest(),flush=True)
e,f,a,b,H,X,Y=s.symbols('e f a b H X Y');zs=(f,a,b,H,X,Y)
alpha,beta,gamma,t=s.symbols('alpha beta gamma t')
q=6*e**2+2*f**2+a**2+b**2-H**2-X**2-Y**2-X*(a+b)+Y*(b-a)
c=2*f*a*b-2*H*X*Y+e*(-4*X**2-4*Y**2+4*X*(a+b)+4*Y*(a-b)-a*a-b*b+4*f*f)-4*e**3
G=s.hessian(q,zs)/2;Gi=G.inv()
S={e:-e,f:-f,a:b,b:a,H:H,X:X,Y:-Y}
T={e:e,f:-f,a:a,b:-b,H:H,X:Y,Y:X}
assert s.expand(q.subs(S,simultaneous=True)-q)==0
assert s.expand(c.subs(S,simultaneous=True)+c)==0
assert s.expand(q.subs(T,simultaneous=True)-q)==0
assert s.expand(c.subs(T,simultaneous=True)-c)==0
print('Both stated symmetries verified',flush=True)
grams=[]
for index,perm in enumerate(itertools.permutations((f,a,b))):
 forms=(H-alpha*perm[0],X-beta*perm[1],Y-gamma*perm[2])
 N=s.Matrix([[s.diff(ell,z) for z in zs] for ell in forms])
 col=(N*Gi*N.T)[:,0].applyfunc(s.expand)
 expect=s.Matrix([alpha**2/2-1,0,0]) if index<2 else s.Matrix([2*alpha**2/3-1,alpha/3,alpha/3 if index<4 else -alpha/3])
 assert col==expect
 print('NORMAL_H_COLUMN',index,list(col),flush=True)
 sub={e:0,H:alpha*perm[0],X:beta*perm[1],Y:gamma*perm[2]}
 M=s.hessian(s.expand(q.subs(sub,simultaneous=True)),(f,a,b))/2
 grams.append(M)
 print('GRAM3',index,M,flush=True)

# If H is paired with f, the inverse-metric normal gives the forbidden line.
n=s.Matrix([-alpha,0,0,1,0,0]);dual=Gi*n
assert dual==s.Matrix([-alpha/2,0,0,-1,0,0])
we,wf,wa,wb,wH,wX,wY=s.symbols('we wf wa wb wH wX wY')
line={e:t*we,f:1+t*wf,a:t*wa,b:t*wb,H:alpha+t*wH,X:t*wX,Y:t*wY}
assert s.expand(c.subs(line,simultaneous=True)).coeff(t,1)==4*we
print('Forbidden fH line has first cubic variation4e(w)',flush=True)

# For cases2/3, rank<=1 and nonzero beta/gamma make two rows equal/opposite.
M=grams[2]
assert M[1,0]==M[2,0]==-beta/2
assert s.expand(M[1,1]-M[2,1])==1-alpha**2+gamma/2
assert s.expand(M[1,2]-M[2,2])==gamma**2-3*gamma/2-1
assert s.factor(2*(M[1,2]-M[2,2]))==(gamma-2)*(2*gamma+1)
for value in [s.Integer(2),-s.Rational(1,2)]:
 A2=1+value/2;B2=4*value/(2*value-1)
 assert 2*value-1!=0
 assert s.expand(M.extract([0,1],[0,1]).det().subs({alpha**2:A2,beta**2:B2,gamma:value}))==0
 prod=s.factor(A2*B2*value**2)
 assert prod in [s.Rational(64,3),s.Rational(3,16)] and prod!=1
 print('CASE2 rank1 alternative',value,'alpha²',A2,'beta²',B2,'scale product squared',prod,flush=True)
M=grams[3]
assert M[1,0]==-M[2,0]==-gamma/2
assert s.expand(M[1,1]+M[2,1])==1-alpha**2-beta/2
assert s.expand(M[1,2]+M[2,2])==1-3*beta/2-beta**2
assert s.factor(-2*(M[1,2]+M[2,2]))==(beta+2)*(2*beta-1)
for value in [s.Rational(1,2),s.Integer(-2)]:
 A2=1-value/2;C2=4*value/(2*value+1)
 assert 2*value+1!=0
 assert s.expand(M.extract([0,1],[0,1]).det().subs({alpha**2:A2,gamma**2:C2,beta:value}))==0
 prod=s.factor(A2*value**2*C2)
 assert prod in [s.Rational(64,3),s.Rational(3,16)] and prod!=1
 print('CASE3 rank1 alternative',value,'alpha²',A2,'gamma²',C2,'scale product squared',prod,flush=True)

# Rank0 in H=f cases would force the incompatible scalar equations below.
for index in (0,1):
 M=grams[index]
 assert M[0,1]==M[0,2]==0 and M[0,0]==2-alpha**2
 # Case0 requires gamma=-beta; case1 requires gamma=beta.
 sign=-1 if index==0 else 1
 sub={gamma:sign*beta}
 assert s.expand(M[1,2].subs(sub))==0
 assert s.expand(M[1,1].subs(sub)-(1-beta-beta**2))==0
 assert s.expand(M[2,2].subs(sub)-(1-beta-beta**2))==0
 assert s.rem(2*beta**4-1,beta**2+beta-1,beta)==3-6*beta
 assert (beta**2+beta-1).subs(beta,s.Rational(1,2))==-s.Rational(1,4)
print('H=f rank0 scalar contradiction verified; rank1 splits into productzero or forbidden fH direction',flush=True)
aa,bb,dd,pp,qq,cc,hh=s.symbols('aa bb dd pp qq cc hh')
rank2_extension=s.Matrix([[aa,bb,0,pp],[bb,dd,0,qq],[0,0,0,cc],[pp,qq,cc,hh]])
assert s.expand(rank2_extension.det()+(aa*dd-bb**2)*cc**2)==0
print('Rank2 radical extension determinant=-(det nondegenerate2block)*radical_pairing²: PASS',flush=True)
print('Cases4/5 follow the exact S symmetry; no Groebner computation used',flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True)
print('PASS',flush=True)
