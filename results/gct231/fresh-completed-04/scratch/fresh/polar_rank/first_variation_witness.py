from datetime import datetime,timezone
import sympy as s
r=s.sqrt(2);x,y,z=s.symbols('x y z')
A=s.Matrix([[0,1,0,0],[1,0,-2,1],[0,-2,0,0],[0,1,0,0]])
B=s.Matrix([[-1-r,0,0,1],[0,0,0,0],[0,0,0,0],[1,0,0,-1+r]])
C=s.Matrix([[2+r,0,1,0],[0,-9,0,0],[1,0,1,1],[0,0,1,2-r]])
swap=[0,1,3,2]
A=s.Matrix(4,4,lambda i,j:A[swap[i],swap[j]])
B=s.Matrix(4,4,lambda i,j:B[swap[i],swap[j]])
C=s.Matrix(4,4,lambda i,j:C[swap[i],swap[j]])
M=s.ones(4)+x*A+y*B+z*C
P=s.Poly(s.expand(sum((-1)**(4-mask.bit_count())*s.prod(sum(M[i,j] for j in range(4) if mask>>j&1) for i in range(4)) for mask in range(1,16))-24),x,y,z)
assert (M[0,1],M[0,2],M[0,3])==(1+x,1+y,1+z)
assert all(mon[2]>=2 for mon,coef in P.terms())
assert not P.is_zero
print('UTC',datetime.now(timezone.utc).isoformat())
print('A',A,'B',B,'C',C)
print('EXACT_REMAINDER',s.factor(P.as_expr()))
print('All pencil and first-variation coefficients vanish; canonical01,02,03 pivots are x,y,z: PASS')
print('Higher-z coefficients do not vanish; this is not a three-plane solution')
