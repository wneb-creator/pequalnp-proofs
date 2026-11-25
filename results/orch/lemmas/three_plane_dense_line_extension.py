import sympy as s,itertools
from pathlib import Path
A=s.Matrix([[1,-1,s.I,-s.I],[-1,s.I,-s.I,1],[s.I,-s.I,1,-1],[-s.I,1,-1,s.I]])
z=s.symbols('z0:9');a=s.symbols('a');pos=[(0,0),(1,1),(2,2),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
B=s.zeros(4)
for v,(i,j) in zip(z,pos):B[i,j]=B[j,i]=v
B[3,3]=-sum(z[:3])-2*sum(z[3:]);M=s.ones(4)+a*A+B
f=s.Poly(s.expand(sum(s.prod(M[i,p[i]] for i in range(4)) for p in itertools.permutations(range(4))))-24,a,*z)
lineqs=[]
for i in [1,2,3]:
 eq=s.expand(sum(co*s.prod(v**p for v,p in zip(z,mon[1:])) for mon,co in f.terms() if mon[0]==i and sum(mon[1:])==1));lineqs.append(eq);print('linear',i,s.factor(eq),flush=True)
C,_=s.linear_eq_to_matrix(lineqs,z);ns=C.nullspace();print('W dim',len(ns),flush=True)
# Add B00=0 to quotient by A, whose00entry1.
C=C.col_join(s.Matrix([[1]+[0]*8]));ns=C.nullspace();print('quotient dim',len(ns),flush=True)
w=s.symbols('w0:'+str(len(ns)));sub=dict(zip(z,sum((wi*ni for wi,ni in zip(w,ns)),s.zeros(9,1))))
qs=[]
for i in [0,1,2]:
 q=s.expand(sum(co*s.prod(v**p for v,p in zip(z,mon[1:])) for mon,co in f.terms() if mon[0]==i and sum(mon[1:])==2)).subs(sub).expand();qs.append(q);print('quad',i,s.factor(q),flush=True)
print('basis',s.Matrix.hstack(*ns),flush=True)
Q=[s.hessian(q,w)/2 for q in qs]
for j,q in enumerate(Q):print('rank',j,q.rank(),flush=True)
l,m,n=s.symbols('l m n');print('detpencil',s.factor((l*Q[0]+m*Q[1]+n*Q[2]).det()),flush=True)
