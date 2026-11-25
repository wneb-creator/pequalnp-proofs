from datetime import datetime,timezone
import sympy as s
from itertools import combinations

print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
x,y=s.symbols('x y');rt=s.sqrt(2)
edges=list(combinations(range(4),2))
aa=s.symbols('a01 a02 a03 a12 a13 a23')
A=s.zeros(4)
for (i,j),a in zip(edges,aa):A[i,j]=A[j,i]=a
B=s.Matrix([[-1-rt,0,0,1],[0,0,0,0],[0,0,0,0],[1,0,0,-1+rt]])
def ryser(M):
 n=M.rows
 return s.expand(sum((-1)**(n-mask.bit_count())*s.prod(sum(M[i,j] for j in range(n) if mask>>j&1) for i in range(n)) for mask in range(1,1<<n)))
P=s.Poly(ryser(s.ones(4)+x*B+y*A)-24,x,y)
lin=[v for mon,v in P.terms() if mon[1]==1]
sol=next(iter(s.linsolve(lin,aa)));sub=dict(zip(aa,sol))
print('LINEAR_SOLUTION',sub,flush=True)
vs=sorted(set().union(*(v.free_symbols for v in sol)),key=str)
eq={mon:s.factor(s.expand(p.subs(sub)),extension=rt) for mon,p in P.terms()}
eq={mon:p for mon,p in eq.items() if p!=0}
print('PARAMETERS',vs,flush=True)
for mon,p in eq.items():print('EQUATION',mon,p,flush=True)
for lam in [-2,(10+6*rt)/7]:
    ss={aa[3]:lam*(aa[4]+aa[5])}
    print('BRANCH lambda',lam,flush=True)
    for mon,p in eq.items():
        pp=s.factor(s.expand(p.subs(ss)),extension=rt)
        if pp!=0:print('BRANCH_EQUATION',mon,pp,flush=True)
    normalized=[s.expand(p.subs(ss).subs(aa[4],1-aa[5])) for p in eq.values()]
    gb=s.groebner(normalized,aa[1],aa[5],extension=rt)
    print('NORMALIZED_SUM1_GROEBNER',list(gb),flush=True)
    if list(gb)!=[1]:print('NORMALIZED_SUM1_SOLUTIONS',s.solve_poly_system(list(gb),aa[1],aa[5]),flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True)
