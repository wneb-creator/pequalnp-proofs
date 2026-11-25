import sympy as s,itertools,time
start=time.time();vs=s.symbols('x:9');coords=[(i,j) for i in range(4) for j in range(i,4)];T=s.zeros(4)
for v,(i,j) in zip(vs,coords[:-1]):T[i,j]=T[j,i]=v
T[3,3]=-sum(T[i,j] for i in range(4) for j in range(4));h=s.symbols('h')
P=s.Poly(s.expand(sum(s.prod(1+h*T[i,pi[i]] for i in range(4)) for pi in itertools.permutations(range(4)))),h)
c=P.coeff_monomial(h**3);p=P.coeff_monomial(h**4);det=s.Poly(T.det(method='domain-ge'),*vs)
d=s.trace(T);rows=[sum(T[i,j] for j in range(4)) for i in range(4)]
qs=[d*d,sum(T[i,i]**2 for i in range(4)),sum(r*r for r in rows),sum(T[i,i]*rows[i] for i in range(4)),sum(T[i,j]**2 for i in range(4) for j in range(4))]
labels=['per','trace*c']+[f'Q{i}*Q{j}' for i in range(5) for j in range(i,5)]
ps=[s.Poly(e,*vs) for e in [p,d*c]+[qs[i]*qs[j] for i in range(5) for j in range(i,5)]]
mons=sorted(set(det.monoms()).union(*(set(p.monoms()) for p in ps)))
M=s.Matrix([[p.coeff_monomial(m) for p in ps] for m in mons]);b=s.Matrix([det.coeff_monomial(m) for m in mons])
print('matrix shape',M.shape,'rank',M.rank(),'augmented rank',M.row_join(b).rank(),'seconds',time.time()-start,flush=True)
try:
 sol,params=M.gauss_jordan_solve(b)
 print('SOLUTION',list(zip(labels,sol)),'params',params,flush=True)
except ValueError as exc: print('NO IDENTITY',exc,flush=True)
