import sympy as s,itertools,json,time
from pathlib import Path
start=time.monotonic();base=Path(__file__).parent
x=s.symbols('a b c u v w p q r');a,b,c,u,v,w,p,q,r=x
T=s.Matrix([[a,u,v,w],[u,b,p,q],[v,p,c,r],[w,q,r,-a-b-c-2*(u+v+w+p+q+r)]])
z=s.symbols('z');full=s.Poly(s.expand(sum(s.prod(1+z*T[i,perm[i]] for i in range(4)) for perm in itertools.permutations(range(4)))-24),z)
assert full.coeff_monomial(z)==0
Q=s.Poly(full.coeff_monomial(z**2),*x).primitive()[1].as_expr()
C=s.Poly(full.coeff_monomial(z**3),*x).primitive()[1].as_expr()
F=s.Poly(full.coeff_monomial(z**4),*x).primitive()[1].as_expr()
G=s.hessian(Q,x)/2;assert G.det()!=0
Gi=G.inv();X=s.Matrix(x);grad=s.Matrix([s.diff(C,y) for y in x])
columns=[];matrices=[];labels=[]
for i,j in itertools.combinations(range(9),2):
 K=s.zeros(9);K[i,j]=1;K[j,i]=-1;A=Gi*K
 assert A.T*G+G*A==s.zeros(9)
 columns.append(s.expand((grad.T*A*X)[0]));matrices.append(A);labels.append([i,j])
columns += [C]+[s.expand(y*Q) for y in x]
polys=[s.Poly(f,*x,domain=s.QQ) for f in columns];monomials=sorted(set().union(*(set(p.monoms()) for p in polys)))
mat=s.Matrix([[p.coeff_monomial(m) for p in polys] for m in monomials])
print('GRAM_DET',G.det(),flush=True);print('CUBIC_MOD_Q_MATRIX',mat.shape,flush=True)
rank=mat.rank();ker=mat.nullspace();print('EXACT_RANK',rank,'NULLITY',len(ker),'SECONDS',time.monotonic()-start,flush=True)
report={'variables':[str(y) for y in x],'quadratic':str(Q),'cubic':str(C),'quartic':str(F),'gram':[[str(t) for t in row] for row in G.tolist()],'gram_det':str(G.det()),'matrix_shape':list(mat.shape),'matrix_rank':rank,'kernel':[[str(t) for t in v] for v in ker],'column_basis':'36 Q-skew derivations indexed by i<j, then C, then9 variables times Q','skew_pairs':labels,'seconds':time.monotonic()-start}
(base/'stabilizer.json').write_text(json.dumps(report,indent=2)+'\n')
(base/'stabilizer-matrix.json').write_text(json.dumps([[str(t) for t in row] for row in mat.tolist()])+'\n')
if len(ker)==0:print('Only scalar infinitesimal linear automorphisms preserve the quadratic and cubic ideals.',flush=True)
