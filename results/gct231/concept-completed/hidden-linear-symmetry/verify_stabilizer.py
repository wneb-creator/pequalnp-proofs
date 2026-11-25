from pathlib import Path
import json,hashlib,itertools,sympy as s
b=Path(__file__).parent;d=json.loads((b/'stabilizer-fast.json').read_text());M=json.loads((b/'stabilizer-integer-matrix.json').read_text());rows=d['independent_rows'];A=[M[i][:] for i in rows];prev=1;sign=1;n=len(A)
for k in range(n-1):
 pivot=next(i for i in range(k,n) if A[i][k])
 if pivot!=k:A[k],A[pivot]=A[pivot],A[k];sign=-sign
 a=A[k][k]
 for i in range(k+1,n):
  for j in range(k+1,n):
   numerator=A[i][j]*a-A[i][k]*A[k][j]
   assert numerator%prev==0
   A[i][j]=numerator//prev
  A[i][k]=0
 prev=a
det=sign*A[-1][-1];assert det and det%1009
print('minor size',n,'integer determinant',det,'mod1009',det%1009,flush=True)
x=s.symbols(d['variables']);a,bb,c,u,v,w,p,q,r=x;T=s.Matrix([[a,u,v,w],[u,bb,p,q],[v,p,c,r],[w,q,r,-a-bb-c-2*(u+v+w+p+q+r)]])
for k,key in [(2,'quadratic'),(3,'cubic')]:
 rook=0
 for I in itertools.combinations(range(4),k):
  for J in itertools.combinations(range(4),k):
   rook+=sum(s.prod(T[I[i],J[perm[i]]] for i in range(k)) for perm in itertools.permutations(range(k)))
 rook*=s.factorial(4-k)
 prim=s.Poly(s.expand(rook),*x).primitive()[1].as_expr()
 expected=s.sympify(d[key],locals=dict(zip(d['variables'],x)))
 assert s.expand(prim-expected)==0
 print('independent rook coefficient PASS',key,flush=True)
out={'integer_matrix_sha256':hashlib.sha256((b/'stabilizer-integer-matrix.json').read_bytes()).hexdigest(),'scale':6,'row_indices':rows,'column_indices':list(range(46)),'exact_determinant':str(det),'determinant_mod1009':det%1009,'rook_coefficient_check':'PASS for degrees2 and3'}
(b/'stabilizer-minor-certificate.json').write_text(json.dumps(out,indent=2)+'\n')
