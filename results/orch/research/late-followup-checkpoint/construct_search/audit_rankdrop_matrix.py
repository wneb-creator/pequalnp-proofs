from pathlib import Path
import sympy as s,itertools,json,collections,time,resource,hashlib
resource.setrlimit(resource.RLIMIT_AS,(512*2**20,512*2**20));resource.setrlimit(resource.RLIMIT_CPU,(60,65))
base=Path('/tmp/oec/pequalnp-pilot-78');path=base/'geometry_search/tracezero_rankdrop/matrix.json';dat=json.loads(path.read_text());v=s.symbols(' '.join(dat['variables']));p=v[:6];b=v[6:10];k,l=v[10:];Q=s.Matrix([[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]])/2

def matrix(P,B,D):
 X=[(a-d)/2 for a,d in zip(P,D)];off=[(3*d-a)/2 for a,d in zip(P,D)];T=s.Matrix([[0,X[0],X[1],X[2]],[X[0],B[0],off[2],off[1]],[X[1],off[2],B[1],off[0]],[X[2],off[1],off[0],B[2]]]);return Q*T*Q.T
A=matrix([p[0],p[2],p[4]],[b[0],b[2],-b[0]-b[2]],[s.Integer(1),s.Integer(0),k]);B=matrix([p[1],p[3],p[5]],[b[1],b[3],-b[1]-b[3]],[s.Integer(0),s.Integer(1),l]);W=[]
for j in range(7):
 ww=[s.Integer(i==j) for i in range(7)];W.append(matrix(ww[:3],ww[3:6],[s.Integer(0),s.Integer(0),ww[6]]))
for computed,given in zip([A,B],dat['AB_matrices']):assert all(s.expand(x-s.sympify(y))==0 for x,y in zip(computed,list(s.Matrix(given))))
for computed,given in zip(W,dat['W_basis']):assert all(s.expand(x-s.sympify(y))==0 for x,y in zip(computed,list(s.Matrix(given))))
start=time.monotonic();actual=[[0]*7 for _ in range(9)];exps=[tuple(x) for x in dat['parameter_exponents']]
for perm in itertools.permutations(range(4)):
 for pos in range(4):
  poly={(0,0):s.Integer(1)}
  for i,j in enumerate(perm):
   if i==pos:continue
   nxt=collections.defaultdict(lambda:s.Integer(0))
   for (u,w),co in poly.items():nxt[u,w]+=co;nxt[u+1,w]+=co*A[i,j];nxt[u,w+1]+=co*B[i,j]
   poly=nxt
  for r,exp in enumerate(exps):
   for col,V in enumerate(W):actual[r][col]+=V[pos,perm[pos]]*poly.get(exp,0)
for r in range(9):
 scale=s.sympify(dat['row_scale_to_actual_derivative'][r])
 for c in range(7):assert s.expand(actual[r][c]-scale*s.sympify(dat['matrix'][r][c]))==0,(r,c)
report={'verdict':'PASS full symbolic direct24-term permanent derivative audit','entries':63,'basis_entries':16*9,'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'seconds':time.monotonic()-start,'scope':'Exact quotient firstvariation matrix; no claim on its rank locus'};(base/'construct_search/rankdrop-matrix-audit.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)
