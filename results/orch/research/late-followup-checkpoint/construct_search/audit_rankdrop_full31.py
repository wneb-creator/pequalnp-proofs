from pathlib import Path
import sympy as S,json,itertools,collections,resource,time,hashlib
resource.setrlimit(resource.RLIMIT_AS,(512*2**20,512*2**20));resource.setrlimit(resource.RLIMIT_CPU,(60,65))
b=Path('/tmp/oec/pequalnp-pilot-78');path=b/'geometry_search/tracezero_rankdrop/full31-shifted.json';dat=json.loads(path.read_text());v=S.symbols(' '.join(dat['variables']));p=v[:6];bs=v[6:10];k,l=v[10:12];w=v[12:];Q=S.Matrix([[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]])/2;Z=S.Integer(0);O=S.Integer(1)
def matrix(P,B,D):
 X=[(a-d)/2 for a,d in zip(P,D)];off=[(3*d-a)/2 for a,d in zip(P,D)];T=S.Matrix([[0,X[0],X[1],X[2]],[X[0],B[0],off[2],off[1]],[X[1],off[2],B[1],off[0]],[X[2],off[1],off[0],B[2]]]);return Q*T*Q.T
A=matrix([p[0]+3,p[2],p[4]+3*k],[bs[0],bs[2],-bs[0]-bs[2]],[O,Z,k]);B=matrix([p[1],p[3]+3,p[5]+3*l],[bs[1],bs[3],-bs[1]-bs[3]],[Z,O,l]);W=matrix([w[0],w[1],w[2]+3],list(w[3:]),[Z,Z,O]);start=time.monotonic();poly=collections.defaultdict(lambda:S.Integer(0))
for mask in range(1,16):
 cols=[j for j in range(4) if mask>>j&1];term={(0,0,0):S.Integer((-1)**(4-len(cols)))}
 for i in range(4):
  co=[S.Integer(len(cols)),S.expand(sum(A[i,j] for j in cols)),S.expand(sum(B[i,j] for j in cols)),S.expand(sum(W[i,j] for j in cols))];nxt=collections.defaultdict(lambda:S.Integer(0))
  for exp,val in term.items():
   nxt[exp]+=val*co[0]
   for r in range(3):ee=list(exp);ee[r]+=1;nxt[tuple(ee)]+=val*co[r+1]
  term=nxt
 for exp,val in term.items():poly[exp]+=val
assert S.expand(poly[(0,0,0)]-24)==0
for exp in [(1,0,0),(0,1,0),(0,0,1)]:assert S.expand(poly[exp])==0
for exp,g,scale in zip(dat['parameter_exponents'],dat['generators'],dat['scales_to_actual_permanent_coefficients']):assert S.expand(poly[tuple(exp)]-S.sympify(g)*S.sympify(scale))==0,exp
r={'verdict':'PASS independent full Ryser symbolic audit','coefficients':31,'linear_coefficients':3,'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'seconds':time.monotonic()-start,'scope':'Exact shifted rank3 chart equations only; no feasibility verdict'};(b/'construct_search/rankdrop-full31-audit.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r),flush=True)
