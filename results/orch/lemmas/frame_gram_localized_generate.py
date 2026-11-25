from pathlib import Path
import sympy as s,json,hashlib,resource
resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(60,60))
job=Path('/tmp/oec/pequalnp-pilot-79');source=job/'four-frame-short-net.json';digest=hashlib.sha256(source.read_bytes()).hexdigest();model=json.loads(source.read_text());names=model['variables'];assert names==['u01','u02','u03','u12','u13','u23','a','b','g','h','k'];vv=s.symbols(' '.join(names));u01,u02,u03,u12,u13,u23,a,b,g,h,k=vv;scope=dict(zip(names,vv));x,y,z=s.symbols('x y z');scope.update(x=x,y=y,z=z,Matrix=s.Matrix);M=s.sympify(model['matrix'],locals=scope);A=M.subs({x:1,y:0,z:0});B=M.subs({x:0,y:1,z:0});C=M.subs({x:0,y:0,z:1});idx=[0,2,3];T=B.extract(idx,idx)
def permanent2(T):return T[0,0]*T[1,1]+T[0,1]*T[1,0]
K=s.Matrix(3,3,lambda i,j:permanent2(T.minor_submatrix(i,j)));one=s.ones(3,1);u=s.Matrix([A[1,j]-A[1,1] for j in idx]);v=s.Matrix([C[1,j]-C[1,1] for j in idx]);n=u.cross(v);N=s.expand(sum(n));assert s.expand(N-(u01*u13-u12*u13-u01*u12))==0
alph=v.cross(one);beta=one.cross(u);assert (alph*u.T+beta*v.T+n*one.T-N*s.eye(3)).applyfunc(s.expand)==s.zeros(3)
G=[s.expand(N*K[i,j]-n[i]*(K*one)[j]-n[j]*(K*one)[i]) for i in range(3) for j in range(i,3)]
qU=s.expand((u.T*K*u)[0]);qV=s.expand((v.T*K*v)[0]);qUV=s.expand((u.T*K*v)[0]);qOne=s.expand((one.T*K*one)[0]);counter=0
for i in range(3):
 for j in range(i,3):
  assert s.expand(N*G[counter]-alph[i]*alph[j]*qU-(alph[i]*beta[j]+beta[i]*alph[j])*qUV-beta[i]*beta[j]*qV+n[i]*n[j]*qOne)==0;counter+=1
base=[s.sympify(q,locals=scope) for q in model['equations']];assert len(base)==19;target=u02*(a*a+8*a*(u02+u03)+8*(u02+u03)**2);iv=s.Symbol('iv');outvars=vv[1:]
def primitive(e,variables):return s.Poly(s.expand(e),*variables).clear_denoms()[1].primitive()[1].as_expr()
def write(label,eqs,variables):
 path=job/('frame-gram-localized-'+label+'.msolve');path.write_text(','.join(map(str,variables))+'\n1000000007\n'+',\n'.join(str(primitive(q,variables)).replace('**','^').replace(' ','') for q in eqs)+'\n');return path.name
allq=[s.expand(q.subs(u01,1)) for q in base+G];outputs=[write('base',allq,outvars),write('triangle',allq+[iv*s.expand((N*u02*u12).subs(u01,1))-1],outvars+(iv,)),write('path',[q.subs({u02:0,u13:0}) for q in allq]+[iv*u12*u23-1],tuple(v for v in outvars if v not in [u02,u13])+(iv,))]
assert hashlib.sha256(source.read_bytes()).hexdigest()==digest
payload={'classification':'Conditional localized frame equations: six Gram entry equations are valid when N is nonzero and the four Gram pairings vanish. No ideal-membership or char0 conclusion claimed.','source_sha256':digest,'variables':names,'gram_K':str(K),'u':str(u),'v':str(v),'n':str(n),'N':str(N),'gram_pairings':[str(qU),str(qV),str(qUV),str(qOne)],'gram_entry_equations':[str(q) for q in G],'target':str(target),'files':outputs};(job/'frame-gram-localized-model.json').write_text(json.dumps(payload,indent=2)+'\n');print(json.dumps({'files':outputs,'gram_terms':[len(s.Poly(q,*vv).terms()) for q in G]}),flush=True)
