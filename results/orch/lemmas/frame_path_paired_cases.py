from pathlib import Path
import sympy as s,json,itertools,resource,time
from sympy.polys.matrices import DomainMatrix
resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(120,120))
job=Path('/tmp/oec/pequalnp-pilot-79');source=json.loads((job/'four-frame-short-net.json').read_text());vv=s.symbols(' '.join(source['variables']));u01,u02,u03,u12,u13,u23,a,b,g,h,k=vv;scope=dict(zip(source['variables'],vv));r=s.Symbol('r');quads=[s.sympify(q,locals=scope) for q in source['equations'] if s.Poly(s.sympify(q,locals=scope),*vv).total_degree()==2];results=[];start=time.monotonic()
def modroot(x):return s.rem(s.expand(x),r*r-2,r)
def mons(n,d):
 if n==1:yield(d,);return
 for a in range(d+1):
  for b in mons(n-1,d-a):yield(a,)+b
for sign2,sign3 in itertools.product([1,-1],repeat=2):
 la=lambda sign:-4+2*sign*r
 aa=la(1)*u03;gg=la(-1)*u12;dd=la(sign2);ee=-la(-sign2)*u23;tt=la(sign3)*u12;HH=la(-sign3)*u03;kk=modroot(-aa-2*u03+2*u23-ee);hh=modroot(HH-kk);bb=modroot(HH-2+2*u03-dd);linear=modroot(tt+gg+hh+2*u12+2*u23-ee);sub={u01:1,u02:0,u13:0,a:aa,b:bb,g:gg,h:hh,k:kk};variables=[u03,u12,u23];qs=[modroot(q.subs(sub,simultaneous=True)) for q in quads];eliminated=None;elimination=None
 for v in [u03,u23,u12]:
  coeff=s.expand(linear).coeff(v)
  if coeff:
   eliminated=v;elimination=modroot(-(linear-coeff*v)*s.invert(coeff,r*r-2,r));variables.remove(v);qs=[modroot(q.subs(v,elimination)) for q in qs];assert modroot(linear.subs(v,elimination))==0;break
 case={'signs':[1,sign2,sign3],'substitutions':{str(v):str(x) for v,x in sub.items()},'linear':str(linear),'eliminated':str(eliminated),'elimination':str(elimination),'variables':[str(v) for v in variables],'quadratics':[str(q) for q in qs]};found=False
 for D in [2,3,4]:
  cols=[(m,p) for d in range(D+1) for m in mons(len(variables),d) for p in [0,1]];index={k:i for i,k in enumerate(cols)};rows=[];origins=[]
  for qi,q in enumerate(qs):
   degree=s.Poly(q,*variables).total_degree()
   for d in range(D-degree+1):
    for m in mons(len(variables),d):
     for p in [0,1]:
      poly=s.Poly(modroot(q*s.prod(v**e for v,e in zip(variables,m))*r**p),*variables,r);row={index[(tuple(exp[:-1]),exp[-1])]:c for exp,c in poly.terms() if c};rows.append(row);origins.append([qi,list(m),p])
  target=[s.Integer(1) if m==(0,)*len(variables) and p==0 else s.Integer(0) for m,p in cols];matrix=[[row.get(i,s.Integer(0)) for row in rows]+[target[i]] for i in range(len(cols))];dm=DomainMatrix.from_list_sympy(len(matrix),len(matrix[0]),matrix).convert_to(s.QQ);rr,pivots=dm.rref();member=len(rows) not in pivots;status={'signs':case['signs'],'degree':D,'rows':len(rows),'columns':len(cols),'rank':len(pivots),'constant_member':member};print(json.dumps(status),flush=True)
  if not member:continue
  m=rr.to_Matrix();weights=[s.Integer(0)]*len(rows)
  for i,col in enumerate(pivots):weights[col]=m[i,len(rows)]
  assert [sum(w*row.get(i,0) for w,row in zip(weights,rows) if w) for i in range(len(cols))]==target
  cert=[{'origin':o,'numerator':int(w.p),'denominator':int(w.q)} for w,o in zip(weights,origins) if w];status['support']=len(cert);status['max_bits']=max(max(abs(t['numerator']).bit_length(),t['denominator'].bit_length()) for t in cert);results.append({'case':case,'status':status,'certificate':cert});found=True;break
 if not found:results.append({'case':case,'status':{'constant_member':False}})
 (job/'frame-path-paired-exact-certificates.json').write_text(json.dumps({'classification':'exact conditional path cases after triangle removes both chords and paired-root relations hold','cases':results,'seconds':time.monotonic()-start},indent=2)+'\n')
