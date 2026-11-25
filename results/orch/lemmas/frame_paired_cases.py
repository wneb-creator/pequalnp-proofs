from pathlib import Path
import sympy as s,json,itertools,resource,time
resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(120,120))
job=Path('/tmp/oec/pequalnp-pilot-79');payload=json.loads((job/'four-frame-short-net.json').read_text());vv=s.symbols(' '.join(payload['variables']));u01,u02,u03,u12,u13,u23,a,b,g,h,k=vv;scope=dict(zip(payload['variables'],vv));r=s.Symbol('r');edges=[u02,u03,u12,u13,u23]
quads=[s.sympify(e,locals=scope) for e in payload['equations'] if s.Poly(s.sympify(e,locals=scope),*vv).total_degree()==2];assert len(quads)==6
def modroot(expr):return s.rem(s.expand(expr),r*r-2,r)
results=[]
for sign2,sign3 in itertools.product([1,-1],repeat=2):
 la=lambda sign:-4+2*sign*r
 aa=la(1)*(u02+u03);gg=la(-1)*(u12+u13);bb=la(sign2)*(1-u03);cc=la(-sign2)*(u12+u23);dd=la(sign3)*(1-u13);ee=la(-sign3)*(u02-u23);hh=modroot(-cc-gg-2*(u12+u13+u23));kk=modroot(-ee-aa-2*(u02+u03)+2*u23)
 substitutions={u01:1,a:aa,b:bb,g:gg,h:hh,k:kk};linear=modroot(dd+bb-hh-kk+2-2*u03-2*u13);qs=[modroot(q.subs(substitutions,simultaneous=True)) for q in quads];eliminated=None;elimination=None;left=edges[:]
 for candidate in [u23,u03,u13]:
  coefficient=s.expand(linear).coeff(candidate)
  if coefficient!=0:
   assert not coefficient.free_symbols.difference({r});inverse=s.invert(coefficient,r*r-2,r);elimination=modroot(-(linear-coefficient*candidate)*inverse);eliminated=candidate;left.remove(candidate);qs=[modroot(q.subs(candidate,elimination)) for q in qs];assert modroot(linear.subs(candidate,elimination))==0;break
 result={'signs':[1,sign2,sign3],'substitutions':{str(v):str(z) for v,z in substitutions.items()},'linear':str(linear),'eliminated':str(eliminated) if eliminated is not None else None,'elimination':str(elimination) if elimination is not None else None,'variables':[str(v) for v in left],'quadratics':[str(q) for q in qs]}
 factored=[str(s.factor(q.subs(r,s.sqrt(2)),extension=s.sqrt(2))) for q in qs];result['factored_quadratics']=factored;results.append(result);print(json.dumps(result),flush=True)
(job/'frame-paired-cases.json').write_text(json.dumps(results,indent=2)+'\n')
