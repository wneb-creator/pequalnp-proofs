import sympy as s,itertools,time,resource,signal,json
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));signal.signal(signal.SIGALRM,lambda a,b: (_ for _ in ()).throw(TimeoutError('120-second limit')));signal.alarm(120)
start=time.monotonic();job=Path('/tmp/oec/pequalnp-pilot-79');x,y=s.symbols('x y');pars=s.symbols('v0:8');coords=s.symbols('a b c f e d');a,b,c,f,e,d=coords
B=s.Matrix([[a,d,e],[d,b,f],[e,f,c]]);H=s.Matrix([[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]]);Z=s.zeros(4);Z[1:4,1:4]=B;T=H*Z*H/4
invariants=[s.trace(B*B),B.per(),T.per()]
for index,pivots in enumerate([(0,1),(3,4),(0,3),(0,4)]):
 subs={coords[pivots[0]]:x,coords[pivots[1]]:y};others=[i for i in range(6) if i not in pivots]
 subs.update({coords[i]:pars[2*j]*x+pars[2*j+1]*y for j,i in enumerate(others)})
 polys=[]
 for invariant in invariants:
  polys.extend(s.Poly(s.expand(invariant.subs(subs,simultaneous=True)),x,y).coeffs())
 polys=[s.Poly(p,*pars).clear_denoms()[1].primitive()[1] for p in polys]
 assert len(polys)==12
 lines=[','.join(map(str,pars)),'0']+[str(p.as_expr()).replace('**','^')+(',' if j+1<len(polys) else '') for j,p in enumerate(polys)]
 name='centered-two-coordinate-'+str(index)+'-rational';(job/(name+'.msolve')).write_text('\n'.join(lines)+'\n')
 print(json.dumps({'name':name,'pivots':[str(coords[i]) for i in pivots],'terms':sum(len(p.terms()) for p in polys),'seconds':time.monotonic()-start}),flush=True)
(job/'centered-two-coordinate-model.txt').write_text('CAS model only; not Lean checked.\nAll centered symmetric4x4 perturbations are H diag(0,B) H/4. B=[[a,d,e],[d,b,f],[e,f,c]]. Required invariants trace(B²),permanent(B),permanent(T) vanish on a plane. Each chart fixes two independent coordinate rows to x,y and parametrizes four remaining rows by eight variables. The 15 coordinate charts have four S3-orbits: two diagonal, two offdiagonal, diagonal+complementary offdiagonal, diagonal+other offdiagonal. Representatives (a,b),(f,e),(a,f),(a,e).\n')
