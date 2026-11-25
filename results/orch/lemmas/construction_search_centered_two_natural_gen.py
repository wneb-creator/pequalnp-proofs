import sympy as s,itertools,json,resource,signal,time
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3))
signal.signal(signal.SIGALRM,lambda a,b: (_ for _ in ()).throw(TimeoutError('120-second limit')));signal.alarm(120)
start=time.time();R=s.Matrix(2,2,s.symbols('r0:4'));M=s.Matrix(2,2,s.symbols('m0:4'));h=s.symbols('h');x,y,z=s.symbols('x y z');v=s.Matrix([x,y]);r=R*v;w=M*v
uu=s.Matrix([x,y,w[0]]);vv=s.Matrix([r[0],r[1],w[1]]);dd=uu+vv;oo=h*(uu-vv)/2
B=s.Matrix([[dd[0],oo[2],oo[1]],[oo[2],dd[1],oo[0]],[oo[1],oo[0],dd[2]]])
H=s.Matrix([[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]])
Z=s.zeros(4);Z[1:4,1:4]=B;T=H*Z*H/4
red=lambda f:s.rem(s.Poly(s.expand(f),h),s.Poly(h*h+2,h)).as_expr()
q=red(s.trace(B*B));c=red(B.per());d=red(T.per())
qs=s.Poly(q,x,y).coeffs();cs=s.Poly(c,x,y).coeffs();ds=s.Poly(d,x,y).coeffs();polys=qs+cs+ds
assert len(qs)==3 and len(cs)==4 and len(ds)==5
params=list(R)+list(M)
for name,prime,extra in [('mod97',97,False),('rational',0,True)]:
 xs=params+([h] if extra else [])
 ps=polys+([h*h+2] if extra else [])
 if not extra:ps=[p.subs(h,17) for p in ps]
 ps=[s.Poly(p,*xs).clear_denoms()[1].primitive()[1] for p in ps]
 if prime:ps=[s.Poly(p.as_expr(),*xs,modulus=prime) for p in ps]
 lines=[','.join(map(str,xs)),str(prime)]+[str(p.as_expr()).replace('**','^')+(',' if k+1<len(ps) else '') for k,p in enumerate(ps)]
 Path('/tmp/oec/pequalnp-pilot-79/centered-two-natural-'+name+'.msolve').write_text('\n'.join(lines)+'\n')
 print(name,'variables',len(xs),'equations',len(ps),'terms',sum(len(p.terms()) for p in ps),'seconds',time.time()-start,flush=True)
Path('/tmp/oec/pequalnp-pilot-79/centered-two-natural-model.txt').write_text('Exploratory CAS model, not Lean checked.\nB = '+str(B)+'\nT=H diag(0,B) H/4. Coefficients of trace(B^2), permanent(B), permanent(T) vanish. h^2+2=0.\n')
