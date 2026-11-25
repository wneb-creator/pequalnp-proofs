from pathlib import Path
import json,resource,time,sympy as s
resource.setrlimit(resource.RLIMIT_AS,(256*2**20,256*2**20));resource.setrlimit(resource.RLIMIT_CPU,(30,35))
b=Path('/tmp/oec/pequalnp-pilot-78/construct_search'); dat=json.loads((b/'extra-quartic-independent.json').read_text()); v=s.symbols('p00 p01 p02 p10 p11 p12 p20 p21 p22 b00 b01 b02 b10 b11 b12 b20 b21 b22')
f=sum(s.Rational(a,d)*s.prod(v[i] for i in m) for m,a,d in dat['terms']);start=time.monotonic();print('START',len(dat['terms']),flush=True)
c,fac=s.factor_list(f,*v); print('FACTOR',c,[(s.Poly(p,*v).total_degree(),len(s.Poly(p,*v).terms()),e) for p,e in fac], 'SECONDS',time.monotonic()-start,flush=True)
# Restrictions to B=0, P=0, and diagonal P,B can reveal invariant contractions.
for name,sub in [('Bzero',{x:0 for x in v[9:]}),('Pzero',{x:0 for x in v[:9]}),('diagonal',{v[i]:0 for i in [1,2,3,5,6,7,10,11,12,14,15,16]})]:
 print(name,s.factor(f.subs(sub)),flush=True)
